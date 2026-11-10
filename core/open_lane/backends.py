"""Backends for the open lane: a session with tools instead of one response.

- ClaudeCodeToolBackend: the Claude Code CLI headless, as core.agent.backends.claude_code, with the four
  tools attached as an MCP server (mcp_server.py) and nothing else: no built-in tools, no files, no
  project settings. The CLI runs under the user's own login; its environment has the API keys removed.
  The session's wall clock is open_lane.worker_seconds; the tools' budgets are the session's.
- FakeToolBackend: replays scripted tool calls from JSON files, in order, against the same session code,
  so the whole loop (tools, submissions, receipts, records, resume) runs without a model. A script is

      {"calls": [{"tool": "lean_check", "args": {...}}, ...], "response": "the final text"}

  and a string argument may be {"$file": "relative path"} to read it from a file next to the script, or
  {"$project_file": "relative path"} to read it from the Lean project.

Both need to know the run before they answer: the loop calls bind(cfg, model, entries, run_path) once.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

from ..agent.backends import BackendError, Response
from ..agent.backends.api import StopRun
from ..agent.backends.claude_code import ClaudeCodeBackend, _join, _parse_output, model_events, models_used, refused, swapped
from ..util import REPO_ROOT
from .session import Session, ToolError

TOOL_NAMES = ("lean_check", "run_python", "search_library", "read_file", "submit_candidate")
SYSTEM_PROMPT = (
    "You are working on a research task with five tools (lean_check, run_python, search_library, read_file and "
    "submit_candidate) and no others; you have no files of your own. Use the tools as the message says, "
    "submit what you prove, and end with the notes the message asks for, in exactly that format."
)


class _Bound:
    cfg: dict | None = None

    def bind(self, cfg: dict, model: str, entries: list[dict], run_path: Path) -> None:
        self.cfg, self.model, self.entries, self.run_path = cfg, model, entries, Path(run_path)

    def session(self, where) -> Session:
        if self.cfg is None:
            raise BackendError("the open-lane backend was not bound to a run")
        if where is None:
            raise BackendError("the open-lane backend needs the attempt's folder")
        return Session.create(Path(where) / "open_lane", self.cfg, self.model, self.entries, self.run_path)


class ClaudeCodeToolBackend(_Bound, ClaudeCodeBackend):
    name = "claude_code_tools"

    def command_line(self, mcp_config: Path | None = None) -> list[str]:
        cmd = [self.command, "-p", "--tools", "", "--output-format", "stream-json", "--verbose", "--no-session-persistence"]
        cmd += ["--setting-sources", "", "--disable-slash-commands", "--strict-mcp-config"]
        if mcp_config is not None:
            cmd += ["--mcp-config", str(mcp_config), "--allowedTools", ",".join(f"mcp__cpl__{t}" for t in TOOL_NAMES)]
            cmd += ["--max-turns", str(int(self.cfg["open_lane"]["max_turns"]))]
        cmd += ["--system-prompt", SYSTEM_PROMPT, "--model", self.cfg["agent_model"]]
        if self.cfg["effort"] is not None:
            cmd += ["--effort", self.cfg["effort"]]
        return cmd

    def mcp_config(self, session: Session, where: Path) -> Path:
        env = {"PYTHONDONTWRITEBYTECODE": "1"}
        elan = Path("~/.elan/bin").expanduser()
        if elan.is_dir():
            env["PATH"] = f"{elan}:{os.environ.get('PATH', '')}"
        code = (f"import sys; sys.path.insert(0, {str(REPO_ROOT)!r}); from core.open_lane.mcp_server import main; "
                f"sys.exit(main(['--session', {str(session.path)!r}]))")
        cfg = {"mcpServers": {"cpl": {"command": self.cfg["open_lane"]["python"] or shutil.which("python3") or "python3",
                                      "args": ["-c", code], "env": env}}}
        path = Path(where) / "mcp.json"
        path.write_text(json.dumps(cfg, indent=1))
        return path

    def respond(self, prompt, index: int, where=None) -> Response:
        session = self.session(where)
        mcp = self.mcp_config(session, Path(where))
        cmd = self.command_line(mcp)
        t0 = time.monotonic()
        failures = []
        tries = int(self.retries["tries"])
        timeout = float(self.cfg["open_lane"]["worker_seconds"])
        events, declined = [], None
        for attempt in range(tries):
            with tempfile.TemporaryDirectory(prefix="cpl-claude-code-") as cwd:
                try:
                    r = self.run(cmd, prompt.text, self.env, cwd, timeout)
                except subprocess.TimeoutExpired:
                    # the session's wall clock ran out: what it submitted stands; the text is what we have
                    r = None
                    retry, what = False, f"the session did not finish within {timeout:g} s"
                except OSError as exc:
                    raise StopRun(f"could not run the Claude Code CLI: {exc}") from exc
            if r is not None:
                out = (r.stdout or "").strip()
                data, messages = _parse_output(out)
                events = model_events(out)
                swap = swapped(events, data, self.cfg["agent_model"])
                if swap:
                    raise StopRun(f"{swap}; the run stops rather than record another model's work as {self.cfg['agent_model']}'s")
                text = _join(messages) if messages else (data or {}).get("result")
                declined = refused(events)
                if declined is not None:  # what the session submitted before it stands; the loop counts refusals
                    data, text = data if isinstance(data, dict) else {}, _join(messages) if messages else ""
                    self.log(f"  Claude Code: the model declined to go on ({declined or 'no category given'})")
                    break
                if r.returncode == 0 and isinstance(data, dict) and not data.get("is_error") and text is not None:
                    break
                message = ""
                if isinstance(data, dict):
                    message = str(data.get("result") or data.get("error") or data.get("subtype") or "")
                message = message or (r.stderr or "")[-2000:] or out[-2000:] or f"exit code {r.returncode}"
                if isinstance(data, dict) and data.get("subtype") == "error_max_turns":
                    data, text = data, _join(messages) if messages else "(the session reached its turn limit)"
                    break
                retry, what = self._classify(message)
            failures.append(what)
            if not retry:
                if r is None:
                    data, messages, text = {"timed_out": True}, [], "(the session ran out of time)"
                    break
                raise StopRun(f"Claude Code stopped the run: {what}")
            if attempt + 1 >= tries:
                raise StopRun(f"Claude Code kept failing after {tries} tries; last: {what}. Resume later with `python -m core.loop resume`.")
            wait = self._wait(attempt)
            self.log(f"  Claude Code: {what}; trying again in {wait:.0f} s")
            self.sleep(wait)

        Path(where).mkdir(parents=True, exist_ok=True)
        tmp = Path(where) / "response_raw.json.tmp"
        tmp.write_text(json.dumps({**data, "assistant_messages": messages}))
        tmp.replace(Path(where) / "response_raw.json")
        usage = data.get("usage") or {}
        last_stop = messages[-1].get("stop_reason") if messages else None
        session.reload()  # the tools ran in the MCP server's process; the counters are in the saved session
        meta = {
            "backend": self.name,
            "source": data.get("session_id"),
            "model": self.cfg["agent_model"],
            "stop_reason": "refusal" if declined is not None else
                           (last_stop or data.get("stop_reason") or ("end_turn" if not data.get("is_error") else "error")),
            "stop_details": {"category": declined} if declined is not None else None,
            "models_used": models_used(data),
            "safety_stops": data.get("safety_stops"),
            "model_events": events,
            "input_tokens": int(usage.get("input_tokens") or 0),
            "output_tokens": int(usage.get("output_tokens") or 0),
            "cache_creation_input_tokens": int(usage.get("cache_creation_input_tokens") or 0),
            "cache_read_input_tokens": int(usage.get("cache_read_input_tokens") or 0),
            "cost_usd": 0.0,
            "api_equivalent_usd": data.get("total_cost_usd"),
            "num_turns": data.get("num_turns"),
            "assistant_messages": len(messages),
            "tools_used": session.state["used"],
            "submissions": len(session.receipts()),
            "request": {"command": cmd[:1] + cmd[1:10]},
            "failed_tries": failures,
            "seconds": round(time.monotonic() - t0, 1),
        }
        return Response(text=str(text), meta=meta)


class FakeToolBackend(_Bound):
    name = "fake_tools"

    def __init__(self, scripts):
        self.items: list[Path] = []
        for src in scripts:
            p = Path(src)
            if p.is_dir():
                self.items += sorted(p.glob("*.json"))
            elif p.is_file():
                self.items.append(p)
            else:
                raise BackendError(f"no scripts at {p}")

    def __len__(self) -> int:
        return len(self.items)

    def available(self, index: int) -> bool:
        return 0 <= index < len(self.items)

    @staticmethod
    def _resolve(value, base: Path, project: Path):
        """{"$file": p} reads a file next to the script; {"$project_file": p} one of the Lean project."""
        if isinstance(value, dict) and set(value) == {"$file"}:
            return (base / value["$file"]).read_text()
        if isinstance(value, dict) and set(value) == {"$project_file"}:
            return (project / value["$project_file"]).read_text()
        if isinstance(value, dict):
            return {k: FakeToolBackend._resolve(v, base, project) for k, v in value.items()}
        if isinstance(value, list):
            return [FakeToolBackend._resolve(v, base, project) for v in value]
        return value

    def respond(self, prompt, index: int, where=None) -> Response:
        if not self.available(index):
            raise BackendError(f"the fake tool backend has {len(self.items)} scripts; asked for number {index + 1}")
        path = self.items[index]
        script = json.loads(path.read_text())
        session = self.session(where)
        t0 = time.monotonic()
        outcomes = []
        for call in script.get("calls", []):
            tool, args = call["tool"], self._resolve(call.get("args", {}), path.parent, session.lean_project)
            try:
                result = session.call(tool, args)
                outcomes.append({"tool": tool, "ok": True, "status": result.get("status"), "scoring": (result.get("scoring") or {}).get("status")})
            except ToolError as exc:
                outcomes.append({"tool": tool, "ok": False, "error": str(exc)})
        text = script.get("response", "")
        meta = {"backend": self.name, "source": path.name, "input_tokens": 0, "output_tokens": 0, "cost_usd": 0.0,
                "stop_reason": "end_turn", "tool_calls": outcomes, "tools_used": session.state["used"],
                "submissions": len(session.receipts()), "seconds": round(time.monotonic() - t0, 1)}
        return Response(text=text, meta=meta)
