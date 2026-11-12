"""Backends for the open lane: a session with tools instead of one response.

- ClaudeCodeToolBackend: the Claude Code CLI headless, as core.agent.backends.claude_code, with the five
  tools attached as an MCP server (mcp_server.py) and nothing else: no built-in tools, no files, no
  project settings, no memory. The CLI runs under the user's own login; its environment has the API keys
  removed. What the CLI reports it loaded (its init event) must be exactly the session's tools (the five, or
  the seven of a python_then_lean proof round: inventory) of the cpl
  server, connected, with no skill, slash command or memory folder, and only the run's model may answer.
  Every run of the CLI is checked (a session that ran out of time on what the CLI printed until then) and
  its verdict kept next to the session's receipts (Session.log_context): a run that fails the check, or
  whose context cannot be checked, stops the run, and none of the session's proofs is counted, a resumed
  session's included (core.open_lane.records).
  The session's wall clock is open_lane.worker_seconds, started in the session (Session.start_clock) before
  each run of the CLI, with its last open_lane.notes_reserve_seconds kept for the agent's answer: no tool call
  runs into them. A run of the CLI that reaches the limit is stopped with every process under it (the tools'
  server, and a compile it was waiting for). The init event is checked as soon as the CLI prints it, and a
  session that fails is stopped there, before the agent works in it. The tools' budgets are the session's.
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
import threading
import time
from pathlib import Path

from ..agent.backends import BackendError, Response
from ..agent.backends.api import StopRun
from ..agent.backends.claude_code import (ClaudeCodeBackend, _join, _parse_output, cli_init, isolation_problems, model_events,
                                          models_used, refused, swapped)
from ..util import REPO_ROOT
from .session import Session, ToolError, kill_tree

TOOL_NAMES = ("lean_check", "run_python", "search_library", "read_file", "submit_candidate")
SERVER = "cpl"
MCP_TOOLS = tuple(f"mcp__{SERVER}__{t}" for t in TOOL_NAMES)
SYSTEM_PROMPT = (
    "You are working on a research task with five tools (lean_check, run_python, search_library, read_file and "
    "submit_candidate) and no others; you have no files of your own. Use the tools as the message says, "
    "submit what you prove, and end with the notes the message asks for, in exactly that format."
)
# A proof round of a python_then_lean run (core/open_lane/workflow.py): two more tools, and a research folder.
RESEARCH_TOOL_NAMES = TOOL_NAMES + ("research_write", "research_list")
RESEARCH_SYSTEM_PROMPT = (
    "You are working on a research task with seven tools (lean_check, run_python, search_library, read_file, "
    "submit_candidate, research_write and research_list) and no others. Your files are the research folder "
    "(Research/), which persists between your sessions, and the workspaces the message describes. Use the tools "
    "as the message says and end with the notes the message asks for, in exactly that format."
)


def mcp_tools(names) -> tuple[str, ...]:
    return tuple(f"mcp__{SERVER}__{t}" for t in names)


def inventory(session) -> tuple[tuple[str, ...], str]:
    """The tools a session's CLI must load, and its system prompt: the research inventory in a python_then_lean
    proof round, the five otherwise (the sessions after the proof rounds included)."""
    if session is not None and session.phase():
        return mcp_tools(session.tool_names()), RESEARCH_SYSTEM_PROMPT
    return MCP_TOOLS, SYSTEM_PROMPT


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


class EarlyStop(Exception):
    """A session of the CLI stopped at its init event, which fails the check; `output` is what it printed."""

    def __init__(self, reason: str, output: str):
        super().__init__(reason)
        self.output = output


def _init_problem(line: str, tools: tuple[str, ...] = MCP_TOOLS) -> str | None:
    """Why a session cannot count, read off one line of the CLI's output if it is the init event, else None."""
    init = cli_init(line)
    if init is None:
        return None
    return "; ".join(isolation_problems(init, tools, {SERVER}, required=SERVER)) or None


def _run_cli(cmd, prompt_text, env, cwd, timeout_s, early=None):
    """subprocess.run for one session of the CLI, with two differences. A session stopped at its limit, or
    interrupted, is stopped with every process under it: subprocess.run kills the CLI alone, and the tools'
    server would finish the call it was serving (a compile can take an hour) beside whatever comes next. And
    `early`, given each line the CLI prints, may return a reason to stop the session at once (the init event,
    where the CLI says what it loaded, comes before any work): EarlyStop, so that a session that cannot count
    is not worked in for hours. TimeoutExpired and EarlyStop carry what the CLI printed until then."""
    proc = subprocess.Popen(cmd, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
                            env=env, cwd=cwd)
    out, err, why = [], [], []
    expired = threading.Event()

    def feed():
        try:
            proc.stdin.write(prompt_text)
            proc.stdin.close()
        except OSError:  # the CLI ended before it read the prompt
            pass

    def expire():
        expired.set()
        kill_tree(proc.pid)

    helpers = [threading.Thread(target=feed, daemon=True), threading.Thread(target=lambda: err.append(proc.stderr.read()), daemon=True)]
    for h in helpers:
        h.start()
    timer = threading.Timer(timeout_s, expire)
    timer.daemon = True
    timer.start()
    try:
        for line in proc.stdout:
            out.append(line)
            if early is not None and not why:
                reason = early(line)
                if reason:
                    why.append(reason)
                    kill_tree(proc.pid)
        proc.wait()
    except BaseException:
        kill_tree(proc.pid)
        raise
    finally:
        timer.cancel()
        for h in helpers:
            h.join(timeout=10)
        proc.stdout.close()
        if not helpers[1].is_alive():  # a pipe still being read stays open: closing it would wait for the read
            proc.stderr.close()
    text, errors = "".join(out), "".join(err)
    if expired.is_set():
        raise subprocess.TimeoutExpired(cmd, timeout_s, output=text, stderr=errors)
    if why:
        raise EarlyStop(why[0], text)
    return subprocess.CompletedProcess(cmd, proc.returncode, text, errors)


class ClaudeCodeToolBackend(_Bound, ClaudeCodeBackend):
    name = "claude_code_tools"

    def __init__(self, cfg: dict, log=print, runner=None, **kwargs):
        super().__init__(cfg, log=log, runner=runner, **kwargs)
        self.early = runner is None
        if runner is None:  # the real CLI (checked by ClaudeCodeBackend), run so that its whole tree stops with it
            self.run = _run_cli

    def command_line(self, mcp_config: Path | None = None, session: Session | None = None) -> list[str]:
        tools, system = inventory(session)
        cmd = [self.command, "-p", "--tools", "", "--output-format", "stream-json", "--verbose", "--no-session-persistence"]
        cmd += ["--setting-sources", "", "--disable-slash-commands", "--strict-mcp-config"]
        if mcp_config is not None:
            cmd += ["--mcp-config", str(mcp_config), "--allowedTools", ",".join(tools)]
            cmd += ["--max-turns", str(int(self.cfg["open_lane"]["max_turns"]))]
        cmd += ["--system-prompt", system, "--model", self.cfg["agent_model"]]
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
        cfg = {"mcpServers": {SERVER: {"command": self.cfg["open_lane"]["python"] or shutil.which("python3") or "python3",
                                      "args": ["-c", code], "env": env}}}
        path = Path(where) / "mcp.json"
        path.write_text(json.dumps(cfg, indent=1))
        return path

    def _context(self, session: Session, out: str, timed_out: bool = False) -> dict | None:
        """One run of the CLI for this session, checked on what it printed: only the run's model answered, and the
        CLI loaded the five tools of the cpl server, connected, and nothing else. The verdict is kept next to the
        session's receipts; a run that fails, or that printed nothing to check, stops the run (StopRun), and the
        session's proofs are not counted. Returns the CLI's init event."""
        data, _ = _parse_output(out)
        events = model_events(out)
        init = cli_init(out)
        swap = swapped(events, data, self.cfg["agent_model"])
        tools, _ = inventory(session)
        problems = ([swap] if swap else []) + isolation_problems(init, tools, {SERVER}, required=SERVER)
        session.log_context({"verified": not problems, "problems": problems, "timed_out": timed_out, "cli": init})
        if swap:
            raise StopRun(f"{swap}; the run stops rather than record another model's work as {self.cfg['agent_model']}'s, "
                          "and none of this session's proofs is counted")
        if problems:
            raise StopRun(f"Claude Code ran this session with more or other than this run's {len(tools)} tools, or did not say what "
                          "it ran it with (" + "; ".join(problems) + "); none of this session's proofs is counted, and the run stops")
        return init

    def respond(self, prompt, index: int, where=None) -> Response:
        session = self.session(where)
        mcp = self.mcp_config(session, Path(where))
        cmd = self.command_line(mcp, session)
        tools, _ = inventory(session)
        t0 = time.monotonic()
        failures = []
        tries = int(self.retries["tries"])
        timeout = float(self.cfg["open_lane"]["worker_seconds"])
        reserve = float(self.cfg["open_lane"].get("notes_reserve_seconds", 0))  # a run from before the reserve has none
        events, declined, init = [], None, None
        for attempt in range(tries):
            with tempfile.TemporaryDirectory(prefix="cpl-claude-code-") as cwd:
                session.start_clock(timeout, reserve)  # read by the tools' server when the CLI starts it
                try:
                    r = self.run(cmd, prompt.text, self.env, cwd, timeout,
                                 **({"early": lambda line: _init_problem(line, tools)} if self.early else {}))
                except EarlyStop as exc:
                    # what the CLI said it loaded fails the check: stopped before the agent worked in the session
                    self._context(session, exc.output)  # keeps the verdict and stops the run
                    raise StopRun(f"Claude Code was stopped at the start of the session: {exc}") from exc
                except subprocess.TimeoutExpired as exc:
                    # the session's wall clock ran out: what it submitted stands once what the CLI printed until then
                    # shows the context it ran in; the text is what we have
                    r = None
                    init = self._context(session, _decoded(exc.stdout if exc.stdout is not None else exc.output), timed_out=True)
                    retry, what = False, f"the session did not finish within {timeout:g} s"
                except OSError as exc:
                    raise StopRun(f"could not run the Claude Code CLI: {exc}") from exc
            if r is not None:
                out = (r.stdout or "").strip()
                data, messages = _parse_output(out)
                events = model_events(out)
                failed = r.returncode != 0 or not isinstance(data, dict) or bool(data.get("is_error"))
                if failed and cli_init(out) is None and not messages:
                    # the CLI ended before it started a session (no tool can have run): nothing to check, kept as such
                    session.log_context({"verified": None, "note": "the CLI ended before it started a session"})
                else:
                    init = self._context(session, out)
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
        tmp.write_text(json.dumps({**data, "assistant_messages": messages, "cli_init": init}))
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
            "cli": init,  # what the CLI reported it loaded (checked above)
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


def _decoded(out) -> str:
    """What a CLI that ran out of time printed until then (bytes from subprocess, or text)."""
    if out is None:
        return ""
    return out.decode("utf-8", errors="replace") if isinstance(out, bytes) else str(out)


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
        ol = self.cfg["open_lane"]
        session.start_clock(float(ol["worker_seconds"]), float(ol.get("notes_reserve_seconds", 0)))  # the tools run here, on the same clock
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
