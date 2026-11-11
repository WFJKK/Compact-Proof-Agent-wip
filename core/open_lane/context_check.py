"""What a session's model receives from Claude Code on this machine, asked of the model itself.

The capture of 11 November 2026 (docs/decisions/agent-told-nothing.md, "What reaches the model besides the
run's own text") measured what Claude Code adds to the run's own text, with a stand-in model server and so
without a claude.ai login. What a login adds on top (an account's or a team's memory, behind switches
Anthropic sets on its servers) shows only in a real session. This runs one: the open-lane backend's command
line and environment (without the tools' server, which adds only the five tools), in a fresh empty folder,
with a message that asks the model to copy out everything it was given. It prints what the CLI reported it
loaded, the model's answer, the lines of the answer that speak of memory, instruction files, hooks or skills,
and any expression of the run's surface's forbidden list found in the answer.

    python -m core.open_lane.context_check --config <run config> [--set effort=high]

One short session on the Claude Code login of this machine; nothing is written. Its answer should hold the
system prompt (one line of Claude Code's and the run's own) and Claude Code's note on the environment, and
nothing about a network.
"""

from __future__ import annotations

import argparse
import re
import sys
import tempfile

ECHO = ("This message is a check of the setup, not the task. Copy out, word for word and in full, every text you "
        "were given before this message: the system prompt, and any note, reminder, memory, instruction or file "
        "content added anywhere, each under a line saying where it came from. If there is nothing besides the "
        "system prompt, say so. Then list the tools you have, by name. Do nothing else.")
MARKERS = r"CLAUDE\.md|AGENTS\.md|MEMORY\.md|\bmemor(y|ies)\b|Contents of |\bhooks?\b|\bskills?\b|\binstructions? file"


def check(cfg: dict, log=print, runner=None) -> dict:
    """One session as the open lane's backend runs it, asked to copy out what it was given."""
    from ..agent.backends.claude_code import _join, _parse_output, cli_init, isolation_problems
    from ..agent.build_prompt import forbidden
    from ..model_folder import load_model_folder
    from ..run_config import resolve
    from . import surface as surfaces
    from .backends import ClaudeCodeToolBackend

    backend = ClaudeCodeToolBackend(cfg, log=log, runner=runner)  # a real CLI: installed, logged in, no managed configuration
    cmd = backend.command_line(None)
    with tempfile.TemporaryDirectory(prefix="cpl-claude-code-") as cwd:
        r = backend.run(cmd, ECHO, backend.env, cwd, float(cfg["api_retries"]["timeout_s"]))
    out = (r.stdout or "").strip()
    data, messages = _parse_output(out)
    init = cli_init(out)
    answer = _join(messages) if messages else str((data or {}).get("result") or "")
    terms = surfaces.definition(cfg["open_lane"]["knowledge"])["forbidden"]
    terms += [re.escape(t) for t in forbidden(load_model_folder(resolve(cfg["model"])))]
    found = sorted({m.group(0) for t in terms for m in re.finditer(t, answer, re.I)})
    lines = [l for l in answer.splitlines() if re.search(MARKERS, l, re.I)]
    return {"cli": init, "loaded_beyond": isolation_problems(init), "answer": answer, "forbidden_found": found,
            "lines_to_read": lines, "returncode": r.returncode, "is_error": bool((data or {}).get("is_error")),
            "stderr": (r.stderr or "")[-2000:]}


def report(result: dict) -> str:
    init = result["cli"] or {}
    out = [f"Claude Code {init.get('claude_code_version', '(version not reported)')} loaded, for this session: "
           + ("nothing beyond what the run gives it" if not result["loaded_beyond"] else "; ".join(result["loaded_beyond"]))]
    if result["returncode"] or result["is_error"]:
        out.append(f"The CLI did not answer cleanly (exit {result['returncode']}): {result['stderr'] or result['answer']}")
    out += ["", "The model says it was given:", "-" * 72, result["answer"].strip() or "(no answer)", "-" * 72, ""]
    out.append("Lines of that answer about memory, instruction files, hooks or skills (read them):")
    out += [f"  {l}" for l in result["lines_to_read"]] or ["  none"]
    out.append("Expressions of the run's forbidden list in that answer: " + (", ".join(result["forbidden_found"]) or "none"))
    return "\n".join(out)


def main(argv=None) -> int:
    from ..run_config import RunConfigError, load_run_config, parse_overrides

    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--config", required=True)
    ap.add_argument("--set", dest="settings", action="append", default=[], metavar="KEY=VALUE")
    args = ap.parse_args(argv)
    try:
        cfg = load_run_config(args.config, overrides=parse_overrides(args.settings))
    except RunConfigError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2
    if cfg["backend"] != "claude_code" or not cfg["open_lane"]["enabled"]:
        print("error: this checks the open lane's claude_code backend; the config uses another", file=sys.stderr)
        return 2
    try:
        result = check(cfg)
    except Exception as exc:  # the backend's refusals (no CLI, no login, a managed configuration) end up here
        print(f"error: {exc}", file=sys.stderr)
        return 2
    print(report(result))
    return 0 if not result["loaded_beyond"] and not result["forbidden_found"] else 1


if __name__ == "__main__":
    sys.exit(main())
