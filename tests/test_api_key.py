"""An open-lane run billed to an API key (`auth: api_key`, ported from the level-1 pipeline): the key from the
variable api_key_env names, never ANTHROPIC_API_KEY; the CLI under --bare with an apiKeyHelper; the key checked
before the run; what each try billed checked; and a dollar budget per run and per round, kept in the run's
spend.jsonl across tries, rounds and resumes. A stand-in CLI and stand-ins for Lean; no model, no network."""

from __future__ import annotations

import json
from pathlib import Path

import pytest
import yaml

from core import loop
from core.agent.backends import BackendError
from core.agent.backends.api import StopRun
from core.agent.build_prompt import Prompt
from core.open_lane import api_budget
from core.open_lane.backends import ClaudeCodeToolBackend, MCP_TOOLS
from core.open_lane.session import Session
from core.run_config import RunConfigError, merge
from core.util import REPO_ROOT
from tests.test_stages import A, IDENT, call, fake_project, fake_service

KEY = "sk-ant-test-0123456789"


@pytest.fixture(autouse=True)
def _surface(request):
    request.getfixturevalue("stand_in_surface")


def cfg_for(tmp_path: Path, **over) -> dict:
    project = fake_project(tmp_path)
    raw = {"run_id": "key", "model": "tests/max2_tiny", "backend": "claude_code", "rule_set": ["single", "skip"],
           "prompt_template": "open_lane_v6", "agent_model": "m", "rounds_max": 3, "runs_dir": str(tmp_path / "runs"),
           "auth": "api_key", "api_budget": {"run_usd": 10, "round_usd": 4},
           "open_lane": {"enabled": True, "lean_project": str(project), "work_dir": str(tmp_path / "work")}}
    raw.update(over)
    return merge(raw)


def init_event(source="apiKeyHelper") -> dict:
    ev = {"type": "system", "subtype": "init", "session_id": "s", "claude_code_version": "2.1.322", "model": "m",
          "tools": list(MCP_TOOLS), "mcp_servers": [{"name": "cpl", "status": "connected"}], "slash_commands": [],
          "skills": [], "apiKeySource": source}
    return {k: v for k, v in ev.items() if v is not None}


def printed(text="CLAIM: nothing", cost=1.25, subtype="success", source="apiKeySource", is_error=False, init=None) -> str:
    events = [init if init is not None else init_event(),
              {"type": "assistant", "message": {"role": "assistant", "content": [{"type": "text", "text": text}], "stop_reason": "end_turn"}},
              {"type": "result", "subtype": subtype, "is_error": is_error, "result": text, "session_id": "s", "num_turns": 1,
               "usage": {"input_tokens": 10, "output_tokens": 5}, **({"total_cost_usd": cost} if cost is not None else {})}]
    return "\n".join(json.dumps(e) for e in events) + "\n"


class Done:
    def __init__(self, stdout, returncode=0):
        self.stdout, self.stderr, self.returncode = stdout, "", returncode


def keyed(tmp_path: Path, answers: list, environ: dict | None = None, **over):
    """A ClaudeCodeToolBackend billed to a key, on a stand-in CLI that gives `answers` in turn (a text it prints, or
    an exception it raises); bound to a stand-in run. Returns the backend, the run's folder and the calls."""
    import subprocess

    cfg = cfg_for(tmp_path, **over)
    run = tmp_path / "runs" / "key"
    run.mkdir(parents=True, exist_ok=True)
    calls, it = [], iter(answers)

    def cli(cmd, prompt_text, env, cwd, timeout_s):
        calls.append({"cmd": cmd, "env": env})
        a = next(it)
        if a == "timeout":
            raise subprocess.TimeoutExpired(cmd, timeout_s, output=json.dumps(init_event()) + "\n")
        return a if isinstance(a, Done) else Done(a)

    env = {"PATH": "/usr/bin", "CPL_ANTHROPIC_KEY": KEY, "ANTHROPIC_API_KEY": "sk-not-this-one", **(environ or {})}
    b = ClaudeCodeToolBackend(cfg, log=lambda *a: None, runner=cli, sleep=lambda s: None, environ=env)
    b.bind(cfg, "tests/max2_tiny", [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64}], run)
    return b, run, calls


def respond(b, run: Path, k: int):
    where = run / f"round_{k:03d}" / "attempt_0"
    where.mkdir(parents=True, exist_ok=True)
    return b.respond(Prompt("one", "two", {}), k - 1, where=where), where


def test_the_config_names_who_pays_and_a_key_comes_with_a_budget(tmp_path):
    assert merge({"run_id": "x", "model": "tests/max2_tiny", "backend": "fake", "rule_set": ["single"]})["auth"] == "login"
    assert cfg_for(tmp_path)["api_budget"] == {"run_usd": 10, "round_usd": 4}
    for over, why in (({"backend": "fake"}, "auth api_key is for the open lane's claude_code backend"),
                      ({"api_budget": {"run_usd": 0, "round_usd": 4}}, "api_budget.run_usd must be a positive number"),
                      ({"api_budget": {"run_usd": 10}}, "api_budget.round_usd must be a positive number"),
                      ({"auth": "card"}, "auth must be login or api_key"),
                      ({"api_key_env": "ANTHROPIC_API_KEY"}, "api_key_env must not be ANTHROPIC_API_KEY")):
        with pytest.raises(RunConfigError, match=why):
            cfg_for(tmp_path / str(len(why)), **over)


def test_the_key_comes_from_its_own_variable_and_never_from_anthropic_api_key(tmp_path):
    b, run, calls = keyed(tmp_path, [printed()])
    assert b.env["CPL_ANTHROPIC_KEY"] == KEY and "ANTHROPIC_API_KEY" not in b.env and "ANTHROPIC_AUTH_TOKEN" not in b.env
    r, where = respond(b, run, 1)
    cmd = calls[0]["cmd"]
    assert cmd[:3] == ["claude", "-p", "--bare"] and json.loads(cmd[cmd.index("--settings") + 1]) == {"apiKeyHelper": "printenv CPL_ANTHROPIC_KEY"}
    assert cmd[cmd.index("--max-budget-usd") + 1] == "4.00" and KEY not in " ".join(cmd)
    code = json.loads((where / "mcp.json").read_text())["mcpServers"]["cpl"]["args"][1]
    assert "'CPL_ANTHROPIC_KEY'" in code and "'ANTHROPIC_API_KEY'" in code and code.startswith("import os, sys; [os.environ.pop(v, None)")
    assert r.meta["auth"] == "api_key" and r.meta["billed_to"] == "apiKeyHelper" and r.meta["cost_usd"] == 1.25
    # no key: no run; a key with a line ending: no run; a workspace goes as a header
    with pytest.raises(BackendError, match="CPL_ANTHROPIC_KEY is not set"):
        keyed(tmp_path / "a", [], environ={"CPL_ANTHROPIC_KEY": ""})
    with pytest.raises(BackendError, match="spaces or line breaks"):
        keyed(tmp_path / "b", [], environ={"CPL_ANTHROPIC_KEY": KEY + "\n"})
    with pytest.raises(BackendError, match="workspace ID"):
        keyed(tmp_path / "c", [], environ={"CPL_ANTHROPIC_WORKSPACE": "default"})
    b2, _, _ = keyed(tmp_path / "d", [], environ={"CPL_ANTHROPIC_WORKSPACE": "wrkspc_01Abc"})
    assert b2.env["ANTHROPIC_CUSTOM_HEADERS"] == "anthropic-workspace-id: wrkspc_01Abc"
    # under a login the key's variable never reaches the CLI, and the command line is as before
    cfg = cfg_for(tmp_path / "e", auth="login")
    login = ClaudeCodeToolBackend(cfg, log=lambda *a: None, runner=lambda *a, **k: None, environ={"PATH": "/usr/bin", "CPL_ANTHROPIC_KEY": KEY})
    assert "CPL_ANTHROPIC_KEY" not in login.env and "--bare" not in login.command_line(Path("m.json"))


def test_the_key_is_checked_before_the_run_for_free(tmp_path):
    seen = []

    def http(answer):
        def get(url, headers, timeout_s=30):
            seen.append((url, headers))
            return answer
        return get

    cfg = cfg_for(tmp_path)
    env = {"PATH": "/usr/bin", "CPL_ANTHROPIC_KEY": KEY, "CPL_ANTHROPIC_WORKSPACE": "wrkspc_1"}
    ClaudeCodeToolBackend(cfg, runner=lambda *a: None, environ=env, http=http((200, '{"id": "m"}')))
    assert seen[0][0] == "https://api.anthropic.com/v1/models/m" and seen[0][1]["x-api-key"] == KEY
    assert seen[0][1]["anthropic-workspace-id"] == "wrkspc_1"
    for answer, why in (((401, '{"error": "invalid x-api-key ' + KEY + '"}'), "refused the key in CPL_ANTHROPIC_KEY"),
                        ((404, "{}"), "cannot use the model m"), ((200, '{"lifecycle": "retired"}'), "is retired")):
        with pytest.raises(BackendError, match=why) as info:
            ClaudeCodeToolBackend(cfg, runner=lambda *a: None, environ=env, http=http(answer))
        assert KEY not in str(info.value)  # never echoed


def test_every_try_is_capped_and_counted_across_tries_rounds_and_resumes(tmp_path):
    """Round budget $4, run budget $10. Round 1: a try that cost $1.25. Round 2: a try stopped at the session's
    time limit (no cost reported: it counts at its cap, $4). Round 3: a try that reached its cap. Then the run
    has $10 - $9.25 = $0.75 left, and a fourth round's session gets that, then nothing."""
    b, run, calls = keyed(tmp_path, [printed(cost=1.25), "timeout",
                                     printed(text="partial", cost=0.0, subtype="error_max_budget_usd", is_error=True),
                                     printed(cost=0.75)])
    r1, _ = respond(b, run, 1)
    r2, _ = respond(b, run, 2)
    assert r2.text == "(the session ran out of time)"
    st = api_budget.state(run, {"run_usd": 10, "round_usd": 4})
    assert st["rounds"] == {1: 1.25, 2: 4.0} and st["unreported"] == 1
    r3, _ = respond(b, run, 3)
    assert calls[2]["cmd"][calls[2]["cmd"].index("--max-budget-usd") + 1] == "4.00"
    assert r3.meta["stop_reason"] == "budget" and "spending cap ($4.00)" in r3.meta["stop_details"]["budget"] and r3.text == "partial"
    # round 3 counted at what the CLI reported (0.0 here); the run: 1.25 + 4 + 0
    assert b.exhausted(run) is None
    r4, _ = respond(b, run, 4)
    assert calls[3]["cmd"][calls[3]["cmd"].index("--max-budget-usd") + 1] == "4.00"
    assert r4.meta["api_budget"]["run_counted_usd"] == 6.0
    # the run's budget raised and spent: a session with less than a cent left makes no call
    api_budget.set_run_budget(run, 6.0)
    assert "the run's API budget is spent: $6.00 counted of $6.00" == b.exhausted(run)
    r5, _ = respond(b, run, 5)
    assert len(calls) == 4 and r5.text.startswith("(the run's API budget is spent") and r5.meta["stop_reason"] == "budget"
    log = [json.loads(l) for l in (run / "spend.jsonl").read_text().splitlines()]
    assert [(e["event"], e.get("round"), e.get("try")) for e in log if e["event"] != "budget"] == [
        ("start", 1, 1), ("end", 1, 1), ("start", 2, 1), ("end", 2, 1), ("start", 3, 1), ("end", 3, 1), ("start", 4, 1), ("end", 4, 1)]
    assert all(KEY not in l for l in (run / "spend.jsonl").read_text().splitlines())


def test_a_try_that_billed_anything_but_the_key_stops_the_run(tmp_path):
    for source in ("/login managed key", "ANTHROPIC_API_KEY", "none"):
        b, run, _ = keyed(tmp_path / source.replace("/", "_").replace(" ", "_"), [printed(init=init_event(source))])
        with pytest.raises(StopRun, match=f"billed '{source}'"):
            respond(b, run, 1)


def test_an_account_that_cannot_pay_stops_at_once_and_the_key_never_reaches_a_record(tmp_path):
    poor = printed(text="Your credit balance is too low to access the Anthropic API", cost=None, subtype="error", is_error=True)
    b, run, calls = keyed(tmp_path, [Done(poor, returncode=1)])
    with pytest.raises(StopRun, match="cannot pay for more"):
        respond(b, run, 1)
    assert len(calls) == 1  # not retried
    echo = printed(text=f"the helper printed {KEY}")
    b, run, _ = keyed(tmp_path / "echo", [echo])
    r, where = respond(b, run, 1)
    assert KEY not in r.text and "<the API key>" in r.text and KEY not in (where / "response_raw.json").read_text()


def test_the_loop_ends_the_rounds_when_the_runs_budget_is_spent_and_a_resume_raises_it(tmp_path, monkeypatch):
    """A run on the stand-in Lean service with a key: each session costs $3 of a $5 run budget ($4 a round).
    Round 1 spends $3; round 2's session gets the $2 left and spends it; the rounds end there, with nothing
    locked and no seed check. `resume --budget-usd 9` goes on to round 3."""
    project = fake_project(tmp_path)
    raw = {"extends": str(REPO_ROOT / "config" / "pilot" / "base.yaml"), "run_id": "keyrun", "model": "tests/max2_ladder",
           "networks": [A], "backend": "claude_code", "rounds_max": 3, "runs_dir": str(tmp_path / "runs"), "workers": 1,
           "agent_model": "m", "auth": "api_key", "api_budget": {"run_usd": 5, "round_usd": 4},
           "open_lane": {"lean_project": str(project), "work_dir": str(tmp_path / "work"), "seed_check": {"network": "max2_ladder-n2v24d8-s3"}}}
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(raw))
    monkeypatch.setattr(loop, "check_lean_lock", lambda project: {})
    monkeypatch.setattr(loop, "check_inspection", lambda project: None)
    monkeypatch.setattr(loop, "lean_identity", lambda project, knowledge="minimal": dict(IDENT))
    monkeypatch.setattr(loop, "git_state", lambda: {"commit": "c", "dirty": False})
    monkeypatch.setattr(Session, "_service", fake_service(448))
    caps = []

    def cli(cmd, prompt_text, env, cwd, timeout_s):
        cap = float(cmd[cmd.index("--max-budget-usd") + 1])
        caps.append(cap)
        return Done(printed(cost=min(3.0, cap)))

    def make(cfg, log=print):
        return ClaudeCodeToolBackend(cfg, log=log, runner=cli, sleep=lambda s: None,
                                     environ={"PATH": "/usr/bin", "CPL_ANTHROPIC_KEY": KEY})

    monkeypatch.setattr(loop, "make_backend", make)
    lines: list[str] = []
    ctx = loop.start(path, log=lines.append)
    assert any("billed to the API key in CPL_ANTHROPIC_KEY: at most $5.00 for the run and $4.00 for a round" in l for l in lines)
    loop.drive(ctx)
    assert caps == [4.0, 2.0] and ctx.run.done_rounds() == [0, 1, 2]
    assert any("the run's API budget is spent: $5.00 counted of $5.00; stopping after round 2" in l for l in lines), lines
    from core.open_lane import stages

    assert not stages.started(ctx.run)  # nothing locked, no seed check: the rounds did not end, they stopped
    ctx2 = loop.resume(ctx.run.path, log=lines.append, budget_usd=9)
    assert any("the run's API budget is now $9.00 (was $5.00; $5.00 counted so far)" in l for l in lines)
    loop.drive(ctx2)
    assert caps == [4.0, 2.0, 4.0] and 3 in ctx2.run.done_rounds()
    with pytest.raises(loop.LoopError, match="not billed to an API key"):
        raw2 = {**raw, "run_id": "login", "auth": "login"}
        p2 = tmp_path / "login.yaml"
        p2.write_text(yaml.safe_dump(raw2))
        c = loop.start(p2, log=lines.append)
        loop.resume(c.run.path, log=lines.append, budget_usd=3)
