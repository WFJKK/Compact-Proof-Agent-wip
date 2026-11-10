"""The Claude Code backend, against a fake CLI. No test here runs the real CLI or calls a model."""

import json
import subprocess

import pytest
import yaml

from core import loop
from core.agent.backends import BackendError
from core.agent.backends.api import StopRun
from core.agent.backends.claude_code import ClaudeCodeBackend
from core.agent.build_prompt import Prompt
from core.run_config import merge
from tests.test_api import RESPONSE_TEXT

PROMPT = Prompt("PART ONE", "PART TWO", {})


def result_event(text=RESPONSE_TEXT, is_error=False, **extra):
    d = {
        "type": "result",
        "subtype": "success" if not is_error else "error_during_execution",
        "is_error": is_error,
        "result": text,
        "session_id": "sess_123",
        "total_cost_usd": 0.42,
        "num_turns": 1,
        "usage": {"input_tokens": 5000, "output_tokens": 20000, "cache_creation_input_tokens": 0, "cache_read_input_tokens": 3600},
    }
    d.update(extra)
    return d


def assistant_event(text, stop_reason="end_turn"):
    return {
        "type": "assistant",
        "message": {"role": "assistant", "content": [{"type": "thinking", "thinking": "..."}, {"type": "text", "text": text}], "stop_reason": stop_reason},
        "session_id": "sess_123",
    }


def stream(*events):
    """What the CLI prints with --output-format stream-json --verbose: one JSON object per line."""
    init = {"type": "system", "subtype": "init", "session_id": "sess_123"}
    return "\n".join(json.dumps(e) for e in (init, *events)) + "\n"


def result_json(text=RESPONSE_TEXT, is_error=False, **extra):
    """A whole answer in one assistant message, then the result event."""
    if is_error:
        return stream(result_event(text, is_error=True, **extra))
    return stream(assistant_event(text), result_event(text, **extra))


class Completed:
    def __init__(self, stdout="", stderr="", returncode=0):
        self.stdout, self.stderr, self.returncode = stdout, stderr, returncode


class FakeCli:
    def __init__(self, outcomes):
        self.outcomes = list(outcomes)
        self.calls = []

    def __call__(self, cmd, prompt_text, env, cwd, timeout_s):
        self.calls.append({"cmd": cmd, "prompt": prompt_text, "env": env, "cwd": cwd, "timeout": timeout_s})
        if not self.outcomes:
            raise AssertionError("an unexpected CLI run")
        out = self.outcomes.pop(0)
        if isinstance(out, Exception):
            raise out
        return out


def config(**over):
    return merge({"run_id": "cc-test", "model": "models/max2", "backend": "claude_code", **over})


def backend(outcomes, environ=None, **over):
    sleeps, logs = [], []
    cli = FakeCli(outcomes)
    b = ClaudeCodeBackend(config(**over), log=logs.append, runner=cli, sleep=sleeps.append, environ=environ or {"PATH": "/usr/bin"})
    return b, cli, sleeps, logs


def test_the_cli_is_run_as_a_plain_model_call():
    b, cli, _, _ = backend([Completed(result_json())], effort="high")
    r = b.respond(PROMPT, 0)
    call = cli.calls[0]
    cmd = call["cmd"]
    assert cmd[:2] == ["claude", "-p"]
    for flag in ("--no-session-persistence", "--disable-slash-commands", "--strict-mcp-config"):
        assert flag in cmd
    assert "--bare" not in cmd  # --bare would ignore the subscription login
    assert cmd[cmd.index("--setting-sources") + 1] == ""
    assert cmd[cmd.index("--tools") + 1] == ""  # no tools at all
    assert cmd[cmd.index("--output-format") + 1] == "stream-json" and "--verbose" in cmd
    assert cmd[cmd.index("--model") + 1] == "claude-fable-5-1" and cmd[cmd.index("--effort") + 1] == "high"
    assert call["prompt"] == PROMPT.text  # the whole prompt, on stdin
    assert call["cwd"] and "cpl-claude-code-" in call["cwd"]
    assert r.text == RESPONSE_TEXT


def test_no_api_key_ever_reaches_the_cli():
    env = {"PATH": "/usr/bin", "HOME": "/home/x", "ANTHROPIC_API_KEY": "sk-should-not-leak", "CPL_ANTHROPIC_KEY": "sk-nor-this", "ANTHROPIC_AUTH_TOKEN": "t"}
    b, cli, _, _ = backend([Completed(result_json())], environ=env)
    b.respond(PROMPT, 0)
    seen = cli.calls[0]["env"]
    assert "ANTHROPIC_API_KEY" not in seen and "CPL_ANTHROPIC_KEY" not in seen and "ANTHROPIC_AUTH_TOKEN" not in seen
    assert seen["HOME"] == "/home/x"  # the login lives under HOME, so that stays


def test_response_is_saved_raw_and_tokens_recorded(tmp_path):
    b, _, _, _ = backend([Completed(result_json())])
    r = b.respond(PROMPT, 0, tmp_path)
    raw = json.loads((tmp_path / "response_raw.json").read_text())
    assert raw["session_id"] == "sess_123" and [m["text"] for m in raw["assistant_messages"]] == [RESPONSE_TEXT]
    m = r.meta
    assert m["backend"] == "claude_code" and m["input_tokens"] == 5000 and m["output_tokens"] == 20000
    assert m["cost_usd"] == 0.0 and m["api_equivalent_usd"] == 0.42 and m["stop_reason"] == "end_turn"


def test_a_long_answer_split_over_several_messages_is_joined():
    """The CLI continues an answer that hit its output limit in a new assistant message, and the
    result event's text holds only the last piece. The response is all pieces, joined exactly."""
    head, tail = RESPONSE_TEXT[:40], RESPONSE_TEXT[40:]
    out = stream(assistant_event(head, stop_reason="max_tokens"), assistant_event(tail), result_event(tail, num_turns=2))
    b, _, _, _ = backend([Completed(out)])
    r = b.respond(PROMPT, 0)
    assert r.text == RESPONSE_TEXT
    assert r.meta["assistant_messages"] == 2 and r.meta["num_turns"] == 2 and r.meta["stop_reason"] == "end_turn"


def test_messages_that_ended_on_their_own_are_joined_on_a_new_line():
    out = stream(assistant_event("CLAIM: a"), assistant_event("NOTES: b"), result_event("NOTES: b"))
    b, _, _, _ = backend([Completed(out)])
    assert b.respond(PROMPT, 0).text == "CLAIM: a\nNOTES: b"


def test_a_plain_json_result_still_parses():
    """The old one-object output: no assistant events, so the result's own text is used."""
    b, _, _, _ = backend([Completed(json.dumps(result_event()))])
    assert b.respond(PROMPT, 0).text == RESPONSE_TEXT


def test_noise_around_the_stream_is_ignored():
    out = "some warning line\n" + stream(assistant_event(RESPONSE_TEXT), result_event()) + "trailing text\n"
    b, _, _, _ = backend([Completed(out)])
    assert b.respond(PROMPT, 0).text == RESPONSE_TEXT


def test_usage_limits_are_retried_with_growing_waits():
    limited = Completed(result_json("You have hit your usage limit. Try again later.", is_error=True), returncode=1)
    b, cli, sleeps, logs = backend([limited, limited, Completed(result_json())], api_retries={"tries": 5, "first_wait_s": 60, "max_wait_s": 1800, "timeout_s": 600})
    r = b.respond(PROMPT, 0)
    assert r.text == RESPONSE_TEXT and len(cli.calls) == 3
    assert len(sleeps) == 2 and sleeps[1] > sleeps[0] * 1.5 and sleeps[0] >= 60
    assert len(r.meta["failed_tries"]) == 2 and "usage or rate limit" in logs[0]


def test_a_login_problem_stops_the_run_at_once():
    b, cli, sleeps, _ = backend([Completed("", stderr="Error: not logged in. Please run claude login", returncode=1)])
    with pytest.raises(StopRun, match="login"):
        b.respond(PROMPT, 0)
    assert sleeps == [] and len(cli.calls) == 1


def test_endless_failures_stop_after_the_configured_tries():
    junk = Completed("not json at all", returncode=2)
    b, _, sleeps, _ = backend([junk] * 3, api_retries={"tries": 3, "first_wait_s": 1, "max_wait_s": 4, "timeout_s": 600})
    with pytest.raises(StopRun, match="after 3 tries"):
        b.respond(PROMPT, 0)
    assert len(sleeps) == 2


def test_a_hung_cli_is_retried():
    hung = subprocess.TimeoutExpired(cmd="claude", timeout=1)
    b, _, sleeps, _ = backend([hung, Completed(result_json())])
    assert b.respond(PROMPT, 0).text == RESPONSE_TEXT and len(sleeps) == 1


def test_missing_cli_is_reported_before_the_run_starts(monkeypatch):
    monkeypatch.setattr("shutil.which", lambda name: None)
    with pytest.raises(BackendError, match="not installed"):
        ClaudeCodeBackend(config(claude_code_command="claude-nowhere"), environ={"PATH": "/usr/bin"})


# through the loop, still with the fake CLI ---------------------------------------------
def test_a_subscription_run_records_zero_cost_and_resumes(trained_stub, tmp_path, monkeypatch):
    limited = Completed(result_json("usage limit reached", is_error=True), returncode=1)
    cli = FakeCli([Completed(result_json()), limited, limited, limited])
    monkeypatch.setattr(loop, "git_state", lambda: {"commit": "abc", "dirty": False})
    monkeypatch.setattr(
        loop, "ClaudeCodeBackend",
        lambda cfg, log=print: ClaudeCodeBackend(cfg, log=log, runner=cli, sleep=lambda s: None, environ={"PATH": "/usr/bin"}),
    )
    cfg = {
        "run_id": "cc-run", "model": str(trained_stub), "runs_dir": str(tmp_path / "runs"), "backend": "claude_code",
        "knob_values": [0], "sandbox": "process", "rounds_max": 3,
        "api_retries": {"tries": 3, "first_wait_s": 1, "max_wait_s": 2, "timeout_s": 60},
    }
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    ctx = loop.start(path, log=lambda *a: None)
    with pytest.raises(StopRun, match="after 3 tries"):
        loop.drive(ctx)
    assert ctx.run.done_rounds() == [0, 1]
    meta = ctx.run.read(1, "meta.json")
    assert meta["cost_usd"] == 0.0 and meta["tokens"] == {"input": 5000, "output": 20000}
    assert ctx.run.read(1, "attempt_0/response_meta.json")["api_equivalent_usd"] == 0.42
    # The limit lifts: resume finishes without re-asking for round 1.
    cli.outcomes = [Completed(result_json()), Completed(result_json())]
    ctx2 = loop.resume(ctx.run.path, log=lambda *a: None)
    loop.drive(ctx2)
    assert ctx2.run.done_rounds() == [0, 1, 2, 3] and len(cli.calls) == 6


def test_a_stream_cut_off_mid_line_is_joined_exactly():
    """The CLI resumes an interrupted stream in a new message with no stop reason, in the middle
    of a line: nothing goes between the pieces (three real cases from the first max2 runs)."""
    from core.agent.backends.claude_code import _join

    text = RESPONSE_TEXT
    for marker, offset in (("make_proof", 4), ("knob", 2)):
        at = text.index(marker) + offset
        pieces = [assistant_event(text[:at], stop_reason=None), assistant_event(text[at:], stop_reason=None)]
        b, _, _, _ = backend([Completed(stream(*pieces, result_event(text[at:], num_turns=2)))])
        assert b.respond(PROMPT, 0).text == text
    # A resume that repeats a few characters from before the cut: dropped when that is what makes the recipe parse.
    at = text.index("make_proof") + 4
    assert _join([{"stop_reason": None, "text": text[:at]}, {"stop_reason": None, "text": text[at - 8 :]}]) == text
    # A cut inside indentation with a clean resume keeps every space.
    code_line = next(l for l in text.splitlines() if l.startswith("    "))
    at = text.index(code_line) + 2
    assert _join([{"stop_reason": None, "text": text[:at]}, {"stop_reason": None, "text": text[at:]}]) == text


def test_the_cli_may_not_answer_with_another_model():
    b, cli, _, _ = backend([Completed(result_json())])
    b.respond(PROMPT, 0)
    assert cli.calls[0]["env"]["CLAUDE_CODE_NO_MODEL_FALLBACK"] == "1"


def test_an_answer_from_another_model_stops_the_run():
    swap = {"type": "system", "subtype": "model_refusal_fallback", "original_model": "claude-fable-5-1",
            "fallback_model": "claude-opus-4-8", "api_refusal_category": "frontier_llm", "scope": "session"}
    b, cli, sleeps, _ = backend([Completed(stream(swap, assistant_event(RESPONSE_TEXT), result_event()))])
    with pytest.raises(StopRun, match="claude-opus-4-8 instead of claude-fable-5-1"):
        b.respond(PROMPT, 0)
    assert len(cli.calls) == 1 and sleeps == []
    # no event, but another model's output in modelUsage: what the CLI printed for a swap on 26 October 2026
    usage = {"claude-fable-5-1": {"outputTokens": 0, "canonicalModel": "claude-fable-5-1"},
             "claude-opus-4-8": {"outputTokens": 4, "canonicalModel": "claude-opus-4-8"}}
    b, _, _, _ = backend([Completed(result_json(modelUsage=usage, safety_stops=2))])
    with pytest.raises(StopRun, match="output from claude-opus-4-8"):
        b.respond(PROMPT, 0)


def test_a_refusal_is_recorded_as_one_and_not_retried(tmp_path):
    declined = {"type": "assistant", "session_id": "sess_123", "message": {"role": "assistant", "content": [], "stop_reason": "refusal"}}
    event = {"type": "system", "subtype": "model_refusal_no_fallback", "original_model": "claude-fable-5-1",
             "api_refusal_category": "cyber", "api_refusal_explanation": "declined"}
    b, cli, sleeps, logs = backend([Completed(stream(declined, event, result_event("", is_error=True, safety_stops=1)))])
    r = b.respond(PROMPT, 0, tmp_path)
    assert len(cli.calls) == 1 and sleeps == []  # the loop counts refusals; the backend does not ask again
    assert r.text == "" and r.meta["stop_reason"] == "refusal" and r.meta["stop_details"] == {"category": "cyber"}
    assert r.meta["safety_stops"] == 1 and any("declined" in line for line in logs)


def test_the_models_that_answered_are_recorded():
    usage = {"claude-fable-5-1": {"outputTokens": 20000, "canonicalModel": "claude-fable-5-1"}}
    b, _, _, _ = backend([Completed(result_json(modelUsage=usage, safety_stops=0))])
    m = b.respond(PROMPT, 0).meta
    assert m["models_used"] == {"claude-fable-5-1": 20000} and m["safety_stops"] == 0 and m["model_events"] == []
