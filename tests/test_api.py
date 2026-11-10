"""The API backend, against a mock client. No test here calls the real API."""

import json

import anthropic
import httpx2
import pytest
import yaml
from anthropic.types import Message

from core import loop
from core.agent.backends import BackendError
from core.agent.backends.api import ApiBackend, StopRun, cost_usd, load_prices
from core.agent.build_prompt import Prompt
from core.run_config import merge

REQUEST = httpx2.Request("POST", "https://api.anthropic.com/v1/messages")
RESPONSE_TEXT = """CLAIM: It checks every input.

WHY IT HELPS: It does not.

PREDICTION: Full accuracy at B.

KNOB: Unused.

RECIPE:
```python
import helpers


def make_proof(weights, info, knob):
    return helpers.proof(helpers.full_tree(info["input_space"]))
```

NOTES: First try.
"""


def message(text=RESPONSE_TEXT, stop_reason="end_turn", stop_details=None, usage=None):
    return Message.model_validate(
        {
            "id": "msg_test",
            "type": "message",
            "role": "assistant",
            "model": "claude-fable-5-1",
            "content": [{"type": "thinking", "thinking": "Let me think.", "signature": "sig"}]
            + ([{"type": "text", "text": text}] if text else []),
            "stop_reason": stop_reason,
            "stop_sequence": None,
            "stop_details": stop_details,
            "usage": usage or {"input_tokens": 1200, "output_tokens": 30000, "cache_creation_input_tokens": 3600, "cache_read_input_tokens": 0},
        }
    )


def status_error(cls, status, headers=None, msg="error"):
    return cls(msg, response=httpx2.Response(status, request=REQUEST, headers=headers or {}), body=None)


class FakeStream:
    def __init__(self, outcome):
        self.outcome = outcome

    def __enter__(self):
        if isinstance(self.outcome, Exception):
            raise self.outcome
        return self

    def __exit__(self, *exc):
        return False

    def get_final_message(self):
        return self.outcome


class FakeClient:
    def __init__(self, outcomes):
        self.outcomes = list(outcomes)
        self.calls = []
        self.messages = self

    def stream(self, **kw):
        self.calls.append(kw)
        if not self.outcomes:
            raise AssertionError("an unexpected API call")
        return FakeStream(self.outcomes.pop(0))


def config(**over):
    return merge({"run_id": "api-test", "model": "models/max2", "backend": "api", **over})


PROMPT = Prompt("PART ONE", "PART TWO", {})


def backend(outcomes, **over):
    sleeps, logs = [], []
    b = ApiBackend(config(**over), log=logs.append, client=FakeClient(outcomes), sleep=sleeps.append)
    return b, sleeps, logs


def test_the_request_has_the_run_configs_settings():
    b, _, _ = backend([message()], effort="max", max_output_tokens=50000)
    b.respond(PROMPT, 0)
    kw = b.client.calls[0]
    assert kw["model"] == "claude-fable-5-1" and kw["max_tokens"] == 50000
    assert kw["thinking"] == {"type": "adaptive"} and kw["output_config"] == {"effort": "max"}
    part1, part2 = kw["messages"][0]["content"]
    assert part1 == {"type": "text", "text": "PART ONE", "cache_control": {"type": "ephemeral", "ttl": "1h"}}
    assert part2 == {"type": "text", "text": "PART TWO"}
    assert "system" not in kw
    b, _, _ = backend([message()], thinking=None, effort=None)
    b.respond(PROMPT, 0)
    assert "thinking" not in b.client.calls[0] and "output_config" not in b.client.calls[0]


def test_the_key_comes_from_the_named_variable_and_nowhere_else(monkeypatch):
    seen = {}

    class Capture:
        def __init__(self, **kw):
            seen.update(kw)

    monkeypatch.setattr(anthropic, "Anthropic", Capture)
    ApiBackend(config(), environ={"CPL_ANTHROPIC_KEY": "sk-test-1"})
    assert seen["api_key"] == "sk-test-1" and seen["max_retries"] == 0
    with pytest.raises(BackendError, match="no API key"):
        ApiBackend(config(), environ={"ANTHROPIC_API_KEY": "sk-should-not-be-used"})
    with pytest.raises(BackendError, match="must not be"):
        ApiBackend({**config(), "api_key_env": "ANTHROPIC_API_KEY"}, environ={"ANTHROPIC_API_KEY": "x"})
    with pytest.raises(Exception, match="ANTHROPIC_API_KEY"):
        merge({"run_id": "x", "model": "models/max2", "api_key_env": "ANTHROPIC_API_KEY"})


def test_the_response_is_saved_raw_and_priced(tmp_path):
    b, _, _ = backend([message()])
    r = b.respond(PROMPT, 0, tmp_path)
    assert r.text == RESPONSE_TEXT  # thinking blocks are left out of the response text
    raw = json.loads((tmp_path / "response_raw.json").read_text())
    assert raw["content"][0]["type"] == "thinking" and raw["id"] == "msg_test"
    m = r.meta
    assert (m["input_tokens"], m["output_tokens"], m["cache_creation_input_tokens"]) == (1200, 30000, 3600)
    price = load_prices()["claude-fable-5-1"]
    expected = (1200 * price["input"] + 30000 * price["output"] + 3600 * price["cache_write_1h"]) / 1e6
    assert m["cost_usd"] == pytest.approx(expected) and m["stop_reason"] == "end_turn"
    assert cost_usd({"input_tokens": 1}, None) is None


@pytest.mark.parametrize(
    "error",
    [
        status_error(anthropic.OverloadedError, 529),
        status_error(anthropic.InternalServerError, 500),
        status_error(anthropic.RateLimitError, 429, {"retry-after": "42"}),
        anthropic.APIConnectionError(request=REQUEST),
        anthropic.APITimeoutError(request=REQUEST),
    ],
)
def test_passing_errors_are_retried_with_growing_waits(error):
    b, sleeps, logs = backend([error, error, message()])
    r = b.respond(PROMPT, 0)
    assert r.text == RESPONSE_TEXT and len(sleeps) == 2
    assert len(r.meta["failed_tries"]) == 2 and logs
    if isinstance(error, anthropic.RateLimitError):
        assert min(sleeps) >= 42  # the server's retry-after wins over the doubling
    else:
        assert sleeps[1] > sleeps[0] * 1.5


@pytest.mark.parametrize(
    "error, words",
    [
        (status_error(anthropic.BadRequestError, 400, msg="spend limit reached"), "spend limit"),
        (status_error(anthropic.APIStatusError, 402, msg="billing"), "billing"),
        (status_error(anthropic.AuthenticationError, 401), "not accepted"),
        (status_error(anthropic.PermissionDeniedError, 403), "not accepted"),
        (status_error(anthropic.RateLimitError, 429), "spend cap"),
    ],
)
def test_errors_that_waiting_cannot_fix_stop_the_run_at_once(error, words):
    b, sleeps, _ = backend([error])
    with pytest.raises(StopRun, match=words):
        b.respond(PROMPT, 0)
    assert sleeps == [] and len(b.client.calls) == 1


def test_endless_failures_stop_after_the_configured_tries():
    err = status_error(anthropic.OverloadedError, 529)
    b, sleeps, _ = backend([err] * 3, api_retries={"tries": 3, "first_wait_s": 1, "max_wait_s": 4, "timeout_s": 60})
    with pytest.raises(StopRun, match="after 3 tries"):
        b.respond(PROMPT, 0)
    assert len(sleeps) == 2 and max(sleeps) <= 4 * 1.1


def test_cut_off_and_refused_responses_are_recorded():
    b, _, logs = backend([message(stop_reason="max_tokens", text="CLAIM: half")])
    assert b.respond(PROMPT, 0).meta["stop_reason"] == "max_tokens" and "max_output_tokens" in logs[-1]
    details = {"type": "refusal", "category": "frontier_llm", "explanation": "no"}
    b, _, logs = backend([message(stop_reason="refusal", stop_details=details, text="")])
    r = b.respond(PROMPT, 0)
    assert r.text == "" and r.meta["stop_details"]["category"] == "frontier_llm" and "declined" in logs[-1]


# through the loop, still with the mock -------------------------------------------------
def start_api_run(tmp_path, trained_stub, outcomes, monkeypatch, **over):
    client = FakeClient(outcomes)
    monkeypatch.setattr(loop, "git_state", lambda: {"commit": "abc", "dirty": False})
    monkeypatch.setattr(loop, "ApiBackend", lambda cfg, log=print: ApiBackend(cfg, log=log, client=client, sleep=lambda s: None))
    cfg = {
        "run_id": "api-run",
        "model": str(trained_stub),
        "runs_dir": str(tmp_path / "runs"),
        "backend": "api",
        "knob_values": [0],
        "sandbox": "process",
        "rounds_max": 3,
        **over,
    }
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    return loop.start(path, log=lambda *a: None), client


def test_api_rounds_record_tokens_and_cost(trained_stub, tmp_path, monkeypatch):
    ctx, client = start_api_run(tmp_path, trained_stub, [message(), message()], monkeypatch, rounds_max=2)
    loop.drive(ctx)
    assert len(client.calls) == 2 and ctx.run.done_rounds() == [0, 1, 2]
    meta = ctx.run.read(1, "meta.json")
    assert meta["tokens"] == {"input": 1200, "output": 30000} and meta["cost_usd"] > 0
    assert ctx.run.read(1, "attempt_0/response_meta.json")["backend"] == "api"
    assert (ctx.run.round_path(1) / "attempt_0" / "response_raw.json").is_file()
    sent = client.calls[1]["messages"][0]["content"]
    assert sent[0]["text"] == ctx.run.read(2, "prompt.json")["part1"]
    assert "ROUND 2 OF 2" in sent[1]["text"]


def test_a_stopped_run_resumes_without_paying_twice(trained_stub, tmp_path, monkeypatch):
    spend = status_error(anthropic.BadRequestError, 400, msg="spend limit reached")
    ctx, client = start_api_run(tmp_path, trained_stub, [message(), spend], monkeypatch)
    with pytest.raises(StopRun):
        loop.drive(ctx)
    assert ctx.run.done_rounds() == [0, 1] and not ctx.run.round_path(2).joinpath("attempt_0", "response.md").exists()
    client.outcomes = [message(), message()]
    ctx2 = loop.resume(ctx.run.path, log=lambda *a: None)
    loop.drive(ctx2)
    assert ctx2.run.done_rounds() == [0, 1, 2, 3]
    assert len(client.calls) == 4  # rounds 1 and 2 (refused by the spend limit), then 2 and 3


def test_repeated_refusals_stop_the_run(trained_stub, tmp_path, monkeypatch):
    details = {"type": "refusal", "category": "frontier_llm", "explanation": "no"}
    refusal = message(stop_reason="refusal", stop_details=details, text="")
    ctx, client = start_api_run(tmp_path, trained_stub, [refusal] * 3, monkeypatch, rounds_max=10, max_consecutive_refusals=2)
    loop.drive(ctx)
    assert ctx.run.done_rounds() == [0, 1, 2] and len(client.calls) == 2
    assert loop.consecutive_refusals(ctx.run) == 2


def test_api_runs_start_only_from_a_clean_commit_with_a_key(trained_stub, tmp_path, monkeypatch):
    cfg = {"run_id": "dirty", "model": str(trained_stub), "runs_dir": str(tmp_path / "runs"), "backend": "api", "sandbox": "process"}
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    monkeypatch.setattr(loop, "git_state", lambda: {"commit": "abc", "dirty": True})
    with pytest.raises(loop.LoopError, match="clean commit"):
        loop.start(path, log=lambda *a: None)
    monkeypatch.setattr(loop, "git_state", lambda: {"commit": "abc", "dirty": False})
    monkeypatch.delenv("CPL_ANTHROPIC_KEY", raising=False)
    with pytest.raises(BackendError, match="no API key"):
        loop.start(path, log=lambda *a: None)
    assert not (tmp_path / "runs" / "dirty").exists()  # nothing was made before the checks passed


def test_the_workspace_id_goes_out_as_a_header_only_when_set(monkeypatch):
    made = []
    monkeypatch.setattr(anthropic, "Anthropic", lambda **kw: made.append(kw) or object())
    ApiBackend(config(), environ={"CPL_ANTHROPIC_KEY": "k", "CPL_ANTHROPIC_WORKSPACE": "wrkspc_x"})
    ApiBackend(config(), environ={"CPL_ANTHROPIC_KEY": "k"})
    assert made[0]["default_headers"] == {"anthropic-workspace-id": "wrkspc_x"}
    assert "default_headers" not in made[1]


def test_a_missing_workspace_says_which_variable_to_set():
    b = ApiBackend(config(), client=object())
    exc = anthropic.BadRequestError(
        "This API key is not scoped to a workspace", response=httpx2.Response(400, request=REQUEST), body=None
    )
    retry, _, what = b._classify(exc)
    assert not retry and "CPL_ANTHROPIC_WORKSPACE" in what
