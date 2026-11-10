"""The API backend: one call to the Messages API per attempt.

The key comes from the environment variable the run config names in
api_key_env, never ANTHROPIC_API_KEY (Claude Code would bill its own work to
that one), and is passed to the client explicitly. A key not scoped to one
workspace also needs the workspace ID, from the variable api_workspace_env
names, which goes out as the anthropic-workspace-id header. Each call streams, since
long thinking would otherwise run into the SDK's limit for plain requests.

Part 1 of the prompt, the same every round, is sent as a cached block; Part 2
follows it. Errors that pass by themselves (overloaded, server errors, a rate
limit with a retry-after, a lost connection) are retried with growing waits.
Anything that will not get better by waiting stops the run: a spend limit
(400, or a 429 without a retry-after), billing (402), authentication (401),
permission (403), or a request the API rejects. The raw response is saved next
to the attempt before anything else happens to it, with the tokens used and the
cost, priced from config/prices.yaml.
"""

from __future__ import annotations

import json
import os
import random
import time
from pathlib import Path

from ...util import REPO_ROOT, read_yaml
from . import BackendError, Response

PRICES = REPO_ROOT / "config" / "prices.yaml"
FORBIDDEN_KEY_VARIABLES = ("ANTHROPIC_API_KEY",)
TOKENS_PER_MILLION = 1_000_000


class StopRun(BackendError):
    """An API error that waiting will not fix; the run stops and can be resumed later."""


def load_prices() -> dict:
    return read_yaml(PRICES) or {}


def cost_usd(usage: dict, price: dict | None) -> float | None:
    if not price:
        return None
    cached_write = usage.get("cache_creation_input_tokens") or 0
    total = (
        (usage.get("input_tokens") or 0) * price["input"]
        + (usage.get("output_tokens") or 0) * price["output"]
        + cached_write * price.get("cache_write_1h", price["input"])
        + (usage.get("cache_read_input_tokens") or 0) * price.get("cache_read", price["input"])
    )
    return round(total / TOKENS_PER_MILLION, 6)


def _dump(obj):
    if hasattr(obj, "model_dump"):
        return obj.model_dump(mode="json")
    return obj


class ApiBackend:
    name = "api"

    def __init__(self, cfg: dict, log=print, client=None, sleep=time.sleep, environ=None):
        env = os.environ if environ is None else environ
        var = cfg["api_key_env"]
        if var in FORBIDDEN_KEY_VARIABLES:
            raise BackendError(f"api_key_env must not be {var}")
        if client is None:
            key = env.get(var)
            if not key:
                raise BackendError(f"no API key: set {var} (see the README); the run has not called the API")
            import anthropic

            extra = {}
            workspace = env.get(cfg.get("api_workspace_env") or "WORKSPACE_ENV_UNSET")
            if workspace:
                extra["default_headers"] = {"anthropic-workspace-id": workspace}
            client = anthropic.Anthropic(api_key=key, max_retries=0, timeout=float(cfg["api_retries"]["timeout_s"]), **extra)
        self.client = client
        self.cfg = cfg
        self.log = log
        self.sleep = sleep
        self.retries = cfg["api_retries"]
        self.price = load_prices().get(cfg["agent_model"])

    def available(self, index: int) -> bool:
        return True

    def request(self, prompt) -> dict:
        content = [
            {"type": "text", "text": prompt.part1, "cache_control": {"type": "ephemeral", "ttl": "1h"}},
            {"type": "text", "text": prompt.part2},
        ]
        kw = {
            "model": self.cfg["agent_model"],
            "max_tokens": int(self.cfg["max_output_tokens"]),
            "messages": [{"role": "user", "content": content}],
        }
        if self.cfg["thinking"] is not None:
            kw["thinking"] = dict(self.cfg["thinking"])
        if self.cfg["effort"] is not None:
            kw["output_config"] = {"effort": self.cfg["effort"]}
        return kw

    def _wait(self, attempt: int, retry_after: float | None) -> float:
        wait = min(self.retries["max_wait_s"], self.retries["first_wait_s"] * 2**attempt)
        if retry_after is not None:
            wait = max(wait, min(retry_after, self.retries["max_wait_s"] * 3))
        return wait * (1 + 0.1 * random.random())

    def _classify(self, exc) -> tuple[bool, float | None, str]:
        """(retry?, the server's retry-after if any, a description)."""
        import anthropic

        if isinstance(exc, (anthropic.APIConnectionError, anthropic.APITimeoutError)):
            return True, None, f"connection problem ({type(exc).__name__})"
        if isinstance(exc, anthropic.APIStatusError):
            status = exc.status_code
            message = str(getattr(exc, "message", exc))[:300]
            retry_after = None
            try:
                h = exc.response.headers.get("retry-after")
                retry_after = float(h) if h is not None else None
            except (AttributeError, TypeError, ValueError):
                retry_after = None
            if status == 429:
                if retry_after is None:
                    return False, None, f"429 without a retry-after, which means a spend cap was reached: {message}"
                return True, retry_after, f"rate limited: {message}"
            if status in (500, 502, 503, 504, 529):
                return True, retry_after, f"{status}: {message}"
            if status == 400:
                if "workspace" in message.lower():
                    var = self.cfg.get("api_workspace_env") or "CPL_ANTHROPIC_WORKSPACE"
                    return False, None, (f"400, the key is not scoped to one workspace: set {var} to the workspace ID "
                                         f"(see the README, 'Running with your own API key'): {message}")
                return False, None, f"400 (a spend limit, or a request the API rejects): {message}"
            if status == 402:
                return False, None, f"402, a billing problem: {message}"
            if status in (401, 403):
                return False, None, f"{status}, the key is not accepted: {message}"
            return False, None, f"{status}: {message}"
        if isinstance(exc, anthropic.APIError):  # for example an error event in the middle of a stream
            return True, None, f"{type(exc).__name__}: {str(exc)[:300]}"
        raise exc

    def respond(self, prompt, index: int, where=None) -> Response:
        kw = self.request(prompt)
        t0 = time.monotonic()
        failures = []
        for attempt in range(int(self.retries["tries"])):
            try:
                with self.client.messages.stream(**kw) as stream:
                    message = stream.get_final_message()
                break
            except Exception as exc:
                retry, retry_after, what = self._classify(exc)
                failures.append(what)
                if not retry:
                    raise StopRun(f"the API call stopped the run: {what}") from exc
                if attempt + 1 >= int(self.retries["tries"]):
                    raise StopRun(f"the API kept failing after {attempt + 1} tries; last: {what}") from exc
                wait = self._wait(attempt, retry_after)
                self.log(f"  API: {what}; trying again in {wait:.0f} s")
                self.sleep(wait)
        raw = _dump(message)
        if where is not None:
            Path(where).mkdir(parents=True, exist_ok=True)
            tmp = Path(where) / "response_raw.json.tmp"
            tmp.write_text(json.dumps(raw))
            tmp.replace(Path(where) / "response_raw.json")  # saved before anything else touches it
        text = "".join(b.get("text", "") for b in raw.get("content", []) if b.get("type") == "text")
        usage = raw.get("usage") or {}
        meta = {
            "backend": self.name,
            "source": raw.get("id"),
            "model": raw.get("model"),
            "stop_reason": raw.get("stop_reason"),
            "stop_details": raw.get("stop_details"),
            "input_tokens": usage.get("input_tokens") or 0,
            "output_tokens": usage.get("output_tokens") or 0,
            "cache_creation_input_tokens": usage.get("cache_creation_input_tokens") or 0,
            "cache_read_input_tokens": usage.get("cache_read_input_tokens") or 0,
            "output_tokens_details": usage.get("output_tokens_details"),
            "cost_usd": cost_usd(usage, self.price),
            "request": {k: kw[k] for k in ("model", "max_tokens") if k in kw}
            | {"thinking": kw.get("thinking"), "output_config": kw.get("output_config")},
            "failed_tries": failures,
            "seconds": round(time.monotonic() - t0, 1),
        }
        if meta["stop_reason"] == "max_tokens":
            self.log("  API: the response hit max_output_tokens and may be cut off; raise it or lower effort")
        if meta["stop_reason"] == "refusal":
            self.log(f"  API: the model declined this round ({(meta['stop_details'] or {}).get('category')})")
        return Response(text=text, meta=meta)
