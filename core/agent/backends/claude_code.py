"""The Claude Code backend: one headless run of the official Claude Code CLI per attempt.

This lets a run draw on a Claude subscription (Pro or Max) through the user's
own Claude Code login instead of billing an API key. Each attempt runs

    claude -p --tools "" --output-format stream-json --verbose --no-session-persistence
           --setting-sources "" --disable-slash-commands --strict-mcp-config
           --model <agent_model> --effort <effort> --system-prompt <short>

with the prompt on stdin and an empty temporary folder as the working
directory, so the CLI behaves as a plain model call: no tools, no files, no
project settings, no MCP servers. The streamed output holds every assistant
message and a final result event. A long answer arrives as several assistant
messages, because the CLI continues when one hits its output limit or when its
stream is cut off, and the result's own text field holds only the last of
them; so the response text is joined from the assistant messages (see _join:
a cut falls in the middle of a line as often as not, so the pieces are
concatenated exactly), and the result event gives the tokens used. The CLI's own dollar figure is recorded as api_equivalent_usd, while
cost_usd stays 0 because nothing is billed per call.

The CLI's environment has ANTHROPIC_API_KEY and the pipeline's key variable
removed, so it cannot fall back to billing an API key, and has
CLAUDE_CODE_NO_MODEL_FALLBACK set, so it cannot answer with another model when
the requested one declines. An answer that still shows another model (a swap
event, or another model's output in modelUsage) stops the run; a refusal is
recorded as one (stop_reason refusal), and the loop counts refusals. Each
round's meta records the output tokens of every model that answered. Usage-limit and
overload errors are retried with growing waits (a subscription's window can
take a while to reset); a login problem stops the run, which `resume`
continues later.

Whether a subscription may be used this way is governed by Anthropic's terms
for Claude Code, which have changed over time: check the current policy for
your account before relying on it.
"""

from __future__ import annotations

import json
import os
import random
import shutil
import subprocess
import tempfile
import time
from pathlib import Path

from . import BackendError, Response
from .api import StopRun

SYSTEM_PROMPT = (
    "You are answering a research prompt. You have no tools and no files. Answer the message directly and "
    "completely, in exactly the format it asks for, and nothing else."
)
KEY_VARIABLES = ("ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN")
# Unless this is set, the CLI answers with another model when the requested one declines (its "refusal
# fallback") or is unavailable, and says so only in its events and the result's modelUsage: the records
# would credit the run's model with another model's work. A run checks every answer for a swap anyway.
NO_MODEL_FALLBACK = {"CLAUDE_CODE_NO_MODEL_FALLBACK": "1"}
SWAP_EVENTS = ("model_fallback", "model_refusal_fallback", "model_consent_fallback")
REFUSAL_EVENT = "model_refusal_no_fallback"
LIMIT_WORDS = ("usage limit", "rate limit", "rate_limit", "overloaded", "too many requests", "capacity", "529", "429")
LOGIN_WORDS = ("not logged in", "login", "authenticat", "unauthorized", "invalid api key", "401", "403")
STDERR_TAIL = 2000


def _parse_output(out: str) -> tuple[dict | None, list[dict]]:
    """The CLI's result event and every assistant message's text, in order.

    stream-json prints one JSON object per line. Lines that are not JSON
    objects are ignored. A plain `json` result (one object) parses the same way.
    """
    result, messages = None, []
    for line in out.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            ev = json.loads(line)
        except ValueError:
            continue
        if not isinstance(ev, dict):
            continue
        if ev.get("type") == "assistant":
            msg = ev.get("message") if isinstance(ev.get("message"), dict) else {}
            content = msg.get("content")
            parts = []
            if isinstance(content, str):
                parts.append(content)
            elif isinstance(content, list):
                for block in content:
                    if isinstance(block, dict) and block.get("type") == "text" and isinstance(block.get("text"), str):
                        parts.append(block["text"])
            if parts:
                messages.append({"text": "".join(parts), "stop_reason": msg.get("stop_reason")})
        elif ev.get("type") == "result":
            result = ev
    return result, messages


def model_events(out: str) -> list[dict]:
    """The CLI's events about the model itself, in order: a swap to another model, or a refusal."""
    events = []
    for line in out.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            ev = json.loads(line)
        except ValueError:
            continue
        if not isinstance(ev, dict):
            continue
        if ev.get("type") == "system" and ev.get("subtype") in (*SWAP_EVENTS, REFUSAL_EVENT):
            keep = ("subtype", "original_model", "fallback_model", "api_refusal_category", "api_refusal_explanation", "scope")
            events.append({k: ev[k] for k in keep if k in ev})
        elif ev.get("type") == "assistant" and isinstance(ev.get("message"), dict) and ev["message"].get("stop_reason") == "refusal":
            events.append({"subtype": "refusal"})
    return events


def models_used(data) -> dict:
    """Output tokens per model, from the result's modelUsage (empty when the CLI gave none)."""
    usage = data.get("modelUsage") if isinstance(data, dict) else None
    if not isinstance(usage, dict):
        return {}
    return {m: int((u or {}).get("outputTokens") or 0) for m, u in usage.items() if isinstance(u, dict) or u is None}


def swapped(events: list[dict], data, model: str) -> str | None:
    """Why the answer is not (only) the run's model's, or None."""
    for e in events:
        if e["subtype"] in SWAP_EVENTS:
            return f"Claude Code answered with {e.get('fallback_model')} instead of {e.get('original_model') or model} ({e['subtype']})"
    usage = data.get("modelUsage") if isinstance(data, dict) else None
    others = sorted(m for m, u in (usage or {}).items() if isinstance(u, dict) and (u.get("outputTokens") or 0) > 0
                    and model not in (m, u.get("canonicalModel")))
    if others:
        return f"Claude Code's answer has output from {', '.join(others)}, not only {model}"
    return None


def refused(events: list[dict]) -> str | None:
    """The refusal category ('' when none came with it) if the model declined, else None."""
    hits = [e for e in events if e["subtype"] in (REFUSAL_EVENT, "refusal")]
    if not hits:
        return None
    return next((str(e["api_refusal_category"]) for e in hits if e.get("api_refusal_category")), "")


MAX_RESUME_OVERLAP = 4096


def _overlap(a: str, b: str) -> int:
    """The longest k with a ending in b[:k]: what a resumed stream repeated before the cut."""
    for k in range(min(len(a), len(b), MAX_RESUME_OVERLAP), 0, -1):
        if a.endswith(b[:k]):
            return k
    return 0


def _concat(messages: list[dict], drop_overlap: bool) -> str:
    text = ""
    for i, m in enumerate(messages):
        part = m["text"]
        if i:
            cut = messages[i - 1].get("stop_reason") in (None, "max_tokens")
            if cut and drop_overlap:
                part = part[_overlap(text, part) :]
            elif not cut and not text.endswith("\n"):
                text += "\n"
        text += part
    return text


def _join(messages: list[dict]) -> str:
    """Assistant messages in order, as one answer.

    The CLI splits an answer when its stream is cut off (a message with no stop reason,
    or max_tokens at the output limit) and continues it in the next message, at the exact
    character where it stopped, in the middle of a line as often as not. So nothing goes
    between such pieces. A resumed stream sometimes repeats a few characters from before
    the cut; when the plain join holds no recipe that parses, the join that drops the
    repetition is tried, and kept if it does. Messages that ended on their own are
    separated by a newline.
    """
    plain = _concat(messages, drop_overlap=False)
    if len(messages) < 2 or not any(m.get("stop_reason") in (None, "max_tokens") for m in messages[:-1]):
        return plain
    from ..parse import ParseError, parse_response

    try:
        parse_response(plain)
        return plain
    except ParseError:
        pass
    trimmed = _concat(messages, drop_overlap=True)
    try:
        parse_response(trimmed)
        return trimmed
    except ParseError:
        return plain


def _run_cli(cmd, prompt_text, env, cwd, timeout_s):
    """subprocess.run, kept separate so tests can replace it."""
    return subprocess.run(
        cmd, input=prompt_text, capture_output=True, text=True, env=env, cwd=cwd, timeout=timeout_s
    )


class ClaudeCodeBackend:
    name = "claude_code"

    def __init__(self, cfg: dict, log=print, runner=None, sleep=time.sleep, environ=None, check_login: bool = True):
        self.cfg = cfg
        self.log = log
        self.run = runner or _run_cli
        self.sleep = sleep
        self.retries = cfg["api_retries"]
        self.command = cfg["claude_code_command"]
        env = dict(os.environ if environ is None else environ)
        for var in KEY_VARIABLES + (cfg["api_key_env"],):
            env.pop(var, None)  # the CLI's own login, never a key from the environment
        env.update(NO_MODEL_FALLBACK)
        self.env = env
        if runner is None:
            if shutil.which(self.command) is None:
                raise BackendError(f"the Claude Code CLI ({self.command!r}) is not installed or not on PATH")
            if check_login:
                self._check_login()

    def _check_login(self) -> None:
        try:
            r = subprocess.run([self.command, "auth", "status"], capture_output=True, text=True, env=self.env, timeout=60)
            status = json.loads(r.stdout) if r.stdout.strip().startswith("{") else {}
        except (OSError, subprocess.TimeoutExpired, ValueError) as exc:
            raise BackendError(f"could not check the Claude Code login: {exc}") from exc
        if not status.get("loggedIn"):
            raise BackendError("Claude Code is not logged in; run `claude` once and sign in with your subscription")

    def available(self, index: int) -> bool:
        return True

    def command_line(self) -> list[str]:
        # Not --bare: that mode skips keychain reads and accepts only an API key, so a subscription
        # login would look logged out. These flags give the same isolation without touching auth.
        cmd = [self.command, "-p", "--tools", "", "--output-format", "stream-json", "--verbose", "--no-session-persistence"]
        cmd += ["--setting-sources", "", "--disable-slash-commands", "--strict-mcp-config"]
        cmd += ["--system-prompt", SYSTEM_PROMPT, "--model", self.cfg["agent_model"]]
        if self.cfg["effort"] is not None:
            cmd += ["--effort", self.cfg["effort"]]
        return cmd

    def _wait(self, attempt: int) -> float:
        wait = min(self.retries["max_wait_s"], self.retries["first_wait_s"] * 2**attempt)
        return wait * (1 + 0.1 * random.random())

    @staticmethod
    def _classify(text: str) -> tuple[bool, str]:
        """(retry?, description) for an error the CLI reported."""
        low = text.lower()
        if any(w in low for w in LOGIN_WORDS) and not any(w in low for w in LIMIT_WORDS):
            return False, f"Claude Code login problem: {text[:300]}"
        if any(w in low for w in LIMIT_WORDS):
            return True, f"usage or rate limit: {text[:300]}"
        return True, f"Claude Code error: {text[:300]}"

    def respond(self, prompt, index: int, where=None) -> Response:
        cmd = self.command_line()
        t0 = time.monotonic()
        failures = []
        tries = int(self.retries["tries"])
        events, declined = [], None
        for attempt in range(tries):
            with tempfile.TemporaryDirectory(prefix="cpl-claude-code-") as cwd:
                try:
                    r = self.run(cmd, prompt.text, self.env, cwd, float(self.retries["timeout_s"]))
                except subprocess.TimeoutExpired:
                    retry, what = True, f"Claude Code did not answer within {self.retries['timeout_s']:g} s"
                    r = None
                except OSError as exc:
                    raise StopRun(f"could not run the Claude Code CLI: {exc}") from exc
            if r is not None:
                out = (r.stdout or "").strip()
                data, messages = _parse_output(out)
                events = model_events(out)
                swap = swapped(events, data, self.cfg["agent_model"])
                if swap:
                    raise StopRun(f"{swap}; the run stops rather than record another model's answer as {self.cfg['agent_model']}'s")
                text = _join(messages) if messages else (data or {}).get("result")
                declined = refused(events)
                if declined is not None:  # the loop counts refusals (max_consecutive_refusals); asking again is its call
                    data, text = data if isinstance(data, dict) else {}, _join(messages) if messages else ""
                    self.log(f"  Claude Code: the model declined this round ({declined or 'no category given'})")
                    break
                if r.returncode == 0 and isinstance(data, dict) and not data.get("is_error") and text is not None:
                    break
                message = ""
                if isinstance(data, dict):
                    message = str(data.get("result") or data.get("error") or data.get("subtype") or "")
                message = message or (r.stderr or "")[-STDERR_TAIL:] or out[-STDERR_TAIL:] or f"exit code {r.returncode}"
                retry, what = self._classify(message)
            failures.append(what)
            if not retry:
                raise StopRun(f"Claude Code stopped the run: {what}")
            if attempt + 1 >= tries:
                raise StopRun(f"Claude Code kept failing after {tries} tries; last: {what}. Resume later with `python -m core.loop resume`.")
            wait = self._wait(attempt)
            self.log(f"  Claude Code: {what}; trying again in {wait:.0f} s")
            self.sleep(wait)

        if where is not None:
            Path(where).mkdir(parents=True, exist_ok=True)
            tmp = Path(where) / "response_raw.json.tmp"
            tmp.write_text(json.dumps({**data, "assistant_messages": messages}))
            tmp.replace(Path(where) / "response_raw.json")
        usage = data.get("usage") or {}
        last_stop = messages[-1].get("stop_reason") if messages else None
        meta = {
            "backend": self.name,
            "source": data.get("session_id"),
            "model": self.cfg["agent_model"],
            "stop_reason": "refusal" if declined is not None else
                           (last_stop or data.get("stop_reason") or ("end_turn" if not data.get("is_error") else "error")),
            "stop_details": {"category": declined} if declined is not None else None,
            "models_used": models_used(data),  # output tokens per model that answered, from the CLI's modelUsage
            "safety_stops": data.get("safety_stops"),
            "model_events": events,
            "input_tokens": int(usage.get("input_tokens") or 0),
            "output_tokens": int(usage.get("output_tokens") or 0),
            "cache_creation_input_tokens": int(usage.get("cache_creation_input_tokens") or 0),
            "cache_read_input_tokens": int(usage.get("cache_read_input_tokens") or 0),
            "cost_usd": 0.0,  # a subscription is not billed per call
            "api_equivalent_usd": data.get("total_cost_usd"),
            "num_turns": data.get("num_turns"),
            "assistant_messages": len(messages),
            "request": {"command": cmd[:1] + cmd[1:10]},
            "failed_tries": failures,
            "seconds": round(time.monotonic() - t0, 1),
        }
        return Response(text=str(text), meta=meta)
