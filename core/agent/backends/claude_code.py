"""The Claude Code backend: one headless run of the official Claude Code CLI per attempt.

This lets a run draw on a Claude subscription (Pro or Max) through the user's
own Claude Code login instead of billing an API key. Each attempt runs

    claude -p --tools "" --output-format stream-json --verbose --no-session-persistence
           --setting-sources "" --disable-slash-commands --strict-mcp-config
           --model <agent_model> --effort <effort> --system-prompt <short>

with the prompt on stdin and an empty temporary folder as the working
directory, so the CLI behaves as a plain model call: no tools, no files, no
project settings, no MCP servers. Two things the flags do not reach are dealt
with apart (docs/decisions/agent-told-nothing.md, "What Claude Code adds"): the
CLI's auto-memory and an organisation's memory are switched off by the CLI's
own switches (ISOLATION_ENV), and a machine with an organisation's managed
Claude Code configuration is refused, since its CLAUDE.md and what its hooks
print reach the model whatever the flags say. Every session's init event, where
the CLI says what it loaded, is kept and checked: a tool, an MCP server, a
skill, a slash command or a memory folder that the run did not give stops the
run. The streamed output holds every assistant
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
import re
import shutil
import subprocess
import sys
import tempfile
import time
import urllib.error
import urllib.parse
import urllib.request
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
# The CLI's auto-memory folder and an organisation's memory would put text in front of the model that the run
# did not write, and --setting-sources does not reach them (tested with 2.1.322).
ISOLATION_ENV = {"CLAUDE_CODE_DISABLE_AUTO_MEMORY": "1", "CLAUDE_CODE_DISABLE_ORG_MEMORY": "1"}
# Where the CLI reads an organisation's managed configuration. A CLAUDE.md there and what a managed hook prints
# reach the model whatever the flags say; a managed MCP configuration makes --strict-mcp-config refuse to start.
MANAGED_DIRS = {"darwin": "/Library/Application Support/ClaudeCode", "win32": "C:\\Program Files\\ClaudeCode"}
MANAGED_DEFAULT_DIR = "/etc/claude-code"
MANAGED_ENTRIES = ("CLAUDE.md", "managed-settings.json", "managed-settings.d", "managed-mcp.json")
INIT_KEYS = ("claude_code_version", "model", "tools", "mcp_servers", "slash_commands", "skills", "plugins", "agents",
             "memory_paths", "output_style", "apiKeySource")
# Who pays (`auth`, ported from the level-1 pipeline): login, the CLI's own login; api_key, the key in the
# variable api_key_env names, through an apiKeyHelper under --bare. What a try's init event may say the CLI billed
# (apiKeySource) with api_key: the helper, and nothing else.
AUTH_MODES = ("login", "api_key")
API_KEY_SOURCE = "apiKeyHelper"
VARIABLE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*")
WORKSPACE = re.compile(r"wrkspc_[A-Za-z0-9_-]+")
API_URL = "https://api.anthropic.com"
# An API account that cannot pay for more (no credit left, or its spend limit reached): waiting does not help.
BILLING_WORDS = ("credit balance", "api usage limits")
# The run's model cannot be used: it does not exist, or the login or key has no access to it.
MODEL_WORDS = ("issue with the selected model", "may not have access to it", "not_found_error")
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


def managed_configuration(root=None) -> list[Path]:
    """The organisation-managed Claude Code files on this machine (none on a machine nobody manages)."""
    base = Path(root) if root is not None else Path(MANAGED_DIRS.get(sys.platform, MANAGED_DEFAULT_DIR))
    found = []
    for name in MANAGED_ENTRIES:
        p = base / name
        if p.is_dir():
            found += sorted(p.iterdir())
        elif p.exists():
            found.append(p)
    return found


def cli_init(out: str) -> dict | None:
    """What the CLI reported it loaded for the session (its init event), or None if it reported nothing."""
    for line in out.splitlines():
        line = line.strip()
        if not line.startswith("{"):
            continue
        try:
            ev = json.loads(line)
        except ValueError:
            continue
        if isinstance(ev, dict) and ev.get("type") == "system" and ev.get("subtype") == "init":
            return {k: ev[k] for k in INIT_KEYS if k in ev}
    return None


def isolation_problems(init: dict | None, tools=(), servers=(), required: str | None = None) -> list[str]:
    """What the CLI loaded beyond what the run gives the model: a tool or an MCP server not named, any skill,
    slash command or memory folder; and, when `required` names the run's own MCP server, that server missing
    or not connected. No init event at all is a problem only when a server is required."""
    if init is None:
        return ["the CLI did not report what it loaded (no init event)"] if required else []
    problems = []
    extra = [str(t) for t in init.get("tools") or [] if t not in tools]
    if extra:
        problems.append("tools " + ", ".join(extra))
    status = {}
    for srv in init.get("mcp_servers") or []:
        name = srv.get("name") if isinstance(srv, dict) else srv
        status[str(name)] = srv.get("status") if isinstance(srv, dict) else None
    extra = sorted(n for n in status if n not in servers)
    if extra:
        problems.append("MCP servers " + ", ".join(extra))
    if required and required not in status:
        problems.append(f"no {required} MCP server (the run's tools)")
    elif required and status[required] in ("failed", "needs-auth", "disabled"):
        problems.append(f"the {required} MCP server (the run's tools) is {status[required]}")
    for key, what in (("skills", "skills"), ("slash_commands", "slash commands")):
        if init.get(key):
            problems.append(what + " " + ", ".join(str(x.get("name", x) if isinstance(x, dict) else x) for x in init[key]))
    if init.get("memory_paths"):
        paths = init["memory_paths"]
        problems.append("memory folders " + (", ".join(f"{k}: {v}" for k, v in paths.items()) if isinstance(paths, dict) else str(paths)))
    return problems


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


def _http_get(url: str, headers: dict, timeout_s: float = 30) -> tuple[int, str]:
    """(status, the start of the body) of a GET; kept separate so tests can replace it."""
    req = urllib.request.Request(url, headers=headers, method="GET")
    try:
        with urllib.request.urlopen(req, timeout=timeout_s) as r:
            return r.status, r.read(1 << 16).decode("utf-8", errors="replace")
    except urllib.error.HTTPError as exc:
        return exc.code, exc.read(1 << 16).decode("utf-8", errors="replace")


class ClaudeCodeBackend:
    name = "claude_code"

    def __init__(self, cfg: dict, log=print, runner=None, sleep=time.sleep, environ=None, check_login: bool = True, http=None):
        self.cfg = cfg
        self.log = log
        self.run = runner or _run_cli
        self.sleep = sleep
        self.retries = cfg["api_retries"]
        self.command = cfg["claude_code_command"]
        self.auth = cfg.get("auth") or "login"
        if self.auth not in AUTH_MODES:
            raise BackendError(f"auth must be login or api_key, not {self.auth!r}")
        self.key_var = str(cfg.get("api_key_env") or "")
        self.workspace_var = str(cfg.get("api_workspace_env") or "")
        for var, what in ((self.key_var, "api_key_env"), (self.workspace_var, "api_workspace_env")):
            if var and (not VARIABLE.fullmatch(var) or var in KEY_VARIABLES):
                raise BackendError(f"{what} must name an environment variable other than {' and '.join(KEY_VARIABLES)}, not {var!r}")
        env = dict(os.environ if environ is None else environ)
        for var in KEY_VARIABLES:
            env.pop(var, None)  # never a key that happens to be in the environment
        self.workspace = None
        if self.auth == "api_key":
            if not self.key_var or not env.get(self.key_var):
                raise BackendError(f"auth is api_key, but {self.key_var or 'api_key_env'} is not set: put your API key in it first")
            if not env[self.key_var].isprintable() or any(c.isspace() for c in env[self.key_var]):
                raise BackendError(f"the value of {self.key_var} has spaces or line breaks, which an API key does not have "
                                   "(a line ending from the file it came from?)")
            self.workspace = env.get(self.workspace_var) if self.workspace_var else None
            if self.workspace:
                if not WORKSPACE.fullmatch(self.workspace):
                    raise BackendError(f"{self.workspace_var} must hold a workspace ID (wrkspc_...)")
                env["ANTHROPIC_CUSTOM_HEADERS"] = f"anthropic-workspace-id: {self.workspace}"
        else:
            for var in (self.key_var, self.workspace_var):
                if var:
                    env.pop(var, None)  # the CLI's own login, never a key from the environment
        env.update(NO_MODEL_FALLBACK)
        env.update(ISOLATION_ENV)
        self.env = env
        self.http = http or _http_get
        if runner is None:
            if shutil.which(self.command) is None:
                raise BackendError(f"the Claude Code CLI ({self.command!r}) is not installed or not on PATH")
            managed = managed_configuration()
            if managed:
                raise BackendError("this machine has an organisation's managed Claude Code configuration ("
                                   + ", ".join(map(str, managed)) + "), which reaches the model whatever the run's flags "
                                   "say: Claude Code cannot run a session here as a plain model call")
            if self.auth == "api_key":
                self._check_flags()
                self._check_key()
            elif check_login:
                self._check_login()
        elif http is not None and self.auth == "api_key":
            self._check_key()

    def _check_flags(self) -> None:
        """The api_key mode needs --bare, --settings and --max-budget-usd, which older versions of the CLI lack."""
        try:
            r = subprocess.run([self.command, "--help"], capture_output=True, text=True, env=self.env, timeout=60)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise BackendError(f"could not run `{self.command} --help`: {exc}") from exc
        missing = [f for f in ("--bare", "--max-budget-usd", "--settings") if f not in (r.stdout or "") + (r.stderr or "")]
        if missing:
            raise BackendError(f"this Claude Code has no {', '.join(missing)}; update it (`claude update`) to bill an API key")

    def _check_key(self) -> None:
        """Ask the API whether it takes the key and lets it use the run's model (GET /v1/models/<model>, free of
        charge). The CLI retries a refused key from its helper for minutes; this finds it before the run starts."""
        base = (self.env.get("ANTHROPIC_BASE_URL") or API_URL).rstrip("/")
        model = self.cfg["agent_model"]
        headers = {"x-api-key": self.env[self.key_var], "anthropic-version": "2023-06-01"}
        if self.workspace:
            headers["anthropic-workspace-id"] = self.workspace
        try:
            status, body = self.http(f"{base}/v1/models/{urllib.parse.quote(model, safe='')}", headers)
        except (OSError, ValueError) as exc:  # no network, no certificates: the first session will tell
            self.log(f"WARNING: could not check the API key before the run ({type(exc).__name__}: {self.scrub(exc)[:200]}); going on")
            return
        said = self.scrub(" ".join(str(body).split())[:300])
        if status in (401, 403):
            raise BackendError(f"the API refused the key in {self.key_var} (HTTP {status}): {said}")
        if status == 404:
            raise BackendError(f"the key in {self.key_var} cannot use the model {model} (HTTP 404): {said}")
        if status == 400 and "workspace" in said.lower():
            raise BackendError(f"the key in {self.key_var} is not scoped to one workspace: set {self.workspace_var or 'api_workspace_env'} "
                               f"to the workspace ID (HTTP 400): {said}")
        if status != 200:
            self.log(f"WARNING: checking the API key before the run gave HTTP {status}: {said}; going on")
            return
        try:
            lifecycle = json.loads(body).get("lifecycle")
        except (ValueError, AttributeError):
            lifecycle = None
        if lifecycle == "retired":
            raise BackendError(f"the model {model} is retired: the API no longer answers it")
        if lifecycle == "deprecated":
            self.log(f"WARNING: the model {model} is deprecated: the API still answers it, but not for long")

    def scrub(self, text) -> str:
        """The text with the key's value taken out, should anything ever echo it."""
        text = str(text)
        key = self.env.get(self.key_var) if self.auth == "api_key" and self.key_var else None
        return text.replace(key, "<the API key>") if key else text

    def key_flags(self) -> list[str]:
        """With api_key: --bare reads no login at all (no OAuth, no keychain), so the key is the only way the CLI
        can pay; the helper prints the key from its variable, so the value is on no command line and in no file."""
        if self.auth != "api_key":
            return []
        return ["--bare", "--settings", json.dumps({"apiKeyHelper": f"printenv {self.key_var}"})]

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

    def _classify(self, text: str) -> tuple[bool, str]:
        """(retry?, description) for an error the CLI reported."""
        low = text.lower()
        if any(w in low for w in BILLING_WORDS):
            return False, f"the API account cannot pay for more: {text[:300]}"
        if any(w in low for w in MODEL_WORDS):
            return False, f"the model {self.cfg['agent_model']} cannot be used here: {text[:300]}"
        if any(w in low for w in LOGIN_WORDS) and not any(w in low for w in LIMIT_WORDS):
            if getattr(self, "auth", "login") == "api_key":
                return False, f"the API key in {self.key_var} was refused: {text[:300]}"
            return False, f"Claude Code login problem: {text[:300]}"
        if any(w in low for w in LIMIT_WORDS):
            return True, f"usage or rate limit: {text[:300]}"
        return True, f"Claude Code error: {text[:300]}"

    def respond(self, prompt, index: int, where=None) -> Response:
        cmd = self.command_line()
        t0 = time.monotonic()
        failures = []
        tries = int(self.retries["tries"])
        events, declined, init = [], None, None
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
                init = cli_init(out)
                problems = isolation_problems(init)
                if problems:
                    raise StopRun("Claude Code gave the model more than this run does (" + "; ".join(problems)
                                  + "); the run stops rather than record that answer")
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
            tmp.write_text(json.dumps({**data, "assistant_messages": messages, "cli_init": init}))
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
            "cli": init,  # what the CLI reported it loaded (checked above)
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
