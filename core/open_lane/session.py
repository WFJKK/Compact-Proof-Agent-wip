"""One open-lane session: the agent's workspace, its five tools, their budgets and their log.

A session lives in an attempt's folder:

    attempt_j/open_lane/
        session.json          what the tools need (paths, networks, budgets) and what was used so far
        tools.jsonl           every tool call, appended as it happens: tool, arguments, outcome, seconds
        workspace/            the agent's Lean modules (Candidate/<Name>.lean) and their compiled output
        submissions/<n>/      one folder per submit_candidate call: the candidate as submitted, receipt.json

The tools:

- lean_check(path, source, network, claimed_count, certificate): save a module in the workspace and compile
  it against the protected module of that network and claim (`accept.py compile` of the Lean project, in its
  box), returning the compiler's messages. Counts against the compile budget.
- run_python(code, network): run code in the recipe sandbox with that network's weights and info, returning
  what it printed. Same limits as a recipe.
- search_library(query, max_results): search the files of the Lean project that the run shows the agent (its
  surface, core.open_lane.surface: in the minimal-knowledge condition the specification, the network's
  semantics and the counted language; no docs, none of the fixed rules' sources).
- read_file(path, start, lines): read a stretch of one of those files, or of a module of the workspace, numbered.
- submit_candidate(network, claimed_count, theorem, modules, scored, kind): hand the workspace's modules to
  the acceptance service (`accept.py submit`); returns the receipt. The workspace modules that the listed
  ones import (transitively) are added. Counts against the submission budget.

The service is the Lean project's; this file is its client and never decides anything about a proof.

Carried modules: a new session's workspace starts with the modules of every submission the service accepted
in the run's earlier rounds (the latest accepted version of each module), compiled there before the agent
begins, through the same `accept.py compile` as lean_check and without charge to the budgets. The agent
imports them instead of pasting their code again; whatever it submits is compiled and checked afresh by the
service, as every submission is. session.json's `carried` says what was carried and whether it compiled.

Budgets persist in session.json, so a session that is started again (a resumed run) continues them rather
than starting afresh, and its earlier submissions and their receipts stay.

A session after the proof rounds (core.open_lane.stages) works under a lock (core.open_lane.lock): the
locked proof's checker modules are in its workspace, cannot be saved over, and are written again from the
lock before every compile and submission. When the service accepts a scored proof of the seed check, or a
lemma of the scaling question, Lean is asked whether the modules the service compiled hold the locked
checker; the answer goes into the submission's lock.json and to the agent (`locked_checker`). That is a
question about which checker a proof has, never about whether the proof is valid: that stays the service's.

In a run whose surface names the Lean project's library, Lean is also asked, of every module that compiled
and of every accepted submission, whether its constants mention a constant of that library which the run does
not show (core.open_lane.offered). The answer goes to the agent (`offered`) and, for a submission, into its
offered.json; a proof that does is recorded without a length (core.open_lane.records). What the compiler
prints is not filtered, and the agent can ask Lean about any constant: a compile whose output matches an
expression the surface forbids is marked in the log (`showed`), for whoever reviews the run.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
import sys
import time
from pathlib import Path

from ..runner import Limits, run_recipe
from ..sandbox import Sandbox
from ..util import REPO_ROOT
from . import offered
from . import surface as surfaces

MAX_TEXT = 20000  # characters of compiler output, program output or search results returned to the agent


def error_lines(text: str, limit: int = 20) -> list[str]:
    """The compiler's error lines (the message head only, cut to a line), for the tool log: the log keeps
    the first 500 characters of a compile's output, which in pilot 2 were warnings that hid the errors."""
    out = []
    for line in text.splitlines():
        if ": error" in line or line.startswith("error"):
            out.append(line[:300])
            if len(out) >= limit:
                break
    return out


def shorten_paths(text: str, run_dir) -> str:
    """A text for the agent with this machine's paths made short: a module the service compiled (in a session's
    workspace or a submission's folder) by its path in Candidate/, anything else in the run's folder as <run>/,
    the home folder as ~. Lean names a file by its absolute path, which names the run and the machine's user:
    nothing the agent needs, and a run named for a pilot would match the surface's forbidden list in every
    message Lean prints."""
    if not text:
        return text
    run = str(Path(run_dir))
    text = re.sub(re.escape(run) + r"/round_\d+/attempt_\d+/open_lane/(?:workspace|submissions/\d+)/", "", text)
    text = text.replace(run + "/", "<run>/")
    home = str(Path.home())
    if home not in ("", "/"):
        text = text.replace(home + "/", "~/")
    return text


def excerpt(text: str, limit: int = MAX_TEXT) -> str:
    """Compiler output cut to the limit: the first errors and the last lines (one later error, a `decide`
    that cannot reduce, can be thousands of lines, and the first error is the one to fix)."""
    if len(text) <= limit:
        return text
    head, tail = limit * 3 // 4, limit // 4
    return text[:head] + "\n[...]\n" + text[-tail:]
MAX_SOURCE = 400_000  # characters of one module
MODULE_PATH = re.compile(r"^Candidate/([A-Za-z_][A-Za-z0-9_]*/)*[A-Za-z_][A-Za-z0-9_]*\.lean$")
SUBMIT_TIMEOUT_S = 4 * 3600
COMPILE_TIMEOUT_S = 3600
EARLY_WORD_TIMEOUT_S = 180  # for Lean's word, at a compile, on what a module uses of the library; asked again at a submission
IMPORT_LINE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$")  # as the service reads imports
ROUND_DIR = re.compile(r"^round_(\d+)$")


class ToolError(ValueError):
    """A tool refused the call: the message goes back to the agent."""


def module_imports(text: str) -> list[str]:
    """The imports at the head of a module, read as the service reads them: blank lines and `--` comments are
    skipped, and the first other line ends the imports."""
    out = []
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("--"):
            continue
        m = IMPORT_LINE.match(line)
        if not m:
            break
        out.append(m.group(1))
    return out


def module_name(rel: str) -> str:
    """Candidate/A/B.lean -> Candidate.A.B"""
    return rel[: -len(".lean")].replace("/", ".")


def module_rel(name: str) -> str:
    """Candidate.A.B -> Candidate/A/B.lean"""
    return name.replace(".", "/") + ".lean"


def carried_modules(run_path: Path, k: int) -> list[dict]:
    """The modules of the submissions the service accepted in rounds 1 to k - 1 of the run, the latest accepted
    version of each module path (by round, attempt and submission), in an order where every module comes after
    the carried modules it imports. Each entry names the submission it comes from and what that submission
    proved; `source` is the submitted file."""
    latest: dict[str, dict] = {}
    for kk in range(1, k):
        rdir = Path(run_path) / f"round_{kk:03d}"
        attempts = sorted((p for p in rdir.glob("attempt_*") if p.name[len("attempt_"):].isdigit()),
                          key=lambda p: int(p.name[len("attempt_"):]))
        for adir in attempts:
            sub = adir / "open_lane" / "submissions"
            if not sub.is_dir():
                continue
            for d in sorted(p for p in sub.iterdir() if p.is_dir() and p.name.isdigit()):
                try:
                    receipt = json.loads((d / "receipt.json").read_text())
                    manifest = json.loads((d / "manifest.json").read_text())
                except (OSError, ValueError):
                    continue
                if receipt.get("status") != "accepted":
                    continue
                kept = offered.read(d)  # in a run that holds proofs to its surface: is this one clean?
                for rel in manifest.get("modules") or []:
                    f = d / rel
                    if not isinstance(rel, str) or not MODULE_PATH.match(rel) or f.is_symlink() or not f.is_file():
                        continue
                    latest[rel] = {
                        "beyond_offered": bool(kept) and kept.get("clean") is False,
                        "path": rel, "source": str(f), "round": kk, "attempt": int(adir.name[len("attempt_"):]),
                        "submission": int(d.name), "kind": manifest.get("kind", "performance"),
                        "theorem": manifest.get("theorem"), "statement": receipt.get("statement"),
                        "scored": (receipt.get("scoring") or {}).get("status") == "scored",
                        "certified": receipt.get("certified_count"), "length": (receipt.get("scoring") or {}).get("length"),
                        "network": manifest.get("network"), "claimed_count": int(manifest.get("claimed_count") or 0),
                        "certificate": (manifest.get("scored") or {}).get("certificate") or None,
                    }
    names = {module_name(rel): rel for rel in latest}
    deps = {n: [i for i in module_imports(Path(latest[rel]["source"]).read_text()) if i in names] for n, rel in names.items()}
    order: list[str] = []
    state: dict[str, int] = {}

    def visit(n: str) -> None:
        if state.get(n):  # done, or on the current path (a cycle, which the compiler will report)
            return
        state[n] = 1
        for dep in deps[n]:
            visit(dep)
        state[n] = 2
        order.append(n)

    for n in sorted(names):
        visit(n)
    return [latest[names[n]] for n in order]


def under_lock(stage: str | None, receipt: dict) -> bool:
    """Whether Lean is asked if an accepted submission has the locked checker (core.open_lane.lock.same_checker):
    a scored proof of the seed check, whose count is the locked checker's only then, and a lemma of the scaling
    question, whose statement is about the locked checker only then."""
    if receipt.get("status") != "accepted":
        return False
    if stage == "seed_check":
        return (receipt.get("scoring") or {}).get("status") == "scored"
    return stage == "scaling" and receipt.get("claim_kind") == "auxiliary"


def compiler_showed(path: Path) -> int:
    """How many compiles of the session in `path` printed something that matches an expression its surface
    forbids (tools.jsonl, `showed`): the agent can ask Lean about the whole library, and this is where that
    would be seen. A match is a reason to read the log, not a verdict: the agent's own names can match too."""
    log = Path(path) / "tools.jsonl"
    if not log.is_file():
        return 0
    n = 0
    for line in log.read_text().splitlines():
        try:
            n += bool((json.loads(line).get("outcome") or {}).get("showed"))
        except ValueError:
            pass
    return n


def _shortened(value, run_dir):
    """Every string in a receipt's fields as the agent sees them, its paths made short (shorten_paths)."""
    if isinstance(value, str):
        return shorten_paths(value, run_dir)
    if isinstance(value, dict):
        return {k: _shortened(v, run_dir) for k, v in value.items()}
    if isinstance(value, list):
        return [_shortened(v, run_dir) for v in value]
    return value


def round_of(path: Path) -> int | None:
    """The round of a session folder <run>/round_<k>/attempt_<j>/open_lane, or None for a folder elsewhere."""
    m = ROUND_DIR.match(Path(path).parent.parent.name)
    return int(m.group(1)) if m else None


# What sessions made before a run had a surface could read: these folders of the Lean project, and the folders
# of the run's worked examples (session.json's `readable`). A session of today records its surface instead.
LEGACY_READABLE = ("CompactCheck/", "docs/", "examples/open_lane/max2_tiny_brute/", "examples/open_lane/max2_tiny_scored/",
                   "accept/", "README.md", "lean-toolchain", "lakefile.toml")


class Session:
    def __init__(self, path: Path):
        self.path = Path(path)
        self.state_path = self.path / "session.json"
        self.state = json.loads(self.state_path.read_text())
        self.workspace = self.path / "workspace"
        self.workspace.mkdir(parents=True, exist_ok=True)
        (self.workspace / "out").mkdir(exist_ok=True)
        self.lean_project = Path(self.state["lean_project"])

    # creation ------------------------------------------------------------------------------
    @classmethod
    def create(cls, path: Path, cfg: dict, model: str, entries: list[dict], run_path: Path, stage: dict | None = None) -> "Session":
        """Make (or reopen) the session folder of an attempt. Budgets carry over if it exists.

        `stage` makes it a session after the proof rounds (core.open_lane.stages): its name (seed_check or
        scaling), the lock of the proof it is about (core.open_lane.lock) and that proof's submission folder.
        Such a session starts from the locked proof's modules alone, the locked ones cannot be changed in it,
        and `entries` are the networks it works on (for the seed check, the second network)."""
        path = Path(path)
        path.mkdir(parents=True, exist_ok=True)
        state_path = path / "session.json"
        if state_path.exists():
            session = cls(path)
            if session.state.get("carried") == "pending":  # interrupted while compiling them: do it again
                session._carry(carried_modules(Path(run_path), round_of(path) or 0))
            return session
        ol = cfg["open_lane"]
        work = ol["work_dir"] or str(run_path / "open_lane_work")
        state = {
            "lean_project": str(Path(ol["lean_project"]).expanduser().resolve()),
            "work_dir": str(Path(work).expanduser().resolve()),
            "repo": str(REPO_ROOT),
            "model": model,
            "networks": {e["id"]: {"setting": e["setting"], "n_inputs": e["n_inputs"]} for e in entries},
            "budgets": {"lean_check": int(ol["compile_calls"]), "submit_candidate": int(ol["submissions"]),
                        "run_python": int(ol["python_calls"])},
            "used": {"lean_check": 0, "submit_candidate": 0, "run_python": 0},
            "limits": {"time_limit_s": cfg["time_limit_s"], "memory_limit_mb": cfg["memory_limit_mb"],
                       "max_proof_mb": cfg["max_proof_mb"], "threads_per_recipe": cfg["threads_per_recipe"]},
            "sandbox": cfg["sandbox"],
            "sandbox_dir": cfg["sandbox_dir"],
            "surface": surfaces.of_run(cfg),
            "knowledge": ol.get("knowledge", "minimal"),
            "created": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
        }
        k = round_of(path)
        carried = carried_modules(Path(run_path), k) if k and not stage else []
        state["carried"] = "pending" if carried else []
        if stage:
            state["stage"] = stage
        tmp = path / "session.json.tmp"
        tmp.write_text(json.dumps(state, indent=1))
        tmp.replace(state_path)
        session = cls(path)
        if stage:
            session._seed_stage()
        elif carried:
            session._carry(carried)
        return session

    def surface(self) -> dict:
        """What this session shows of the Lean project (core.open_lane.surface)."""
        if self.state.get("surface"):
            return self.state["surface"]
        return surfaces.legacy(list(self.state.get("readable") or LEGACY_READABLE), self.state.get("knowledge", "minimal"))

    def _offered(self, oleans: dict, protected: str | None = None) -> dict | None:
        """In a run that holds proofs to its surface: whether these compiled modules use only what the run
        offers of the Lean project's library, for the agent. None when the run has no such rule, or when Lean
        could not be asked (a module that was just compiled is asked about again when it is submitted)."""
        surface = self.surface()
        if not offered.applies(surface):
            return None
        try:
            verdict = offered.of_oleans(surface, self.lean_project, oleans, protected, timeout_s=EARLY_WORD_TIMEOUT_S)
        except Exception:  # the compile's result must reach the agent whatever this question does
            return None
        return {"clean": verdict["clean"], "note": offered.note(verdict)}

    # a session after the proof rounds: the locked proof --------------------------------------
    def _lock(self) -> dict | None:
        return (self.state.get("stage") or {}).get("lock")

    def _seed_stage(self) -> None:
        """The locked proof in the workspace: its locked modules as they were submitted, and its other
        modules (the instance for the network it was proved on) to read and adapt. Nothing is compiled."""
        stage = self.state["stage"]
        for rel, text in stage["lock"]["modules"].items():
            dst = self.workspace / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(text)
        for rel in stage["lock"]["free"]:
            src = Path(stage["submission"]) / rel
            if MODULE_PATH.match(rel) and src.is_file() and not src.is_symlink():
                dst = self.workspace / rel
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_bytes(src.read_bytes())

    def _apply_lock(self, network: str, claimed_count: int, certificate: list | None) -> dict | None:
        """Before anything is compiled or submitted in a session with a lock: every locked module is written
        into the workspace again from the lock, for this network (the protected module's name replaced,
        nothing else). So what the service sees of the checker is the locked text whatever the session did.
        Returns what was applied, for the submission's record."""
        lock = self._lock()
        if not lock:
            return None
        from .lock import LockError, protected_name, renamed

        new = None
        if lock["protected"]:
            try:
                new = protected_name(self.lean_project, network, claimed_count, certificate)
            except LockError as exc:
                raise ToolError(str(exc))
        for rel, text in lock["modules"].items():
            dst = self.workspace / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_text(renamed(text, lock["protected"], new) if new else text)
        return {"digest": lock["digest"], "protected_from": lock["protected"], "protected_to": new, "modules": sorted(lock["modules"])}

    def _carry(self, carried: list[dict]) -> None:
        """Put the carried modules in the workspace and compile them there, in import order (not charged)."""
        for m in carried:
            dst = self.workspace / m["path"]
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(Path(m["source"]).read_bytes())
        out = []
        for m in carried:
            cmd = ["compile", str(self.workspace), m["path"], "--model", self.state["model"], "--network", m["network"],
                   "--claimed", str(m["claimed_count"])]
            if m["certificate"]:
                cpath = self.path / "carried_certificate.json"
                cpath.write_text(json.dumps(m["certificate"]))
                cmd += ["--certificate", str(cpath)]
            if m["network"] in self.state["networks"]:
                res = self._service(cmd, COMPILE_TIMEOUT_S)
            else:
                res = {"ok": False, "error": f"{m['network']} is not one of this run's networks"}
            text = (res.get("messages") or res.get("error") or "").strip()
            entry = {k: v for k, v in m.items() if k not in ("source", "certificate")}
            entry.update(lines=len((self.workspace / m["path"]).read_text().splitlines()), compiled=bool(res.get("ok")),
                         errors=[] if res.get("ok") else (error_lines(text, 3) or [text[:300]]))
            out.append(entry)
        self.state["carried"] = out
        self._save()

    def reload(self) -> None:
        """Re-read the saved state: the tools run in the MCP server's process, which saves its counters here."""
        self.state = json.loads(self.state_path.read_text())

    def _save(self) -> None:
        tmp = self.path / "session.json.tmp"
        tmp.write_text(json.dumps(self.state, indent=1))
        tmp.replace(self.state_path)

    def _log(self, tool: str, args: dict, outcome: dict, seconds: float) -> None:
        short = {k: (v if not isinstance(v, str) or len(v) < 2000 else v[:2000] + f"... ({len(v)} chars)") for k, v in args.items()}
        line = {"at": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "tool": tool, "args": short, "outcome": outcome, "seconds": round(seconds, 2)}
        with open(self.path / "tools.jsonl", "a") as f:
            f.write(json.dumps(line) + "\n")

    def _spend(self, tool: str) -> None:
        used, budget = self.state["used"][tool], self.state["budgets"][tool]
        if used >= budget:
            raise ToolError(f"the {tool} budget of this session ({budget} calls) is used up")
        self.state["used"][tool] = used + 1
        self._save()

    def remaining(self) -> dict:
        return {t: self.state["budgets"][t] - self.state["used"][t] for t in self.state["budgets"]}

    # the service, called as a program: the pipeline is a client of it, never a second service ---------
    def _service(self, args: list[str], timeout_s: float) -> dict:
        cmd = [sys.executable, "-B", str(self.lean_project / "scripts" / "accept.py")] + args + \
              ["--repo", self.state["repo"], "--work", self.state["work_dir"], "--mode", "hardened",
               "--knowledge", self.state.get("knowledge", "minimal")]
        env = {k: v for k, v in os.environ.items() if k not in ("ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN")}
        try:
            r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_s, env=env)
        except subprocess.TimeoutExpired:
            return {"status": "timeout", "ok": False, "error": f"the service did not answer within {timeout_s:g} s"}
        try:
            return json.loads(r.stdout)
        except ValueError:
            return {"status": "error", "ok": False, "error": f"the service failed: {(r.stderr or r.stdout)[-1500:]}"}

    def _network(self, network: str) -> dict:
        if network not in self.state["networks"]:
            raise ToolError(f"{network!r} is not one of this run's networks: {sorted(self.state['networks'])}")
        return self.state["networks"][network]

    # tools -------------------------------------------------------------------------------------
    def lean_check(self, path: str, source: str, network: str, claimed_count: int, certificate: list | None = None) -> dict:
        t0 = time.monotonic()
        args = {"path": path, "source": source, "network": network, "claimed_count": claimed_count, "certificate": certificate}
        try:
            if not isinstance(path, str) or not MODULE_PATH.match(path):
                raise ToolError("path must be Candidate/<Name>.lean (identifiers only)")
            if not isinstance(source, str) or len(source) > MAX_SOURCE:
                raise ToolError(f"source must be a string of at most {MAX_SOURCE} characters")
            self._network(network)
            if isinstance(claimed_count, bool) or not isinstance(claimed_count, int) or claimed_count < 0:
                raise ToolError("claimed_count must be a natural number")
            if path in ((self._lock() or {}).get("modules") or {}):
                raise ToolError(f"{path} is locked: this session runs the accepted checker unchanged. Write in another "
                                "module, which may import it.")
            self._spend("lean_check")
            src = self.workspace / path
            src.parent.mkdir(parents=True, exist_ok=True)
            src.write_text(source)
            self._apply_lock(network, claimed_count, certificate)
            cmd = ["compile", str(self.workspace), path, "--model", self.state["model"], "--network", network, "--claimed", str(claimed_count)]
            if certificate:
                cpath = self.path / "certificate.json"
                cpath.write_text(json.dumps(certificate))
                cmd += ["--certificate", str(cpath)]
            res = self._service(cmd, COMPILE_TIMEOUT_S)
            if "error" in res and not res.get("messages"):
                raise ToolError(str(res["error"]))
            text = shorten_paths((res.get("messages") or "").strip(), self.run_dir())
            out = {"ok": bool(res.get("ok")), "timed_out": bool(res.get("timed_out")), "module": res.get("module"),
                   "protected_module": res.get("protected_module"), "messages": excerpt(text) if text else "(no messages)",
                   "seconds": res.get("seconds"), "remaining": self.remaining()}
            logged = {"ok": out["ok"], "messages": out["messages"][:500], "errors": error_lines(out["messages"])}
            showed = surfaces.matches(text, self.surface().get("forbidden") or [])
            if showed:  # Lean printed what the run does not show the agent (a #print, a goal, a suggestion): kept for review
                logged["showed"] = [line for _, _, line in showed[:5]]
            compiled = self.workspace / "out" / (path[: -len(".lean")] + ".olean")
            if out["ok"] and compiled.is_file():
                said = self._offered({module_name(path): compiled})
                if said is not None and not said["clean"]:  # said now, while it costs a compile and not a submission
                    out["offered"] = said
                    logged["offered"] = False
            self._log("lean_check", args, logged, time.monotonic() - t0)
            return out
        except ToolError as exc:
            self._log("lean_check", args, {"error": str(exc)}, time.monotonic() - t0)
            raise

    def run_python(self, code: str, network: str) -> dict:
        t0 = time.monotonic()
        args = {"code": code, "network": network}
        try:
            if not isinstance(code, str) or len(code) > MAX_SOURCE:
                raise ToolError("code must be a string")
            self._network(network)
            self._spend("run_python")
            from ..model_folder import load_model_folder
            from ..run_config import resolve
            from ..zoo import load_weights, network_entry

            folder = load_model_folder(resolve(self.state["model"]))
            entry = network_entry(folder, network)
            weights = load_weights(folder, network)
            info = {"sizes": folder.sizes(entry["setting"]), "input_space": folder.input_space(entry["setting"])}
            lim = self.state["limits"]
            limits = Limits.from_config({"time_limit_s": lim["time_limit_s"], "memory_limit_mb": lim["memory_limit_mb"],
                                         "max_proof_mb": lim["max_proof_mb"], "threads_per_recipe": lim["threads_per_recipe"]})
            recipe = WRAPPER.replace("@@CODE@@", repr(code))
            from ..sandbox import choose, protected_paths

            sb = choose({"sandbox": self.state["sandbox"], "sandbox_image": "auto-research-compact-proof-sandbox:1"},
                        protected_paths(None, folder, self.path.parent))
            ex = run_recipe(recipe, folder.source(), weights, info, 0.0, limits, self.state["sandbox_dir"], sandbox=sb,
                            helpers=RUN_PYTHON_HELPERS)
            if ex.status == "ok" and isinstance(ex.proof, dict):
                output = str(ex.proof.get("stdout", ""))
            else:
                output = f"({ex.status}) {ex.error or ''}"
            out = {"status": ex.status, "output": output[-MAX_TEXT:], "runtime_s": ex.runtime_s, "remaining": self.remaining()}
            self._log("run_python", args, {"status": ex.status, "output": output[:500]}, time.monotonic() - t0)
            return out
        except ToolError as exc:
            self._log("run_python", args, {"error": str(exc)}, time.monotonic() - t0)
            raise

    MAX_READ_LINES = 400

    def read_file(self, path: str, start: int = 1, lines: int = 200) -> dict:
        """A module of the workspace, or a file of the Lean project that the run's surface shows, by line range."""
        t0 = time.monotonic()
        args = {"path": path, "start": start, "lines": lines}
        try:
            if isinstance(path, str) and MODULE_PATH.match(path):  # a module of the agent's own workspace
                p = self.workspace / path
                if p.is_symlink() or not p.is_file():
                    raise ToolError(f"no module {path} in your workspace")
            else:
                surface = self.surface()
                p = surfaces.served(surface, self.lean_project, path)
                if p is None:
                    raise ToolError("path must be a module of your workspace (Candidate/<Name>.lean) or one of the files of "
                                    "the Lean project that this run offers: " + ", ".join(surfaces.names(surface)))
                if p.is_symlink() or not p.is_file():
                    raise ToolError(f"no file {path} in the Lean project")
            all_lines = p.read_text().splitlines()
            start = max(1, int(start or 1))
            n = max(1, min(int(lines or 200), self.MAX_READ_LINES))
            chunk = all_lines[start - 1:start - 1 + n]
            text = "\n".join(f"{start + i}: {ln}" for i, ln in enumerate(chunk))
            out = {"path": path, "total_lines": len(all_lines), "start": start, "end": start + len(chunk) - 1,
                   "text": text[:MAX_TEXT], "truncated": len(chunk) < len(all_lines) - start + 1 or len(text) > MAX_TEXT}
            self._log("read_file", args, {"lines": len(chunk)}, time.monotonic() - t0)
            return out
        except ToolError as exc:
            self._log("read_file", args, {"error": str(exc)}, time.monotonic() - t0)
            raise

    def search_library(self, query: str, max_results: int = 40) -> dict:
        """The lines that match, in the files of the Lean project that the run's surface shows."""
        t0 = time.monotonic()
        args = {"query": query, "max_results": max_results}
        try:
            if not isinstance(query, str) or not query.strip():
                raise ToolError("query must be a non-empty string (a regular expression)")
            try:
                rx = re.compile(query)
            except re.error as exc:
                raise ToolError(f"not a regular expression: {exc}")
            n = max(1, min(int(max_results or 40), 200))
            hits = []
            for rel, f in surfaces.listing(self.surface(), self.lean_project):
                if not rel.endswith((".lean", ".md", ".txt")):
                    continue
                try:
                    lines = f.read_text().splitlines()
                except (OSError, UnicodeDecodeError):
                    continue
                for i, line in enumerate(lines, 1):
                    if rx.search(line):
                        hits.append(f"{rel}:{i}: {line.rstrip()[:240]}")
                        if len(hits) >= n:
                            break
                if len(hits) >= n:
                    break
            text = "\n".join(hits) if hits else "(no match)"
            out = {"matches": len(hits), "text": text[:MAX_TEXT], "truncated": len(hits) >= n}
            self._log("search_library", args, {"matches": len(hits)}, time.monotonic() - t0)
            return out
        except ToolError as exc:
            self._log("search_library", args, {"error": str(exc)}, time.monotonic() - t0)
            raise

    def submit_candidate(self, network: str, claimed_count: int, theorem: str, modules: list, scored: dict | None = None,
                         kind: str = "performance") -> dict:
        t0 = time.monotonic()
        args = {"network": network, "claimed_count": claimed_count, "theorem": theorem, "modules": modules, "scored": scored, "kind": kind}
        try:
            self._network(network)
            if kind not in ("performance", "auxiliary"):
                raise ToolError("kind must be performance (a proof of Target) or auxiliary (a lemma)")
            if not isinstance(modules, list) or not modules or not all(isinstance(m, str) and MODULE_PATH.match(m) for m in modules):
                raise ToolError("modules must be a list of Candidate/<Name>.lean paths saved with lean_check")
            for m in modules:
                if not (self.workspace / m).is_file():
                    raise ToolError(f"{m} is not in the workspace; save it with lean_check first")
            if not isinstance(theorem, str) or not theorem.startswith("Candidate."):
                raise ToolError("theorem must be the full name of the theorem proving Target, under Candidate.")
            stage, lock = self.state.get("stage") or {}, self._lock()
            if stage.get("name") == "seed_check":
                if kind != "performance" or not isinstance(scored, dict):
                    raise ToolError("the seed check takes scored proofs only: a performance submission with a scored block")
                for key in ("checker", "sound"):
                    if scored.get(key) != lock[key]:
                        raise ToolError(f"scored.{key} must be {lock[key]}: the seed check runs the locked checker")
            elif stage.get("name") == "scaling" and kind != "auxiliary":
                raise ToolError("this session takes lemmas only (kind auxiliary): the proof rounds are over")
            applied = self._apply_lock(network, claimed_count, (scored or {}).get("certificate") if isinstance(scored, dict) else None)
            if lock:  # the locked modules always go along, so the constants the manifest names are the locked ones
                modules = list(dict.fromkeys(list(modules) + list(lock["modules"])))
            modules = self.with_imports(modules)
            self._spend("submit_candidate")
            n = len(list((self.path / "submissions").glob("*"))) if (self.path / "submissions").is_dir() else 0
            cdir = self.path / "submissions" / f"{n:03d}"
            (cdir / "Candidate").mkdir(parents=True)
            for m in modules:
                dst = cdir / m
                dst.parent.mkdir(parents=True, exist_ok=True)
                dst.write_bytes((self.workspace / m).read_bytes())
            manifest = {"schema": "open-lane-candidate-v1", "candidate_id": f"{self.path.parent.name}-s{n:03d}", "kind": kind,
                        "model": self.state["model"], "network": network, "claimed_count": claimed_count,
                        "theorem": theorem, "modules": modules}
            if scored is not None:
                manifest["scored"] = scored
            (cdir / "manifest.json").write_text(json.dumps(manifest, indent=1))
            # hardened: Landlock where it exists, else process mode, which the receipt records as weak
            receipt = self._service(["submit", str(cdir)], SUBMIT_TIMEOUT_S)
            if "status" not in receipt:
                receipt = {"status": "error", "reason": receipt.get("error", "no receipt")}
            if receipt.get("status") == "timeout" and "reason" not in receipt:
                receipt["reason"] = receipt.get("error")
            receipt["submission"] = n
            (cdir / "receipt.json").write_text(json.dumps(receipt, indent=1))
            if applied:
                # the locked modules as they went to the service: the lock's text, renamed for this network. The
                # receipt carries the hash of every module the service compiled, so it says the same.
                import hashlib

                from .lock import renamed

                unasked = None
                seen = (receipt.get("digests") or {}).get("modules") or {}
                expected = {rel: renamed(text, lock["protected"], applied["protected_to"]) if applied["protected_to"] else text
                            for rel, text in lock["modules"].items()}
                applied["intact"] = all((cdir / rel).is_file() and (cdir / rel).read_text() == text for rel, text in expected.items())
                applied["in_receipt"] = bool(seen) and all(
                    seen.get(module_name(rel)) == hashlib.sha256(text.encode()).hexdigest() for rel, text in expected.items())
                (cdir / "lock.json").write_text(json.dumps(applied, indent=1))
                if under_lock(stage.get("name"), receipt):
                    # the checker this proof (or lemma) was accepted with, read by Lean from the modules the service
                    # has just compiled: is it the locked one? Asked now, before the session does anything else.
                    from .lock import same_checker

                    try:
                        check = same_checker(lock, cdir, self.lean_project, scored=stage["name"] == "seed_check")
                    except Exception as exc:  # the receipt is saved and must reach the agent whatever this question does
                        check = {"verified": None, "why": f"the question failed: {exc!r}"}
                    if check["verified"] is None:  # Lean could not be asked: nothing is recorded, the round asks again
                        unasked = check["why"]
                    else:
                        applied.update(verified=check["verified"], why=check["why"], fingerprints=check.get("fingerprints"),
                                       constants=check.get("constants"))
                        tmp = cdir / "lock.json.tmp"
                        tmp.write_text(json.dumps(applied, indent=1))
                        tmp.replace(cdir / "lock.json")
            out = {k: receipt.get(k) for k in ("status", "reason", "claim_kind", "certified_count", "domain_size", "claimed_count",
                                                "network", "statement", "axioms", "score_eligible", "execution_assurance", "scoring", "seconds")}
            out = _shortened(out, self.run_dir())  # the receipt itself stays as the service wrote it
            out["submission"] = n
            out["modules"] = modules
            surface = self.surface()
            if offered.applies(surface) and receipt.get("status") == "accepted":
                # does the accepted proof use only what this run offers of the Lean project's library? Asked of
                # Lean now, of the modules the service has just compiled; the records ask again if this fails.
                try:
                    verdict = offered.ask(surface, self.lean_project, cdir)
                    out["offered"] = {"clean": verdict["clean"], "note": offered.note(verdict)}
                except Exception as exc:  # the receipt is saved and must reach the agent whatever this question does
                    out["offered"] = {"clean": None, "note": "This submission was accepted. Whether it uses only what this run "
                                                               f"offers could not be asked now ({exc}); it is asked again when "
                                                               "this session ends."}
            if applied and "verified" in applied:
                counts = applied["verified"] and applied["intact"]
                why = (applied["why"] or "the locked modules did not reach the service unchanged") + "."
                if stage["name"] == "seed_check":
                    note = ("Lean finds the locked checker in this proof: it counts as a result of the seed check." if counts else
                            "This proof was accepted, but it does not count as a result of the seed check: " + why)
                else:
                    note = (f"Lean finds the locked checker in this submission: {lock['checker']} in a statement of yours is the "
                            "checker that was locked." if counts else
                            f"This lemma was accepted, but {lock['checker']} in it is not shown to be the locked checker: " + why)
                out["locked_checker"] = {"same": counts, "note": note}
            elif applied and unasked:
                out["locked_checker"] = {"same": None, "note": "This submission was accepted. Whether it has the locked checker could "
                                                               f"not be asked now ({unasked}); it is asked again when this session ends."}
            out["remaining"] = self.remaining()
            scoring = receipt.get("scoring") or {}
            outcome = {"status": receipt.get("status"), "scoring": scoring.get("status"),
                       "reason": (receipt.get("reason") or scoring.get("reason") or "")[:300],
                       "length": scoring.get("length"), "certified": receipt.get("certified_count")}
            if "locked_checker" in out:
                outcome["locked_checker"] = out["locked_checker"]["same"]
            if "offered" in out:
                outcome["offered"] = out["offered"]["clean"]
            self._log("submit_candidate", args, outcome, time.monotonic() - t0)
            return out
        except ToolError as exc:
            self._log("submit_candidate", args, {"error": str(exc)}, time.monotonic() - t0)
            raise

    CONTEXT_FILE = "context.jsonl"

    def log_context(self, entry: dict) -> None:
        """Append the verdict on one run of Claude Code for this session (core.open_lane.backends): `verified`
        True, False (a model swap, a tool, server, skill, slash command or memory folder beyond the run's, or no
        report of what the CLI loaded), or None (the CLI ended before it started a session). Append-only."""
        with open(self.path / self.CONTEXT_FILE, "a") as f:
            f.write(json.dumps({"at": time.strftime("%Y-%m-%dT%H:%M:%S%z"), **entry}) + "\n")

    def context(self) -> dict | None:
        """The session's context over every run of Claude Code: {"verified": False, "problems": [...]} if any run
        failed its check, {"verified": True, ...} if every run that started a session passed, None for a session
        no run of Claude Code started (the fake backend, a session from before the check)."""
        p = self.path / self.CONTEXT_FILE
        if not p.is_file():
            return None
        runs = [json.loads(line) for line in p.read_text().splitlines() if line.strip()]
        judged = [e for e in runs if e.get("verified") is not None]
        if not judged:
            return None
        problems = [q for e in judged if e["verified"] is not True for q in (e.get("problems") or ["not verified"])]
        return {"verified": not problems, "problems": problems, "runs": len(judged)}

    def run_dir(self) -> Path:
        """The run's folder, for a session at <run>/round_<k>/attempt_<j>/open_lane (else the session's folder)."""
        return self.path.parent.parent.parent if round_of(self.path) is not None else self.path

    def with_imports(self, modules: list[str]) -> list[str]:
        """The modules, and after them every module of the workspace they import, directly or not: the service
        compiles only what a submission lists, and a carried module is in the workspace without being retyped."""
        out, todo = list(modules), list(modules)
        while todo:
            f = self.workspace / todo.pop()
            if f.is_symlink() or not f.is_file():
                continue
            for name in module_imports(f.read_text()):
                rel = module_rel(name)
                if name.startswith("Candidate.") and MODULE_PATH.match(rel) and rel not in out and (self.workspace / rel).is_file():
                    out.append(rel)
                    todo.append(rel)
        return out

    def receipts(self) -> list[dict]:
        out = []
        sub = self.path / "submissions"
        if sub.is_dir():
            for d in sorted(sub.iterdir()):
                p = d / "receipt.json"
                if p.is_file():
                    try:
                        out.append(json.loads(p.read_text()))
                    except ValueError:
                        out.append({"status": "error", "reason": f"unreadable receipt {p}", "submission": int(d.name)})
        return out

    # the tool table -------------------------------------------------------------------------
    TOOLS = {
        "lean_check": {
            "description": "Save a Lean module in your workspace and compile it against the protected module of a network "
                           "and a claimed count (Protected.N_<network>_c<claimed>, which the service builds; with a "
                           "certificate the name carries its hash). Returns the compiler's messages (errors, goals, "
                           "#eval output). Each call counts against the compile budget.",
            "schema": {"type": "object", "properties": {
                "path": {"type": "string", "description": "Candidate/<Name>.lean"},
                "source": {"type": "string", "description": "the module's full source"},
                "network": {"type": "string"},
                "claimed_count": {"type": "integer"},
                "certificate": {"type": "array", "items": {}, "description": "optional: numbers (integers, floats or [p, q]) for a scored proof"}},
                "required": ["path", "source", "network", "claimed_count"]},
        },
        "run_python": {
            "description": "Run Python code in the recipe sandbox with `weights` (a dict of numpy arrays, the network's "
                           "state_dict), `info` (sizes and input_space) and `np` in scope; returns what it printed. "
                           "No network access; the recipe time and memory limits apply.",
            "schema": {"type": "object", "properties": {"code": {"type": "string"}, "network": {"type": "string"}},
                       "required": ["code", "network"]},
        },
        "search_library": {
            "description": "Search the files of the Lean project that this run offers (your prompt lists them) with a "
                           "regular expression, matched against each line's text (not against file names or line "
                           "numbers); returns the matching lines as file:line: text. To read a stretch of a file, use "
                           "read_file.",
            "schema": {"type": "object", "properties": {"query": {"type": "string"}, "max_results": {"type": "integer"}},
                       "required": ["query"]},
        },
        "read_file": {
            "description": "Read lines of a module of your workspace (Candidate/<Name>.lean: those you saved with "
                           "lean_check and those carried over from earlier rounds) or of one of the files of the Lean "
                           "project that this run offers (your prompt lists them; no other file can be read). Returns up "
                           "to 400 numbered lines from `start`.",
            "schema": {"type": "object", "properties": {"path": {"type": "string"}, "start": {"type": "integer"},
                                                        "lines": {"type": "integer"}},
                       "required": ["path"]},
        },
        "submit_candidate": {
            "description": "Submit modules from your workspace to the acceptance service as a proof that the network "
                           "answers at least claimed_count inputs correctly (theorem : Target). Returns the receipt: "
                           "status accepted or rejected with the reason, the axioms, and, with `scored`, the scoring "
                           "block (status scored or refused, the bill and the length). Each call counts against the "
                           "submission budget.",
            "schema": {"type": "object", "properties": {
                "network": {"type": "string"}, "claimed_count": {"type": "integer"},
                "theorem": {"type": "string", "description": "Candidate.<...>.<name> proving Target"},
                "modules": {"type": "array", "items": {"type": "string"},
                            "description": "paths in your workspace (saved with lean_check or carried over); the "
                                           "workspace modules they import are added"},
                "scored": {"type": "object", "description": "optional: {checker, sound, instance, certificate, claimed_bill}"},
                "kind": {"type": "string", "enum": ["performance", "auxiliary"],
                         "description": "performance (default): theorem proves Target; auxiliary: theorem is a lemma with any statement, accepted with no count and no score, listed to you in later rounds"}},
                "required": ["network", "claimed_count", "theorem", "modules"]},
        },
    }

    def call(self, tool: str, arguments: dict) -> dict:
        if tool not in self.TOOLS:
            raise ToolError(f"no tool {tool!r}; the tools are {sorted(self.TOOLS)}")
        if not isinstance(arguments, dict):
            raise ToolError("arguments must be an object")
        fn = getattr(self, tool)
        required = self.TOOLS[tool]["schema"]["required"]
        missing = [k for k in required if k not in arguments]
        if missing:
            raise ToolError(f"{tool} needs {missing}")
        allowed = set(self.TOOLS[tool]["schema"]["properties"])
        extra = sorted(set(arguments) - allowed)
        if extra:
            raise ToolError(f"{tool} does not take {extra}")
        return fn(**arguments)


# The fixed rules lane's helpers.py names that lane's rules, which this lane's agent is not told
# (docs/decisions/agent-told-nothing.md), so the folder run_python's code runs in does not hold it.
RUN_PYTHON_HELPERS = False


def run_python_folder(model_source: str) -> dict[str, str]:
    """The text files in the folder run_python's code runs in, which it can read, by name: the wrapper around
    the agent's code (recipe.py), the model's code and the harness. (The rest is the weights and input.json.)
    The check before a run scans them as it scans the prompt."""
    from ..runner import sandbox_texts

    return {"recipe.py": WRAPPER, **sandbox_texts(model_source, helpers=RUN_PYTHON_HELPERS)}


WRAPPER = '''"""The open lane's run_python: the agent's code as a recipe, its output as the proof."""
import io, contextlib, traceback
import numpy as np

CODE = @@CODE@@


def make_proof(weights, info, knob):
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        try:
            exec(compile(CODE, "<run_python>", "exec"), {"weights": weights, "info": info, "np": np, "__name__": "__main__"})
        except BaseException:
            buf.write(traceback.format_exc())
    return {"stdout": buf.getvalue()[-20000:]}
'''
