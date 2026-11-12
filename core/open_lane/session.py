"""One open-lane session: the agent's workspace, its five tools, their budgets and their log.

A session lives in an attempt's folder:

    attempt_j/open_lane/
        session.json          what the tools need (paths, networks, budgets) and what was used so far
        tools.jsonl           every tool call, appended as it happens: tool, arguments, outcome, seconds
        workspace/            the agent's Lean modules (Candidate/<Name>.lean) and their compiled output
        submissions/<n>/      one folder per submit_candidate call: the candidate as submitted, receipt.json

The tools:

- lean_check(path, source or edits, network, claimed_count, certificate): save a module in the workspace (its
  full source, or edits to the module saved at that path, each of whose old texts must occur exactly once) and
  compile it against the protected module of that network and claim (`accept.py compile` of the Lean project,
  in its box), returning the compiler's messages. Counts against the compile budget.
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

Drafts: the agent's unfinished work goes on with it. A new session of a proof round also gets the modules
that the workspace of the latest earlier round's session held when that session ended and that are not the
version a carried module has (draft_modules): at their own path, or set apart in drafts/ (drafts/Candidate/...,
which read_file reads) when a carried module holds the path. They are not accepted and are listed apart from
the carried modules; they are never compiled before the agent begins, and a submission of them is checked as
any other. session.json's `drafts` says what was put where, when each was last saved and whether it compiled
then. A draft the agent leaves as it was goes on to the next round the same way.

The Python workspace: py/ in the session folder. Each run_python call starts in a fresh folder, with the
workspace's files at py/ (importable: `import name` loads py/name.py); what the call leaves there is the
workspace afterwards, within open_lane.python_workspace_mb and python_workspace_files (a link, a file with a
second name or an odd name is not kept). save_as keeps the call's code itself as py/<name>.py before it
runs. read_file reads its text files. A new session of a proof round starts with the workspace the latest
earlier round's session ended with (python_workspace_from); session.json's `py_files` says when each file
was last saved. Nothing in it is checked or counted: it is the agent's notebook.

Budgets persist in session.json, so a session that is started again (a resumed run) continues them rather
than starting afresh, and its earlier submissions and their receipts stay.

The session's clock: the backend starts it before each run of the agent (start_clock), for as long as that run
may last (open_lane.worker_seconds), and its last open_lane.notes_reserve_seconds are kept for the agent's
answer, which holds its notes for the next round. Every tool's answer says how many seconds are left before
them (`remaining.seconds`). No call starts when none are left, and none runs past them: a compile, a program
or a submission still running then is stopped, with every process it started, and the agent is told so. What
the agent wrote is saved before a call starts (a module before it is compiled, run_python's code before it
runs, as python/<n>.py), so a call or a session that is stopped loses nothing of it.

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

import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

import psutil

from ..runner import WORKSPACE as PY_DIR
from ..runner import Limits, run_recipe, workspace_files
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
PY_MODULE = re.compile(r"^py/[A-Za-z_][A-Za-z0-9_]*\.py$")  # run_python's save_as
MIB = 1024 * 1024
SUBMIT_TIMEOUT_S = 4 * 3600
COMPILE_TIMEOUT_S = 3600
EARLY_WORD_TIMEOUT_S = 180  # for Lean's word, at a compile, on what a module uses of the library; asked again at a submission
LATE_QUESTION_S = 20  # with fewer seconds left after a compile or a submission, Lean's further questions wait for the session's end
TIME_UP = ("this session's time is up: its last {reserve:.0f} s are kept for your answer. Call no more tools; end now with "
           "the answer the message asks for, in its format.")


def _monotonic() -> float:  # the clocks of a session's deadline, apart so that a test can move them
    return time.monotonic()


def _wall() -> float:
    return time.time()


def kill_tree(pid: int) -> None:
    """Kill a process and every process under it. subprocess kills only the process it started, and a compile
    runs in a grandchild of the service's process (the box's runner, which becomes Lean): stopping the service
    alone would leave Lean running beside whatever comes next."""
    try:
        root = psutil.Process(pid)
        procs = root.children(recursive=True) + [root]
    except psutil.Error:
        return
    for p in procs:
        try:
            p.kill()
        except psutil.Error:
            pass
    psutil.wait_procs(procs, timeout=10)
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


def last_compiles(session_path: Path) -> dict[str, dict]:
    """Per module path, the outcome of the last lean_check of a session that saved it (tools.jsonl): a refused
    call saves nothing, so this is the call that saved the text the workspace holds."""
    out: dict[str, dict] = {}
    log = Path(session_path) / "tools.jsonl"
    if not log.is_file():
        return out
    for line in log.read_text().splitlines():
        try:
            e = json.loads(line)
        except ValueError:
            continue
        outcome, path = e.get("outcome") or {}, (e.get("args") or {}).get("path")
        if e.get("tool") == "lean_check" and "ok" in outcome and isinstance(path, str):
            out[path] = outcome
    return out


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()[:16]


def source_session(run_path: Path, k: int) -> tuple[Path | None, int | None]:
    """The session whose unfinished work a new session of proof round k starts from: the latest earlier round's
    (its last attempt), with that round's number; (None, None) in round 1."""
    for kk in range(k - 1, 0, -1):
        attempts = sorted((p for p in (Path(run_path) / f"round_{kk:03d}").glob("attempt_*")
                           if p.name[len("attempt_"):].isdigit() and (p / "open_lane" / "workspace").is_dir()),
                          key=lambda p: int(p.name[len("attempt_"):]))
        if attempts:
            return attempts[-1] / "open_lane", kk
    return None, None


def python_workspace_from(run_path: Path, k: int) -> list[dict]:
    """The Python workspace a new session of proof round k starts with: the files of py/ of the session of
    source_session as it ended, each with the round it was last saved in (None when that is not on record)."""
    src, _ = source_session(run_path, k)
    if src is None:
        return []
    try:
        before = json.loads((src / "session.json").read_text()).get("py_files") or {}
    except (OSError, ValueError, AttributeError):
        before = {}
    before = before if isinstance(before, dict) else {}
    files, _ = workspace_files(src / PY_DIR)
    out = []
    for rel, path in sorted(files.items()):
        data = path.read_bytes()
        meta = before.get(rel) if isinstance(before.get(rel), dict) else {}
        out.append({"path": rel, "data": data, "bytes": len(data), "sha256": _sha(data),
                    "saved_round": meta.get("saved_round") if meta.get("sha256") == _sha(data) else None})
    return out


def draft_modules(run_path: Path, k: int, carried: list[dict]) -> list[dict]:
    """The agent's unfinished modules for a new session of proof round k, from the session of the latest earlier
    round (its last attempt) as it ended: each module of its workspace whose text is not the version a module
    carried into round k has, and each draft it had set apart and left as it was (its workspace still holding,
    at that path, what it held when the draft was set apart). A draft goes to its own path, or to drafts/ when a
    carried module holds the path. Each entry: path, text, set_apart, lines, sha256, the round its text was last
    saved in and whether it compiled then (None when no compile of it is on record)."""
    src, kk = source_session(run_path, k)
    if src is None:
        return []
    held = {m["path"]: Path(m["source"]).read_bytes() for m in carried}
    try:
        before = {d["path"]: d for d in json.loads((src / "session.json").read_text()).get("drafts") or []
                  if isinstance(d, dict) and isinstance(d.get("path"), str)}
    except (OSError, ValueError, AttributeError):
        before = {}
    saved = last_compiles(src)
    found: dict[str, tuple[bytes, dict]] = {}
    ws = src / "workspace"
    for f in sorted(ws.glob("Candidate/**/*.lean")):
        rel = f.relative_to(ws).as_posix()
        if f.is_symlink() or not f.is_file() or not MODULE_PATH.match(rel):
            continue
        data = f.read_bytes()
        prior = before.get(rel) or {}
        if rel in saved:  # saved in that session
            meta = {"saved_round": kk, "compiled": saved[rel].get("ok"), "stopped": bool(saved[rel].get("timed_out"))}
        elif not prior.get("set_apart") and prior.get("sha256") == _sha(data):  # a draft it was given and left as it was
            meta = {k2: prior.get(k2) for k2 in ("saved_round", "compiled", "stopped")}
        else:
            meta = {"saved_round": None, "compiled": None, "stopped": False}
        found[rel] = (data, meta)
    for f in sorted((src / "drafts").glob("Candidate/**/*.lean")):
        rel = f.relative_to(src / "drafts").as_posix()
        prior = before.get(rel) or {}
        if f.is_symlink() or not f.is_file() or not MODULE_PATH.match(rel) or not prior.get("set_apart"):
            continue
        here = ws / rel
        if here.is_file() and _sha(here.read_bytes()) != prior.get("held_sha256"):
            continue  # the agent saved something else at that path since: that is the newer work
        found[rel] = (f.read_bytes(), {k2: prior.get(k2) for k2 in ("saved_round", "compiled", "stopped")})
    out = []
    for rel, (data, meta) in sorted(found.items()):
        if held.get(rel) == data:
            continue  # the accepted version, carried
        out.append({"path": rel, "text": data, "set_apart": rel in held, "lines": len(data.decode("utf-8", "replace").splitlines()),
                    "sha256": _sha(data), **meta, **({"held_sha256": _sha(held[rel])} if rel in held else {})})
    return out


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
            k = round_of(path) or 0
            if session.state.get("py_files") == "pending":  # interrupted while putting them in place: again
                session._place_python(python_workspace_from(Path(run_path), k))
            if session.state.get("drafts") == "pending":
                session._place_drafts(draft_modules(Path(run_path), k, carried_modules(Path(run_path), k)))
            if session.state.get("carried") == "pending":  # interrupted while compiling them: do it again
                session._carry(carried_modules(Path(run_path), k))
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
        drafts = draft_modules(Path(run_path), k, carried) if k and not stage else []
        python = python_workspace_from(Path(run_path), k) if k and not stage else []
        state["carried"] = "pending" if carried else []
        state["drafts"] = "pending" if drafts else []
        state["py_limits"] = {"mb": float(ol["python_workspace_mb"]), "files": int(ol["python_workspace_files"])}
        state["py_files"] = "pending" if python else {}
        if stage:
            state["stage"] = stage
        tmp = path / "session.json.tmp"
        tmp.write_text(json.dumps(state, indent=1))
        tmp.replace(state_path)
        session = cls(path)
        if stage:
            session._seed_stage()
        else:
            if python:
                session._place_python(python)
            if drafts:
                session._place_drafts(drafts)
            if carried:
                session._carry(carried)
        return session

    def surface(self) -> dict:
        """What this session shows of the Lean project (core.open_lane.surface)."""
        if self.state.get("surface"):
            return self.state["surface"]
        return surfaces.legacy(list(self.state.get("readable") or LEGACY_READABLE), self.state.get("knowledge", "minimal"))

    def _offered(self, oleans: dict, protected: str | None = None, timeout_s: float = EARLY_WORD_TIMEOUT_S) -> dict | None:
        """In a run that holds proofs to its surface: whether these compiled modules use only what the run
        offers of the Lean project's library, for the agent. None when the run has no such rule, or when Lean
        could not be asked (a module that was just compiled is asked about again when it is submitted)."""
        surface = self.surface()
        if not offered.applies(surface):
            return None
        try:
            verdict = offered.of_oleans(surface, self.lean_project, oleans, protected, timeout_s=timeout_s)
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

    def _place_python(self, files: list[dict]) -> None:
        """Put the Python workspace a new session starts with in place (python_workspace_from), within the
        session's limits, the most recently saved files first."""
        dst = self.path / PY_DIR
        shutil.rmtree(dst, ignore_errors=True)
        dst.mkdir()
        cap, most, total, kept = self.state["py_limits"]["mb"] * MIB, self.state["py_limits"]["files"], 0, {}
        for f in sorted(files, key=lambda f: (-(f.get("saved_round") or 0), f["path"])):
            if len(kept) >= most or total + f["bytes"] > cap:
                continue
            (dst / f["path"]).parent.mkdir(parents=True, exist_ok=True)
            (dst / f["path"]).write_bytes(f["data"])
            total += f["bytes"]
            kept[f["path"]] = {k: f[k] for k in ("bytes", "sha256", "saved_round")}
        self.state["py_files"] = dict(sorted(kept.items()))
        self._save()

    def _python_enabled(self) -> bool:
        """Sessions made before the Python workspace have none: their run_python is as it was."""
        return isinstance(self.state.get("py_limits"), dict) and isinstance(self.state.get("py_files"), dict)

    def _collect_python(self, root: Path, call: int) -> dict:
        """After a run_python call: the workspace becomes what the call left in its folder's py/, within the
        limits (files that did not change are kept first, then the changed ones, smallest first). What was
        not kept is said, with why. A py/ the program removed or replaced by a link leaves the workspace as
        it was."""
        old = self.state.get("py_files") or {}
        if root.is_symlink() or not root.is_dir():
            return {"not_kept": ["py/ was removed or replaced by the program: the workspace stays as it was"]}
        files, passed = workspace_files(root)
        entries = []
        for rel, path in files.items():
            try:
                entries.append((rel, path.read_bytes()))
            except OSError:
                passed.append(rel)
        same = [(r, d) for r, d in entries if (old.get(r) or {}).get("sha256") == _sha(d)]
        new = sorted(((r, d) for r, d in entries if (old.get(r) or {}).get("sha256") != _sha(d)), key=lambda e: (len(e[1]), e[0]))
        cap, most = self.state["py_limits"]["mb"] * MIB, self.state["py_limits"]["files"]
        kept, over, total = [], [], 0
        for r, d in same + new:
            if len(kept) < most and total + len(d) <= cap:
                kept.append((r, d))
                total += len(d)
            else:
                over.append(r)
        staging, cur, gone = (self.path / f"{PY_DIR}.new", self.path / PY_DIR, self.path / f"{PY_DIR}.old")
        for d in (staging, gone):
            shutil.rmtree(d, ignore_errors=True)
        staging.mkdir()
        for r, d in kept:
            (staging / r).parent.mkdir(parents=True, exist_ok=True)
            (staging / r).write_bytes(d)
        if cur.exists():
            cur.rename(gone)
        staging.rename(cur)
        shutil.rmtree(gone, ignore_errors=True)
        meta, saved = {}, []
        for r, d in kept:
            prev = old.get(r) or {}
            if prev.get("sha256") == _sha(d):
                meta[r] = prev
            else:
                meta[r] = {"bytes": len(d), "sha256": _sha(d), "saved_round": round_of(self.path), "saved_call": call}
                saved.append(f"py/{r} ({len(d):,} bytes)")
        self.state["py_files"] = dict(sorted(meta.items()))
        self._save()
        in_box = {r for r, _ in entries}
        out = {"saved": saved, "removed": [f"py/{r}" for r in old if r not in in_box and r not in passed],
               "not_kept": [f"py/{r}: over the workspace's limit ({self.state['py_limits']['mb']:g} MB, "
                            f"{most} files)" for r in over]
                           + [f"py/{r}: not a plain file with one name of letters, digits and _ . -" for r in passed]}
        return {k: v for k, v in out.items() if v}

    def _place_drafts(self, drafts: list[dict]) -> None:
        """Put the agent's unfinished modules in place (draft_modules): at their own path in the workspace, or in
        drafts/ when a carried module holds the path. Nothing is compiled."""
        for d in drafts:
            dst = (self.path / "drafts" if d["set_apart"] else self.workspace) / d["path"]
            dst.parent.mkdir(parents=True, exist_ok=True)
            dst.write_bytes(d["text"])
        self.state["drafts"] = [{k: v for k, v in d.items() if k != "text"} for d in drafts]
        self._save()

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
        def short(v):  # a long text cut, at any depth (an edit's old and new texts)
            if isinstance(v, str):
                return v if len(v) < 2000 else v[:2000] + f"... ({len(v)} chars)"
            if isinstance(v, dict):
                return {k: short(x) for k, x in v.items()}
            return [short(x) for x in v] if isinstance(v, list) else v

        line = {"at": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "tool": tool, "args": short(args), "outcome": outcome,
                "seconds": round(seconds, 2)}
        with open(self.path / "tools.jsonl", "a") as f:
            f.write(json.dumps(line) + "\n")

    def _spend(self, tool: str) -> None:
        used, budget = self.state["used"][tool], self.state["budgets"][tool]
        if used >= budget:
            raise ToolError(f"the {tool} budget of this session ({budget} calls) is used up")
        self.state["used"][tool] = used + 1
        self._save()

    def remaining(self) -> dict:
        """What is left of the session's budgets, and, once the backend has started its clock, the seconds left
        before the time kept for the agent's answer."""
        out = {t: self.state["budgets"][t] - self.state["used"][t] for t in self.state["budgets"]}
        left = self.seconds_left()
        if left is not None:
            out["seconds"] = max(0, int(left))
        return out

    # the session's clock ---------------------------------------------------------------------
    def start_clock(self, seconds: float, reserve: float) -> None:
        """Start the clock of one run of the agent (the backend does, before each run): the run may last
        `seconds`, and its last `reserve` seconds are kept for the agent's answer. Kept in session.json, which the
        tools' server reads when it starts. The deadline is kept on the monotonic clock, as the backend's own
        limit on the run is, and on the wall clock, which seconds_left falls back to."""
        self.reload()  # the tools' server of an earlier run saved its counters here
        now_m, now_w = _monotonic(), _wall()
        self.state["clock"] = {"seconds": float(seconds), "reserve_s": float(reserve), "started": time.strftime("%Y-%m-%dT%H:%M:%S%z"),
                               "monotonic_deadline": now_m + float(seconds), "wall_deadline": now_w + float(seconds)}
        self._save()

    def seconds_left(self) -> float | None:
        """Seconds before the time kept for the agent's answer, or None when no clock was started (a session
        made before there was one). The monotonic clock is the backend's (a machine asleep does not use up the
        run), and is shared by its processes; should it not be (it says more than the run's length is left, or
        less than the wall clock does), the wall clock decides."""
        clock = self.state.get("clock")
        if not clock:
            return None
        wall = clock["wall_deadline"] - _wall()
        left = clock["monotonic_deadline"] - _monotonic()
        if not wall - 5 <= left <= clock["seconds"] + 5:
            left = wall
        return left - clock["reserve_s"]

    def _time_for_call(self) -> float | None:
        """The seconds a tool call may take: None without a clock; refused when none are left, before anything
        of the call is spent."""
        left = self.seconds_left()
        if left is not None and left <= 0:
            raise ToolError(TIME_UP.format(reserve=self.state["clock"]["reserve_s"]))
        return left

    # the service, called as a program: the pipeline is a client of it, never a second service ---------
    def _service(self, args: list[str], timeout_s: float) -> dict:
        """One command of the service, stopped after timeout_s with every process it started."""
        cmd = [sys.executable, "-B", str(self.lean_project / "scripts" / "accept.py")] + args + \
              ["--repo", self.state["repo"], "--work", self.state["work_dir"], "--mode", "hardened",
               "--knowledge", self.state.get("knowledge", "minimal")]
        env = {k: v for k, v in os.environ.items() if k not in ("ANTHROPIC_API_KEY", "ANTHROPIC_AUTH_TOKEN")}
        try:
            proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True, env=env)
        except OSError as exc:
            return {"status": "error", "ok": False, "error": f"the service could not be started: {exc}"}
        with proc:
            try:
                out, err = proc.communicate(timeout=max(1.0, float(timeout_s)))
            except subprocess.TimeoutExpired:
                kill_tree(proc.pid)
                proc.wait()
                return {"status": "timeout", "ok": False, "timed_out": True,
                        "error": f"the service did not answer within {timeout_s:.0f} s"}
            except BaseException:  # the session itself is being stopped: the service goes with it
                kill_tree(proc.pid)
                raise
        try:
            return json.loads(out)
        except ValueError:
            return {"status": "error", "ok": False, "error": f"the service failed: {(err or out)[-1500:]}"}

    def _network(self, network: str) -> dict:
        if network not in self.state["networks"]:
            raise ToolError(f"{network!r} is not one of this run's networks: {sorted(self.state['networks'])}")
        return self.state["networks"][network]

    # tools -------------------------------------------------------------------------------------
    MAX_EDITS = 200

    def _edited(self, path: str, edits) -> str:
        """The module saved at path with the edits applied in order: each edit's `old` must occur exactly once in
        the text as the edits before it left it, and is replaced by its `new`. No edits: the module as saved."""
        if not isinstance(edits, list) or len(edits) > self.MAX_EDITS or not all(
                isinstance(e, dict) and set(e) == {"old", "new"} and isinstance(e["old"], str) and isinstance(e["new"], str)
                for e in edits):
            raise ToolError(f"edits must be a list of at most {self.MAX_EDITS} objects {{\"old\": text, \"new\": text}}")
        src = self.workspace / path
        if src.is_symlink() or not src.is_file():
            raise ToolError(f"no module {path} in your workspace to edit: give its full source")
        text = src.read_text()
        for i, e in enumerate(edits, 1):
            first = text.find(e["old"]) if e["old"] else -1
            again = text.find(e["old"], first + 1) if first >= 0 else -1
            if first < 0 or again >= 0:
                n = "does not occur" if first < 0 else "occurs more than once"
                after = " as the edits before it left it" if i > 1 else ""
                raise ToolError(f"edit {i} of {len(edits)}: its old text {n} in {path}{after}; it must occur exactly once "
                                "(give more of the text around it). Nothing was saved or compiled.")
            text = text[:first] + e["new"] + text[first + len(e["old"]):]
        if len(text) > MAX_SOURCE:
            raise ToolError(f"the edited module would be longer than {MAX_SOURCE} characters")
        return text

    def lean_check(self, path: str, source: str | None = None, network: str | None = None, claimed_count: int | None = None,
                   certificate: list | None = None, edits: list | None = None) -> dict:
        t0 = time.monotonic()
        args = {"path": path, "network": network, "claimed_count": claimed_count, "certificate": certificate}
        args.update({k: v for k, v in (("source", source), ("edits", edits)) if v is not None})
        try:
            left = self._time_for_call()
            if not isinstance(path, str) or not MODULE_PATH.match(path):
                raise ToolError("path must be Candidate/<Name>.lean (identifiers only)")
            if (source is None) == (edits is None):
                raise ToolError("give either the module's full source or edits to the module saved at path")
            if source is not None and (not isinstance(source, str) or len(source) > MAX_SOURCE):
                raise ToolError(f"source must be a string of at most {MAX_SOURCE} characters")
            self._network(network)
            if isinstance(claimed_count, bool) or not isinstance(claimed_count, int) or claimed_count < 0:
                raise ToolError("claimed_count must be a natural number")
            if path in ((self._lock() or {}).get("modules") or {}):
                raise ToolError(f"{path} is locked: this session runs the accepted checker unchanged. Write in another "
                                "module, which may import it.")
            if edits is not None:
                source = self._edited(path, edits)
            self._spend("lean_check")
            src = self.workspace / path
            src.parent.mkdir(parents=True, exist_ok=True)
            src.write_text(source)  # saved before anything runs: a compile that is stopped loses nothing
            saved = {"lines": len(source.splitlines()), "sha256": hashlib.sha256(source.encode()).hexdigest()[:16]}
            self._apply_lock(network, claimed_count, certificate)
            cmd = ["compile", str(self.workspace), path, "--model", self.state["model"], "--network", network, "--claimed", str(claimed_count)]
            if certificate:
                cpath = self.path / "certificate.json"
                cpath.write_text(json.dumps(certificate))
                cmd += ["--certificate", str(cpath)]
            limit = COMPILE_TIMEOUT_S if left is None else min(COMPILE_TIMEOUT_S, left)
            res = self._service(cmd, limit)
            if res.get("status") == "timeout" and not res.get("messages"):  # stopped here, at the limit of the call
                why = (f"the {limit:.0f} s this session had left" if limit < COMPILE_TIMEOUT_S else f"the limit of a compile, {limit:.0f} s")
                res = {"ok": False, "timed_out": True, "module": module_name(path),
                       "messages": f"The compile was stopped: it did not finish within {why}. The module is saved.", "seconds": round(limit)}
            if "error" in res and not res.get("messages"):
                raise ToolError(str(res["error"]))
            text = shorten_paths((res.get("messages") or "").strip(), self.run_dir())
            out = {"ok": bool(res.get("ok")), "timed_out": bool(res.get("timed_out")), "module": res.get("module"),
                   "protected_module": res.get("protected_module"), "lines": saved["lines"],
                   "messages": excerpt(text) if text else "(no messages)", "seconds": res.get("seconds")}
            logged = {"ok": out["ok"], "saved": saved, "messages": out["messages"][:500], "errors": error_lines(out["messages"])}
            if out["timed_out"]:
                logged["timed_out"] = True
            showed = surfaces.matches(text, self.surface().get("forbidden") or [])
            if showed:  # Lean printed what the run does not show the agent (a #print, a goal, a suggestion): kept for review
                logged["showed"] = [line for _, _, line in showed[:5]]
            compiled = self.workspace / "out" / (path[: -len(".lean")] + ".olean")
            late = self.seconds_left()
            if out["ok"] and compiled.is_file() and (late is None or late >= LATE_QUESTION_S):
                said = self._offered({module_name(path): compiled},
                                     timeout_s=EARLY_WORD_TIMEOUT_S if late is None else min(EARLY_WORD_TIMEOUT_S, late))
                if said is not None and not said["clean"]:  # said now, while it costs a compile and not a submission
                    out["offered"] = said
                    logged["offered"] = False
            out["remaining"] = self.remaining()
            self._log("lean_check", args, logged, time.monotonic() - t0)
            return out
        except ToolError as exc:
            self._log("lean_check", args, {"error": str(exc)}, time.monotonic() - t0)
            raise

    def run_python(self, code: str, network: str, save_as: str | None = None) -> dict:
        t0 = time.monotonic()
        args = {"code": code, "network": network}
        if save_as is not None:
            args["save_as"] = save_as
        try:
            left = self._time_for_call()
            if not isinstance(code, str) or len(code) > MAX_SOURCE:
                raise ToolError("code must be a string")
            self._network(network)
            python = self._python_enabled()
            if save_as is not None:
                if not python:
                    raise ToolError("this session has no Python workspace")
                if not isinstance(save_as, str) or not PY_MODULE.match(save_as):
                    raise ToolError("save_as must be py/<name>.py, the name an identifier")
                files, rel, size = self.state["py_files"], save_as[len("py/"):], len(code.encode())
                total = sum(f["bytes"] for r, f in files.items() if r != rel) + size
                if total > self.state["py_limits"]["mb"] * MIB or len(set(files) | {rel}) > self.state["py_limits"]["files"]:
                    raise ToolError(f"{save_as} would take the Python workspace over its limit "
                                    f"({self.state['py_limits']['mb']:g} MB, {self.state['py_limits']['files']} files)")
            self._spend("run_python")
            call = self.state["used"]["run_python"]
            saved = Path("python") / f"{call:03d}.py"
            (self.path / saved).parent.mkdir(exist_ok=True)
            (self.path / saved).write_text(code)  # kept before it runs, whole (the log keeps the first 2,000 characters)
            if save_as is not None:  # the module is in the workspace before the code runs
                rel = save_as[len("py/"):]
                (self.path / PY_DIR).mkdir(exist_ok=True)
                (self.path / PY_DIR / rel).write_text(code)
                self.state["py_files"][rel] = {"bytes": len(code.encode()), "sha256": _sha(code.encode()),
                                               "saved_round": round_of(self.path), "saved_call": call}
                self._save()
            from ..model_folder import load_model_folder
            from ..run_config import resolve
            from ..zoo import load_weights, network_entry

            folder = load_model_folder(resolve(self.state["model"]))
            entry = network_entry(folder, network)
            weights = load_weights(folder, network)
            info = {"sizes": folder.sizes(entry["setting"]), "input_space": folder.input_space(entry["setting"])}
            lim = self.state["limits"]
            limit = float(lim["time_limit_s"]) if left is None else min(float(lim["time_limit_s"]), left)
            limits = Limits.from_config({"time_limit_s": limit, "memory_limit_mb": lim["memory_limit_mb"],
                                         "max_proof_mb": lim["max_proof_mb"], "threads_per_recipe": lim["threads_per_recipe"]})
            recipe = WRAPPER.replace("@@CODE@@", repr(code))
            from ..sandbox import choose, protected_paths

            sb = choose({"sandbox": self.state["sandbox"], "sandbox_image": "auto-research-compact-proof-sandbox:1"},
                        protected_paths(None, folder, self.path.parent))
            kept = {}

            def collect(root):
                try:
                    kept.update(self._collect_python(root, call))
                except Exception as exc:  # the call's answer must come back whatever this does
                    kept["not_kept"] = [f"the workspace could not be updated ({exc}); it stays as it was"]

            if python:
                (self.path / PY_DIR).mkdir(exist_ok=True)
            ex = run_recipe(recipe, folder.source(), weights, info, 0.0, limits, self.state["sandbox_dir"], sandbox=sb,
                            helpers=RUN_PYTHON_HELPERS, workspace=(self.path / PY_DIR) if python else None,
                            collect=collect if python else None)
            if ex.status == "ok" and isinstance(ex.proof, dict):
                output = str(ex.proof.get("stdout", ""))
            elif ex.status == "timeout" and limit < float(lim["time_limit_s"]):
                output = f"(timeout) stopped: it ran past the {limit:.0f} s this session had left"
            else:
                output = f"({ex.status}) {ex.error or ''}"
            out = {"status": ex.status, "output": output[-MAX_TEXT:], "runtime_s": ex.runtime_s}
            if save_as is not None and save_as not in kept.get("removed", []) and self.state["py_files"].get(save_as[3:]):
                kept["saved"] = [f"{save_as} ({len(code.encode()):,} bytes, before the code ran)"] + [
                    s for s in kept.get("saved", []) if not s.startswith(save_as + " ")]
            if kept:
                out["py"] = kept
            out["remaining"] = self.remaining()
            logged = {"status": ex.status, "saved": str(saved), "output": output[:500]}
            if kept:
                logged["py"] = kept
            self._log("run_python", args, logged, time.monotonic() - t0)
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
            self._time_for_call()
            if isinstance(path, str) and MODULE_PATH.match(path):  # a module of the agent's own workspace
                p = self.workspace / path
                if p.is_symlink() or not p.is_file():
                    raise ToolError(f"no module {path} in your workspace")
            elif isinstance(path, str) and path.startswith("drafts/") and MODULE_PATH.match(path[len("drafts/"):]):
                p = self.path / path  # a draft set apart, its path held by a carried module
                if p.is_symlink() or not p.is_file():
                    raise ToolError(f"no draft {path}")
            elif isinstance(path, str) and path.startswith(PY_DIR + "/") and self._python_enabled():
                rel = path[len(PY_DIR) + 1:]
                if rel not in self.state["py_files"]:
                    raise ToolError(f"no file {path} in your Python workspace")
                p = self.path / PY_DIR / rel
                if p.is_symlink() or not p.is_file():
                    raise ToolError(f"no file {path} in your Python workspace")
                try:
                    p.read_bytes().decode("utf-8")
                except UnicodeDecodeError:
                    raise ToolError(f"{path} is not text ({p.stat().st_size:,} bytes): load it in run_python") from None
            else:
                surface = self.surface()
                p = surfaces.served(surface, self.lean_project, path)
                if p is None:
                    raise ToolError("path must be a module of your workspace (Candidate/<Name>.lean), a draft set apart "
                                    "(drafts/Candidate/<Name>.lean), a file of your Python workspace (py/...) or one of "
                                    "the files of the Lean project that this run offers: " + ", ".join(surfaces.names(surface)))
                if p.is_symlink() or not p.is_file():
                    raise ToolError(f"no file {path} in the Lean project")
            all_lines = p.read_text().splitlines()
            start = max(1, int(start or 1))
            n = max(1, min(int(lines or 200), self.MAX_READ_LINES))
            chunk = all_lines[start - 1:start - 1 + n]
            text = "\n".join(f"{start + i}: {ln}" for i, ln in enumerate(chunk))
            out = {"path": path, "total_lines": len(all_lines), "start": start, "end": start + len(chunk) - 1,
                   "text": text[:MAX_TEXT], "truncated": len(chunk) < len(all_lines) - start + 1 or len(text) > MAX_TEXT,
                   "remaining": self.remaining()}
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
            self._time_for_call()
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
            out = {"matches": len(hits), "text": text[:MAX_TEXT], "truncated": len(hits) >= n, "remaining": self.remaining()}
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
            left = self._time_for_call()
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
            limit = SUBMIT_TIMEOUT_S if left is None else min(SUBMIT_TIMEOUT_S, left)
            receipt = self._service(["submit", str(cdir)], limit)
            if "status" not in receipt:
                receipt = {"status": "error", "reason": receipt.get("error", "no receipt")}
            if receipt.get("status") == "timeout" and "reason" not in receipt:
                receipt["reason"] = (f"the service did not answer within the {limit:.0f} s this session had left"
                                     if limit < SUBMIT_TIMEOUT_S else receipt.get("error"))
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

                    late = self.seconds_left()
                    try:
                        if late is not None and late < LATE_QUESTION_S:
                            check = {"verified": None, "why": "this session's time ran out before it could be asked"}
                        else:
                            check = same_checker(lock, cdir, self.lean_project, scored=stage["name"] == "seed_check",
                                                 timeout_s=offered.inspect.TIMEOUT_S if late is None else min(offered.inspect.TIMEOUT_S, late))
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
                late = self.seconds_left()
                try:
                    if late is not None and late < LATE_QUESTION_S:
                        raise RuntimeError("this session's time ran out")
                    verdict = offered.ask(surface, self.lean_project, cdir,
                                          timeout_s=offered.inspect.TIMEOUT_S if late is None else min(offered.inspect.TIMEOUT_S, late))
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
                           "certificate the name carries its hash). Give the module's full `source`, or `edits` to the "
                           "module saved at `path`: each replaces its `old` text, which must occur exactly once, by its "
                           "`new` text, in order (no edits: compile the module as saved). Returns the compiler's messages "
                           "(errors, goals, #eval output). Each call counts against the compile budget.",
            "schema": {"type": "object", "properties": {
                "path": {"type": "string", "description": "Candidate/<Name>.lean"},
                "source": {"type": "string", "description": "the module's full source (or give edits instead)"},
                "edits": {"type": "array", "description": "instead of source: changes to the module saved at path, in order",
                          "items": {"type": "object", "properties": {"old": {"type": "string"}, "new": {"type": "string"}},
                                    "required": ["old", "new"]}},
                "network": {"type": "string"},
                "claimed_count": {"type": "integer"},
                "certificate": {"type": "array", "items": {}, "description": "optional: numbers (integers, floats or [p, q]) for a scored proof"}},
                "required": ["path", "network", "claimed_count"]},
        },
        "run_python": {
            "description": "Run Python code in the recipe sandbox with `weights` (a dict of numpy arrays, the network's "
                           "state_dict), `info` (sizes and input_space) and `np` in scope; returns what it printed. "
                           "No network access; the recipe time and memory limits apply. Each call starts in a fresh "
                           "folder, but for py/, your Python workspace: what your code leaves in py/ (code, results "
                           "such as arrays or JSON) is there for your later calls and your next session, and `import "
                           "name` loads py/name.py. `save_as` (py/<name>.py) keeps the code itself there as a module "
                           "before it runs. The answer says what was saved, removed or not kept.",
            "schema": {"type": "object", "properties": {"code": {"type": "string"}, "network": {"type": "string"},
                                                        "save_as": {"type": "string", "description": "optional: py/<name>.py"}},
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
                           "lean_check and those carried over from earlier rounds), of a draft set apart "
                           "(drafts/Candidate/<Name>.lean), of a text file of your Python workspace (py/...) or of one of "
                           "the files of the Lean project that this run offers (your prompt lists them; no other file can "
                           "be read). Returns up to 400 numbered lines from `start`.",
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
        try:
            return fn(**arguments)
        except ToolError as exc:  # a refusal says the time left too, as every answer does
            left = self.seconds_left()
            if left is None or left <= 0:
                raise
            raise ToolError(f"{exc} ({left:.0f} s of this session left)") from None


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
import io, contextlib, os, sys, traceback
import numpy as np

CODE = @@CODE@@
HERE = os.path.dirname(os.path.abspath(__file__))


def make_proof(weights, info, knob):
    kept = os.path.join(HERE, "py")
    if os.path.isdir(kept) and kept not in sys.path:
        sys.path.append(kept)  # after the standard library and numpy: a file in py/ never hides them
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf), contextlib.redirect_stderr(buf):
        try:
            exec(compile(CODE, "<run_python>", "exec"), {"weights": weights, "info": info, "np": np, "__name__": "__main__"})
        except BaseException:
            buf.write(traceback.format_exc())
    text = buf.getvalue()
    for here in {HERE, os.path.realpath(HERE)}:  # paths as the code sees them: py/name.py, not the machine's folder
        text = text.replace(here + os.sep, "")
    return {"stdout": text[-20000:]}
'''
