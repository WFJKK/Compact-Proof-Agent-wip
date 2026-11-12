"""The research folder of a python_then_lean run (core/open_lane/workflow.py): Research/ as the agent names it.

It belongs to the run, not to a session: <run>/research/ holds the files, and every session of the run, of
either phase and after a resume, reads and writes the same folder. The agent writes text files with
research_write and declared outputs of run_python; it lists them with research_list and reads them with
read_file. Nothing in it is checked or counted: a candidate record is the agent's account, its
`agent_assessment` the agent's opinion, and only the acceptance service's receipts say that something is
proved.

Paths are `Research/<part>/.../<name>`, each part of letters, digits and `_ . -` and not starting with a dot,
at most MAX_DEPTH parts. No link is followed or made, and every write replaces a regular file atomically. The
folder is held to the run's research_workspace_mb and research_workspace_files. An index
(<run>/workflow/research_index.json) says which round and call last wrote each file.

Two kinds of file have a form, checked when written:

- Research/candidates/<id>.json: a candidate record, a JSON object whose `id` is the file's name, with at least
  the keys of CANDIDATE_KEYS. No key and no assessment may say that the claim is proved, verified or accepted.
- Research/shortlist.json: the candidates to formalise, in order: a JSON list of {"id", "reason"}.
"""

from __future__ import annotations

import fcntl
import hashlib
import json
import os
import re
import shutil
import stat
import time
from contextlib import contextmanager
from pathlib import Path

PREFIX = "Research"
DIR = "research"  # <run>/research
STATE_DIR = "workflow"  # <run>/workflow: the controller's files (locks, index, probes, transition)
INDEX = "research_index.json"
MAX_DEPTH = 6
MAX_PATH = 200
MAX_FILE_BYTES = 1 << 20  # one text file written with research_write
PART = re.compile(r"^[A-Za-z0-9_][A-Za-z0-9_.-]*$")
CANDIDATE = re.compile(r"^Research/candidates/([A-Za-z][A-Za-z0-9_-]{0,39})\.json$")
SHORTLIST = "Research/shortlist.json"
CANDIDATE_KEYS = ("id", "title", "mechanism_claim", "proof_sketch", "predictions", "experiment_refs", "counterexamples",
                  "estimated_coverage", "estimated_cost", "cost_estimation_method", "unresolved_questions", "agent_assessment")
# What an agent-written record may not say of itself: that a claim is proved. Only a receipt says that.
PROVED_KEYS = re.compile(r"^(verified|accepted|proved|proven|formally_proved|formally_verified|receipt)$", re.I)
PROVED_WORDS = re.compile(r"\b(proved|proven|verified|accepted|certified)\b", re.I)


class ResearchError(ValueError):
    pass


def root(run_dir: Path) -> Path:
    return Path(run_dir) / DIR


def state_dir(run_dir: Path) -> Path:
    d = Path(run_dir) / STATE_DIR
    d.mkdir(parents=True, exist_ok=True)
    return d


@contextmanager
def locked(run_dir: Path, name: str = "lock"):
    """The run's workflow lock: the tools' server and the loop never change these files at once."""
    with open(state_dir(run_dir) / name, "a+") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def check_path(path, prefix_ok: bool = False) -> str:
    """The path relative to Research/ ("candidates/c001.json"), or ResearchError. prefix_ok allows "Research"
    or "Research/" itself (a listing of everything)."""
    if not isinstance(path, str) or len(path) > MAX_PATH or "\\" in path or "\x00" in path:
        raise ResearchError(f"a research path is a string of at most {MAX_PATH} characters: Research/<folder>/.../<name>")
    p = path.rstrip("/") if prefix_ok else path
    if prefix_ok and p == PREFIX:
        return ""
    if not p.startswith(PREFIX + "/"):
        raise ResearchError(f"{path!r} is not under Research/")
    parts = p[len(PREFIX) + 1:].split("/")
    if len(parts) > MAX_DEPTH or not all(PART.match(x) for x in parts) or any(x in (".", "..") for x in parts):
        raise ResearchError(f"{path!r}: each part of a research path is letters, digits and _ . - (not starting with "
                            f"a dot), at most {MAX_DEPTH} parts")
    return "/".join(parts)


def _safe_parent(base: Path, rel: str, create: bool) -> Path:
    """The folder that holds base/rel, every part of it a real folder (never a link)."""
    cur = base
    if create:
        cur.mkdir(parents=True, exist_ok=True)
    if cur.is_symlink():
        raise ResearchError("the research folder is not a plain folder")
    for part in rel.split("/")[:-1]:
        cur = cur / part
        if cur.is_symlink() or (cur.exists() and not cur.is_dir()):
            raise ResearchError(f"Research/{rel}: {part} is not a plain folder")
        if not cur.exists():
            if not create:
                raise ResearchError(f"no file Research/{rel}")
            cur.mkdir()
    return cur


def _files(base: Path) -> dict[str, Path]:
    """The regular files under base with one name each, by path relative to it; nothing else counts."""
    out = {}
    if not base.is_dir() or base.is_symlink():
        return out
    for dirpath, dirnames, filenames in os.walk(base, followlinks=False):
        dirnames[:] = [d for d in dirnames if not os.path.islink(os.path.join(dirpath, d))]
        for f in filenames:
            path = os.path.join(dirpath, f)
            st = os.lstat(path)
            if stat.S_ISREG(st.st_mode) and st.st_nlink == 1 and ".tmp-" not in f:
                out[os.path.relpath(path, base).replace(os.sep, "/")] = Path(path)
    return out


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_index(run_dir: Path) -> dict:
    p = state_dir(run_dir) / INDEX
    return json.loads(p.read_text()) if p.is_file() else {}


def _write_json(path: Path, data) -> None:
    tmp = path.with_name(path.name + f".tmp-{os.getpid()}")
    tmp.write_text(json.dumps(data, indent=1))
    tmp.replace(path)


def usage(run_dir: Path) -> tuple[int, int]:
    """Bytes and files the research folder holds."""
    files = _files(root(run_dir))
    return sum(p.stat().st_size for p in files.values()), len(files)


def validate(rel: str, data: bytes) -> None:
    """The form of the two kinds of file that have one (module docstring)."""
    full = f"{PREFIX}/{rel}"
    m = CANDIDATE.match(full)
    if not m and full != SHORTLIST:
        return
    try:
        value = json.loads(data.decode("utf-8"))
    except (UnicodeDecodeError, ValueError) as exc:
        raise ResearchError(f"{full} must be JSON: {exc}") from None
    if m:
        candidate_problems(value, m.group(1), raise_=True)
    else:
        shortlist_problems(value, raise_=True)


def candidate_problems(value, name: str | None = None, raise_: bool = False) -> list[str]:
    problems = []
    if not isinstance(value, dict):
        problems.append("a candidate record is a JSON object")
    else:
        missing = [k for k in CANDIDATE_KEYS if k not in value]
        if missing:
            problems.append(f"it lacks {', '.join(missing)} (null or [] where there is nothing yet)")
        if name is not None and value.get("id") != name:
            problems.append(f"its id must be {name!r}, the file's name")
        claims = [k for k in value if PROVED_KEYS.match(str(k))]
        if claims:
            problems.append(f"it may not have the keys {claims}: only the acceptance service's receipts say that a claim is proved")
        if PROVED_WORDS.search(str(value.get("agent_assessment") or "")):
            problems.append("agent_assessment is your opinion of the candidate (draft, promising, weak, rejected, ...), "
                            "never that it is proved, verified or accepted: only a receipt says that")
    if problems and raise_:
        raise ResearchError("candidate record: " + "; ".join(problems))
    return problems


def shortlist_problems(value, raise_: bool = False) -> list[str]:
    problems = []
    items = value.get("shortlist") if isinstance(value, dict) else value
    if not isinstance(items, list) or not all(isinstance(x, dict) and isinstance(x.get("id"), str) and
                                              isinstance(x.get("reason"), str) and x["reason"].strip() for x in items):
        problems.append('the shortlist is a JSON list, in order of priority, of {"id": "<candidate id>", "reason": "<why this priority>"}')
    elif len({x["id"] for x in items}) != len(items):
        problems.append("a candidate is listed twice")
    if problems and raise_:
        raise ResearchError("shortlist: " + "; ".join(problems))
    return problems


def write(run_dir: Path, path: str, data: bytes, limits: dict, origin: dict) -> dict:
    """Write one file of the research folder (atomic), within the limits; returns its entry in the index."""
    rel = check_path(path)
    validate(rel, data)
    if len(data) > max(MAX_FILE_BYTES, 0) and origin.get("via") == "research_write":
        raise ResearchError(f"a file written with research_write holds at most {MAX_FILE_BYTES:,} bytes")
    base = root(run_dir)
    with locked(run_dir):
        files = _files(base)
        total = sum(p.stat().st_size for r, p in files.items() if r != rel) + len(data)
        count = len(set(files) | {rel})
        if total > limits["mb"] * (1 << 20) or count > limits["files"]:
            raise ResearchError(f"Research/{rel} would take the research folder over its limit ({limits['mb']:g} MB, "
                                f"{limits['files']} files)")
        parent = _safe_parent(base, rel, create=True)
        target = parent / rel.split("/")[-1]
        if target.is_symlink() or (target.exists() and not target.is_file()):
            raise ResearchError(f"Research/{rel} is not a plain file")
        tmp = parent / f".tmp-{os.getpid()}-{target.name}"
        tmp.write_bytes(data)
        tmp.replace(target)
        index = read_index(run_dir)
        entry = {"bytes": len(data), "sha256": sha(data), "at": time.strftime("%Y-%m-%dT%H:%M:%S%z"), **origin}
        index[f"{PREFIX}/{rel}"] = entry
        _write_json(state_dir(run_dir) / INDEX, dict(sorted(index.items())))
    return entry


def read_bytes(run_dir: Path, path: str) -> bytes:
    rel = check_path(path)
    parent = _safe_parent(root(run_dir), rel, create=False)
    p = parent / rel.split("/")[-1]
    if p.is_symlink() or not p.is_file() or os.lstat(p).st_nlink != 1:
        raise ResearchError(f"no file {path} in the research folder")
    return p.read_bytes()


def listing(run_dir: Path, prefix: str = PREFIX) -> list[dict]:
    rel = check_path(prefix or PREFIX, prefix_ok=True)
    index = read_index(run_dir)
    out = []
    for r, p in sorted(_files(root(run_dir)).items()):
        if rel and not (r == rel or r.startswith(rel + "/")):
            continue
        full = f"{PREFIX}/{r}"
        meta = index.get(full) or {}
        out.append({"path": full, "bytes": p.stat().st_size, "round": meta.get("round"), "via": meta.get("via")})
    return out


def load_json(run_dir: Path, path: str):
    try:
        return json.loads(read_bytes(run_dir, path).decode("utf-8"))
    except (ResearchError, UnicodeDecodeError, ValueError):
        return None


def candidates(run_dir: Path, base: Path | None = None) -> list[dict]:
    """The candidate records in the folder (or in a snapshot of it at base), each with `path` and `problems`
    (empty for a record of the right form)."""
    folder = root(run_dir) if base is None else Path(base)
    out = []
    for r, p in sorted(_files(folder / "candidates").items()):
        full = f"{PREFIX}/candidates/{r}"
        m = CANDIDATE.match(full)
        if not m:
            continue
        try:
            value = json.loads(p.read_text())
        except (OSError, UnicodeDecodeError, ValueError):
            out.append({"id": m.group(1), "path": full, "problems": ["not JSON"]})
            continue
        rec = dict(value) if isinstance(value, dict) else {}
        rec.setdefault("id", m.group(1))
        rec.update(path=full, problems=candidate_problems(value, m.group(1)))
        out.append(rec)
    return out


def shortlist(run_dir: Path, base: Path | None = None) -> list[dict] | None:
    """The shortlist in its order, or None when there is none of the right form."""
    folder = root(run_dir) if base is None else Path(base)
    p = folder / "shortlist.json"
    if p.is_symlink() or not p.is_file():
        return None
    try:
        value = json.loads(p.read_text())
    except (OSError, UnicodeDecodeError, ValueError):
        return None
    if shortlist_problems(value):
        return None
    items = value.get("shortlist") if isinstance(value, dict) else value
    return [{"id": x["id"], "reason": x["reason"]} for x in items]


def snapshot(run_dir: Path, dest: Path) -> dict[str, str]:
    """Copy the whole research folder to dest, read-only; returns {Research/<rel>: sha256}."""
    out = {}
    for r, p in sorted(_files(root(run_dir)).items()):
        data = p.read_bytes()
        target = dest / r
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        os.chmod(target, 0o444)
        out[f"{PREFIX}/{r}"] = sha(data)
    dest.mkdir(parents=True, exist_ok=True)
    for dirpath, dirnames, _ in os.walk(dest, topdown=False):
        os.chmod(dirpath, 0o555)
    return out


def remove_tree(path: Path) -> None:
    """Remove a read-only snapshot (tests)."""
    for dirpath, dirnames, _ in os.walk(path):
        os.chmod(dirpath, 0o755)
    shutil.rmtree(path, ignore_errors=True)
