"""A run that goes on with an earlier run's work (open_lane.continue_from; docs/OPEN_LANE.md, "Continuing an
earlier run").

A continuation is a new run, with its own records, score, budgets and Lean service. It starts where an earlier
open-lane run of the same model and networks left off. When it starts it copies what that run left, once, into
<run>/inherited/, read-only:

    record.json          what was copied, from where and when, with the sha256 of every copied file
    config.yaml  versions.json  archive.jsonl  stages.json     the earlier run's own
    round_<k>/           each complete proof round: meta.json and DONE, each attempt's response.md and
                         response_meta.json, its session's session.json and tools.jsonl, and every submission
                         (manifest.json, receipt.json, research.json, offered.json, lock.json and the submitted
                         modules); for the last of these rounds also the session's workspace modules, its drafts
                         and its Python workspace
    research/            the earlier run's research folder, as it was
    inherited/           the earlier run's own inherited/, when it was itself a continuation

and the earlier run's research folder into its own research folder, where the agent goes on with it.

Round k of a continuation starts as round K + k of the earlier run would have (K its last proof round): the
modules the service accepted there are carried into the workspace, the last session's unfinished modules and
Python files go on, and until this run has notes of its own the latest notes are the earlier run's. The earlier
run's submissions are listed apart and never counted: the frontier, the score and the archive are this run's
alone. Its receipts came from the service it ran with (its versions.json, lean_checker), which may not be
this run's; open_lane.continue_note is shown with them, for what the person running the continuation knows
about that (a fault of the service fixed since, say).

The earlier run's folder is only read. Its rounds without DONE, and its sessions after the proof rounds (the
seed check, the scaling question), are not copied.
"""

from __future__ import annotations

import hashlib
import json
import os
import shutil
import stat
import time
from pathlib import Path

import yaml

from . import research

DIR = "inherited"
RECORD = "record.json"
RUN_FILES = ("config.yaml", "versions.json", "archive.jsonl", "stages.json")
ROUND_FILES = ("meta.json", "DONE")
ATTEMPT_FILES = ("response.md", "response_meta.json")
SESSION_FILES = ("session.json", "tools.jsonl")
SUBMISSION_FILES = ("manifest.json", "receipt.json", "research.json", "offered.json", "lock.json")
LAST_SESSION_DIRS = ("workspace/Candidate", "drafts/Candidate", "py")


class ContinuationError(RuntimeError):
    pass


# the setting ---------------------------------------------------------------------------------------
def setting(cfg: dict) -> str | None:
    """The run this one continues, as its config names it (a run id under runs_dir, or a path); None for a run
    that continues none."""
    ol = cfg.get("open_lane") or {}
    value = ol.get("continue_from") if ol.get("enabled") else None
    return str(value) if value else None


def parent_path(cfg: dict) -> Path:
    """The earlier run's folder: a bare run id is looked for under the run's runs_dir."""
    from ..run_config import resolve

    value = setting(cfg)
    if value is None:
        raise ContinuationError("the run continues no earlier run")
    if "/" not in value and not value.startswith("~"):
        return (resolve(cfg["runs_dir"]) / value).resolve()
    return resolve(value).resolve()


def _read_yaml(p: Path) -> dict:
    with open(p) as f:
        return yaml.safe_load(f) or {}


def _stage_rounds(parent: Path) -> set[int]:
    p = parent / "stages.json"
    try:
        state = json.loads(p.read_text()) if p.is_file() else {}
    except (OSError, ValueError):
        return set()
    return {int(st["round"]) for st in (state.get("stages") or {}).values() if isinstance(st, dict) and st.get("round")}


def proof_rounds(parent: Path) -> tuple[list[int], list[int]]:
    """The earlier run's complete proof rounds, and its proof rounds that are not complete (no DONE)."""
    stages_ = _stage_rounds(parent)
    done, open_ = [], []
    for p in sorted(parent.glob("round_*")):
        tail = p.name[len("round_"):]
        if not p.is_dir() or not tail.isdigit() or int(tail) == 0 or int(tail) in stages_:
            continue
        (done if (p / "DONE").is_file() else open_).append(int(tail))
    return done, open_


def check_parent(cfg: dict, run_path: Path | None = None) -> list[str]:
    """Why the configured earlier run cannot be continued (empty when it can): it must be another open-lane
    run of the same model and networks, with at least one complete proof round."""
    try:
        parent = parent_path(cfg)
    except ContinuationError as exc:
        return [str(exc)]
    if run_path is not None and parent == Path(run_path).expanduser().resolve():
        return ["a run cannot continue itself"]
    if not (parent / "config.yaml").is_file():
        return [f"open_lane.continue_from: no run at {parent}"]
    try:
        pcfg = _read_yaml(parent / "config.yaml")
    except (OSError, yaml.YAMLError) as exc:
        return [f"open_lane.continue_from: the config of the run at {parent} cannot be read: {exc}"]
    errors = []
    name = pcfg.get("run_id") or parent.name
    if not (pcfg.get("open_lane") or {}).get("enabled"):
        errors.append(f"run {name} is not an open-lane run: there is no Lean work to go on with")
    if str(pcfg.get("model")) != str(cfg.get("model")):
        errors.append(f"run {name} is of the model {pcfg.get('model')}, this run of {cfg.get('model')}")
    if list(pcfg.get("networks") or []) != list(cfg.get("networks") or []):
        errors.append(f"run {name} works on the networks {pcfg.get('networks')}, this run on {cfg.get('networks')}: "
                      "a continuation keeps the earlier run's networks")
    if not errors and not proof_rounds(parent)[0]:
        errors.append(f"run {name} has no complete proof round to go on from")
    return errors


# the copy --------------------------------------------------------------------------------------------
def root(run_path: Path) -> Path:
    return Path(run_path) / DIR


def record(run_path: Path) -> dict | None:
    """What the run's copy of the earlier run holds (record.json), or None when it has none."""
    p = root(run_path) / RECORD
    return json.loads(p.read_text()) if p.is_file() else None


def _sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _regular(p: Path) -> bool:
    try:
        st = os.lstat(p)
    except OSError:
        return False
    return stat.S_ISREG(st.st_mode) and st.st_nlink == 1


def _copy_file(src: Path, dest: Path, rel: str, files: dict) -> None:
    if not _regular(src):
        return
    data = src.read_bytes()
    target = dest / rel
    target.parent.mkdir(parents=True, exist_ok=True)
    target.write_bytes(data)
    files[rel] = _sha(data)


def _copy_tree(src: Path, dest: Path, rel: str, files: dict) -> None:
    """Every regular file with one name under src, at rel/<its path>; no link is followed."""
    if not src.is_dir() or src.is_symlink():
        return
    for dirpath, dirnames, filenames in os.walk(src, followlinks=False):
        dirnames[:] = sorted(d for d in dirnames if not os.path.islink(os.path.join(dirpath, d)))
        for f in sorted(filenames):
            p = Path(dirpath) / f
            sub = p.relative_to(src).as_posix()
            if ".tmp-" in f:
                continue
            _copy_file(p, dest, f"{rel}/{sub}", files)


def _attempts(rdir: Path) -> list[Path]:
    return sorted((p for p in rdir.glob("attempt_*") if p.is_dir() and p.name[len("attempt_"):].isdigit()),
                  key=lambda p: int(p.name[len("attempt_"):]))


def _read_only(path: Path) -> None:
    for dirpath, dirnames, filenames in os.walk(path, topdown=False):
        for f in filenames:
            os.chmod(os.path.join(dirpath, f), 0o444)
        os.chmod(dirpath, 0o555)


def remove_tree(path: Path) -> None:
    """Remove a read-only copy (an interrupted copy is made again; tests)."""
    if not path.exists():
        return
    for dirpath, dirnames, _ in os.walk(path):
        os.chmod(dirpath, 0o755)
    shutil.rmtree(path, ignore_errors=True)


def _copy_run(parent: Path, dest: Path, rounds: list[int], files: dict) -> None:
    for name in RUN_FILES:
        _copy_file(parent / name, dest, name, files)
    last = max(rounds)
    for k in rounds:
        rname = f"round_{k:03d}"
        rdir = parent / rname
        for name in ROUND_FILES:
            _copy_file(rdir / name, dest, f"{rname}/{name}", files)
        for adir in _attempts(rdir):
            arel = f"{rname}/{adir.name}"
            for name in ATTEMPT_FILES:
                _copy_file(adir / name, dest, f"{arel}/{name}", files)
            sess = adir / "open_lane"
            if not sess.is_dir():
                continue
            for name in SESSION_FILES:
                _copy_file(sess / name, dest, f"{arel}/open_lane/{name}", files)
            subs = sess / "submissions"
            for d in sorted(p for p in subs.glob("*") if p.is_dir() and p.name.isdigit()):
                srel = f"{arel}/open_lane/submissions/{d.name}"
                for name in SUBMISSION_FILES:
                    _copy_file(d / name, dest, f"{srel}/{name}", files)
                _copy_tree(d / "Candidate", dest, f"{srel}/Candidate", files)
            if k == last:  # the work the last session left: its workspace modules, drafts and Python files
                (dest / arel / "open_lane" / "workspace").mkdir(parents=True, exist_ok=True)
                for sub in LAST_SESSION_DIRS:
                    _copy_tree(sess / sub, dest, f"{arel}/open_lane/{sub}", files)
    _copy_tree(research.root(parent), dest, "research", files)
    index = parent / research.STATE_DIR / research.INDEX
    _copy_file(index, dest, f"{research.STATE_DIR}/{research.INDEX}", files)


def inherit(run_path: Path, cfg: dict, log=print) -> dict:
    """Copy the earlier run's work into the run, once (module docstring), and its research folder into the run's
    own. A copy interrupted before its record is made again. Returns the record."""
    run_path = Path(run_path)
    have = record(run_path)
    if have is not None:
        return have
    errors = check_parent(cfg, run_path)
    if errors:
        raise ContinuationError("; ".join(errors))
    parent = parent_path(cfg)
    rounds, not_done = proof_rounds(parent)
    dest = root(run_path)
    remove_tree(dest)
    dest.mkdir(parents=True)
    files: dict[str, str] = {}
    _copy_run(parent, dest, rounds, files)
    if (parent / DIR / RECORD).is_file():  # the earlier run was itself a continuation: its own copy goes along
        _copy_tree(parent / DIR, dest, DIR, files)
    pcfg = _read_yaml(parent / "config.yaml")
    versions = json.loads((parent / "versions.json").read_text()) if (parent / "versions.json").is_file() else {}
    copied = _research_into(run_path, dest, pcfg.get("run_id") or parent.name, cfg)
    data = {"run_id": pcfg.get("run_id") or parent.name, "path": str(parent), "rounds": rounds, "last_round": max(rounds),
            "not_copied": {"incomplete_rounds": not_done, "stage_rounds": sorted(_stage_rounds(parent))},
            "lean_checker": versions.get("lean_checker"), "config_sha256": _sha((parent / "config.yaml").read_bytes()),
            "copied": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "research": copied, "files": dict(sorted(files.items()))}
    (dest / RECORD).write_text(json.dumps(data, indent=1))
    _read_only(dest)
    log(f"continues run {data['run_id']}: rounds {', '.join(map(str, rounds))} copied ({len(files)} files)"
        + (f"; not copied, not complete: rounds {', '.join(map(str, not_done))}" if not_done else ""))
    return data


def _research_into(run_path: Path, dest: Path, run_id: str, cfg: dict) -> dict[str, str]:
    """The earlier run's research folder (its copy in dest) into the run's own, each file's index entry saying
    where it came from; the folder's limits hold as for any write. A file the run already has is left."""
    src = dest / "research"
    old_index = {}
    p = dest / research.STATE_DIR / research.INDEX
    if p.is_file():
        old_index = json.loads(p.read_text())
    ol = cfg["open_lane"]
    limits = {"mb": float(ol.get("research_workspace_mb") or 50), "files": int(ol.get("research_workspace_files") or 500)}
    out = {}
    for rel, path in sorted(research._files(src).items()):
        full = f"{research.PREFIX}/{rel}"
        data = path.read_bytes()
        if full in research.read_index(run_path):  # copied before an interruption, or the run's own
            out[full] = _sha(data)
            continue
        before = old_index.get(full) or {}
        origin = {"via": "inherited", "from_run": run_id, "round": before.get("round"), "earlier_via": before.get("via")}
        try:
            research.write(run_path, full, data, limits, origin)
        except research.ResearchError as exc:
            raise ContinuationError(f"the research folder of run {run_id} does not fit this run's: {exc}") from exc
        out[full] = _sha(data)
    return out


# what the run's copy holds --------------------------------------------------------------------------------
def roots(run_path: Path) -> list[Path]:
    """The copies of the earlier runs this run goes on from, oldest first: <run>/inherited/inherited before
    <run>/inherited."""
    r = root(run_path)
    if not (r / RECORD).is_file():
        return []
    return roots(r) + [r]


def run_id_of(base: Path) -> str:
    return json.loads((Path(base) / RECORD).read_text())["run_id"]


def rounds_of(base: Path) -> list[int]:
    return list(json.loads((Path(base) / RECORD).read_text())["rounds"])


def origin(path: Path, run_path: Path) -> str | None:
    """The earlier run a session folder or file of the run's copy comes from; None for the run's own."""
    path = Path(path)
    for base in reversed(roots(run_path)):
        try:
            rel = path.relative_to(base)
        except ValueError:
            continue
        if rel.parts and rel.parts[0] == DIR:
            continue  # inside an older copy: a later base in this order is nearer
        return run_id_of(base)
    return None


def records_of(base: Path) -> list[dict]:
    """The earlier run's records (its archive, first occurrence of each id)."""
    p = Path(base) / "archive.jsonl"
    if not p.is_file():
        return []
    seen, out = set(), []
    for line in p.read_text().splitlines():
        line = line.strip()
        if not line:
            continue
        rec = json.loads(line)
        if rec.get("record_id") in seen:
            continue
        seen.add(rec.get("record_id"))
        out.append(rec)
    return out


def lean_checker_of(base: Path) -> dict | None:
    return json.loads((Path(base) / RECORD).read_text()).get("lean_checker")
