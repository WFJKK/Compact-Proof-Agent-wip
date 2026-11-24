"""Opening a finished run with a later pipeline.

A run refuses to go on when the pipeline's checker code, its sandbox code or the model folder changed since it
started: its scores would not be comparable. The scaling proofs come after a finished run, often after a pull
that brings fixes, and they add lemmas and never a score. So they may open such a run when its networks, task
and architecture are still the run's:

- the pipeline's checker and sandbox code may have changed (the Lean checker must be the run's, which opening a
  run checks anyway);
- the model folder may differ from the run's only in the open_lane block of its config.yaml, which says what
  open-lane sessions are shown and given. The folder the run started with is read back with git from the
  pipeline commit the run recorded, and must hash to what the run recorded.

`accept` is the hook core.loop.open_context takes for this (its `changed_since`). Each session then records the
pipeline it ran with (core.open_lane.scaling.steps). A resume still refuses any change.
"""

from __future__ import annotations

import hashlib
import subprocess

import yaml

from ...util import REPO_ROOT, git_state
from ...versions import trusted

TRUSTED_WORDS = {"checker": "checker code", "sandbox": "sandbox code", "model_folder": "model folder"}


class LaterPipelineError(ValueError):
    pass


def model_folder_at(commit: str, folder) -> dict[str, bytes] | None:
    """The model folder's identity files (ModelFolder.identity_files) as they were at a pipeline commit, by
    their path in the folder, read with git; None when git cannot show them (no repository, an unknown
    commit, or a folder outside the repository)."""
    try:
        rel = folder.path.resolve().relative_to(REPO_ROOT.resolve()).as_posix()
        zoo = folder.zoo_dir().resolve().relative_to(folder.path.resolve()).as_posix()
    except ValueError:
        return None
    listing = subprocess.run(["git", "ls-tree", "-r", "-z", "--name-only", commit, "--", rel], cwd=REPO_ROOT, capture_output=True)
    if listing.returncode != 0:
        return None
    out = {}
    for path in listing.stdout.decode("utf-8", "replace").split("\0"):
        name = path[len(rel) + 1:] if path.startswith(rel + "/") else None
        if not name:
            continue
        parts = name.split("/")
        if any(p.startswith(".") for p in parts) or "__pycache__" in parts or name.endswith(".pyc"):
            continue
        if name.startswith(zoo + "/") and parts[-1] != "manifest.json":
            continue  # weights and the like: the manifest names them by their hashes
        blob = subprocess.run(["git", "show", f"{commit}:{path}"], cwd=REPO_ROOT, capture_output=True)
        if blob.returncode != 0:
            return None
        out[name] = blob.stdout
    return out or None


def files_hash(files: dict[str, bytes]) -> str:
    """ModelFolder.folder_hash of files given by their path in the folder and their bytes."""
    h = hashlib.sha256()
    for name in sorted(files):
        h.update(name.encode() + b"\0" + hashlib.sha256(files[name]).hexdigest().encode() + b"\0")
    return h.hexdigest()


def refusal(started: dict, folder, bad: list[str], read=None) -> str | None:
    """Why a run may not be opened with the pipeline as it is now, or None. `started`: what the run recorded
    when it started (versions.json); `bad`: what changed since (core.versions.changed); `read`: model_folder_at,
    or a stand-in for it."""
    if "model_folder" not in bad:
        return None
    commit = (started.get("git") or {}).get("commit")
    if not commit:
        return "the run recorded no pipeline commit to read its model folder back from"
    then = (read or model_folder_at)(commit, folder)
    if then is None:
        return f"git cannot show the model folder as it was at pipeline commit {commit[:12]}, which the run started from"
    if files_hash(then) != started.get("model_folder"):
        return (f"the model folder at pipeline commit {commit[:12]} is not the one the run recorded "
                "(it started with changes that were not committed)")
    now = {p.relative_to(folder.path).as_posix(): p.read_bytes() for p in folder.identity_files() if folder.path in p.parents}
    if set(then) != set(now):
        return "files of the model folder were added or removed since the run started: " + ", ".join(sorted(set(then) ^ set(now)))
    for name in sorted(n for n in now if now[n] != then[n]):
        if name != "config.yaml":
            return f"the model folder's {name} changed since the run started"
        old, new = yaml.safe_load(then[name]), yaml.safe_load(now[name])
        if not isinstance(old, dict) or not isinstance(new, dict):
            return "the model folder's config.yaml is not a mapping"
        outside = sorted(k for k in set(old) | set(new) if k != "open_lane" and old.get(k) != new.get(k))
        if outside:
            return f"the model folder's config.yaml changed outside its open_lane block ({', '.join(outside)})"
    return None


def accept(run, started: dict, folder, bad: list[str], log=print) -> dict:
    """The versions a command that follows a finished run goes on with: the pipeline's as it is now, with what
    changed since the run started, so that the new rounds' records say what ran. Raises LaterPipelineError when
    the run may not be opened (refusal)."""
    commit = (started.get("git") or {}).get("commit") or "?"
    why = refusal(started, folder, bad) if bad else None
    if why:
        raise LaterPipelineError(f"{', '.join(bad)} changed since run {run.run_id} started, and {why}. What follows a finished "
                                 "run needs the run's networks, task and architecture: check out the pipeline commit the run "
                                 f"started from ({commit[:12]}) and run the command there")
    git = git_state()
    if bad:
        log(f"note: the pipeline's {', '.join(TRUSTED_WORDS.get(b, b) for b in bad)} changed since run {run.run_id} started "
            f"(pipeline {commit[:7]}, now {(git.get('commit') or '?')[:7]}); the steps after a finished run add lemmas and no "
            "scores, so they go on" + ("; the model folder differs from the run's only in its open_lane block" if "model_folder" in bad else ""))
    return {**started, **trusted(folder), "git": git, "after_run": {"run_git": started.get("git"), "changed": bad}}
