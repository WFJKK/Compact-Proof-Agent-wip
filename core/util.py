"""Small helpers shared by the core: hashing, atomic writes, git state."""

from __future__ import annotations

import hashlib
import json
import os
import subprocess
from pathlib import Path
from typing import Iterable

import yaml

REPO_ROOT = Path(__file__).resolve().parent.parent


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha256_file(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_files(root: Path, files: Iterable[Path]) -> str:
    """Hash a set of files by their paths relative to root and their contents."""
    h = hashlib.sha256()
    for p in sorted(files, key=lambda q: q.relative_to(root).as_posix()):
        h.update(p.relative_to(root).as_posix().encode())
        h.update(b"\0")
        h.update(sha256_file(p).encode())
        h.update(b"\0")
    return h.hexdigest()


def sha256_json(obj) -> str:
    return sha256_bytes(json.dumps(obj, sort_keys=True, separators=(",", ":")).encode())


def atomic_write(path: Path, data: str | bytes) -> None:
    """Write a file so that readers never see a partial version."""
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_name(path.name + ".tmp")
    mode = "wb" if isinstance(data, bytes) else "w"
    with open(tmp, mode) as f:
        f.write(data)
        f.flush()
        os.fsync(f.fileno())
    os.replace(tmp, path)


def write_json(path: Path, obj) -> None:
    atomic_write(path, json.dumps(obj, indent=2, sort_keys=True) + "\n")


def read_json(path: Path):
    with open(path) as f:
        return json.load(f)


def read_yaml(path: Path):
    with open(path) as f:
        return yaml.safe_load(f)


def git_state(root: Path = REPO_ROOT) -> dict:
    """The commit a result was produced from, and whether the tree was dirty."""
    def run(*args):
        return subprocess.run(["git", *args], cwd=root, capture_output=True, text=True)

    head = run("rev-parse", "HEAD")
    status = run("status", "--porcelain")
    return {
        "commit": head.stdout.strip() if head.returncode == 0 else None,
        "dirty": bool(status.stdout.strip()) if status.returncode == 0 else None,
    }
