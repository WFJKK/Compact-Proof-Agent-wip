"""Run folders, round folders and the append-only archive.

Layout of a run (outside the repository, under the run config's runs_dir):

    <runs_dir>/<run_id>/
        config.yaml        copy of the run config
        config.sha256
        archive.jsonl      one result record per line; append-only
        versions.json      the hashes the run started with
        round_000/         one folder per round, written once (see core.rounds)
            prompt.md
            attempt_0/     response.md  parsed.json  recipe.py  proofs/  results.json
            meta.json  DONE

A round is complete when its DONE marker exists. Files in a completed round
are never rewritten.
"""

from __future__ import annotations

import json
import os
from pathlib import Path

import yaml

from .util import atomic_write, read_json, sha256_bytes, write_json


class ArchiveError(RuntimeError):
    pass


def knob_label(knob, budget=None) -> str:
    """The label of one execution: the budget when the run scores at fixed budgets, else the knob value."""
    return f"b{int(budget)}" if budget is not None else f"k{float(knob):g}"


def record_id(run_id: str, round_k: int, attempt: int, network: str | None = None, knob=None, budget=None) -> str:
    """One id per network and knob value (or budget) in an attempt; an attempt that never ran has one id of its own."""
    base = f"{run_id}/r{round_k:03d}/a{attempt}"
    if network is None:
        return f"{base}/attempt"
    return f"{base}/{network}/{knob_label(knob, budget)}"


class RunDir:
    def __init__(self, runs_dir: str | Path, run_id: str):
        self.run_id = run_id
        self.path = Path(runs_dir).expanduser() / run_id
        self.archive_path = self.path / "archive.jsonl"

    # run level -------------------------------------------------------------
    def exists(self) -> bool:
        return (self.path / "config.yaml").exists()

    def create(self, config: dict) -> None:
        if self.exists():
            raise ArchiveError(f"run {self.run_id} already exists at {self.path}")
        text = yaml.safe_dump(config, sort_keys=True)
        atomic_write(self.path / "config.yaml", text)
        atomic_write(self.path / "config.sha256", sha256_bytes(text.encode()) + "\n")
        self.archive_path.touch()

    def config(self) -> dict:
        with open(self.path / "config.yaml") as f:
            return yaml.safe_load(f)

    # rounds ----------------------------------------------------------------
    def round_path(self, k: int) -> Path:
        return self.path / f"round_{k:03d}"

    def round_done(self, k: int) -> bool:
        return (self.round_path(k) / "DONE").exists()

    def done_rounds(self) -> list[int]:
        out = []
        for p in sorted(self.path.glob("round_*")):
            if (p / "DONE").exists():
                out.append(int(p.name.split("_")[1]))
        return out

    def next_round(self) -> int:
        done = self.done_rounds()
        return (max(done) + 1) if done else 0

    def write(self, k: int, relpath: str, content) -> Path:
        """Write a file into round k; refused once the round is complete."""
        if self.round_done(k):
            raise ArchiveError(f"round {k} is complete; its files are never rewritten")
        target = self.round_path(k) / relpath
        if isinstance(content, (dict, list)):
            write_json(target, content)
        else:
            atomic_write(target, content)
        return target

    def read(self, k: int, relpath: str):
        p = self.round_path(k) / relpath
        if not p.exists():
            return None
        if p.suffix == ".json":
            return read_json(p)
        return p.read_text()

    def mark_done(self, k: int) -> None:
        atomic_write(self.round_path(k) / "DONE", "")

    # archive ---------------------------------------------------------------
    def read_archive(self) -> list[dict]:
        """All records, first occurrence of each record id only."""
        if not self.archive_path.exists():
            return []
        seen, out = set(), []
        with open(self.archive_path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                rid = rec.get("record_id")
                if rid in seen:
                    continue
                seen.add(rid)
                out.append(rec)
        return out

    def append_archive(self, records: list[dict]) -> int:
        """Append records whose ids are not in the archive yet. Returns the number written."""
        have = {r.get("record_id") for r in self.read_archive()}
        new = [r for r in records if r.get("record_id") not in have]
        for r in new:
            if "record_id" not in r:
                raise ArchiveError("every archive record needs a record_id")
        if not new:
            return 0
        with open(self.archive_path, "a") as f:
            for r in new:
                f.write(json.dumps(r, sort_keys=True) + "\n")
            f.flush()
            os.fsync(f.fileno())
        return len(new)
