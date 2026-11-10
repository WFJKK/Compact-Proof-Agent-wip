"""Re-measure a run's proofs under the current cost model.

    python -m core.remeasure --run <runs_dir>/<run_id> [--out <folder>] [--workers N]

Every proof the run archived with status ok is checked again by the current
checker, and the results are written as a new archive to <out>/archive.jsonl
(by default <runs_dir>/<run_id>-remeasured-<cost version>): one record per
original record, with the new length and cost model, the archived length kept
as length_archived. The run's held-out evaluation (<run>/final) is re-measured
the same way into <out>/final/archive.jsonl when it exists. The run itself is
never changed.

The cost model may change lengths, never what a proof certifies, so a proof
whose certified count differs from the archive is reported, as is any proof
that certifies more inputs than the network gets right, which a sound checker
never does. Then, per round, the median Q and the median shortest full-accuracy
proof over the networks are printed under the new lengths, so that runs
measured under different cost models can be compared.
"""

from __future__ import annotations

import argparse
import gzip
import json
import os
import statistics
import sys
from concurrent.futures import ProcessPoolExecutor
from multiprocessing import get_context
from pathlib import Path

from .archive import RunDir, knob_label
from .check.cost import VERSION as COST_VERSION
from .loop import LoopError, select_networks
from .model_folder import load_model_folder
from .run_config import resolve
from .scoring import scored, summarize
from .util import atomic_write
from .zoo import networks

_FOLDERS: dict = {}


def _measure(job):
    """One proof in a worker process: (record id, new result or None, error)."""
    sys.dont_write_bytecode = True
    from .check.checker import check_proof

    folder_path, network, path, rule_set, held_out, record_id = job
    if folder_path not in _FOLDERS:
        _FOLDERS[folder_path] = load_model_folder(folder_path)
    try:
        proof = json.loads(gzip.decompress(Path(path).read_bytes()))
    except (OSError, ValueError) as exc:
        return record_id, None, f"cannot read {path}: {exc}"
    res = check_proof(proof, _FOLDERS[folder_path], network, rule_set=tuple(rule_set), allow_held_out=held_out)
    return record_id, res, None


def proof_path(run: RunDir, r: dict) -> Path:
    return run.round_path(r["round"]) / f"attempt_{r['attempt']}" / "proofs" / f"{r['network']}__{knob_label(r['knob'], r.get('budget'))}.json.gz"


def remeasure_archive(run: RunDir, folder_path: str, entries: list[dict], rule_set, held_out: bool, out: Path, workers: int, log=print) -> list[dict]:
    """Re-check every ok record's proof; write out/archive.jsonl; return the new records."""
    records = run.read_archive()
    real = {e["id"]: e.get("real_correct") for e in entries}
    jobs, same = [], {}  # the same proof at several knob values is checked once
    for r in scored(records):
        if r["network"] not in real:
            continue
        p = proof_path(run, r)
        if not p.exists():
            log(f"  WARNING: {r['record_id']}: proof file missing, record kept as archived")
            continue
        key = (r["network"], r.get("proof_sha256") or r["record_id"])
        if key in same:
            same[key].append(r["record_id"])
            continue
        same[key] = [r["record_id"]]
        jobs.append((folder_path, r["network"], str(p), list(rule_set), held_out, r["record_id"]))
    log(f"{run.path}: {sum(map(len, same.values()))} records, {len(jobs)} distinct proofs to re-measure under {COST_VERSION} with {workers} workers")
    orig = {r["record_id"]: r for r in records}
    new = {rid: dict(r) for rid, r in orig.items()}
    problems = {"certified_changed": [], "rejected": [], "unsound": []}
    done = 0
    results = {}
    with ProcessPoolExecutor(max_workers=workers, mp_context=get_context("spawn")) as ex:
        for rid, res, err in ex.map(_measure, jobs, chunksize=1):
            done += 1
            if done % 50 == 0 or done == len(jobs):
                log(f"  {done}/{len(jobs)}")
            results[rid] = (res, err)
    for key, rids in same.items():
        res, err = results.get(rids[0], (None, "not measured"))
        for rid in rids:
            old = orig[rid]
            if err or res is None or res["status"] != "ok":
                problems["rejected"].append((rid, err or res.get("reason")))
                new[rid].update(status="bad_output", error=f"re-measurement: {err or res.get('reason')}", length_archived=old["length"])
                continue
            if res["certified"] != old["certified"]:
                problems["certified_changed"].append((rid, old["certified"], res["certified"]))
            if real.get(old["network"]) is not None and res["certified"] > real[old["network"]]:
                problems["unsound"].append((rid, res["certified"], real[old["network"]]))
            new[rid].update(
                length=res["length"],
                length_by_rule=res["length_by_rule"],
                length_archived=old["length"],
                cost_model_archived=(old.get("versions") or {}).get("cost_model"),
                cost_model=COST_VERSION,
            )
    out.mkdir(parents=True, exist_ok=True)
    atomic_write(out / "archive.jsonl", "".join(json.dumps(new[r["record_id"]]) + "\n" for r in records))
    for kind, items in problems.items():
        if not items:
            continue
        what = {
            "certified_changed": "proofs certify a different number of inputs than archived (the checker changed, not only the cost model)",
            "rejected": "archived proofs are rejected by the current checker",
            "unsound": "proofs certify more inputs than the network gets right: THE CHECKER OR THE ZOO IS UNSOUND",
        }[kind]
        log(f"  WARNING: {len(items)} {what}; first: {items[:3]}")
    if not any(problems.values()):
        log("  every proof certifies what the archive says, and none more than the network gets right")
    return [new[r["record_id"]] for r in records]


def _median_full(summary: dict, setting: str):
    vals = [m["shortest_full"] for m in summary[setting]["networks"].values() if m["shortest_full"]]
    return statistics.median(vals) if vals else None


def report(run: RunDir, records: list[dict], entries: list[dict], log=print, budget_ratio: float | None = None) -> dict:
    """Per round (cumulative): median Q, Q_grid and shortest full-accuracy proof, per size setting."""
    settings = list(dict.fromkeys(e["setting"] for e in entries))
    out = {}
    log(f"\nper round under {COST_VERSION} (cumulative; median over the networks): Q | Q_grid | shortest full-accuracy proof")
    for k in run.done_rounds():
        s = summarize([r for r in records if r["round"] <= k], entries, budget_ratio)
        out[k] = {
            st: {"Q_median": s[st]["Q_median"], "Q_grid_median": s[st]["Q_grid_median"], "shortest_full_median": _median_full(s, st)}
            for st in settings
        }
        cells = []
        for st in settings:
            full = out[k][st]["shortest_full_median"]
            cells.append(f"{st} {out[k][st]['Q_median']:.4f} | {out[k][st]['Q_grid_median']:.4f} | {'none' if full is None else f'{full:,.0f}'}")
        log(f"  round {k}: " + "; ".join(cells))
    return out


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", required=True, help="the run's folder, <runs_dir>/<run_id>")
    ap.add_argument("--out", help=f"where to write; default <runs_dir>/<run_id>-remeasured-{COST_VERSION}")
    ap.add_argument("--workers", type=int, default=max(1, min(4, (os.cpu_count() or 2) - 1)))
    args = ap.parse_args(argv)
    sys.dont_write_bytecode = True
    run_path = Path(args.run).expanduser().resolve()
    run = RunDir(run_path.parent, run_path.name)
    if not run.exists():
        print(f"error: no run at {run_path}", file=sys.stderr)
        return 2
    out = Path(args.out).expanduser().resolve() if args.out else run_path.parent / f"{run_path.name}-remeasured-{COST_VERSION}"
    if out == run_path or run_path in out.parents:
        print("error: the output folder must be outside the run", file=sys.stderr)
        return 2
    try:
        cfg = run.config()
        folder = load_model_folder(resolve(cfg["model"]))
        dev = select_networks(folder, cfg)
        records = remeasure_archive(run, str(folder.path), dev, cfg["rule_set"], False, out, args.workers)
        ratio = cfg.get("budget_ratio")
        summary = {"run": str(run_path), "cost_model": COST_VERSION, "development": report(run, records, dev, budget_ratio=ratio)}
        final = RunDir(run.path, "final")
        if final.exists() and final.archive_path.exists():
            settings = {e["setting"] for e in dev}
            held = [e for e in networks(folder, "held_out") if e["setting"] in settings]
            frecords = remeasure_archive(final, str(folder.path), held, cfg["rule_set"], True, out / "final", args.workers)
            summary["held_out"] = report(final, frecords, held, budget_ratio=ratio)
        atomic_write(out / "summary.json", json.dumps(summary, indent=1))
        print(f"\nwritten to {out}")
        return 0
    except LoopError as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
