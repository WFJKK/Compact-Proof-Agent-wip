"""Re-score a run's archive under every metric, round by round, without touching the run.

    python -m core.rescore --run <run folder> [--out <file.json>]

The run folder is a run of `core.loop` (`<runs_dir>/<run_id>`) or a saved copy of one (`results/...`):
it needs `archive.jsonl`, `config.yaml` and the model folder the config names. The metrics are recomputed
from the records alone (core.scoring), exactly as the loop computes them, for the frontier after each
round. Written next to the run as `<out>` (default `<run>/rescore.json`, never overwriting an existing
file unless --force), with what the numbers depend on: the run's `versions.json` (cost model, checker,
the Lean service's identity and knowledge condition for an open-lane run), the metric the run was driven
by, and the brute-force line of every network (how it was found). Recomputed scores of two runs are
comparable only when these agree.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

from .archive import RunDir
from .loop import select_networks
from .model_folder import load_model_folder
from .run_config import METRICS, defaults, resolve
from .scoring import summarize
from .util import read_json, read_yaml

METRIC_VERSION = "scoring-v2: Q_above added 26 October 2026"


def rescore(run_path: Path) -> dict:
    run_path = run_path.expanduser().resolve()
    run = RunDir(run_path.parent, run_path.name)
    if not run.exists():
        raise SystemExit(f"no run at {run_path}")
    # the run's own merged config, read without validation: a saved copy need not have the Lean project
    cfg = {**defaults(), **read_yaml(run_path / "config.yaml")}
    folder = load_model_folder(resolve(cfg["model"]))
    entries = select_networks(folder, cfg)
    records = run.read_archive()
    rounds = sorted({r["round"] for r in records})
    per_round = []
    for k in rounds:
        s = summarize([r for r in records if r["round"] <= k], entries, cfg.get("budget_ratio"))
        per_round.append({"after_round": k, "by_setting": {
            setting: {m: v[m] for m in ("Q_median", "Q_grid_median", "Q_exact_mean", "Q_above_mean", "Q_above_worst",
                                        "cost_of_finishing_median")}
            for setting, v in s.items()}})
    final = summarize(records, entries, cfg.get("budget_ratio"))
    versions = read_json(run_path / "versions.json") if (run_path / "versions.json").exists() else None
    return {
        "run": run_path.name,
        "metric_version": METRIC_VERSION,
        "driven_by": cfg["metric"],
        "metrics_available": list(METRICS),
        "versions": versions,
        "brute_force_lines": {nid: m["brute_force_line"] for s in final.values() for nid, m in s["networks"].items()},
        "per_round": per_round,
        "final": final,
    }


def table(result: dict) -> str:
    lines = [f"{result['run']} (driven by {result['driven_by']}; {result['metric_version']})"]
    for nid, line in result["brute_force_lines"].items():
        lines.append(f"  {nid}: brute-force line k inputs for {line['c']:g} k + {line['E']:g}, up to {line['coverage']} ({line['how']})")
    lines.append("  after round | setting | Q_exact | Q_above (worst) | cost of finishing")
    for row in result["per_round"]:
        for setting, m in row["by_setting"].items():
            lines.append(f"  {row['after_round']:>11} | {setting} | {m['Q_exact_mean']:.4f} | {m['Q_above_mean']:.4f} ({m['Q_above_worst']:.4f}) | "
                         f"{m['cost_of_finishing_median']:.2f}")
    return "\n".join(lines)


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", required=True)
    ap.add_argument("--out", default=None, help="where to write the JSON (default <run>/rescore.json)")
    ap.add_argument("--force", action="store_true", help="overwrite an existing output file")
    args = ap.parse_args(argv)
    run_path = Path(args.run).expanduser().resolve()
    result = rescore(run_path)
    out = Path(args.out).expanduser().resolve() if args.out else run_path / "rescore.json"
    if out.exists() and not args.force:
        print(f"{out} exists; not overwritten (use --force)", file=sys.stderr)
    else:
        out.write_text(json.dumps(result, indent=1) + "\n")
        print(f"written {out}", file=sys.stderr)
    print(table(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
