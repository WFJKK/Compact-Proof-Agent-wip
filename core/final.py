"""Final evaluation: a finished run's frontier recipes, on the held-out networks.

    python -m core.final --run <runs_dir>/<run_id>

Every recipe that holds a point of the frontier on some development network is
run at every knob value on every held-out network of the run's size settings,
in the same kind of sandbox as the run. Every proof is checked in Python, and
in Lean too for a model with a Lean checker. This is the only code path that
loads held-out networks.

The results go to <run>/final/, laid out like a run (one folder per source
round, its own archive.jsonl, resumable after a stop), plus final.json and
final.md: per size setting, the metrics on the held-out networks next to those
on the development networks.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from .archive import RunDir
from .lean import LeanError, lean_command, spot_check
from .loop import LoopError, prepare_sandbox, select_networks
from .model_folder import load_model_folder
from .rounds import Context, RoundError, now, run_attempt
from .run_config import resolve
from .runner import Limits
from .sandbox import SandboxError
from .scoring import frontier, summarize
from .util import read_json, write_json
from .versions import changed
from .zoo import networks

METRICS = ("Q_median", "Q_worst", "Q_grid_median", "Q_grid_worst", "Q_exact_mean", "Q_exact_worst", "Q_above_mean", "Q_above_worst",
           "cost_of_finishing_median", "cost_of_finishing_worst", "shortest_full_over_B_median")


class FinalError(RuntimeError):
    pass


def frontier_attempts(records: list[dict]) -> list[tuple[int, int]]:
    """The (round, attempt) pairs whose recipes hold a frontier point on some network."""
    return sorted({(p["round"], p["attempt"]) for pts in frontier(records).values() for p in pts})


def held_out_entries(folder, dev: list[dict]) -> list[dict]:
    settings = list(dict.fromkeys(e["setting"] for e in dev))
    order = {s: i for i, s in enumerate(settings)}
    held = [e for e in networks(folder, "held_out") if e["setting"] in order]
    held.sort(key=lambda e: (order[e["setting"]], e["seed"]))
    if not held:
        raise LoopError(f"{folder.name} has no held-out networks in the run's size settings")
    missing = [e["id"] for e in held if e.get("E") is None or e.get("B") is None]
    if missing:
        raise LoopError(f"E and B are missing for {missing}")
    return held


def evaluate(run_path: str | Path, log=print) -> dict:
    run_path = Path(run_path).expanduser().resolve()
    run = RunDir(run_path.parent, run_path.name)
    if not run.exists():
        raise LoopError(f"no run at {run_path}")
    cfg = run.config()
    if cfg.get("open_lane", {}).get("enabled"):
        raise FinalError(
            "this run used the open lane: its proofs are Lean modules written for the development networks, and "
            "evaluating them on held-out networks needs the frozen-method transfer of the next ticket (a frozen "
            "checker re-proved on each network without agent turns), which does not exist yet. No held-out "
            "numbers are produced for it."
        )
    folder = load_model_folder(resolve(cfg["model"]))
    started = read_json(run.path / "versions.json")
    bad = changed(started, folder)
    if bad:
        raise LoopError(f"{', '.join(bad)} changed since the run started; its held-out numbers would not be comparable")
    sys.dont_write_bytecode = True
    dev = select_networks(folder, cfg)
    held = held_out_entries(folder, dev)
    keys = frontier_attempts(run.read_archive())
    if not keys:
        raise LoopError("the run has no checked proofs, so there is nothing to evaluate")

    final = RunDir(run.path, "final")
    if not final.exists():
        final.create({**cfg, "final_of": run.run_id})
    sb, _ = prepare_sandbox(cfg, folder, final, dev, log)  # the probe runs on a development network
    ctx = Context(
        cfg={**cfg, "screen": False},
        folder=folder,
        run=final,
        entries=held,
        versions=started,
        limits=Limits.from_config(cfg),
        sandbox=sb,
        log=log,
        held_out=True,
    )
    log(f"final evaluation of {len(keys)} frontier recipes on {len(held)} held-out networks ({sb.mode} sandbox)")
    lean = lean_command(folder) is not None
    for k in sorted({k for k, _ in keys}):
        if final.round_done(k):
            continue
        for j in [j for kk, j in keys if kk == k]:
            text = run.read(k, f"attempt_{j}/response.md")
            log(f"round {k} attempt {j}")
            records = run_attempt(ctx, k, j, "final", text)
            final.append_archive(records)
            if lean:
                spot_check(ctx, k, [r for r in records if r["status"] == "ok"], limit=None)
        write_json(final.round_path(k) / "meta.json", {"round": k, "attempts": [j for kk, j in keys if kk == k], "finished": now()})
        final.mark_done(k)

    summary = {
        "run_id": run.run_id,
        "checked_by": "Python and Lean" if lean else "Python",
        "recipes": [list(key) for key in keys],
        "settings": {},
    }
    dev_s = summarize(run.read_archive(), dev, cfg.get("budget_ratio"))
    held_s = summarize(final.read_archive(), held, cfg.get("budget_ratio"))
    for setting in dev_s:
        summary["settings"][setting] = {
            "development": {m: dev_s[setting][m] for m in METRICS},
            "held_out": {m: held_s[setting][m] for m in METRICS},
            "held_out_networks": {nid: {k: v for k, v in m.items() if k != "points"} for nid, m in held_s[setting]["networks"].items()},
        }
    write_json(final.path / "final.json", summary)
    (final.path / "final.md").write_text(render(summary))
    log(render(summary))
    return summary


def _fmt(v) -> str:
    if v is None:
        return "none"
    return f"{v:.4f}" if isinstance(v, float) else str(v)


def render(summary: dict) -> str:
    lines = [
        f"# Held-out evaluation of {summary['run_id']}",
        "",
        f"{len(summary['recipes'])} frontier recipes, checked by {summary['checked_by']}.",
        "",
    ]
    for setting, s in summary["settings"].items():
        lines += [f"## {setting}", "", "| Metric | Development | Held out |", "| --- | --- | --- |"]
        for m in METRICS:
            lines.append(f"| {m} | {_fmt(s['development'][m])} | {_fmt(s['held_out'][m])} |")
        lines += ["", "| Held-out network | Q | Best certified accuracy | Real accuracy |", "| --- | --- | --- | --- |"]
        for nid, m in s["held_out_networks"].items():
            lines.append(f"| {nid} | {m['Q']:.4f} | {m['best_accuracy']:.5f} | {m['real_accuracy']:.5f} |")
        lines.append("")
    return "\n".join(lines)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--run", required=True, help="the run's folder, <runs_dir>/<run_id>")
    args = ap.parse_args(argv)
    try:
        evaluate(args.run)
        return 0
    except (LoopError, RoundError, SandboxError, LeanError, FinalError) as exc:
        print(f"error: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
