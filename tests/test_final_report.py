"""The final evaluation on held-out networks, and reports."""

import ast
from pathlib import Path

import pytest
import yaml

from core import final, loop, report
from core.zoo import networks

CORE = Path(__file__).resolve().parent.parent / "core"


@pytest.fixture(scope="module")
def finished(trained_stub, tmp_path_factory):
    tmp = tmp_path_factory.mktemp("final")
    cfg = {
        "run_id": "final-test",
        "model": str(trained_stub),
        "runs_dir": str(tmp / "runs"),
        "knob_values": [0, 1],
        "fake_responses": [str(Path(__file__).parent / "broken_responses" / "b4_false_claim.md")],
        "rounds_max": 1,
    }
    path = tmp / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    ctx = loop.start(path, log=lambda *a: None)
    loop.drive(ctx)
    return ctx


def test_only_final_turns_on_held_out_loading():
    """No call in the core passes held_out=True or allow_held_out=True, except in final.py and in
    check/exact_counts.py, the offline zoo step that records every network's brute-force count in the
    manifest before any run (python -m core.check.exact_counts); the loop never reaches it."""
    users = set()
    for path in CORE.rglob("*.py"):
        for node in ast.walk(ast.parse(path.read_text())):
            if isinstance(node, ast.Call):
                for kw in node.keywords:
                    if kw.arg in ("held_out", "allow_held_out") and isinstance(kw.value, ast.Constant) and kw.value.value is True:
                        users.add(path.relative_to(CORE).as_posix())
    assert users == {"final.py", "check/exact_counts.py"}


def test_final_evaluates_frontier_recipes_on_held_out_networks(finished):
    ctx = finished
    held = {e["id"] for e in networks(ctx.folder, "held_out")}
    dev = {e["id"] for e in ctx.entries}
    assert not held & {r["network"] for r in ctx.run.read_archive()}  # the run never touched them
    summary = final.evaluate(ctx.run.path, log=lambda *a: None)
    keys = final.frontier_attempts(ctx.run.read_archive())
    assert summary["recipes"] == [list(k) for k in keys] and (1, 0) not in keys  # the false claim certified nothing
    recs = final.RunDir(ctx.run.path, "final").read_archive()
    assert {r["network"] for r in recs} == held and not dev & {r["network"] for r in recs}
    assert len(recs) == len(keys) * len(held) * 2
    assert all(r["status"] == "ok" and r["certified"] <= r["real_correct"] for r in recs)
    s = summary["settings"]["tiny"]
    assert set(s) == {"development", "held_out", "held_out_networks"} and set(s["held_out_networks"]) == held
    assert (ctx.run.path / "final" / "final.md").read_text().startswith("# Held-out evaluation")
    # Running it again finds everything done and checks nothing twice.
    again = final.evaluate(ctx.run.path, log=lambda *a: None)
    assert again == summary and len(final.RunDir(ctx.run.path, "final").read_archive()) == len(recs)


def test_report_and_results(finished, tmp_path, monkeypatch):
    path = report.build_report(finished.run.path)
    text = path.read_text()
    for section in ("## Results per size setting", "## Recipes that hold the frontier", "## Progress", "best certified accuracy within B/100"):
        assert section in text
    assert (path.parent / "frontier_tiny.png").stat().st_size > 1000 and (path.parent / "progress.png").exists()
    monkeypatch.setattr(report, "RESULTS", tmp_path / "results")
    dest = report.copy_to_results(finished.run.path)
    assert (dest / "report.md").exists() and (dest / "config.yaml").exists()
    assert "final-test" in (tmp_path / "results" / "RESULTS.md").read_text()
    with pytest.raises(loop.LoopError, match="never overwritten"):
        report.copy_to_results(finished.run.path)
