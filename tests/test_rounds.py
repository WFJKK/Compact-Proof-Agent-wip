"""End to end on the stub model: fake responses through parse, sandbox, checker and archive."""

import gzip
import json
import shutil
from pathlib import Path

import pytest
import yaml

from core import loop
from core.check.checker import brute_force_proof, check_proof
from core.model_folder import load_model_folder
from core.scoring import frontier, q_score, summarize
from core.zoo import networks

TESTS = Path(__file__).resolve().parent
BROKEN = TESTS / "broken_responses"


def _quiet(*a, **k):
    pass


def _config(tmp_path, model: Path, **over) -> Path:
    cfg = {
        "run_id": "stub-run",
        "model": str(model),
        "runs_dir": str(tmp_path / "runs"),
        "knob_values": [0, 1],
        "time_limit_s": 3,
        "memory_limit_mb": 1024,
        "workers": 2,
        "fake_responses": [str(BROKEN)],
        "rounds_max": 10,
    }
    cfg.update(over)
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    return path


@pytest.fixture(scope="module")
def finished_run(trained_stub, tmp_path_factory):
    tmp = tmp_path_factory.mktemp("run")
    ctx = loop.start(_config(tmp, trained_stub), log=_quiet)
    loop.drive(ctx)
    return ctx


def _by_round(records, k):
    return [r for r in records if r["round"] == k]


def test_baselines_reproduce_the_checker(finished_run):
    ctx = finished_run
    records = ctx.run.read_archive()
    dev = networks(ctx.folder, "dev")
    assert len(dev) == 2
    brute = [r for r in _by_round(records, 0) if r["attempt"] == 0]
    sym = [r for r in _by_round(records, 0) if r["attempt"] == 1]
    assert len(brute) == len(sym) == 2 * 2  # networks x knob values (screening passed)
    for r in brute:
        direct = check_proof(brute_force_proof(ctx.folder, r["network"]), ctx.folder, r["network"])
        assert r["status"] == "ok"
        assert r["length"] == r["B"] == direct["length"]
        assert r["certified"] == direct["certified"]
    for r in sym:
        b = next(x for x in brute if x["network"] == r["network"])
        assert r["status"] == "ok" and r["certified"] == b["certified"] and r["length"] < 0.75 * b["length"]
    for r in brute + sym:  # diagnostics: the only uncertified inputs are the wrong ones
        s = r["uncertified_summary"]
        assert s["uncertified_correct"] == 0 and s["wrong"] == r["n_inputs"] - r["real_correct"]
        assert sum(d["wrong"] for d in r["uncertified_by_group"].values()) == s["wrong"]


def test_broken_responses_get_the_right_status(finished_run):
    records = finished_run.run.read_archive()
    statuses = {k: {r["status"] for r in _by_round(records, k)} for k in range(1, 6)}
    assert statuses[1] == {"parse"}
    assert statuses[2] == {"crash"}
    assert statuses[3] == {"timeout"}
    assert statuses[4] == {"ok"}
    assert statuses[5] == {"bad_output"}
    # Failed recipes stop after the screening network; the run carries on.
    for k in (2, 3, 5):
        assert {r["network"] for r in _by_round(records, k)} == {finished_run.entries[0]["id"]}
    assert "deliberate failure" in _by_round(records, 2)[0]["error"]
    assert "NaN" in _by_round(records, 5)[0]["error"] or "nan" in _by_round(records, 5)[0]["error"]
    # The false claim: most pieces rejected, and nothing certified that is wrong.
    for r in _by_round(records, 4):
        assert r["leaves"]["rejected"] > 0 and r["rejected"]
        assert r["certified"] <= r["real_correct"]
        assert r["rejected_summary"]["by_reason"]["label not constant"] > 0
        whys = {w for d in r["uncertified_by_group"].values() for w in d.get("why", {})}
        assert "label not constant" in whys
    from core.diagnostics import render_attempt

    text = render_attempt(_by_round(records, 4), "smallest token")
    assert "correct but uncertified" in text and "label not constant" in text
    assert render_attempt(_by_round(records, 1)).startswith("status parse")
    assert "timeout x2" in render_attempt(_by_round(records, 3))
    assert finished_run.run.done_rounds() == [0, 1, 2, 3, 4, 5]


def test_round_folders_hold_every_file(finished_run):
    run = finished_run.run
    a = run.round_path(0) / "attempt_0"
    for name in ("response.md", "response_meta.json", "parsed.json", "recipe.py", "results.json"):
        assert (a / name).is_file(), name
    proofs = sorted((a / "proofs").glob("*.json.gz"))
    assert len(proofs) == 4
    proof = json.loads(gzip.decompress(proofs[0].read_bytes()))
    assert proof["network"] in {e["id"] for e in finished_run.entries}
    assert (run.round_path(1) / "attempt_0" / "parsed.json").is_file()
    assert "error" in run.read(1, "attempt_0/parsed.json")
    meta = run.read(0, "meta.json")
    assert meta["versions"]["checker"] and meta["git"]["commit"]
    assert [m["source"] for m in meta["attempts"]] == ["01_brute_force.md", "02_symmetry.md"]


def test_archive_matches_round_results(finished_run):
    run = finished_run.run
    archive = run.read_archive()
    from_rounds = []
    for k in run.done_rounds():
        j = 0
        while run.read(k, f"attempt_{j}/results.json") is not None:
            from_rounds += run.read(k, f"attempt_{j}/results.json")
            j += 1
    assert sorted(r["record_id"] for r in archive) == sorted(r["record_id"] for r in from_rounds)
    assert len({r["record_id"] for r in archive}) == len(archive)


def test_frontier_and_q(finished_run):
    records = finished_run.run.read_archive()
    fr = frontier(records)
    for e in finished_run.entries:
        pts = fr[e["id"]]
        lengths = [p["length"] for p in pts]
        assert lengths == sorted(lengths)
        assert all(a["certified"] < b["certified"] for a, b in zip(pts, pts[1:]))
        assert 0 < q_score(pts, e["E"], e["B"]) < 1
    s = summarize(records, finished_run.entries)
    assert set(s) == {"tiny"}


def test_q_score_by_hand():
    pts = [
        {"length": 10, "certified": 1, "n_inputs": 2},
        {"length": 100, "certified": 2, "n_inputs": 2},
    ]
    # a(b) = 1/2 on [10, 100), 1 on [100, 1000]; E = 1, B = 1000
    expected = (0.5 * (2.302585092994046) + 1.0 * 2.302585092994046) / 6.907755278982137
    assert q_score(pts, 1, 1000) == pytest.approx(expected)
    assert q_score([], 1, 1000) == 0.0
    assert q_score([{"length": 1000, "certified": 2, "n_inputs": 2}], 1, 1000) == 0.0


def test_resume_finishes_a_round_without_asking_again(trained_stub, tmp_path):
    ctx = loop.start(_config(tmp_path, trained_stub, rounds_max=2), log=_quiet)
    loop.drive(ctx)
    run = ctx.run
    before = run.read(2, "attempt_0/results.json")
    # Simulate a crash in the middle of round 2: no DONE marker, no results, but the response was saved.
    (run.round_path(2) / "DONE").unlink()
    (run.round_path(2) / "attempt_0" / "results.json").unlink()
    (run.round_path(2) / "meta.json").unlink()
    asked = []

    class Spy:
        name = "spy"

        def available(self, index):
            return True

        def respond(self, prompt, index):
            asked.append(index)
            raise AssertionError("a saved response must not be asked for again")

    ctx2 = loop.resume(run.path, log=_quiet)
    from core.rounds import run_round

    run_round(ctx2, 2, Spy(), 1, 1, "agent")
    assert asked == [] and run.round_done(2)
    after = run.read(2, "attempt_0/results.json")

    def strip(rs):
        return sorted((r["record_id"], r["status"], r["certified"], r["length"]) for r in rs)

    assert strip(after) == strip(before)
    assert len(run.read_archive()) == len({r["record_id"] for r in run.read_archive()})


def test_run_refuses_to_resume_after_trusted_files_change(trained_stub, tmp_path):
    model = tmp_path / "stub_copy"
    shutil.copytree(trained_stub, model, ignore=shutil.ignore_patterns("__pycache__"))
    ctx = loop.start(_config(tmp_path, model, rounds_max=1, fake_responses=[]), log=_quiet)
    (model / "task.py").write_text((model / "task.py").read_text() + "\n# edited\n")
    with pytest.raises(loop.LoopError, match="model_folder changed"):
        loop.resume(ctx.run.path, log=_quiet)


def test_held_out_networks_cannot_be_selected(trained_stub, tmp_path):
    folder = load_model_folder(trained_stub)
    held = networks(folder, "held_out")[0]["id"]
    with pytest.raises(loop.LoopError, match="not development networks"):
        loop.start(_config(tmp_path, trained_stub, networks=[held]), log=_quiet)


def test_certifying_a_wrong_input_halts_the_run(finished_run):
    """The one invariant a proof cannot fake: a sound checker never certifies more than the network gets right."""
    from core.check.checker import brute_force_proof
    from core.check.worker import CheckerProcess
    from core.rounds import RoundError, execution_record
    from core.runner import Execution

    ctx = finished_run
    entry = dict(ctx.entries[0])
    ex = Execution(status="ok", proof=brute_force_proof(ctx.folder, entry["id"]))
    with CheckerProcess(ctx.folder.path, ctx.versions, timeout_s=120) as checker:
        rec = execution_record(ctx, 90, 0, "test", entry, 0, ex, {}, checker)
        assert rec["status"] == "ok" and rec["certified"] == entry["real_correct"]
        entry["real_correct"] -= 1  # as if the zoo said the network gets one input fewer right
        with pytest.raises(RoundError, match="gets only"):
            execution_record(ctx, 91, 0, "test", entry, 0, ex, {}, checker)


def test_remeasure_reproduces_the_archive(finished_run, tmp_path):
    """Under the same cost model, re-measuring gives the archived lengths and certified counts."""
    from core import remeasure
    from core.check.cost import VERSION

    ctx = finished_run
    out = tmp_path / "again"
    assert remeasure.main(["--run", str(ctx.run.path), "--out", str(out), "--workers", "2"]) == 0
    old = {r["record_id"]: r for r in ctx.run.read_archive()}
    new = [json.loads(line) for line in (out / "archive.jsonl").read_text().splitlines()]
    assert [r["record_id"] for r in new] == list(old)
    checked = 0
    for r in new:
        o = old[r["record_id"]]
        assert r["status"] == o["status"] and r["certified"] == o["certified"]
        if o["status"] == "ok":
            assert r["length"] == o["length"] == r["length_archived"] and r["cost_model"] == VERSION
            checked += 1
    assert checked > 0
    summary = json.loads((out / "summary.json").read_text())
    assert summary["cost_model"] == VERSION and "0" in summary["development"]
    # Never inside the run, never over it.
    assert remeasure.main(["--run", str(ctx.run.path), "--out", str(ctx.run.path / "x")]) == 2
