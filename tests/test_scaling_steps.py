"""The scaling proofs after a run (core/open_lane/scaling_steps.py; python3 -m core.loop scale --run <run>): one
session per size, V then n then d, each with its own time and cap, about the run's scored proofs on its frontier.
On the stand-ins of tests/test_open_lane_compiled.py (a run whose checker the service runs compiled)."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from core import loop
from core.model_folder import load_model_folder
from core.open_lane import scaling_steps, stages
from core.open_lane.session import Session
from core.report import build_report
from core.run_config import scaling_steps_errors
from core.util import REPO_ROOT
from core.zoo import network_entry
from tests.test_open_lane_compiled import COL, COUNTS, SCORED, answers, compiled_run, run_service
from tests.test_stages import A, call

SHORT = COL.replace("Candidate.Col", "Candidate.Short")
SCORED_SHORT = {"checker": "Candidate.Short.D", "sound": "Candidate.Short.D_sound", "certificate": []}
GROWTH_V = "import Candidate.Col\nimport Candidate.Short\nnamespace Candidate.GrowthV\ntheorem bill_in_V : True := trivial\nend Candidate.GrowthV\n"
GROWTH_N = "import Candidate.Col\nnamespace Candidate.GrowthN\ntheorem bill_in_n : True := trivial\nend Candidate.GrowthN\n"

ROUND = {"calls": [
    call("lean_check", path="Candidate/Col.lean", source=COL, network=A),
    call("submit_candidate", network=A, modules=["Candidate/Col.lean"], scored=SCORED),
    call("lean_check", path="Candidate/Short.lean", source=SHORT, network=A),
    call("submit_candidate", network=A, modules=["Candidate/Short.lean"], scored=SCORED_SHORT),
], "response": "CLAIM: two proofs.\nWHY IT HELPS: -\nNOTES: none."}
DISCOVERY = {"calls": [], "response": "CLAIM: none yet.\nWHY IT HELPS: -\nNOTES: -"}
READING = {"calls": [call("read_file", path="py/locked_proof.json")],
           "response": "VERDICT: clean\nFOUND: nothing.\nNOTES: none."}
STEP_V = {"calls": [
    call("read_file", path="py/handed_in_proofs.json"),
    call("read_file", path="Candidate/Short.lean"),
    call("lean_check", path="Candidate/GrowthV.lean", source=GROWTH_V, network=A),
    call("submit_candidate", network=A, modules=["Candidate/GrowthV.lean", "Candidate/Col.lean", "Candidate/Short.lean"],
         theorem="Candidate.GrowthV.bill_in_V", kind="auxiliary"),
], "response": ("CLAIM: Col grows like V^2, brute force like V^3: a smaller exponent.\n"
                "SCALING:\n- Col: bill = 20000 at V = 24; leading order V^2; bill_in_V proves a.\n- Short: the same method.\n"
                "WHY IT HELPS: -\nNOTES: n next.")}
STEP_N = {"calls": [
    call("read_file", path="Candidate/GrowthV.lean"),
    call("lean_check", path="Candidate/GrowthN.lean", source=GROWTH_N, network=A),
    call("submit_candidate", network=A, modules=["Candidate/GrowthN.lean", "Candidate/Col.lean"],
         theorem="Candidate.GrowthN.bill_in_n", kind="auxiliary"),
], "response": "CLAIM: no n in it.\nSCALING:\n- Col: bill independent of n.\nWHY IT HELPS: -\nNOTES: none."}
STEP_D = {"calls": [call("submit_candidate", network=A, modules=["Candidate/Col.lean"], scored=SCORED)],
          "response": "CLAIM: nothing proved.\nSCALING:\n- none.\nWHY IT HELPS: -\nNOTES: ran out."}


@pytest.fixture(autouse=True)
def _stand_ins(stand_in_surface):
    """What the run shows the agent, standing in (tests/conftest.py), as in tests/test_open_lane_compiled.py."""


def two_proofs_service():
    """The stand-in service, with Candidate.Short.D certifying 100 inputs fewer at a bill of 5,000: shorter and
    weaker, so both proofs are on the frontier, and the stronger one finishes cheaper and is locked."""
    base = run_service()

    def service(self, args, timeout_s):
        out = base(self, args, timeout_s)
        if args[0] != "compile" and out.get("status") == "accepted":
            m = json.loads((Path(args[1]) / "manifest.json").read_text())
            if (m.get("scored") or {}).get("checker") == "Candidate.Short.D":
                sc = out["scoring"]
                out["certified_count"] = COUNTS[m["network"]] - 100
                out["scoring"] = {**sc, "bill": 5000, "length": 5000 + sc["extract"] + sc["read"]}
        return out
    return service


def finished_run(tmp_path, monkeypatch, scripts):
    path = compiled_run(tmp_path, monkeypatch, scripts, rounds_max=2, discovery_rounds=1, code_review=True, scaling=False)
    monkeypatch.setattr(Session, "_service", two_proofs_service())
    lines: list[str] = []
    ctx = loop.start(path, log=lines.append)
    loop.drive(ctx)
    assert ctx.run.done_rounds() == [0, 1, 2, 3], lines[-6:]
    return ctx, lines


def test_the_steps_run_in_order_with_their_own_time_and_carry_on(tmp_path, monkeypatch):
    """After a finished run: V first, then n, then d, each a round after the run's last, each with its own session
    time; the proofs are the run's frontier (here two, the locked one and a shorter, weaker one whose module sits
    beside the locked ones); every proof's certificate and plan are in the Python workspace. A lemma is recorded
    with its statement and with the proofs whose checker Lean finds in it: the locked one asked in the session,
    the other after it. The next step starts with the earlier step's lemma modules and its answer. A step can be
    run alone (--only), but only in order; running the command again goes on, and once all are done it does
    nothing. The report and the status say what was found; the run's frontier is unchanged."""
    ctx, lines = finished_run(tmp_path, monkeypatch, [DISCOVERY, ROUND, READING, STEP_V, STEP_N, STEP_D])
    run = ctx.run
    front = stages.scored_proofs(run.read_archive(), network_entry(ctx.folder, A) | {"id": A})
    with pytest.raises(loop.LoopError, match="in order"):
        loop.scale(ctx, only=["n"])
    loop.scale(ctx, only=["V"])
    sp = stages.read_state(run)["scaling_proofs"]
    assert [(s["parameter"], s["round"], s["minutes"], s["usd"]) for s in sp["steps"]] == [("V", 4, 60, 20), ("n", 5, 30, 10), ("d", 6, 30, 10)]
    assert [s["result"] is not None for s in sp["steps"]] == [True, False, False]
    assert [(p["checker"], p["locked"], p["offered"]) for p in sp["proofs"]] == [
        ("Candidate.Short.D", False, True), ("Candidate.Col.D", True, True)]
    assert sp["sizes"] == {"V": {"names": ["d_vocab"], "value": 24}, "n": {"names": ["n_ctx"], "value": 2},
                           "d": {"names": ["d_model"], "value": 8}}
    prompt = run.read(4, "prompt.md")
    assert "THIS SESSION: HOW THE COST GROWS WITH V" in prompt and "This is session 1 of 3." in prompt
    assert "V = 24 (d_vocab), n = 2 (n_ctx), d = 8 (d_model)" in prompt
    assert "while the number of positions n = 2 (n_ctx) and the width d = 8 (d_model) stay" in prompt
    assert "3,600 s of wall clock" in prompt and "This is the first of these sessions." in prompt
    assert "Candidate.Short.D" in prompt and "Candidate/Short.lean" in prompt
    assert "Gross" not in prompt and "Compact Proofs" not in prompt
    session = run.round_path(4) / "attempt_0" / "open_lane"
    log = [json.loads(line) for line in (session / "tools.jsonl").read_text().splitlines()]
    assert [(e["tool"], e["outcome"].get("lines", 0) > 0) for e in log[:2]] == [("read_file", True), ("read_file", True)]
    proofs = json.loads((session / "py" / "handed_in_proofs.json").read_text())["proofs"]
    assert [(p["checker"], p["locked"], p["certified_count"]) for p in proofs] == [
        ("Candidate.Short.D", False, COUNTS[A] - 100), ("Candidate.Col.D", True, COUNTS[A])]
    assert (session / "workspace" / "Candidate" / "Short.lean").read_text() == SHORT
    assert (session / "py" / "locked_proof.json").is_file()
    (lemma,) = sp["steps"][0]["result"]["lemmas"]
    ids = {p["checker"]: p["record_id"] for p in sp["proofs"]}
    assert lemma["theorem"] == "Candidate.GrowthV.bill_in_V" and lemma["statement"] == "∀ w, bill w = 20000"
    assert {rid: c["verified"] for rid, c in lemma["checkers"].items()} == {ids["Candidate.Col.D"]: True, ids["Candidate.Short.D"]: True}
    assert sp["steps"][0]["result"]["answer"]["SCALING"].startswith("- Col: bill = 20000")

    loop.scale(ctx)  # n, then d
    sp = stages.read_state(run)["scaling_proofs"]
    assert all(s["result"] is not None for s in sp["steps"]) and run.done_rounds() == [0, 1, 2, 3, 4, 5, 6]
    second = run.read(5, "prompt.md")
    assert "This is session 2 of 3." in second and "1,800 s of wall clock" in second
    assert "WHAT THE EARLIER SESSIONS FOUND" in second and "Candidate.GrowthV.bill_in_V" in second and "- Col: bill = 20000" in second
    assert (run.round_path(5) / "attempt_0" / "open_lane" / "workspace" / "Candidate" / "GrowthV.lean").read_text() == GROWTH_V  # carried
    (lemma_n,) = sp["steps"][1]["result"]["lemmas"]
    assert {rid: c["verified"] for rid, c in lemma_n["checkers"].items()} == {ids["Candidate.Col.D"]: True, ids["Candidate.Short.D"]: False}
    refused = answers(run, 6)[0]
    assert "auxiliary" in json.dumps(refused) and sp["steps"][2]["result"]["lemmas"] == []

    lines.clear()
    loop.scale(ctx)
    assert lines[-1] == "the scaling proofs are done; nothing to run"
    report = Path(build_report(run.path)).read_text()
    assert "## The scaling proofs" in report and "### V: the number of token values (round 4, 60 minutes, at most $20.00)" in report
    assert "∀ w, bill w = 20000" in report and "- Col: bill independent of n." in report
    status = loop.status_text(run)
    assert "scaling in V (round 4): 1 lemma(s) accepted, 1 shown by Lean to hold a submitted proof's checker" in status
    assert "scaling in d (round 6): 0 lemma(s) accepted" in status
    assert stages.scored_proofs(run.read_archive(), network_entry(ctx.folder, A) | {"id": A}) == front


def test_the_command_refuses_what_it_cannot_do(tmp_path, monkeypatch):
    """Not before the run is finished, not without the model folder's sizes; the steps' settings are checked."""
    path = compiled_run(tmp_path, monkeypatch, [DISCOVERY, ROUND, READING], rounds_max=2, discovery_rounds=1, code_review=True, scaling=False)
    monkeypatch.setattr(Session, "_service", two_proofs_service())
    ctx = loop.start(path, log=lambda line: None)
    with pytest.raises(loop.LoopError, match="proof rounds are not over"):
        loop.scale(ctx)
    loop.drive(ctx)
    block = ctx.folder.config["open_lane"]
    monkeypatch.setitem(ctx.folder.config, "open_lane", {k: v for k, v in block.items() if k != "scaling_sizes"})
    with pytest.raises(loop.LoopError, match="no open_lane.scaling_sizes"):
        loop.scale(ctx)
    assert stages.read_state(ctx.run).get("scaling_proofs") is None
    assert scaling_steps_errors([{"parameter": "n", "minutes": 1, "usd": 1}, {"parameter": "V", "minutes": 1, "usd": 1}]) == [
        "open_lane.scaling_steps: each of V, n, d at most once, in that order"]
    assert scaling_steps_errors([{"parameter": "V", "minutes": 0, "usd": 1}]) == ["open_lane.scaling_steps: V's minutes must be a positive number"]
    assert scaling_steps_errors([{"parameter": "w", "minutes": 1, "usd": 1}])[0].startswith("open_lane.scaling_steps: parameter must be one of V, n, d")


@pytest.mark.parametrize("model, network, expected", [
    ("max4", "max4-v64-s0", {"V": 64, "n": 4, "d": 8}),
    ("min4", "min4-v64-s0", {"V": 64, "n": 4, "d": 8}),
    ("max2", "max2-v64-s0", {"V": 64, "n": 2, "d": 8}),
    ("attn-max4", "attn-max4-v64-s0", {"V": 64, "n": 4, "d": 32}),
    ("attn-min2", "attn-min2-v64d8-s0", {"V": 64, "n": 2, "d": 8}),
])
def test_the_model_folders_say_which_sizes_are_v_n_and_d(model, network, expected):
    """Every model folder with open-lane settings names its sizes for the scaling proofs; an attention model's
    width and head width vary together and are equal wherever it has networks."""
    folder = load_model_folder(REPO_ROOT / "models" / model)
    sizes = scaling_steps.sizes_of(folder, network_entry(folder, network))
    assert {p: s["value"] for p, s in sizes.items()} == expected
    assert sizes["d"]["names"] == (["d_model", "d_head"] if model.startswith("attn") else ["d_model"])
