"""The scaling proofs after a run (core/open_lane/scaling; python3 -m core.loop scale --run <run>): a session
for the checker with its sizes as parameters, then one per size of the network, each with its own time and cap,
about the run's scored proofs on its frontier; further sessions with --again; the links an answer names. The
package takes the sizes from the network's size setting, and nothing outside it is made for it. On the
stand-ins of tests/test_open_lane_compiled.py (a run whose checker the service runs compiled)."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path

import pytest
import yaml

from core import loop
from core.model_folder import load_model_folder
from core import versions
from core.open_lane import after_run, stages
from core.open_lane.scaling import command, later_pipeline, links, plan
from core.open_lane.scaling import prompt as scaling_prompt
from core.open_lane.scaling import sizes as network_sizes
from core.open_lane.scaling import steps as scaling_steps
from core.open_lane.session import Session
from core.report import build_report
from core.run_config import scaling_names_errors, scaling_steps_errors
from core.util import REPO_ROOT
from core.zoo import network_entry
from tests.test_open_lane_compiled import COL, COUNTS, SCORED, answers, compiled_run, run_service
from tests.test_stages import A, call

SHORT = COL.replace("Candidate.Col", "Candidate.Short")
SCORED_SHORT = {"checker": "Candidate.Short.D", "sound": "Candidate.Short.D_sound", "certificate": []}
GENERAL = ("import Candidate.Col\nimport Candidate.Short\nnamespace Candidate.General\n"
           "theorem general_cost : True := trivial\nend Candidate.General\n")
DRAFT = "import Candidate.General\nnamespace Candidate.Draft\n-- unfinished\nend Candidate.Draft\n"
BROKEN = "namespace Candidate.Broken\ntheorem no : False := oops\nend Candidate.Broken\n"  # the stand-in refuses it
GROWTH_V = "import Candidate.General\nnamespace Candidate.GrowthV\ntheorem scaling_V : True := trivial\nend Candidate.GrowthV\n"
GROWTH_N = "import Candidate.Col\nnamespace Candidate.GrowthN\ntheorem bill_in_n : True := trivial\nend Candidate.GrowthN\n"
# What the stand-in service prints as the statement of a lemma: by its name, else a statement that names no checker.
STATEMENTS = {
    "Candidate.General.general_cost": "And (Eq (Candidate.General.Dg 24 2 8) Candidate.Col.D) (∀ V, bill (Candidate.General.Dg V 2 8) = cost V)",
    "Candidate.GrowthV.scaling_V": "∀ V, bill (Candidate.General.Dg V 2 8) ≤ 3 * V ^ 2 ∧ Candidate.Col.D = Candidate.General.Dg 24 2 8",
}
PLAIN = "∀ n, billN n < bruteN n"

ROUND = {"calls": [
    call("lean_check", path="Candidate/Col.lean", source=COL, network=A),
    call("submit_candidate", network=A, modules=["Candidate/Col.lean"], scored=SCORED),
    call("lean_check", path="Candidate/Short.lean", source=SHORT, network=A),
    call("submit_candidate", network=A, modules=["Candidate/Short.lean"], scored=SCORED_SHORT),
], "response": "CLAIM: two proofs.\nWHY IT HELPS: -\nNOTES: none."}
DISCOVERY = {"calls": [], "response": "CLAIM: none yet.\nWHY IT HELPS: -\nNOTES: -"}
# The reading as a real session's answer comes: its opening line runs into the answer (the text before a tool
# call), and the headings are in bold.
READING = {"calls": [call("read_file", path="py/locked_proof.json")],
           "response": "I'll start by reading the locked proof.**VERDICT:** clean\n\n**FOUND:**\n\nnothing.\n\n**NOTES:** none."}
STEP_G = {"calls": [
    call("read_file", path="py/handed_in_proofs.json"),
    call("read_file", path="Candidate/Short.lean"),
    call("run_python", code="print('the model of the bill')", network=A, save_as="py/billmodel.py"),
    call("lean_check", path="Candidate/General.lean", source=GENERAL, network=A),
    call("lean_check", path="Candidate/Draft.lean", source=DRAFT, network=A),
    call("lean_check", path="Candidate/Broken.lean", source=BROKEN, network=A),
    call("submit_candidate", network=A, modules=["Candidate/General.lean", "Candidate/Col.lean", "Candidate/Short.lean"],
         theorem="Candidate.General.general_cost", kind="auxiliary"),
], "response": ("CLAIM: Col's checker has V written in; Dg takes it, and its bill is a theorem.\n"
                "THEOREMS:\n- `V general: Candidate.General.general_cost`\n- V cost: Candidate.General.general_cost\n"
                "- n general: as submitted (it reads n from the shapes)\n- n cost: `Candidate.General.general_cost`\n"
                "- d general: Candidate.General.not_handed_in\n- d cost: none\n"
                "SCALING:\n- Col: Dg V n d, cost V.\n"
                "WHY IT HELPS: -\nNOTES: the formula in V next.")}
STEP_V = {"calls": [
    call("read_file", path="py/billmodel.py"),
    call("read_file", path="Candidate/Draft.lean"),
    call("lean_check", path="Candidate/GrowthV.lean", source=GROWTH_V, network=A),
    call("submit_candidate", network=A, modules=["Candidate/GrowthV.lean", "Candidate/General.lean", "Candidate/Col.lean", "Candidate/Short.lean"],
         theorem="Candidate.GrowthV.scaling_V", kind="auxiliary"),
], "response": ("CLAIM: Col grows like V^2, brute force like V^3: a smaller exponent, a theorem.\n"
                "THEOREMS:\nV general: Candidate.General.general_cost\nV cost: Candidate.General.general_cost\n"
                "V formula: Candidate.GrowthV.scaling_V\nV brute: none\n"
                "SCALING:\n- Col: bill at most 3 V^2; leading order V^2.\n- Short: the same method.\n"
                "WHY IT HELPS: -\nNOTES: n next.")}
STEP_N = {"calls": [
    call("read_file", path="Candidate/GrowthV.lean"),
    call("lean_check", path="Candidate/GrowthN.lean", source=GROWTH_N, network=A),
    call("submit_candidate", network=A, modules=["Candidate/GrowthN.lean", "Candidate/Col.lean"],
         theorem="Candidate.GrowthN.bill_in_n", kind="auxiliary"),
], "response": ("I'll start by reading the earlier lemma.**CLAIM:** no n in it.\n\n**THEOREMS:**\n\n"
                "- **n formula:** `Candidate.GrowthN.bill_in_n`\n- n brute: none\n\n**SCALING:**\n\n"
                "- Col: bill independent of n.\n\n**WHY IT HELPS:** -\n\n**NOTES:** none.")}
STEP_D = {"calls": [call("submit_candidate", network=A, modules=["Candidate/Col.lean"], scored=SCORED)],
          "response": "CLAIM: nothing proved.\nSCALING:\n- none.\nWHY IT HELPS: -\nNOTES: ran out."}
AGAIN_V = {"calls": [call("read_file", path="Candidate/GrowthV.lean")],
           "response": "CLAIM: brute force still to do.\nTHEOREMS:\nV brute: none\nSCALING:\n- as before.\nWHY IT HELPS: -\nNOTES: -"}
STEPS = [STEP_G, STEP_V, STEP_N, STEP_D]
TEXTS = {"general": "open_lane_scaling_frame_v1+open_lane_scaling_part_general_v1",
         "size": "open_lane_scaling_frame_v1+open_lane_scaling_part_size_v1"}
SIZES = [{"symbol": "V", "words": "the number of token values", "names": ["d_vocab"], "value": 24},
         {"symbol": "n", "words": "the number of positions", "names": ["n_ctx"], "value": 2},
         {"symbol": "d", "words": "the width", "names": ["d_model"], "value": 8}]


def scale(ctx, only=None, again=None, minutes=None, usd=None, end_proof_rounds=False) -> None:
    """The command on an opened run, as core.loop.main runs it."""
    loop.follow(ctx, command, argparse.Namespace(only=only, again=again, minutes=minutes, usd=usd, end_proof_rounds=end_proof_rounds))


@pytest.fixture(autouse=True)
def _stand_ins(stand_in_surface):
    """What the run shows the agent, standing in (tests/conftest.py), as in tests/test_open_lane_compiled.py."""


def two_proofs_service():
    """The stand-in service, with Candidate.Short.D certifying 100 inputs fewer at a bill of 5,000: shorter and
    weaker, so both proofs are on the frontier, and the stronger one finishes cheaper and is locked. A lemma's
    statement is STATEMENTS' for its name, and one that names no checker otherwise. Every compile is noted."""
    base = run_service()
    compiles: list[str] = []

    def service(self, args, timeout_s):
        out = base(self, args, timeout_s)
        if args[0] == "compile":
            compiles.append(args[2])
            if args[2] == "Candidate/Broken.lean":
                out = {**out, "ok": False, "messages": "Candidate/Broken.lean:2:22: error: unknown identifier 'oops'"}
        elif out.get("status") == "accepted":
            m = json.loads((Path(args[1]) / "manifest.json").read_text())
            if m["kind"] == "auxiliary":
                out["statement"] = STATEMENTS.get(m["theorem"], PLAIN)
            if (m.get("scored") or {}).get("checker") == "Candidate.Short.D":
                sc = out["scoring"]
                out["certified_count"] = COUNTS[m["network"]] - 100
                out["scoring"] = {**sc, "bill": 5000, "length": 5000 + sc["extract"] + sc["read"]}
        return out
    service.compiles = compiles
    return service


def finished_run(tmp_path, monkeypatch, scripts, **open_lane):
    path = compiled_run(tmp_path, monkeypatch, scripts, rounds_max=2, discovery_rounds=1, code_review=True, scaling=False, **open_lane)
    service = two_proofs_service()
    monkeypatch.setattr(Session, "_service", service)
    lines: list[str] = []
    ctx = loop.start(path, log=lines.append)
    loop.drive(ctx)
    assert ctx.run.done_rounds() == [0, 1, 2, 3], lines[-6:]
    ctx.compiles = service.compiles
    return ctx, lines


def test_the_steps_run_in_order_with_their_own_time_and_carry_on(tmp_path, monkeypatch):
    """After a finished run: first the session for the general checker, then V, n and d, each a round after the
    run's last, each with its own session time and its own text; the proofs are the run's frontier (here two, the
    locked one and a shorter, weaker one whose module sits beside the locked ones); every proof's certificate and
    plan are in the Python workspace. A session's workspace is compiled before it begins, at no charge. A lemma
    is recorded with its statement, with the proofs whose checker Lean finds in it (the locked one asked in the
    session, the other after it) and with the proofs whose checker its statement names. The answer's THEOREMS
    lines are read as links, each with whether its theorem is an accepted submission's. The next session starts
    with the earlier sessions' accepted modules, the modules and the Python files they left, and their answers.
    A step can be run alone (--only), but only in order; running the command again goes on, and once all are
    done it does nothing. The report and the status say what was found; the run's frontier is unchanged."""
    ctx, lines = finished_run(tmp_path, monkeypatch, [DISCOVERY, ROUND, READING] + STEPS)
    run = ctx.run
    front = stages.scored_proofs(run.read_archive(), network_entry(ctx.folder, A) | {"id": A})
    with pytest.raises(loop.LoopError, match="in order; the next ones are general, V, n, d, not V"):
        scale(ctx, only=["V"])
    with pytest.raises(loop.LoopError, match="--minutes and --usd are for the sessions --again adds"):
        scale(ctx, minutes=5)
    del ctx.compiles[:]
    scale(ctx, only=["general"])
    sp = stages.read_state(run)["scaling_proofs"]
    assert [(s["parameter"], s["round"], s["minutes"], s["usd"]) for s in sp["steps"]] == [
        ("general", 4, 90, 30), ("V", 5, 45, 15), ("n", 6, 45, 15), ("d", 7, 45, 15)]
    assert [s["result"] is not None for s in sp["steps"]] == [True, False, False, False]
    assert sp["steps"][0]["template"] == TEXTS["general"]
    assert [(p["checker"], p["locked"], p["offered"]) for p in sp["proofs"]] == [
        ("Candidate.Short.D", False, True), ("Candidate.Col.D", True, True)]
    assert sp["sizes"] == SIZES and sp["network"] == A
    prompt = run.read(4, "prompt.md")
    assert "THIS SESSION: THE CHECKER WITH ITS SIZES AS PARAMETERS" in prompt
    assert ("The sessions, in order: the checker with its sizes as parameters, then the number of token values V, then the "
            "number of positions n, then the width d. This is session 1 of 4.") in " ".join(prompt.split())
    assert "V = 24 (d_vocab), n = 2 (n_ctx), d = 8 (d_model)" in prompt
    assert "5,400 s of wall clock" in prompt and "This is the first of these sessions." in prompt
    assert ("This session has 90 minutes: 80 of tool time, then 10 for writing the answer. `remaining.seconds` in a tool's "
            "answer is the tool time left (about 4,800 at the start)") in prompt
    assert "Every module in your workspace was compiled before this session began" in prompt
    assert "names the submitted checker (Candidate.Short.D, Candidate.Col.D)" in " ".join(prompt.split())
    assert "Candidate.Short.D" in prompt and "Candidate/Short.lean" in prompt
    assert "Gross" not in prompt and "Compact Proofs" not in prompt
    session = run.round_path(4) / "attempt_0" / "open_lane"
    # compiled before the session, in import order, and not charged: the session's own three compiles are its budget's
    assert ctx.compiles[:2] == ["Candidate/Col.lean", "Candidate/Short.lean"]
    assert [(b["path"], b["compiled"]) for b in sp["steps"][0]["compiled_beforehand"]] == [
        ("Candidate/Col.lean", True), ("Candidate/Short.lean", True)]
    assert json.loads((session / "session.json").read_text())["used"]["lean_check"] == 3
    assert any("round 4: scaling, the general checker (90 minutes, $30.00)" in l and "2 of 2 modules compiled beforehand" in l for l in lines)
    log = [json.loads(line) for line in (session / "tools.jsonl").read_text().splitlines()]
    assert [(e["tool"], e["outcome"].get("lines", 0) > 0) for e in log[:2]] == [("read_file", True), ("read_file", True)]
    proofs = json.loads((session / "py" / "handed_in_proofs.json").read_text())["proofs"]
    assert [(p["checker"], p["locked"], p["certified_count"]) for p in proofs] == [
        ("Candidate.Short.D", False, COUNTS[A] - 100), ("Candidate.Col.D", True, COUNTS[A])]
    assert (session / "workspace" / "Candidate" / "Short.lean").read_text() == SHORT
    assert (session / "py" / "locked_proof.json").is_file()
    (lemma,) = sp["steps"][0]["result"]["lemmas"]
    ids = {p["checker"]: p["record_id"] for p in sp["proofs"]}
    assert lemma["theorem"] == "Candidate.General.general_cost" and lemma["statement"] == STATEMENTS["Candidate.General.general_cost"]
    assert {rid: c["verified"] for rid, c in lemma["checkers"].items()} == {ids["Candidate.Col.D"]: True, ids["Candidate.Short.D"]: True}
    assert lemma["names"] == [ids["Candidate.Col.D"]]  # Candidate.General.Dg is not Candidate.Col.D, and Short.D is not named
    assert sp["steps"][0]["result"]["links"] == [
        {"size": "V", "link": "general", "theorem": "Candidate.General.general_cost", "as_submitted": False, "accepted": True},
        {"size": "V", "link": "cost", "theorem": "Candidate.General.general_cost", "as_submitted": False, "accepted": True},
        {"size": "n", "link": "general", "theorem": None, "as_submitted": True, "accepted": None},
        {"size": "n", "link": "cost", "theorem": "Candidate.General.general_cost", "as_submitted": False, "accepted": True},
        {"size": "d", "link": "general", "theorem": "Candidate.General.not_handed_in", "as_submitted": False, "accepted": False},
        {"size": "d", "link": "cost", "theorem": None, "as_submitted": False, "accepted": None}]

    del ctx.compiles[:]
    scale(ctx)  # V, n, then d
    sp = stages.read_state(run)["scaling_proofs"]
    assert all(s["result"] is not None for s in sp["steps"]) and run.done_rounds() == [0, 1, 2, 3, 4, 5, 6, 7]
    second = run.read(5, "prompt.md")
    flat = " ".join(second.split())
    assert "THIS SESSION: THE COST AS A THEOREM IN V" in second and "This is session 2 of 4." in second and "2,700 s of wall clock" in second
    assert "the number of token values V = 24 (d_vocab), while the number of positions n = 2 (n_ctx) and the width d = 8 (d_model) stay" in flat
    assert "proved to be the submitted checker at V = 24" in flat and "This session has 45 minutes: 35 of tool time" in second
    assert "WHAT THE EARLIER SESSIONS FOUND" in second and "The session on the checker with its sizes as parameters (round 4):" in second
    assert "THEOREMS:\n- `V general: Candidate.General.general_cost`\n- V cost:" in second and "SCALING: - Col: Dg V n d, cost V." in second
    assert ("- V: general: Candidate.General.general_cost; cost: Candidate.General.general_cost; formula: not said; brute: not said"
            in second)
    assert "- n: general: the submitted checker, as it is; cost: Candidate.General.general_cost;" in second
    assert "- d: general: Candidate.General.not_handed_in (named, not an accepted submission's theorem); cost: none;" in second
    assert "were asked for formulas" not in second and "was asked for formulas" not in second
    # what the general session left: its accepted module, its draft, its Python file; all compiled beforehand
    work = run.round_path(5) / "attempt_0" / "open_lane"
    assert (work / "workspace" / "Candidate" / "General.lean").read_text() == GENERAL
    assert (work / "workspace" / "Candidate" / "Draft.lean").read_text() == DRAFT
    assert "print('the model of the bill')" in (work / "py" / "billmodel.py").read_text()
    assert ("Left by the earlier sessions without being accepted (drafts: nothing in one is proved until the service accepts "
            "it, and one may not compile): Candidate/Broken.lean, Candidate/Draft.lean.") in second
    # a draft whose last compile failed is not tried again before the session; the others are compiled
    assert sp["steps"][1]["template"] == TEXTS["size"]
    assert [(b["path"], b["compiled"]) for b in sp["steps"][1]["compiled_beforehand"]] == [
        ("Candidate/Broken.lean", False), ("Candidate/Col.lean", True), ("Candidate/Short.lean", True),
        ("Candidate/General.lean", True), ("Candidate/Draft.lean", True)]
    assert ("4 of 5 compiled. Not compiled: Candidate/Broken.lean (not tried: a draft whose last compile, in the session that "
            "left it, did not succeed).") in second
    assert "Your Python workspace also holds the earlier sessions' files: py/billmodel.py." in second
    assert ctx.compiles[:4] == ["Candidate/Col.lean", "Candidate/Short.lean", "Candidate/General.lean", "Candidate/Draft.lean"]
    assert [e["outcome"].get("lines", 0) > 0 for e in map(json.loads, (work / "tools.jsonl").read_text().splitlines()[:2])] == [True, True]
    (lemma_v,) = sp["steps"][1]["result"]["lemmas"]
    assert lemma_v["names"] == [ids["Candidate.Col.D"]] and links.about(lemma_v, sp["proofs"]) == [ids["Candidate.Col.D"]]
    (lemma_n,) = sp["steps"][2]["result"]["lemmas"]
    assert {rid: c["verified"] for rid, c in lemma_n["checkers"].items()} == {ids["Candidate.Col.D"]: True, ids["Candidate.Short.D"]: False}
    assert lemma_n["names"] == [] and links.about(lemma_n, sp["proofs"]) == []  # two formulas of its own
    assert sp["steps"][2]["result"]["links"] == [
        {"size": "n", "link": "formula", "theorem": "Candidate.GrowthN.bill_in_n", "as_submitted": False, "accepted": True},
        {"size": "n", "link": "brute", "theorem": None, "as_submitted": False, "accepted": None}]
    refused = answers(run, 7)[0]
    assert "auxiliary" in json.dumps(refused) and sp["steps"][3]["result"]["lemmas"] == [] and sp["steps"][3]["result"]["links"] == []
    table = links.table(sp["steps"])
    assert {k: (c["theorem"], c["accepted"], c["round"]) for k, c in table["V"].items()} == {
        "general": ("Candidate.General.general_cost", True, 5), "cost": ("Candidate.General.general_cost", True, 5),
        "formula": ("Candidate.GrowthV.scaling_V", True, 5), "brute": (None, None, 5)}
    assert table["d"]["general"]["accepted"] is False and table["n"]["general"]["as_submitted"] is True

    lines.clear()
    scale(ctx)
    assert lines[-1] == "the scaling proofs are done; nothing to run (a further session: --again)"
    report = Path(build_report(run.path)).read_text()
    assert "## The scaling proofs" in report
    assert "### general: the checker with its sizes as parameters (round 4, 90 minutes, at most $30.00)" in report
    assert "### V: the number of token values (round 5, 45 minutes, at most $15.00)" in report
    assert "| V | `Candidate.General.general_cost` | `Candidate.General.general_cost` | `Candidate.GrowthV.scaling_V` | none |" in report
    assert "| n | the submitted checker, as it is | `Candidate.General.general_cost` | `Candidate.GrowthN.bill_in_n` | none |" in report
    assert "| d | `Candidate.General.not_handed_in` (named, not an accepted submission's theorem) | none | not said | not said |" in report
    assert STATEMENTS["Candidate.GrowthV.scaling_V"] in report and "- Col: bill independent of n." in report
    assert f"- `Candidate.GrowthN.bill_in_n`: its modules hold the checker of `{ids['Candidate.Col.D']}`; its statement names no submitted checker" in report
    assert f"its statement names the checker of `{ids['Candidate.Col.D']}`" in report
    status = loop.status_text(run)
    assert "scaling, the general checker (round 4): 1 lemma(s) accepted, 1 with a submitted proof's checker in its statement" in status
    assert "scaling in n (round 6): 1 lemma(s) accepted, 0 with a submitted proof's checker in its statement" in status
    assert "scaling in d (round 7): 0 lemma(s) accepted" in status
    assert "  theorems per size (general, cost, formula, brute), by the sessions' own account of what each says:" in status
    assert "    V: general, cost, formula; missing: brute" in status and "    d: none; missing: general, cost, formula, brute" in status
    assert "the reading of the checker (round 3, a language model's, an alarm and not a check): clean" in status
    assert sp["steps"][2]["result"]["answer"] == {"CLAIM": "no n in it.", "THEOREMS": "- **n formula:** `Candidate.GrowthN.bill_in_n`\n- n brute: none",
                                                  "SCALING": "- Col: bill independent of n.", "WHY IT HELPS": "-", "NOTES": "none."}
    assert stages.scored_proofs(run.read_archive(), network_entry(ctx.folder, A) | {"id": A}) == front


def test_a_further_session_is_added_to_steps_that_are_done(tmp_path, monkeypatch):
    """`--again`: once the steps are done, a further session for a named step (or for each configured one), as a
    round after the last, at the configured time and cap or at the command's. It starts from all the earlier
    sessions had accepted and left. Not while a step waits; the run's earlier results stay as they are. A run
    whose first sessions were asked for formulas (before the links were) is told so in the further session."""
    ctx, lines = finished_run(tmp_path, monkeypatch, [DISCOVERY, ROUND, READING] + STEPS + [AGAIN_V, AGAIN_V])
    run = ctx.run
    scale(ctx, only=["general", "V"])
    with pytest.raises(loop.LoopError, match=r"scaling in n \(round 6\) is not done yet: go on with it first"):
        scale(ctx, again=["V"])
    scale(ctx)
    before = stages.read_state(run)["scaling_proofs"]["steps"]
    # as a run of 24 November 2026 has them: its sessions' records name no prompt text (they were the first one's)
    state = stages.read_state(run)
    for s in state["scaling_proofs"]["steps"]:
        del s["template"]
    stages.write_state(run, state)
    lines.clear()
    scale(ctx, again=["V"], minutes=20, usd=7)
    sp = stages.read_state(run)["scaling_proofs"]
    assert [{k: v for k, v in s.items() if k != "template"} for s in sp["steps"][:4]] == [
        {k: v for k, v in s.items() if k != "template"} for s in before]
    more = sp["steps"][4]
    assert {k: more[k] for k in ("parameter", "minutes", "usd", "round", "again", "template")} == {
        "parameter": "V", "minutes": 20.0, "usd": 7.0, "round": 8, "again": True, "template": TEXTS["size"]}
    assert lines[0] == "added: scaling in V, a further session (round 8, 20 minutes, $7.00)"
    prompt = run.read(8, "prompt.md")
    assert "then the width d, then the number of token values V again. This is session 5 of 5." in " ".join(prompt.split())
    assert "1,200 s of wall clock" in prompt and "This session has 20 minutes: 10 of tool time" in prompt
    assert "The sessions of rounds 4, 5, 6, 7 were asked for formulas, with as much of them proved as could be" in prompt
    assert "The session on the number of positions n (round 6):" in prompt
    work = run.round_path(8) / "attempt_0" / "open_lane" / "workspace" / "Candidate"
    assert sorted(f.name for f in work.glob("*.lean")) == ["Broken.lean", "Col.lean", "Draft.lean", "General.lean", "GrowthN.lean",
                                                           "GrowthV.lean", "Short.lean"]
    assert more["result"]["links"] == [{"size": "V", "link": "brute", "theorem": None, "as_submitted": False, "accepted": None}]
    assert links.table(sp["steps"])["V"]["formula"]["theorem"] == "Candidate.GrowthV.scaling_V"  # the earlier session's stands
    assert "scaling in V, a further session (round 8): 0 lemma(s) accepted" in loop.status_text(run)
    assert "### V: the number of token values, a further session (round 8, 20 minutes, at most $7.00)" in Path(build_report(run.path)).read_text()
    # none named: one more of each configured step, at the configured time
    with pytest.raises(plan.ScalingError, match=r"--again takes some of general, V, n, d \(or `sizes` for every size\), not w"):
        scaling_steps.add_sessions(run, ctx.cfg, stages.read_state(run), ["w"])
    added = scaling_steps.add_sessions(run, ctx.cfg, stages.read_state(run), [])
    assert [(s["parameter"], s["round"], s["minutes"], s["again"]) for s in added] == [
        ("general", 9, 90, True), ("V", 10, 45, True), ("n", 11, 45, True), ("d", 12, 45, True)]


def test_the_links_are_read_from_the_answer_lines_of_that_form_alone():
    """A THEOREMS line is `<size> <link>: <theorem>` for one of the network's sizes, whatever they are called."""
    text = ("- V general: as submitted (it reads V from the shapes)\n* `V cost`: `Candidate.A.cost_thm`, for every V\n"
            "n formula: none\nd brute: Candidate.B.c.\nthe V formula: Candidate.X.y is not a line of the form\nV speed: Candidate.A.b\n"
            "w formula: Candidate.W.f\n")
    assert [(l["size"], l["link"], l["theorem"], l["as_submitted"]) for l in links.parse(text, ["V", "n", "d"])] == [
        ("V", "general", None, True), ("V", "cost", "Candidate.A.cost_thm", False), ("n", "formula", None, False),
        ("d", "brute", "Candidate.B.c", False)]
    other = "n_layers general: Candidate.L.g\nn cost: none\nplaces brute: as submitted\nn_layersx cost: Candidate.L.c\n"
    assert [(l["size"], l["link"], l["theorem"]) for l in links.parse(other, ["n", "n_layers", "places"])] == [
        ("n_layers", "general", "Candidate.L.g"), ("n", "cost", None), ("places", "brute", None)]
    assert links.parse(text, []) == []
    proofs = [{"record_id": "r/a", "checker": "Candidate.Tree.D"}, {"record_id": "r/b", "checker": "Candidate.TreeQ.D"}]
    assert links.names_in("run (Candidate.TreeQ.D p I) = some x", proofs) == ["r/b"]
    assert links.names_in("Candidate.Tree.D.match_1 x ∧ Candidate.Tree.Dx", proofs) == []
    assert links.names_in(None, proofs) == []


def test_the_command_refuses_what_it_cannot_do(tmp_path, monkeypatch):
    """Not before the run is finished; the steps' and the names' settings are checked."""
    path = compiled_run(tmp_path, monkeypatch, [DISCOVERY, ROUND, READING], rounds_max=2, discovery_rounds=1, code_review=True, scaling=False)
    monkeypatch.setattr(Session, "_service", two_proofs_service())
    ctx = loop.start(path, log=lambda line: None)
    with pytest.raises(loop.LoopError, match="proof rounds are not over"):
        scale(ctx)
    with pytest.raises(loop.LoopError, match="proof rounds are not over"):
        scale(ctx, end_proof_rounds=True)  # a run with stages ends its proof rounds itself
    loop.drive(ctx)
    monkeypatch.setitem(ctx.cfg["open_lane"], "scaling_steps", [{"parameter": "w", "minutes": 1, "usd": 1}])
    with pytest.raises(loop.LoopError, match="open_lane.scaling_steps names w, which is no size of this network: its sizes are "
                                             r"V = 24 \(d_vocab\), n = 2 \(n_ctx\), d = 8 \(d_model\)"):
        scale(ctx)
    assert stages.read_state(ctx.run).get("scaling_proofs") is None
    one = {"minutes": 1, "usd": 1}
    assert scaling_steps_errors([{"parameter": "n", **one}, {"parameter": "V", **one}, {"parameter": "sizes", **one}]) == []
    assert scaling_steps_errors([{"parameter": "V", **one}, {"parameter": "V", **one}]) == ["open_lane.scaling_steps: each parameter at most once"]
    assert scaling_steps_errors([{"parameter": "V", "minutes": 0, "usd": 1}]) == ["open_lane.scaling_steps: V's minutes must be a positive number"]
    assert scaling_steps_errors([{"parameter": "2 w", **one}])[0].startswith(
        "open_lane.scaling_steps: parameter must be `general`, `sizes` or the symbol of a size")
    assert scaling_steps_errors([]) == ["open_lane.scaling_steps must be a list of {parameter, minutes, usd}, at least one"]
    a, b = {"name": "a", "symbol": "A", "words": "the a"}, {"name": "b", "symbol": "B", "words": "the b"}
    assert scaling_names_errors({"names": [a, b], "together": [["a", "b"]]}) == [] and scaling_names_errors({"names": []}) == []
    assert scaling_names_errors({"names": [{**a, "symbol": "sizes"}]}) == [
        "open_lane.scaling_names: names and symbols must differ, and no symbol may be `general` or `sizes`"]
    assert scaling_names_errors({"names": [a, {**b, "symbol": "A"}]})[0].startswith("open_lane.scaling_names: names and symbols must differ")
    assert scaling_names_errors({"names": [a], "together": [["a", "c"]]}) == [
        "open_lane.scaling_names: a name under `together` is listed under `names`, and stands in one group"]
    assert scaling_names_errors({"names": [{"name": "a", "symbol": "A"}]})[0].endswith("must be a name with a symbol (letters, digits, _) and words")
    assert scaling_names_errors({"names": {"a": {"symbol": "A", "words": "x"}}})[0].startswith("open_lane.scaling_names must be {names: [")


STEP_P = {"calls": [call("read_file", path="py/handed_in_proofs.json")],
          "response": ("CLAIM: nothing yet.\nTHEOREMS:\nP general: as submitted\nP cost: none\nd_vocab formula: Candidate.X.y\n"
                       "V formula: Candidate.X.y\nSCALING:\n- none.\nWHY IT HELPS: -\nNOTES: -")}


def test_the_sessions_follow_the_network_s_sizes_whatever_they_are_called(tmp_path, monkeypatch):
    """Nothing in the package or its texts knows a size by name. The sizes are the entries of the network's size
    setting; open_lane.scaling_names gives some a symbol and words, and the others go by their own names. The
    steps may leave the general session out, name a size for settings of its own, and take `sizes` for the rest.
    The prompt, the links, the status and the report then speak of these sizes."""
    ctx, lines = finished_run(tmp_path, monkeypatch, [DISCOVERY, ROUND, READING, STEP_P],
                              scaling_names={"names": [{"name": "n_ctx", "symbol": "P", "words": "the number of places"}], "together": []},
                              scaling_steps=[{"parameter": "P", "minutes": 20, "usd": 5}, {"parameter": "sizes", "minutes": 15, "usd": 2}])
    run = ctx.run
    scale(ctx, only=["P"])
    sp = stages.read_state(run)["scaling_proofs"]
    assert [(s["symbol"], s["words"], s["names"], s["value"]) for s in sp["sizes"]] == [
        ("P", "the number of places", ["n_ctx"], 2), ("d_vocab", "the size", ["d_vocab"], 24), ("d_model", "the size", ["d_model"], 8)]
    assert [(s["parameter"], s["round"], s["minutes"], s["usd"]) for s in sp["steps"]] == [
        ("P", 4, 20, 5), ("d_vocab", 5, 15, 2), ("d_model", 6, 15, 2)]
    prompt = run.read(4, "prompt.md")
    flat = " ".join(prompt.split())
    assert "THIS SESSION: THE COST AS A THEOREM IN P" in prompt
    assert ("The sessions, in order: the number of places P, then the size d_vocab, then the size d_model. This is session 1 of 3."
            in flat)
    assert "On this network: P = 2 (n_ctx), d_vocab = 24, d_model = 8. This session varies P and holds the others at these values" in flat
    assert "This session takes one size: the number of places P = 2 (n_ctx), while the size d_vocab = 24 and the size d_model = 8 stay" in flat
    assert "`P formula: Candidate.Module.theorem`" in prompt and "proved to be the submitted checker at P = 2" in flat
    assert not re.search(r"\bV\b|\{[A-Z_]+\}", prompt.split("THIS SESSION:")[1])  # no symbol of another network, nothing left unfilled
    assert sp["steps"][0]["result"]["links"] == [
        {"size": "P", "link": "general", "theorem": None, "as_submitted": True, "accepted": None},
        {"size": "P", "link": "cost", "theorem": None, "as_submitted": False, "accepted": None},
        {"size": "d_vocab", "link": "formula", "theorem": "Candidate.X.y", "as_submitted": False, "accepted": False}]
    status = loop.status_text(run)
    assert "scaling in P (round 4): 0 lemma(s) accepted" in status and "scaling in d_vocab (round 5): not done yet" in status
    assert "    P: general; missing: cost, formula, brute" in status and "    d_model: none; missing: general, cost, formula, brute" in status
    report = Path(build_report(run.path)).read_text()
    assert "on this network P = 2 (n_ctx), d_vocab = 24, d_model = 8." in report
    assert "### P: the number of places (round 4, 20 minutes, at most $5.00)" in report and "### d_vocab: the size (round 5, 15 minutes" in report
    assert "| P | the submitted checker, as it is | none | not said | not said |" in report
    # a further session for every size; one size named
    assert plan.wanted(["sizes"], ctx.cfg, sp["sizes"]) == ["P", "d_vocab", "d_model"]
    assert plan.wanted(["d_model", "P"], ctx.cfg, sp["sizes"]) == ["P", "d_model"]
    with pytest.raises(plan.ScalingError, match=r"--again takes some of general, P, d_vocab, d_model \(or `sizes` for every size\), not V"):
        plan.wanted(["V"], ctx.cfg, sp["sizes"])
    assert plan.settings(ctx.cfg, sp["sizes"]) == {"general": {"minutes": 90, "usd": 30}, "P": {"minutes": 20, "usd": 5},
                                                   "d_vocab": {"minutes": 15, "usd": 2}, "d_model": {"minutes": 15, "usd": 2}}


def test_a_run_that_plans_no_stage_is_told_that_its_proof_rounds_are_over(tmp_path, monkeypatch):
    """A run with stages after its proof rounds says itself when they are over, and locks a proof. A run that
    plans none says nothing: the scaling proofs then need --end-proof-rounds, which ends them for good (a later
    resume makes no more, even with rounds left) and locks the best scored proof, as the stages would have."""
    path = compiled_run(tmp_path, monkeypatch, [DISCOVERY, ROUND, STEP_G, ROUND], rounds_max=2, discovery_rounds=1, scaling=False)
    monkeypatch.setattr(Session, "_service", two_proofs_service())
    ctx = loop.start(path, log=lambda line: None)
    loop.drive(ctx)
    run = ctx.run
    assert run.done_rounds() == [0, 1, 2] and stages.read_state(run) is None
    with pytest.raises(loop.LoopError, match="nothing in this run says its proof rounds are over .* --end-proof-rounds says so"):
        scale(ctx)
    assert stages.read_state(run) is None
    scale(ctx, only=["general"], end_proof_rounds=True)
    state = stages.read_state(run)
    assert state["proof_rounds_ended"] == {"after_round": 2, "why": scaling_steps.ENDED_BY_COMMAND} and state["stages"] == {}
    assert state["locked"]["checker"] == "Candidate.Col.D" and state["scaling_proofs"]["steps"][0]["round"] == 3
    assert state["scaling_proofs"]["steps"][0]["result"]["lemmas"][0]["theorem"] == "Candidate.General.general_cost"
    monkeypatch.setitem(ctx.cfg, "rounds_max", 5)  # rounds left, and a response is there: no proof round is made
    loop.drive(ctx)
    assert run.done_rounds() == [0, 1, 2, 3]
    assert "scaling, the general checker (round 3): 1 lemma(s) accepted" in loop.status_text(run)
    assert "## The scaling proofs" in Path(build_report(run.path)).read_text()


def _folder_files(folder) -> dict:
    return {p.relative_to(folder.path).as_posix(): p.read_bytes() for p in folder.identity_files() if folder.path in p.parents}


def _other_open_lane_block(config: bytes) -> bytes:
    """config.yaml with other notes for open-lane sessions: a difference inside its open_lane block."""
    cfg = yaml.safe_load(config)
    cfg["open_lane"] = {**cfg["open_lane"], "notes": "as an earlier pipeline had them"}
    return yaml.safe_dump(cfg).encode()


def test_a_later_pipeline_scales_a_run_whose_networks_it_did_not_change(tmp_path, monkeypatch):
    """The sessions come after a finished run, with the pipeline as it is by then (a pull may have changed the
    checker code and a model folder's open_lane block). A resume still refuses a run whose trusted hashes
    changed; the command opens it when the model folder differs from the run's only in its open_lane block, read
    back from the pipeline commit the run recorded, and its sessions say which pipeline they ran with."""
    ctx, lines = finished_run(tmp_path, monkeypatch, [DISCOVERY, ROUND, READING] + STEPS)
    run, folder = ctx.run, ctx.folder
    then = {**_folder_files(folder), "config.yaml": _other_open_lane_block((folder.path / "config.yaml").read_bytes())}
    recorded = json.loads((run.path / "versions.json").read_text())
    recorded.update({"checker": "0" * 64, "model_folder": later_pipeline.files_hash(then), "git": {"commit": "a" * 40, "dirty": False}})
    (run.path / "versions.json").write_text(json.dumps(recorded))
    monkeypatch.setattr(later_pipeline, "model_folder_at", lambda commit, f: then if commit == "a" * 40 else None)
    with pytest.raises(loop.LoopError, match="checker, model_folder changed since run run started; results would not be comparable"):
        loop.resume(run.path, log=lambda line: None)
    log: list[str] = []
    after = loop.resume(run.path, log=log.append, changed_since=command.changed_since)
    assert [l for l in log if l.startswith("note:")] == [
        f"note: the pipeline's checker code, model folder changed since run run started (pipeline aaaaaaa, now "
        f"{after.versions['git']['commit'][:7]}); the steps after a finished run add lemmas and no scores, so they go on; "
        "the model folder differs from the run's only in its open_lane block"]
    scale(after, only=["general"])
    step = stages.read_state(run)["scaling_proofs"]["steps"][0]
    assert step["result"] is not None and step["pipeline"] == {"commit": after.versions["git"]["commit"],
                                                               "changed_since_run": ["checker", "model_folder"]}
    records = [r for r in run.read_archive() if r["round"] == 4]
    assert records and all(r["versions"]["after_run"] == {"run_git": {"commit": "a" * 40, "dirty": False},
                                                           "changed": ["checker", "model_folder"]} for r in records)
    assert f"Ran with pipeline {after.versions['git']['commit'][:7]}; changed since the run started: checker, model_folder" in \
        Path(build_report(run.path)).read_text()
    # a model folder that changed outside its open_lane block: the run is not opened
    monkeypatch.setattr(later_pipeline, "model_folder_at", lambda commit, f: {**then, "model.py": then["model.py"] + b"\n# was\n"})
    recorded["model_folder"] = later_pipeline.files_hash({**then, "model.py": then["model.py"] + b"\n# was\n"})
    (run.path / "versions.json").write_text(json.dumps(recorded))
    with pytest.raises(loop.LoopError, match="the model folder's model.py changed since the run started. What follows a finished run "
                                             "needs the run's networks, task and architecture"):
        loop.resume(run.path, log=lambda line: None, changed_since=command.changed_since)


@pytest.mark.parametrize("change, why", [
    (lambda f: {**f, "model.py": f["model.py"] + b"\n# changed\n"}, "the model folder's model.py changed since the run started"),
    (lambda f: {**f, "config.yaml": f["config.yaml"].replace(b"d_vocab", b"d_vocab_was")},
     "the model folder's config.yaml changed outside its open_lane block"),
    (lambda f: {k: v for k, v in f.items() if k != "task.py"}, "files of the model folder were added or removed since the run started: task.py"),
])
def test_a_later_pipeline_does_not_scale_a_run_whose_networks_or_task_changed(change, why):
    """Anything of the model folder outside its open_lane block (the networks' manifest, the task, the
    architecture, the sizes) must be as the run started; and the folder must be readable back from the run's
    pipeline commit, as the run recorded it."""
    folder = load_model_folder(REPO_ROOT / "tests" / "max2_ladder")
    then = change(_folder_files(folder))
    started = {"git": {"commit": "a" * 40}, "model_folder": later_pipeline.files_hash(then)}
    read = lambda commit, f: then
    assert later_pipeline.refusal(started, folder, ["model_folder"], read=read).startswith(why)
    assert later_pipeline.refusal(started, folder, ["checker"], read=read) is None  # the model folder did not change
    assert later_pipeline.refusal({**started, "model_folder": "b" * 64}, folder, ["model_folder"], read=read).startswith(
        "the model folder at pipeline commit aaaaaaaaaaaa is not the one the run recorded")
    assert later_pipeline.refusal(started, folder, ["model_folder"], read=lambda commit, f: None).startswith(
        "git cannot show the model folder as it was at pipeline commit aaaaaaaaaaaa")


def test_the_model_folder_read_back_from_git_hashes_as_the_folder_does():
    """model_folder_at reads a model folder's identity files at a commit; at HEAD, for a folder git has no
    changes in, they hash to the folder's own hash."""
    import subprocess

    folder = load_model_folder(REPO_ROOT / "models" / "max4")
    if subprocess.run(["git", "status", "--porcelain", "--", "models/max4"], cwd=REPO_ROOT, capture_output=True, text=True).stdout.strip():
        pytest.skip("models/max4 has uncommitted changes")
    then = later_pipeline.model_folder_at("HEAD", folder)
    if then is None:
        pytest.skip("git cannot show HEAD here")
    assert later_pipeline.files_hash(then) == folder.folder_hash() and set(then) == set(_folder_files(folder))


# the sizes and the plan ----------------------------------------------------------------------------------
@pytest.mark.parametrize("model, network, expected", [
    ("max4", "max4-v64-s0", {"V": 64, "n": 4, "d": 8}),
    ("min4", "min4-v64-s0", {"V": 64, "n": 4, "d": 8}),
    ("max2", "max2-v64-s0", {"V": 64, "n": 2, "d": 8}),
    ("attn-max4", "attn-max4-v64-s0", {"V": 64, "n": 4, "d": 32}),
    ("attn-min2", "attn-min2-v64d8-s0", {"V": 64, "n": 2, "d": 8}),
])
def test_every_model_folder_has_its_sizes_without_declaring_anything(model, network, expected):
    """The sizes are read from the network's size setting, named by config/defaults.yaml's table: an attention
    model's width and head width are one size where they are equal. No model folder says anything for it."""
    folder = load_model_folder(REPO_ROOT / "models" / model)
    sizes = network_sizes.of_network({}, folder, network_entry(folder, network) | {"id": network})
    assert {s["symbol"]: s["value"] for s in sizes} == expected and [s["symbol"] for s in sizes] == ["V", "n", "d"]
    assert sizes[2]["names"] == (["d_model", "d_head"] if model.startswith("attn") else ["d_model"])
    assert not any(key.startswith("scaling") for key in folder.config.get("open_lane") or {})


class _Folder:
    """A model folder as the sizes see it: its size settings."""

    def __init__(self, **sizes):
        self._sizes = sizes

    def sizes(self, setting: str) -> dict:
        return dict(self._sizes)


def test_sizes_are_named_by_the_table_and_otherwise_by_themselves():
    entry = {"id": "net", "setting": "s"}
    sizes = network_sizes.of_network({}, _Folder(n_layers=2, d_model=16, n_ctx=3, d_head=4, dropout=0.1, d_vocab=10, tied=True), entry)
    assert [(s["symbol"], s["names"], s["value"]) for s in sizes] == [
        ("V", ["d_vocab"], 10), ("n", ["n_ctx"], 3), ("d", ["d_model"], 16), ("h", ["d_head"], 4), ("n_layers", ["n_layers"], 2)]
    assert [network_sizes.text(s) for s in sizes] == ["V = 10 (d_vocab)", "n = 3 (n_ctx)", "d = 16 (d_model)", "h = 4 (d_head)", "n_layers = 2"]
    assert network_sizes.phrase(sizes[0]) == "the number of token values V" and network_sizes.phrase(sizes[4]) == "the size n_layers"
    together = network_sizes.of_network({}, _Folder(d_vocab=10, d_model=16, d_head=16), entry)
    assert [(s["symbol"], s["names"]) for s in together] == [("V", ["d_vocab"]), ("d", ["d_model", "d_head"])]
    assert network_sizes.text(together[1]) == "d = 16 (d_model and d_head, varied together)"
    assert network_sizes.listed(["V"]) == "V" and network_sizes.listed(["V", "n", "d"]) == "V, n and d"
    own = {"open_lane": {"scaling_names": {"names": [{"name": "d_vocab", "symbol": "d_model", "words": "the tokens"}]}}}
    with pytest.raises(network_sizes.SizesError, match=r"the sizes of net cannot be told apart or named as steps \(d_model\)"):
        network_sizes.of_network(own, _Folder(d_vocab=10, d_model=16), entry)
    with pytest.raises(network_sizes.SizesError, match="has no whole-number entry"):
        network_sizes.of_network({}, _Folder(dropout=0.1), entry)
    # the first scaling proofs (24 November 2026) kept the sizes by symbol: read as the list
    old = {"sizes": {"V": {"names": ["d_vocab"], "value": 64}, "n": {"names": ["n_ctx"], "value": 4},
                     "d": {"names": ["d_model", "d_head"], "value": 32}}}
    assert network_sizes.stored(old, {}) == [
        {"symbol": "V", "words": "the number of token values", "names": ["d_vocab"], "value": 64},
        {"symbol": "n", "words": "the number of positions", "names": ["n_ctx"], "value": 4},
        {"symbol": "d", "words": "the width", "names": ["d_model", "d_head"], "value": 32}]
    assert network_sizes.stored({"sizes": SIZES}, {}) == SIZES


def test_the_steps_are_expanded_against_the_network_s_sizes():
    one = {"minutes": 45, "usd": 15}
    steps = [{"parameter": "general", "minutes": 90, "usd": 30}, {"parameter": "n", "minutes": 60, "usd": 20}, {"parameter": "sizes", **one}]
    assert [(s["parameter"], s["minutes"]) for s in plan.expand(steps, SIZES)] == [("general", 90), ("n", 60), ("V", 45), ("d", 45)]
    assert [s["parameter"] for s in plan.planned({}, SIZES)] == ["general", "V", "n", "d"]  # config/defaults.yaml's
    assert [s["parameter"] for s in plan.planned({}, SIZES[:1])] == ["general", "V"]
    with pytest.raises(plan.ScalingError, match="names h, which is no size of this network"):
        plan.expand([{"parameter": "h", **one}], SIZES)
    assert plan.name({"parameter": "general"}) == "scaling, the general checker" and plan.kind({"parameter": "d"}) == "size"
    assert plan.words({"parameter": "d", "again": True}, SIZES) == "the width d again"
    assert plan.step_config({"open_lane": {"worker_seconds": 1}, "api_budget": {"round_usd": 1}}, {"minutes": 2, "usd": 3}) == {
        "open_lane": {"worker_seconds": 120}, "api_budget": {"round_usd": 3.0}}


def test_the_texts_are_a_frame_and_a_part_for_each_kind_of_session():
    """Every part fills the frame's seven places, and neither names a size: the symbols come from the run."""
    frame = (scaling_prompt.TEMPLATES / f"{scaling_prompt.FRAME}.md").read_text()
    assert {name for name in scaling_prompt.PART_SECTIONS} <= set(re.findall(r"\{([A-Z_]+)\}", frame))
    for kind, name in scaling_prompt.PARTS.items():
        part = scaling_prompt.read_part(name)
        assert set(part) == set(scaling_prompt.PART_SECTIONS), kind
        text = frame + "\n".join(part.values())
        assert not re.search(r"\b(V|n|d)\b(?! *=)", re.sub(r"\{[A-Z_]+\}", "", text)), kind
        for word in ("d_vocab", "n_ctx", "d_model", "token", "position", "width"):
            assert word not in text, (kind, word)
    assert scaling_prompt.asked_for_links({"template": TEXTS["size"]}) and not scaling_prompt.asked_for_links({})
    assert not scaling_prompt.asked_for_links({"template": scaling_prompt.FIRST})
    assert (scaling_prompt.TEMPLATES / f"{scaling_prompt.FIRST}.md").is_file()  # what the first sessions were asked, kept


# the package stands by itself ----------------------------------------------------------------------------
def test_nothing_outside_the_package_is_made_for_the_scaling_proofs():
    """The scaling proofs can follow any open-lane run on one network because nothing else is made for them:
    the loop driver and the report know them only through core/open_lane/after_run.py; no model folder declares
    anything for them; and no file a run's identity rests on (core.versions) knows of them, so bringing a
    change to them never makes a finished run look changed."""
    core = REPO_ROOT / "core"
    package = core / "open_lane" / "scaling"
    imports = re.compile(r"^\s*(from\s+\S*\bscaling\b\S*\s+import|import\s+\S*\bscaling\b|from\s+\S+\s+import\s+.*\bscaling\b)", re.M)
    outside = [p.relative_to(REPO_ROOT).as_posix() for p in sorted(core.rglob("*.py"))
               if package not in p.parents and imports.search(p.read_text())]
    assert outside == ["core/open_lane/after_run.py"]
    assert list(after_run.commands()) == ["scale"]
    for name, mod in after_run.commands().items():
        for attr in ("NAME", "HELP", "Error", "add_arguments", "changed_since", "run", "status_lines", "report_lines"):
            assert hasattr(mod, attr), (name, attr)
    for path in versions._files(versions.CHECKER_FILES + versions.SANDBOX_FILES):
        assert not re.search(r"scaling_(steps|names|sizes)|open_lane[./]scaling/", Path(path).read_text()), path
    for config in sorted((REPO_ROOT / "models").glob("*/config.yaml")) + [REPO_ROOT / "tests" / "max2_ladder" / "config.yaml"]:
        assert "scaling_" not in config.read_text(), config
    for text in ("loop.py", "open_lane/session.py", "open_lane/stages.py", "model_folder.py"):
        assert not re.search(r"scaling_(steps|names|sizes)|compiled_beforehand", (core / text).read_text()), text
