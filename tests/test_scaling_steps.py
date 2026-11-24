"""The scaling proofs after a run (core/open_lane/scaling_steps.py; python3 -m core.loop scale --run <run>): a
session for the checker with its sizes as parameters, then one per size (V, n, d), each with its own time and
cap, about the run's scored proofs on its frontier; further sessions with --again; the links an answer names.
On the stand-ins of tests/test_open_lane_compiled.py (a run whose checker the service runs compiled)."""

from __future__ import annotations

import json
from pathlib import Path

import pytest
import yaml

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


def finished_run(tmp_path, monkeypatch, scripts):
    path = compiled_run(tmp_path, monkeypatch, scripts, rounds_max=2, discovery_rounds=1, code_review=True, scaling=False)
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
        loop.scale(ctx, only=["V"])
    with pytest.raises(loop.LoopError, match="--minutes and --usd are for the sessions --again adds"):
        loop.scale(ctx, minutes=5)
    del ctx.compiles[:]
    loop.scale(ctx, only=["general"])
    sp = stages.read_state(run)["scaling_proofs"]
    assert [(s["parameter"], s["round"], s["minutes"], s["usd"]) for s in sp["steps"]] == [
        ("general", 4, 90, 30), ("V", 5, 45, 15), ("n", 6, 45, 15), ("d", 7, 45, 15)]
    assert [s["result"] is not None for s in sp["steps"]] == [True, False, False, False]
    assert sp["steps"][0]["template"] == "open_lane_scaling_general_v1"
    assert [(p["checker"], p["locked"], p["offered"]) for p in sp["proofs"]] == [
        ("Candidate.Short.D", False, True), ("Candidate.Col.D", True, True)]
    assert sp["sizes"] == {"V": {"names": ["d_vocab"], "value": 24}, "n": {"names": ["n_ctx"], "value": 2},
                           "d": {"names": ["d_model"], "value": 8}}
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
    state = json.loads((session / "session.json").read_text())
    assert [(b["path"], b["compiled"]) for b in state["prebuilt"]] == [("Candidate/Col.lean", True), ("Candidate/Short.lean", True)]
    assert state["used"]["lean_check"] == 3
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
    loop.scale(ctx)  # V, n, then d
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
    built = json.loads((work / "session.json").read_text())["prebuilt"]
    assert [(b["path"], b["compiled"]) for b in built] == [
        ("Candidate/Broken.lean", False), ("Candidate/Col.lean", True), ("Candidate/Short.lean", True),
        ("Candidate/General.lean", True), ("Candidate/Draft.lean", True)]
    assert ("4 of 5 compiled. Not compiled: Candidate/Broken.lean (not tried: a draft whose last compile, in the session that "
            "left it, did not succeed).") in second
    assert "Your Python workspace also holds the earlier sessions' files: py/billmodel.py." in second
    assert ctx.compiles[:4] == ["Candidate/Col.lean", "Candidate/Short.lean", "Candidate/General.lean", "Candidate/Draft.lean"]
    assert [e["outcome"].get("lines", 0) > 0 for e in map(json.loads, (work / "tools.jsonl").read_text().splitlines()[:2])] == [True, True]
    (lemma_v,) = sp["steps"][1]["result"]["lemmas"]
    assert lemma_v["names"] == [ids["Candidate.Col.D"]] and scaling_steps.about(lemma_v, sp["proofs"]) == [ids["Candidate.Col.D"]]
    (lemma_n,) = sp["steps"][2]["result"]["lemmas"]
    assert {rid: c["verified"] for rid, c in lemma_n["checkers"].items()} == {ids["Candidate.Col.D"]: True, ids["Candidate.Short.D"]: False}
    assert lemma_n["names"] == [] and scaling_steps.about(lemma_n, sp["proofs"]) == []  # two formulas of its own
    assert sp["steps"][2]["result"]["links"] == [
        {"size": "n", "link": "formula", "theorem": "Candidate.GrowthN.bill_in_n", "as_submitted": False, "accepted": True},
        {"size": "n", "link": "brute", "theorem": None, "as_submitted": False, "accepted": None}]
    refused = answers(run, 7)[0]
    assert "auxiliary" in json.dumps(refused) and sp["steps"][3]["result"]["lemmas"] == [] and sp["steps"][3]["result"]["links"] == []
    table = scaling_steps.links_table(sp)
    assert {k: (c["theorem"], c["accepted"], c["round"]) for k, c in table["V"].items()} == {
        "general": ("Candidate.General.general_cost", True, 5), "cost": ("Candidate.General.general_cost", True, 5),
        "formula": ("Candidate.GrowthV.scaling_V", True, 5), "brute": (None, None, 5)}
    assert table["d"]["general"]["accepted"] is False and table["n"]["general"]["as_submitted"] is True

    lines.clear()
    loop.scale(ctx)
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
    loop.scale(ctx, only=["general", "V"])
    with pytest.raises(loop.LoopError, match=r"scaling in n \(round 6\) is not done yet: go on with it first"):
        loop.scale(ctx, again=["V"])
    loop.scale(ctx)
    before = stages.read_state(run)["scaling_proofs"]["steps"]
    # as a run of 24 November 2026 has them: its sessions' records name no prompt text (they were the first one's)
    state = stages.read_state(run)
    for s in state["scaling_proofs"]["steps"]:
        del s["template"]
    stages.write_state(run, state)
    lines.clear()
    loop.scale(ctx, again=["V"], minutes=20, usd=7)
    sp = stages.read_state(run)["scaling_proofs"]
    assert [{k: v for k, v in s.items() if k != "template"} for s in sp["steps"][:4]] == [
        {k: v for k, v in s.items() if k != "template"} for s in before]
    more = sp["steps"][4]
    assert {k: more[k] for k in ("parameter", "minutes", "usd", "round", "again", "template")} == {
        "parameter": "V", "minutes": 20.0, "usd": 7.0, "round": 8, "again": True, "template": "open_lane_scaling_step_v2"}
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
    assert scaling_steps.links_table(sp)["V"]["formula"]["theorem"] == "Candidate.GrowthV.scaling_V"  # the earlier session's stands
    assert "scaling in V, a further session (round 8): 0 lemma(s) accepted" in loop.status_text(run)
    assert "### V: the number of token values, a further session (round 8, 20 minutes, at most $7.00)" in Path(build_report(run.path)).read_text()
    # none named: one more of each configured step, at the configured time
    with pytest.raises(scaling_steps.ScalingError, match="--again takes some of general, V, n, d, not w"):
        scaling_steps.add_sessions(run, ctx.cfg, stages.read_state(run), ["w"])
    added = scaling_steps.add_sessions(run, ctx.cfg, stages.read_state(run), [])
    assert [(s["parameter"], s["round"], s["minutes"], s["again"]) for s in added] == [
        ("general", 9, 90, True), ("V", 10, 45, True), ("n", 11, 45, True), ("d", 12, 45, True)]


def test_the_links_are_read_from_the_answer_lines_of_that_form_alone():
    text = ("- V general: as submitted (it reads V from the shapes)\n* `V cost`: `Candidate.A.cost_thm`, for every V\n"
            "n formula: none\nd brute: Candidate.B.c.\nthe V formula: Candidate.X.y is not a line of the form\nV speed: Candidate.A.b\n")
    assert [(l["size"], l["link"], l["theorem"], l["as_submitted"]) for l in scaling_steps.parse_links(text)] == [
        ("V", "general", None, True), ("V", "cost", "Candidate.A.cost_thm", False), ("n", "formula", None, False),
        ("d", "brute", "Candidate.B.c", False)]
    proofs = [{"record_id": "r/a", "checker": "Candidate.Tree.D"}, {"record_id": "r/b", "checker": "Candidate.TreeQ.D"}]
    assert scaling_steps.names_in("run (Candidate.TreeQ.D p I) = some x", proofs) == ["r/b"]
    assert scaling_steps.names_in("Candidate.Tree.D.match_1 x ∧ Candidate.Tree.Dx", proofs) == []
    assert scaling_steps.names_in(None, proofs) == []


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
        "open_lane.scaling_steps: each of general, V, n, d at most once, in that order"]
    assert scaling_steps_errors([{"parameter": "V", "minutes": 1, "usd": 1}, {"parameter": "general", "minutes": 1, "usd": 1}]) == [
        "open_lane.scaling_steps: each of general, V, n, d at most once, in that order"]
    assert scaling_steps_errors([{"parameter": "general", "minutes": 1, "usd": 1}, {"parameter": "d", "minutes": 1, "usd": 1}]) == []
    assert scaling_steps_errors([{"parameter": "V", "minutes": 0, "usd": 1}]) == ["open_lane.scaling_steps: V's minutes must be a positive number"]
    assert scaling_steps_errors([{"parameter": "w", "minutes": 1, "usd": 1}])[0].startswith("open_lane.scaling_steps: parameter must be one of general, V, n, d")


def _folder_files(folder) -> dict:
    return {p.relative_to(folder.path).as_posix(): p.read_bytes() for p in folder.identity_files() if folder.path in p.parents}


def _without_scaling_sizes(config: bytes) -> bytes:
    """config.yaml as it was before the model folder named its sizes for the scaling proofs."""
    cfg = yaml.safe_load(config)
    cfg["open_lane"] = {k: v for k, v in cfg["open_lane"].items() if k != "scaling_sizes"}
    return yaml.safe_dump(cfg).encode()


def test_a_later_pipeline_scales_a_run_whose_networks_it_did_not_change(tmp_path, monkeypatch):
    """The steps come after a finished run, with the pipeline as it is by then (the pull that brings them changes
    the checker code and the model folders' open_lane blocks). A resume still refuses a run whose trusted
    hashes changed; the steps open it when the model folder differs from the run's only in its open_lane block,
    read back from the pipeline commit the run recorded, and say which pipeline they ran with."""
    ctx, lines = finished_run(tmp_path, monkeypatch, [DISCOVERY, ROUND, READING] + STEPS)
    run, folder = ctx.run, ctx.folder
    then = {**_folder_files(folder), "config.yaml": _without_scaling_sizes((folder.path / "config.yaml").read_bytes())}
    versions = json.loads((run.path / "versions.json").read_text())
    versions.update({"checker": "0" * 64, "model_folder": loop.files_hash(then), "git": {"commit": "a" * 40, "dirty": False}})
    (run.path / "versions.json").write_text(json.dumps(versions))
    monkeypatch.setattr(loop, "model_folder_at", lambda commit, f: then if commit == "a" * 40 else None)
    with pytest.raises(loop.LoopError, match="checker, model_folder changed since run run started; results would not be comparable"):
        loop.resume(run.path, log=lambda line: None)
    log: list[str] = []
    after = loop.resume(run.path, log=log.append, after_run=True)
    assert [l for l in log if l.startswith("note:")] == [
        f"note: the pipeline's checker code, model folder changed since run run started (pipeline aaaaaaa, now "
        f"{after.versions['git']['commit'][:7]}); the steps after a finished run add lemmas and no scores, so they go on; "
        "the model folder differs from the run's only in its open_lane block"]
    loop.scale(after, only=["general"])
    step = stages.read_state(run)["scaling_proofs"]["steps"][0]
    assert step["result"] is not None and step["pipeline"] == {"commit": after.versions["git"]["commit"],
                                                               "changed_since_run": ["checker", "model_folder"]}
    records = [r for r in run.read_archive() if r["round"] == 4]
    assert records and all(r["versions"]["after_run"] == {"run_git": {"commit": "a" * 40, "dirty": False},
                                                           "changed": ["checker", "model_folder"]} for r in records)
    assert f"Ran with pipeline {after.versions['git']['commit'][:7]}; changed since the run started: checker, model_folder" in \
        Path(build_report(run.path)).read_text()


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
    started = {"git": {"commit": "a" * 40}, "model_folder": loop.files_hash(then)}
    read = lambda commit, f: then
    assert loop.after_run_refusal(started, folder, ["model_folder"], read=read).startswith(why)
    assert loop.after_run_refusal(started, folder, ["checker"], read=read) is None  # the model folder did not change
    assert loop.after_run_refusal({**started, "model_folder": "b" * 64}, folder, ["model_folder"], read=read).startswith(
        "the model folder at pipeline commit aaaaaaaaaaaa is not the one the run recorded")
    assert loop.after_run_refusal(started, folder, ["model_folder"], read=lambda commit, f: None).startswith(
        "git cannot show the model folder as it was at pipeline commit aaaaaaaaaaaa")


def test_the_model_folder_read_back_from_git_hashes_as_the_folder_does():
    """model_folder_at reads a model folder's identity files at a commit; at HEAD, for a folder git has no
    changes in, they hash to the folder's own hash."""
    import subprocess

    folder = load_model_folder(REPO_ROOT / "models" / "max4")
    if subprocess.run(["git", "status", "--porcelain", "--", "models/max4"], cwd=REPO_ROOT, capture_output=True, text=True).stdout.strip():
        pytest.skip("models/max4 has uncommitted changes")
    then = loop.model_folder_at("HEAD", folder)
    if then is None:
        pytest.skip("git cannot show HEAD here")
    assert loop.files_hash(then) == folder.folder_hash() and set(then) == set(_folder_files(folder))


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
