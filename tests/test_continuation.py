"""A run that goes on with an earlier run's work (open_lane.continue_from, core/open_lane/continuation.py), on
stand-ins for the Lean project and its service with the fake backend, as tests/test_python_then_lean.py."""

from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path

import pytest
import yaml

from core import loop
from core.archive import RunDir
from core.open_lane import continuation, research, workflow
from core.open_lane.session import Session, carried_modules
from core.run_config import RunConfigError, load_run_config
from tests.test_python_then_lean import CANDIDATE, ptl_run, read_only
from tests.test_stages import A, GENERAL, INSTANCE, SCORED, call, fake_service, stand_in_inspect


@pytest.fixture(autouse=True)
def _stand_ins(request, monkeypatch):
    """The stand-in surface and Lean's stand-in answers, as in tests/test_python_then_lean.py."""
    request.getfixturevalue("stand_in_surface")
    from core.open_lane import inspect

    monkeypatch.setattr(inspect, "inspect_submission", stand_in_inspect)


DRAFT = "import Candidate.Col\n\nnamespace Candidate.Draft\n\ntheorem t : True := trivial\n\nend Candidate.Draft\n"
BAD = "import Candidate.Col\n\nnamespace Candidate.Bad\n\ntheorem performance : True := trivial\n\nend Candidate.Bad\n"
EQ1 = "the candidate redeclares CompactCheck.Tensor.get.eq_1, a constant of the trusted modules"
NOTE = "Round 2's rejection of the earlier run was a fault of the acceptance service, fixed since."

PARENT = [
    {"calls": [  # discovery: a candidate, notes, the shortlist and a Python file
        call("research_write", path="Research/candidates/c001.json", text=json.dumps(CANDIDATE)),
        call("research_write", path="Research/notes.md", text="columns decide"),
        call("research_write", path="Research/shortlist.json", text=json.dumps([{"id": "c001", "reason": "the only one"}])),
        call("run_python", code="x = 1\nprint(x)", network=A, save_as="py/helper.py"),
    ], "response": "CLAIM: c001.\nWHY IT HELPS: columns.\nNOTES: formalise c001."},
    {"calls": [  # formalization: a lemma accepted, a draft, a submission the service of then rejected
        call("lean_check", path="Candidate/Col.lean", source=GENERAL, network=A, claimed_count=576),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.Col.D_sound", modules=["Candidate/Col.lean"],
             kind="auxiliary"),
        call("lean_check", path="Candidate/Draft.lean", source=DRAFT, network=A, claimed_count=576),
        call("lean_check", path="Candidate/Bad.lean", source=BAD, network=A, claimed_count=576),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.Bad.performance", modules=["Candidate/Bad.lean"]),
    ], "response": "CLAIM: a lemma.\nWHY IT HELPS: -\nNOTES: go on with Draft and submit Bad again."},
]
CHILD = [
    {"calls": [  # round 1: the earlier run's submission compiled again as it was, and a scored proof on its lemma
        call("lean_check", path="Candidate/Bad.lean", edits=[], network=A, claimed_count=576),
        call("lean_check", path="Candidate/ColRun.lean", source=INSTANCE, network=A, claimed_count=576),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.ColRun.performance",
             modules=["Candidate/ColRun.lean"], scored=SCORED),
    ], "response": "CLAIM: 576 of 576.\nWHY IT HELPS: columns.\nNOTES: child notes one."},
    {"calls": [], "response": "CLAIM: nothing more.\nWHY IT HELPS: -\nNOTES: none."},
]


def then_service(extract: int):
    """The service as the earlier run had it: a submission of Candidate.Bad is rejected (as round 3 of
    attn-min2-ptl-1 was, for a fault fixed since); everything else as fake_service."""
    base = fake_service(extract)

    def service(self, args, timeout_s):
        if args[0] == "submit":
            m = json.loads((Path(args[1]) / "manifest.json").read_text())
            if "Bad" in m["theorem"]:
                return {"status": "rejected", "reason": EQ1, "claim_kind": m["kind"], "network": m["network"],
                        "claimed_count": m["claimed_count"], "theorem": m["theorem"], "certified_count": None}
        return base(self, args, timeout_s)
    return service


def tree_hash(root: Path) -> dict[str, str]:
    return {p.relative_to(root).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
            for p in sorted(root.rglob("*")) if p.is_file()}


def parent_run(tmp_path: Path, monkeypatch) -> RunDir:
    path = ptl_run(tmp_path, monkeypatch, PARENT, rounds_max=2, discovery_rounds=1, service=then_service(448),
                   seed_check=None, scaling=False)
    ctx = loop.start(path, log=lambda *a: None)
    loop.drive(ctx)
    assert ctx.run.done_rounds() == [0, 1, 2]
    return ctx.run


def child_config(tmp_path: Path, name: str, scripts: list[dict], parent: str, rounds_max: int, **open_lane) -> Path:
    """A continuation of `parent` on the parent's config (tmp_path/run.yaml), with its own scripts."""
    cfg = yaml.safe_load((tmp_path / "run.yaml").read_text())
    paths = []
    for i, script in enumerate(scripts):
        p = tmp_path / f"{name}_script_{i}.json"
        p.write_text(json.dumps(script))
        paths.append(str(p))
    cfg["run_id"] = name
    cfg["rounds_max"] = rounds_max
    cfg["open_lane"].update(fake_scripts=paths, discovery_rounds=0, continue_from=parent, seed_check=None, scaling=False,
                            **open_lane)
    out = tmp_path / f"{name}.yaml"
    out.write_text(yaml.safe_dump(cfg))
    return out


def session_state(run: RunDir, k: int) -> dict:
    return json.loads((run.round_path(k) / "attempt_0" / "open_lane" / "session.json").read_text())


def test_a_continuation_goes_on_from_the_earlier_runs_work_and_counts_none_of_it(tmp_path, monkeypatch):
    parent = parent_run(tmp_path, monkeypatch)
    before = tree_hash(parent.path)
    assert [r["status"] for r in parent.read_archive() if r["round"] == 2] == ["lemma", "rejected"]
    monkeypatch.setattr(Session, "_service", fake_service(448))  # the service as it is now: Bad is accepted
    lines: list[str] = []
    ctx = loop.start(child_config(tmp_path, "ptl-2", CHILD, "ptl", 2, continue_note=NOTE), log=lines.append)
    loop.drive(ctx)
    run = ctx.run
    assert run.done_rounds() == [0, 1, 2]
    assert any("continues run ptl: rounds 1, 2 copied" in l for l in lines), lines

    # the copy: once, read-only, every file hashed; the earlier run's folder only read
    rec = continuation.record(run.path)
    assert rec["run_id"] == "ptl" and rec["rounds"] == [1, 2] and rec["last_round"] == 2 and rec["path"] == str(parent.path)
    base = run.path / continuation.DIR
    assert read_only(base) and read_only(base / "round_002" / "attempt_0" / "open_lane" / "session.json")
    for rel, sha in rec["files"].items():
        assert hashlib.sha256((base / rel).read_bytes()).hexdigest() == sha
    assert "round_002/attempt_0/open_lane/workspace/Candidate/Draft.lean" in rec["files"]
    assert "round_001/attempt_0/open_lane/workspace/Candidate/Draft.lean" not in rec["files"]  # only the last session's work
    assert not any("/out/" in rel or rel.endswith(".olean") for rel in rec["files"])
    assert tree_hash(parent.path) == before

    # the research folder goes on in the run's own, each file saying where it came from
    index = research.read_index(run.path)
    assert index["Research/candidates/c001.json"]["via"] == "inherited" and index["Research/candidates/c001.json"]["from_run"] == "ptl"
    assert set(rec["research"]) == {"Research/candidates/c001.json", "Research/notes.md", "Research/shortlist.json"}
    tr = workflow.transition(run.path)
    assert tr["round"] == 1 and tr["ranked"] and [x["id"] for x in tr["shortlist"]] == ["c001"]

    # round 1 starts where round 3 of the earlier run would have
    p1 = run.read(1, "prompt.md")
    stats = run.read(1, "meta.json")["prompt"]
    assert stats["template"] == "open_lane_formalization_v1" and stats["phase"] == "formalization"
    assert "Round 1: formalization round 1 of 2, the last proof round being 2." in p1
    assert "1. c001: the only one" in p1
    assert ("YOUR SUBMISSIONS SO FAR\nnone yet\n\nBefore this run, in the earlier run ptl, whose work this run goes on with "
            "(the acceptance service that answered them is this run's; they count there, not here):\n") in p1
    assert "- round 2 submission 0: max2_ladder-n2v24d8-s0, claimed 576: lemma (auxiliary lemma accepted)" in p1
    assert f"- round 2 submission 1: max2_ladder-n2v24d8-s0, claimed 576: rejected: {EQ1}" in p1
    assert NOTE in p1
    assert "LATEST NOTES\nThese are the notes of round 2 of the earlier run ptl.\ngo on with Draft and submit Bad again." in p1
    assert "- Candidate/Col.lean (" in p1 and "round 2 of the earlier run ptl, submission 0, accepted lemma Candidate.Col.D_sound): compiled" in p1
    assert "- Candidate/Bad.lean (7 lines; last saved in round 2 of the earlier run ptl; it compiled then)" in p1
    assert "- Candidate/Draft.lean (7 lines; last saved in round 2 of the earlier run ptl; it compiled then)" in p1
    assert "- py/helper.py (" in p1 and "bytes, last saved in round 1 of the earlier run ptl)" in p1
    assert "- Research/candidates/c001.json (" in p1 and "round 1 of the earlier run ptl)" in p1
    s1 = session_state(run, 1)
    assert [(m["path"], m["from_run"], m["round"], m["compiled"]) for m in s1["carried"]] == [("Candidate/Col.lean", "ptl", 2, True)]
    assert {d["path"]: d["from_run"] for d in s1["drafts"]} == {"Candidate/Bad.lean": "ptl", "Candidate/Draft.lean": "ptl"}
    assert s1["py_files"]["helper.py"]["from_run"] == "ptl"
    ws = run.round_path(1) / "attempt_0" / "open_lane" / "workspace"
    assert (ws / "Candidate" / "Draft.lean").read_text() == DRAFT and (ws / "Candidate" / "Col.lean").read_text() == GENERAL

    # nothing of the earlier run is this run's: its records, its frontier and its score are its own
    records = run.read_archive()
    assert records and all(r["record_id"].startswith("ptl-2/") for r in records)
    ok = [r for r in records if r["status"] == "ok" and r.get("lane") == "open"]
    assert len(ok) == 1 and ok[0]["round"] == 1 and ok[0]["certified"] == 576
    assert not [r for r in records if r["status"] in ("lemma", "rejected")]

    # round 2: this run's own notes and receipts, and the drafts left untouched still named as the earlier run's
    p2 = run.read(2, "prompt.md")
    assert "LATEST NOTES\nchild notes one." in p2
    assert "YOUR SUBMISSIONS SO FAR\n- round 1 submission 0: max2_ladder-n2v24d8-s0, claimed 576: ok, certified 576" in p2
    assert "Before this run, in the earlier run ptl" in p2
    s2 = session_state(run, 2)
    drafts = {d["path"]: d for d in s2["drafts"]}
    assert drafts["Candidate/Draft.lean"]["from_run"] == "ptl" and drafts["Candidate/Draft.lean"]["saved_round"] == 2
    assert "from_run" not in drafts["Candidate/Bad.lean"] and drafts["Candidate/Bad.lean"]["saved_round"] == 1
    assert "- Candidate/Bad.lean (7 lines; last saved in round 1; it compiled then)" in p2
    # the submission of round 1 took Col.lean along (ColRun imports it): its accepted version is now this run's
    assert {(m["path"], m.get("from_run"), m["round"]) for m in s2["carried"]} == {("Candidate/Col.lean", None, 1),
                                                                                  ("Candidate/ColRun.lean", None, 1)}

    # the status names the earlier run; a resume redoes nothing and copies nothing again
    status = loop.status_text(run)
    assert f"continues run ptl ({parent.path}): its rounds 1, 2 copied" in status and "discovery: no rounds in this run" in status
    n, copied = len(records), rec["copied"]
    ctx2 = loop.resume(run.path, log=lambda *a: None)
    loop.drive(ctx2)
    assert len(run.read_archive()) == n and continuation.record(run.path)["copied"] == copied
    assert tree_hash(parent.path) == before


def test_a_continuation_of_a_continuation_carries_both_earlier_runs(tmp_path, monkeypatch):
    parent_run(tmp_path, monkeypatch)
    monkeypatch.setattr(Session, "_service", fake_service(448))
    loop.drive(loop.start(child_config(tmp_path, "ptl-2", CHILD, "ptl", 2), log=lambda *a: None))
    end = {"calls": [], "response": "CLAIM: none.\nWHY IT HELPS: -\nNOTES: none."}
    ctx = loop.start(child_config(tmp_path, "ptl-3", [end], "ptl-2", 1), log=lambda *a: None)
    loop.drive(ctx)
    run = ctx.run
    assert [continuation.run_id_of(b) for b in continuation.roots(run.path)] == ["ptl", "ptl-2"]
    carried = {(m["path"], m.get("from_run"), m["round"]) for m in carried_modules(run.path, 1)}
    assert carried == {("Candidate/Col.lean", "ptl-2", 1), ("Candidate/ColRun.lean", "ptl-2", 1)}  # the latest accepted versions
    assert {(m["path"], m["from_run"]) for m in carried_modules(run.path / continuation.DIR, 1)} == {("Candidate/Col.lean", "ptl")}
    p1 = run.read(1, "prompt.md")
    assert p1.index("Before this run, in the earlier run ptl-2") < p1.index("Before that, in the earlier run ptl,")
    assert "These are the notes of round 2 of the earlier run ptl-2.\nnone." in p1
    # the drafts and Python files go on from the latest session, ptl-2's round 2, naming where each was saved
    drafts = {d["path"]: d for d in session_state(run, 1)["drafts"]}
    assert drafts["Candidate/Draft.lean"]["from_run"] == "ptl" and drafts["Candidate/Bad.lean"]["from_run"] == "ptl-2"


def test_what_a_continuation_refuses(tmp_path, monkeypatch):
    parent_run(tmp_path, monkeypatch)

    def cfg(**changes) -> dict:
        c = load_run_config(child_config(tmp_path, "ptl-2", CHILD, "ptl", 2))
        for key, value in changes.items():
            c[key] = value
        return c

    assert continuation.check_parent(cfg()) == []
    assert "of the model tests/max2_ladder, this run of tests/max2_tiny" in continuation.check_parent(cfg(model="tests/max2_tiny"))[0]
    assert "a continuation keeps the earlier run's networks" in continuation.check_parent(cfg(networks=["max2_ladder-n2v24d8-s3"]))[0]
    assert "no run at" in continuation.check_parent({**cfg(), "open_lane": {**cfg()["open_lane"], "continue_from": "nowhere"}})[0]
    me = cfg()
    assert continuation.check_parent(me, Path(me["runs_dir"]) / "ptl") == ["a run cannot continue itself"]
    # the start refuses before any folder is made
    bad = child_config(tmp_path, "ptl-x", CHILD, "nowhere", 2)
    with pytest.raises(loop.LoopError, match="no run at"):
        loop.start(bad, log=lambda *a: None)
    assert not (Path(me["runs_dir"]) / "ptl-x").exists()
    # discovery_rounds 0 only in a continuation; a note only with an earlier run to go with
    raw = yaml.safe_load((tmp_path / "run.yaml").read_text())
    raw["open_lane"]["discovery_rounds"] = 0
    (tmp_path / "zero.yaml").write_text(yaml.safe_dump(raw))
    with pytest.raises(RunConfigError, match="at least 1 and less than rounds_max"):
        load_run_config(tmp_path / "zero.yaml")
    raw["open_lane"].update(discovery_rounds=1, continue_note="x")
    (tmp_path / "note.yaml").write_text(yaml.safe_dump(raw))
    with pytest.raises(RunConfigError, match="continue_note .* needs open_lane.continue_from"):
        load_run_config(tmp_path / "note.yaml")


def test_an_interrupted_copy_is_made_again(tmp_path, monkeypatch):
    parent = parent_run(tmp_path, monkeypatch)
    monkeypatch.setattr(Session, "_service", fake_service(448))
    real = continuation.inherit
    monkeypatch.setattr(continuation, "inherit", lambda *a, **k: (_ for _ in ()).throw(KeyboardInterrupt()))
    with pytest.raises(KeyboardInterrupt):
        loop.start(child_config(tmp_path, "ptl-2", CHILD, "ptl", 2), log=lambda *a: None)
    run = RunDir(parent.path.parent, "ptl-2")
    (run.path / continuation.DIR / "round_001").mkdir(parents=True)  # a copy cut short, without its record
    assert continuation.record(run.path) is None
    monkeypatch.setattr(continuation, "inherit", real)
    loop.drive(loop.resume(run.path, log=lambda *a: None))
    rec = continuation.record(run.path)
    assert rec["rounds"] == [1, 2] and run.done_rounds() == [0, 1, 2]
    assert "Before this run, in the earlier run ptl" in run.read(1, "prompt.md")


def test_a_session_stopped_by_its_spending_cap_left_no_notes(tmp_path):
    """Round 3 of attn-min2-ptl-1 reached its spending cap: its response is what it had said so far, not its
    answer, so the next round's notes are round 2's, with a word that round 3 left none."""
    from core.open_lane.prompt import latest_notes

    run = RunDir(tmp_path, "r")
    for k, text, meta in ((2, "CLAIM: x.\nWHY IT HELPS: -\nNOTES: prune the stages.", {"stop_reason": "end_turn"}),
                          (3, "I'll start by reading the plan.Run lemmas compile.", {"stop_reason": "budget"})):
        a = run.round_path(k) / "attempt_0"
        a.mkdir(parents=True)
        (a / "response.md").write_text(text)
        (a / "response_meta.json").write_text(json.dumps(meta))
    assert latest_notes(run, 4, 6000) == ("Round 3 ended without notes: the session ended before your answer. Its unfinished "
                                          "modules are in your workspace. These are the notes of round 2.\nprune the stages.")
    # a session of a backend without the NOTES format, which ended as it should, still gives its whole answer
    (run.round_path(3) / "attempt_0" / "response_meta.json").write_text(json.dumps({"stop_reason": "end_turn"}))
    assert latest_notes(run, 4, 6000) == "I'll start by reading the plan.Run lemmas compile."
