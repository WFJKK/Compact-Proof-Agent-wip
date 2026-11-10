"""After the proof rounds of an open-lane run: the lock, the seed check and the scaling question.

No Lean and no model: the Lean project is a folder of stand-in files, the acceptance service is a function
that accepts what it is handed and writes the receipt the real one would, the sessions are scripts of tool
calls (the fake backend), and Lean's account of what a submission's compiled modules declare
(core.open_lane.inspect) is a stand-in that reads the toy sources below. What is tested is the pipeline's
side: which proof is locked and why, that the locked modules reach the service unchanged whatever a session
does, that a result counts only when the checker is the locked one, and what the run records. Lean's own
account, on modules compiled by Lean, is tested in tests/test_lock_lean.py.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest
import yaml

from core import loop
from core.open_lane import stages
from core.open_lane import inspect
from core.open_lane.lock import LockError, lockable, protected_name, read_lock, renamed, same_checker
from core.open_lane.session import Session
from core.run_config import RunConfigError, load_run_config, read_run_config_file
from core.util import REPO_ROOT


@pytest.fixture(autouse=True)
def _surface(request):
    """These tests run on stand-in Lean projects, so on the stand-in surface (tests/conftest.py) unless a test
    is marked real_surface. The surfaces a run uses are tested in tests/test_surface.py."""
    if request.node.get_closest_marker("real_surface") is None:
        request.getfixturevalue("stand_in_surface")

A, B = "max2_ladder-n2v24d8-s0", "max2_ladder-n2v24d8-s3"  # two development seeds of one size
PA = "N_max2_ladder_n2v24d8_s0_c576"

GENERAL = f"""import Protected.{PA}
import CompactCheck.CountedOps

namespace Candidate.Col

open CompactCheck Protected.{PA}

def D : Checker := fun I => pure I.nzero

theorem D_sound : True := trivial

end Candidate.Col
"""
INSTANCE = f"""import Candidate.Col

namespace Candidate.ColRun

open CompactCheck Protected.{PA}

theorem D_instance : True := trivial
theorem performance : True := trivial

end Candidate.ColRun
"""
ONE_MODULE = f"""import Protected.{PA}

namespace Candidate.One

def D : Nat := 0
theorem D_sound : True := trivial
theorem D_instance : True := trivial
theorem performance : True := trivial

end Candidate.One
"""

MAKE_PROTECTED = '''import hashlib, json, re


def canonical_cert(cert):
    return list(cert)


def module_name(network_id, claimed, cert=None):
    name = "N_" + re.sub(r"[^A-Za-z0-9]", "_", network_id) + f"_c{claimed}"
    if cert:
        name += "_h" + hashlib.sha256(json.dumps(cert).encode()).hexdigest()[:16]
    return name
'''


def submission(path: Path, modules: dict, scored: dict | None, network: str = A, claimed: int = 576) -> Path:
    for rel, text in modules.items():
        (path / rel).parent.mkdir(parents=True, exist_ok=True)
        (path / rel).write_text(text)
    manifest = {"schema": "open-lane-candidate-v1", "kind": "performance", "model": "tests/max2_ladder", "network": network,
                "claimed_count": claimed, "theorem": "Candidate.ColRun.performance", "modules": list(modules)}
    if scored is not None:
        manifest["scored"] = scored
    (path / "manifest.json").write_text(json.dumps(manifest))
    return path


SCORED = {"checker": "Candidate.Col.D", "sound": "Candidate.Col.D_sound", "instance": "Candidate.ColRun.D_instance",
          "certificate": [], "claimed_bill": 20000}
PROJECT = Path("/nowhere")  # the stand-in below needs no Lean project


def stand_in_inspect(lean_project, submission, where=(), closure=()):
    """In place of core.open_lane.inspect.inspect_submission: what Lean would say about the toy modules of
    this file, read from their source. Good for these sources only (one namespace per module, a `def` or
    `theorem` per line, one import per line): Lean's real account is tested in tests/test_lock_lean.py.
    The canonical text of a constant is the source of its module and of what that imports, with the
    protected module's name left out, so a changed module is a changed checker here as it is in Lean."""
    import re

    submission = Path(submission)
    manifest = json.loads((submission / "manifest.json").read_text())
    texts = {rel[:-5].replace("/", "."): (submission / rel).read_text() for rel in manifest["modules"]}
    imports = {m: re.findall(r"^import\s+([\w.]+)", t, re.M) for m, t in texts.items()}
    protected = next((i for m in texts for i in imports[m] if i.startswith("Protected.")), None)
    declared = {}
    for m, t in texts.items():
        space = (re.search(r"^namespace\s+([\w.]+)", t, re.M) or [None, ""])[1]
        for kind, name in re.findall(r"^(def|theorem)\s+(\w+)", t, re.M):
            declared.setdefault(f"{space}.{name}" if space else name, []).append((m, kind))
    plain = lambda t: re.sub(r"N_[A-Za-z0-9_]+", "N_", t)

    def reach(m, seen=None):
        seen = seen if seen is not None else []
        if m in texts and m not in seen:
            seen.append(m)
            for i in imports[m]:
                reach(i, seen)
        return seen

    closures = {}
    for c in closure:
        entries = []
        for m, kind in declared.get(c, [])[:1]:
            entries.append({"name": c, "declared": c, "modules": [x for x, _ in declared[c]], "kind": kind,
                            "text": "\n".join(plain(texts[x]) for x in sorted(reach(m)))})
            if protected:
                entries.append({"name": "Protected._.graph", "declared": f"{protected}.graph", "modules": [protected],
                                "kind": "def", "text": "the graph"})
        closures[c] = {"found": c in declared, "constants": entries}
    info = {"modules": {m: {"imports": imports[m], "constants": 1, "is_module": False} for m in texts},
            "duplicates": [{"name": c, "modules": sorted(x for x, _ in ms)} for c, ms in sorted(declared.items()) if len(ms) > 1],
            "reserved": [], "where": {c: sorted(x for x, _ in declared.get(c, [])) for c in where},
            "closures": closures, "protected": protected}
    inspect.unambiguous(info)
    return info


@pytest.fixture(autouse=True)
def lean_stand_in(monkeypatch):
    monkeypatch.setattr(inspect, "inspect_submission", stand_in_inspect)


def test_a_proof_is_locked_by_module_the_checker_apart_from_the_instance(tmp_path):
    """The locked modules are the ones that declare the checker and its soundness theorem, with what they
    import; the instance must be declared outside them. Where a constant is declared and what a module
    imports is Lean's account, not a guess from names: a file named like the checker that does not declare
    it is not locked, and the file that does is. A proof in one module, or one whose checker Lean finds in
    no module or in two, cannot be locked, and the reason says so. The lock carries the checker's
    fingerprints."""
    lock = read_lock(submission(tmp_path / "two", {"Candidate/ColRun.lean": INSTANCE, "Candidate/Col.lean": GENERAL}, SCORED), PROJECT)
    assert list(lock["modules"]) == ["Candidate/Col.lean"] and lock["free"] == ["Candidate/ColRun.lean"]
    assert (lock["checker"], lock["sound"], lock["protected"]) == ("Candidate.Col.D", "Candidate.Col.D_sound", PA)
    assert lock["home"] == {"checker": "Candidate/Col.lean", "sound": "Candidate/Col.lean"}
    assert lock["modules"]["Candidate/Col.lean"] == GENERAL and len(lock["digest"]) == 64
    assert set(lock["fingerprints"]) == {"checker", "context", "sound_statement"} and all(len(v) == 64 for v in lock["fingerprints"].values())
    assert set(lock["constants"]["checker"]) == {"Candidate.Col.D"} and set(lock["constants"]["context"]) == {"Protected._.graph"}
    # what the checker's module imports is locked with it
    deep = {"Candidate/Lemmas.lean": "theorem l : True := trivial\n", "Candidate/Col.lean": "import Candidate.Lemmas\n" + GENERAL,
            "Candidate/ColRun.lean": INSTANCE}
    assert sorted(read_lock(submission(tmp_path / "deep", deep, SCORED), PROJECT)["modules"]) == ["Candidate/Col.lean", "Candidate/Lemmas.lean"]
    # the checker declared in another file than the one named like it (a review's case, 10 November 2026)
    elsewhere = {"Candidate/Col.lean": f"import Protected.{PA}\n", "Candidate/Real.lean": "import Candidate.Lemmas\n" + GENERAL,
                 "Candidate/Lemmas.lean": "theorem l : True := trivial\n",
                 "Candidate/ColRun.lean": INSTANCE.replace("import Candidate.Col", "import Candidate.Real")}
    moved = read_lock(submission(tmp_path / "elsewhere", elsewhere, SCORED), PROJECT)
    assert sorted(moved["modules"]) == ["Candidate/Lemmas.lean", "Candidate/Real.lean"]
    assert sorted(moved["free"]) == ["Candidate/Col.lean", "Candidate/ColRun.lean"] and moved["home"]["checker"] == "Candidate/Real.lean"
    one = {"checker": "Candidate.One.D", "sound": "Candidate.One.D_sound", "instance": "Candidate.One.D_instance",
           "certificate": [], "claimed_bill": 1}
    assert "the instance belongs in a module of its own" in lockable(submission(tmp_path / "one", {"Candidate/One.lean": ONE_MODULE}, one), PROJECT)
    nowhere = {**SCORED, "checker": "Candidate.Other.D"}
    assert "Candidate.Other.D must be declared in exactly one submitted module; Lean finds it in none" in lockable(submission(
        tmp_path / "named", {"Candidate/Col.lean": GENERAL, "Candidate/ColRun.lean": INSTANCE}, nowhere), PROJECT)
    twice = {**elsewhere, "Candidate/Col.lean": GENERAL}
    assert "Candidate.Col.D is declared by more than one module (Candidate.Col, Candidate.Real)" in lockable(
        submission(tmp_path / "twice", twice, SCORED), PROJECT)
    with pytest.raises(LockError, match="not a scored proof"):
        read_lock(submission(tmp_path / "plain", {"Candidate/Col.lean": GENERAL}, None), PROJECT)


def test_a_result_counts_only_when_lean_finds_the_locked_checker_in_it(tmp_path):
    """After a seed-check submission is accepted, Lean is asked again, about the modules the service compiled
    for it: the checker and the soundness theorem must be declared where they were locked, and the checker's
    fingerprints (its kernel terms, the graph and task it reaches, the soundness statement) must be the
    lock's. The locked text being unchanged is not the evidence: here the text is the lock's in one case and
    the checker is still another."""
    lock = read_lock(submission(tmp_path / "a", {"Candidate/ColRun.lean": INSTANCE, "Candidate/Col.lean": GENERAL}, SCORED), PROJECT)
    new = "N_max2_ladder_n2v24d8_s3_c570"
    general_b, instance_b = renamed(GENERAL, PA, new), INSTANCE.replace(PA, new)
    same = same_checker(lock, submission(tmp_path / "b", {"Candidate/ColRun.lean": instance_b, "Candidate/Col.lean": general_b}, SCORED, B, 570), PROJECT)
    assert same["verified"] is True and same["why"] is None and same["fingerprints"] == lock["fingerprints"]
    changed = general_b.replace("pure I.nzero", "pure (I.nofNat 570)")
    other = same_checker(lock, submission(tmp_path / "c", {"Candidate/ColRun.lean": instance_b, "Candidate/Col.lean": changed}, SCORED, B, 570), PROJECT)
    assert other["verified"] is False
    assert "the checker's kernel terms differ from the locked checker's (changed: Candidate.Col.D)" in other["why"]
    again = {"Candidate/ColRun.lean": instance_b, "Candidate/Col.lean": general_b,
             "Candidate/Again.lean": "namespace Candidate.Col\ndef D : Nat := 1\nend Candidate.Col\n"}
    twice = same_checker(lock, submission(tmp_path / "d", again, SCORED, B, 570), PROJECT)
    assert twice["verified"] is False and "Candidate.Col.D is declared by more than one module (Candidate.Again, Candidate.Col)" in twice["why"]
    gone = same_checker(lock, submission(tmp_path / "e", {"Candidate/ColRun.lean": instance_b}, SCORED, B, 570), PROJECT)
    assert gone["verified"] is False and "the compiled modules declare no Candidate.Col.D" in gone["why"]
    # the locked modules can be in a submission whose manifest names another checker: that proof is not about the lock
    named = same_checker(lock, submission(tmp_path / "f", {"Candidate/ColRun.lean": instance_b, "Candidate/Col.lean": general_b},
                                          {**SCORED, "checker": "Candidate.ColRun.E"}, B, 570), PROJECT)
    assert named["verified"] is False and "names Candidate.ColRun.E as its checker, not the locked Candidate.Col.D" in named["why"]


def test_leans_answer_becomes_fingerprints_or_is_refused_where_it_does_not_single_out_a_constant():
    """What the pipeline makes of Lean's answer (core.open_lane.inspect), on an answer written out here. The
    three fingerprints are digests over the constants' canonical texts by name: the candidate's constants
    the checker depends on, those the soundness statement is written in, and the protected module's that
    either reaches. An answer is refused when a name does not say which constant is meant (declared twice,
    or under the marker of the protected module) or the compiled module does not show what a constant is
    (an axiom, a file of Lean's module system)."""
    import copy

    def entry(name, module, kind="def", text="terms"):
        return {"name": name, "declared": name.replace("Protected._", "Protected.N"), "modules": [module], "kind": kind, "text": text}

    info = {"modules": {"Candidate.Col": {"imports": [], "constants": 2, "is_module": False}}, "duplicates": [], "reserved": [],
            "where": {}, "protected": "Protected.N", "closures": {
                "Candidate.Col.D": {"found": True, "constants": [entry("Candidate.Col.D", "Candidate.Col"), entry("Protected._.graph", "Protected.N")]},
                "Candidate.Col.D_sound": {"found": True, "constants": [
                    entry("Candidate.Col.D_sound", "Candidate.Col", "theorem"), entry("Candidate.Col.D", "Candidate.Col"),
                    entry("Protected._.task", "Protected.N")]}}}
    inspect.unambiguous(info)
    prints, parts = inspect.fingerprints(info, "Candidate.Col.D", "Candidate.Col.D_sound")
    assert {k: sorted(v) for k, v in parts.items()} == {"checker": ["Candidate.Col.D"], "sound_statement": ["Candidate.Col.D", "Candidate.Col.D_sound"],
                                                       "context": ["Protected._.graph", "Protected._.task"]}
    assert set(prints) == {"checker", "sound_statement", "context"} and len(set(prints.values())) == 3

    def changed(edit):
        other = copy.deepcopy(info)
        edit(other)
        return other

    def text_of(root, i, text):
        return lambda o: o["closures"][root]["constants"][i].__setitem__("text", text)

    # another body for the checker is another checker; another graph is another context and the same checker
    body = inspect.fingerprints(changed(text_of("Candidate.Col.D", 0, "other terms")), "Candidate.Col.D", "Candidate.Col.D_sound")[0]
    assert body["checker"] != prints["checker"] and body["context"] == prints["context"]
    graph = inspect.fingerprints(changed(text_of("Candidate.Col.D", 1, "another graph")), "Candidate.Col.D", "Candidate.Col.D_sound")[0]
    assert graph["checker"] == prints["checker"] and graph["context"] != prints["context"]
    refused = [
        (lambda o: o["duplicates"].append({"name": "Candidate.Col.D", "modules": ["Candidate.Col", "Candidate.Again"]}), "declared by more than one module"),
        (lambda o: o["reserved"].append("Protected._.graph"), "is named under Protected._"),
        (lambda o: o["closures"]["Candidate.Col.D"]["constants"][0].__setitem__("kind", "axiom"), "does not show what Candidate.Col.D is"),
        (lambda o: o["modules"]["Candidate.Col"].__setitem__("is_module", True), "does not show what Candidate.Col.D is"),
        (lambda o: o["closures"]["Candidate.Col.D"].update(found=False, constants=[]), "declare no Candidate.Col.D"),
    ]
    for edit, message in refused:
        with pytest.raises(inspect.Refused, match=message):
            other = changed(edit)
            inspect.unambiguous(other)
            inspect.fingerprints(other, "Candidate.Col.D", "Candidate.Col.D_sound")
    # a refusal is an answer of Lean's about the proof; InspectError that is not one means Lean could not be asked
    assert issubclass(inspect.Refused, inspect.InspectError)


def test_a_locked_module_changes_in_the_protected_modules_name_and_nowhere_else(tmp_path):
    new = "N_max2_ladder_n2v24d8_s3_c570"
    out = renamed(GENERAL, PA, new)
    assert out == GENERAL.replace(PA, new) and out.count(new) == 2 and PA not in out
    assert renamed(GENERAL, None, new) == GENERAL and renamed(GENERAL, PA, PA) == GENERAL
    # a whole identifier only: a longer name that starts the same is another module
    assert renamed(f"import Protected.{PA}_h0123\n", PA, new) == f"import Protected.{PA}_h0123\n"
    # the name is the Lean project's to give
    (tmp_path / "scripts").mkdir()
    (tmp_path / "scripts" / "make_protected.py").write_text(MAKE_PROTECTED)
    assert protected_name(tmp_path, B, 570) == new
    assert protected_name(tmp_path, B, 570, [1, 2]).startswith(new + "_h")
    with pytest.raises(LockError, match="did not name"):
        protected_name(tmp_path / "nowhere", B, 570)


# a whole run ---------------------------------------------------------------------------------------
IDENT = {"commit": json.loads(loop.LEAN_LOCK.read_text())["commit"], "toolchain": "t", "lean_project": "p", "policy": "q", "acceptcheck": "b"}


def fake_project(tmp_path: Path) -> Path:
    project = tmp_path / "lean"
    files = {"scripts/accept.py": "", "scripts/make_protected.py": MAKE_PROTECTED, "CompactCheck/Spec.lean": "-- spec",
             "CompactCheck/Counted.lean": "-- counted", "CompactCheck/CountedOps.lean": "-- ops",
             "examples/open_lane/max2_tiny_scored/Candidate/Max2TinyScored.lean": "-- the linear example",
             "examples/open_lane/attn_max2_tiny_scored/Candidate/AttnTinyScored.lean": "-- facts and glue",
             ".lake/build/bin/acceptcheck": ""}
    for rel, text in files.items():
        (project / rel).parent.mkdir(parents=True, exist_ok=True)
        (project / rel).write_text(text)
    return project


def fake_service(extract: int):
    """The acceptance service, standing in: every module compiles, and a submission is accepted as claimed,
    with the receipt the real service writes (the hashes of the modules it was handed among its digests)."""
    def service(self, args, timeout_s):
        if args[0] != "submit":
            return {"ok": True, "messages": ""}
        cdir = Path(args[1])
        m = json.loads((cdir / "manifest.json").read_text())
        digests = {**IDENT, "modules": {rel[:-5].replace("/", "."): hashlib.sha256((cdir / rel).read_bytes()).hexdigest() for rel in m["modules"]}}
        receipt = {"status": "accepted", "network": m["network"], "claim_kind": m["kind"], "claimed_count": m["claimed_count"],
                   "theorem": m["theorem"], "candidate_id": m["candidate_id"], "digests": digests, "seconds": 1.0,
                   "receipt_path": str(cdir / "receipt.json"), "isolation": "none"}
        if m["kind"] == "auxiliary":
            return {**receipt, "statement": "∀ w, bill w = 20000"}
        receipt["certified_count"] = m["claimed_count"]
        if "scored" in m:
            bill, read = m["scored"]["claimed_bill"], len(m["scored"]["certificate"])
            receipt["scoring"] = {"status": "scored", "bill": bill, "extract": extract, "read": read, "length": bill + extract + read,
                                  "description_size": 900}
        return receipt
    return service


def call(tool, **args):
    return {"tool": tool, "args": args}


def pilot_run(tmp_path: Path, monkeypatch, scripts: list[dict], rounds_max: int = 1, **open_lane) -> Path:
    """A run config on the pilot's base (config/pilot/base.yaml), for two seeds of a small size, with the fake
    backend playing `scripts` (one per round) and the stand-ins for the Lean project and its service."""
    project = fake_project(tmp_path)
    paths = []
    for i, script in enumerate(scripts):
        p = tmp_path / f"script_{i}.json"
        p.write_text(json.dumps(script))
        paths.append(str(p))
    cfg = {"extends": str(REPO_ROOT / "config" / "pilot" / "base.yaml"), "run_id": "stages", "model": "tests/max2_ladder",
           "networks": [A], "backend": "fake", "rounds_max": rounds_max, "runs_dir": str(tmp_path / "runs"), "workers": 1,
           "open_lane": {"lean_project": str(project), "work_dir": str(tmp_path / "work"), "fake_scripts": paths,
                         "seed_check": {"network": B}, **open_lane}}
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    monkeypatch.setattr(loop, "check_lean_lock", lambda project: {})
    monkeypatch.setattr(loop, "check_inspection", lambda project: None)
    monkeypatch.setattr(loop, "lean_identity", lambda project, knowledge="minimal": dict(IDENT))
    monkeypatch.setattr(Session, "_service", fake_service(448))
    return path


ROUND_1 = {"calls": [
    # a shorter proof kept in one module, then the proof with its checker apart
    call("lean_check", path="Candidate/One.lean", source=ONE_MODULE, network=A, claimed_count=576),
    call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.One.performance", modules=["Candidate/One.lean"],
         scored={"checker": "Candidate.One.D", "sound": "Candidate.One.D_sound", "instance": "Candidate.One.D_instance",
                 "certificate": [], "claimed_bill": 15000}),
    call("lean_check", path="Candidate/Col.lean", source=GENERAL, network=A, claimed_count=576),
    call("lean_check", path="Candidate/ColRun.lean", source=INSTANCE, network=A, claimed_count=576),
    call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.ColRun.performance", modules=["Candidate/ColRun.lean"],
         scored=SCORED),
], "response": "CLAIM: two proofs.\nWHY IT HELPS: columns.\nNOTES: none."}

INSTANCE_B = INSTANCE.replace("ColRun", "ColRunB").replace(PA, "N_max2_ladder_n2v24d8_s3_c570")
SEED_CHECK = {"calls": [
    call("lean_check", path="Candidate/Col.lean", source=GENERAL.replace("pure I.nzero", "pure (I.nofNat 576)"), network=B, claimed_count=570),
    call("lean_check", path="Candidate/ColRunB.lean", source=INSTANCE_B, network=B, claimed_count=570),
    call("submit_candidate", network=B, claimed_count=570, theorem="Candidate.ColRunB.performance", modules=["Candidate/ColRunB.lean"],
         scored={**SCORED, "checker": "Candidate.ColRunB.D", "instance": "Candidate.ColRunB.D_instance"}),
    call("submit_candidate", network=B, claimed_count=570, theorem="Candidate.ColRunB.t", modules=["Candidate/ColRunB.lean"], kind="auxiliary"),
    call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.ColRun.performance", modules=["Candidate/ColRun.lean"], scored=SCORED),
    # a second declaration of the locked checker, in a module of the session's own
    call("lean_check", path="Candidate/Again.lean", source="namespace Candidate.Col\ndef D : Nat := 1\nend Candidate.Col\n", network=B, claimed_count=570),
    call("submit_candidate", network=B, claimed_count=570, theorem="Candidate.ColRunB.performance",
         modules=["Candidate/ColRunB.lean", "Candidate/Again.lean"], scored={**SCORED, "instance": "Candidate.ColRunB.D_instance"}),
    call("submit_candidate", network=B, claimed_count=570, theorem="Candidate.ColRunB.performance", modules=["Candidate/ColRunB.lean"],
         scored={**SCORED, "instance": "Candidate.ColRunB.D_instance"}),
], "response": "CLAIM: 570 of 576.\nWHY IT HELPS: six inputs differ.\nNOTES: none."}

GROWTH = "import Candidate.Col\n\nnamespace Candidate.Growth\n\ntheorem bill_fixed : True := trivial\n\nend Candidate.Growth\n"
SCALING = {"calls": [
    call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.ColRun.performance", modules=["Candidate/ColRun.lean"], scored=SCORED),
    call("lean_check", path="Candidate/Growth.lean", source=GROWTH, network=A, claimed_count=576),
    call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.Growth.bill_fixed", modules=["Candidate/Growth.lean"], kind="auxiliary"),
], "response": "CLAIM: quadratic against cubic.\nWHY IT HELPS: bill_fixed proves a.\nNOTES: none."}


def test_a_run_proves_one_network_then_checks_a_second_seed_with_the_checker_locked(tmp_path, monkeypatch):
    """The pilot's three parts on stand-ins. Round 1 submits two scored proofs: the shorter one in a single
    module, the other with its checker apart. When the proof rounds end, the best proof that can be locked is
    locked (the single-module one is passed over, with the reason). The seed check's session cannot save
    over the locked module, cannot name another checker, cannot submit a lemma or a proof of the first
    network; its instance for the second seed is accepted with the locked module as it was, the protected
    module's name alone replaced, which the receipt's hashes confirm. The scaling session takes lemmas only.
    Nothing after the proof rounds moves the run's score, and a resumed run adds nothing."""
    lines = []
    ctx = loop.start(pilot_run(tmp_path, monkeypatch, [ROUND_1, SEED_CHECK, SCALING]), log=lines.append)
    assert ctx.cfg["open_lane"]["scaling"] is True and ctx.cfg["prompt_template"] == "open_lane_v5"
    loop.drive(ctx)
    run = ctx.run
    assert run.done_rounds() == [0, 1, 2, 3]
    state = stages.read_state(run)
    assert state["proof_rounds_ended"] == {"after_round": 1, "why": "the round limit (1)"}
    locked = state["locked"]
    assert (locked["network"], locked["submission"], locked["length"], locked["certified"]) == (A, 1, 20448, 576)
    assert locked["modules"] == ["Candidate/Col.lean"] and locked["free"] == ["Candidate/ColRun.lean"]
    assert [(p["length"], "module of its own" in p["reason"]) for p in state["passed_over"]] == [(15448, True)]
    assert state["stages"]["seed_check"]["round"] == 2 and state["stages"]["scaling"]["round"] == 3

    # the seed check
    records = run.read_archive()
    check = [r for r in records if r.get("stage") == "seed_check"]
    assert [r["status"] for r in check] == ["ok", "ok"] and all(r["network"] == B and r["certified"] == 570 for r in check)
    # the first accepted proof came with a second declaration of the checker's name (the stand-in service takes
    # it; the real one refuses a constant declared twice): Lean does not find the locked checker in it alone
    assert check[0]["lock"]["intact"] and check[0]["lock"]["verified"] is False
    assert "Candidate.Col.D is declared by more than one module (Candidate.Again, Candidate.Col)" in check[0]["lock"]["why"]
    assert check[1]["lock"] == {"digest": locked["digest"], "of": locked["record_id"], "intact": True, "in_receipt": True,
                                "verified": True, "why": None, "fingerprints": locked["fingerprints"]}
    tools = [json.loads(l) for l in (run.round_path(2) / "attempt_0" / "open_lane" / "tools.jsonl").read_text().splitlines()]
    errors = [t["outcome"].get("error", "") for t in tools]
    assert "Candidate/Col.lean is locked" in errors[0] and errors[1] == ""
    assert "scored.checker must be Candidate.Col.D" in errors[2] and "scored proofs only" in errors[3]
    assert "is not one of this run's networks" in errors[4] and errors[5:] == ["", "", ""]
    # the session is told, when the receipt arrives, whether Lean finds the locked checker in the accepted proof
    assert [t["outcome"].get("locked_checker") for t in tools[6:]] == [False, True]
    asked = json.loads((run.round_path(2) / "attempt_0" / "open_lane" / "submissions" / "000" / "lock.json").read_text())
    assert asked["intact"] and asked["verified"] is False and "declared by more than one module" in asked["why"]
    sent = run.round_path(2) / "attempt_0" / "open_lane" / "submissions" / "001"
    new = "N_max2_ladder_n2v24d8_s3_c570"
    assert (sent / "Candidate/Col.lean").read_text() == GENERAL.replace(PA, new)  # the locked text, renamed, not the session's
    assert sorted(json.loads((sent / "manifest.json").read_text())["modules"]) == ["Candidate/Col.lean", "Candidate/ColRunB.lean"]
    result = state["stages"]["seed_check"]["result"]
    per_input = (170368 - 448) // 576
    assert (result["certified"], result["real_correct"], result["length"]) == (570, 576, 20448)
    assert result["finishing_total"] == 20448 + 6 * per_input and result["ratio"] == pytest.approx(170368 / (20448 + 6 * per_input))
    assert result["outcome"] == "certified" and result["lock_intact"] and result["lock_in_receipt"] and result["lock_verified"]
    assert result["record_id"] == check[1]["record_id"] and result["fingerprints"] == locked["fingerprints"]
    assert any(f"on {B} the locked checker certified 570 of the 576" in l for l in lines)

    # the scaling question: lemmas only, about the locked checker
    scaling = [r for r in records if r.get("stage") == "scaling"]
    assert [r["status"] for r in scaling] == ["lemma"] and state["stages"]["scaling"]["result"]["lemmas"][0]["theorem"] == "Candidate.Growth.bill_fixed"
    # Lean is asked about a lemma's submission too: Candidate.Col.D in its statement is the locked checker
    assert scaling[0]["lock"]["verified"] is True and state["stages"]["scaling"]["result"]["lemmas"][0]["locked_checker"] is True
    # the report: the two networks side by side, on what the claim of one checker rests, and the lemma
    report = "\n".join(stages.report_lines(run))
    assert f"| {A} (written for) | 576 of 576 | 20,448 | 170,368 | 8.332 |" in report
    assert f"| {B} (second seed, checker locked) | 570 of 576 | 20,448 | 170,368 |" in report
    assert "The same checker on both: Lean reads the locked checker's kernel terms" in report and "the receipt's hashes say the same" in report
    assert "- `Candidate.Growth.bill_fixed`: ∀ w, bill w = 20000 (the locked checker)" in report
    assert "Passed over, though it finishes cheaper" in report and "module of its own" in report
    tools = [json.loads(l) for l in (run.round_path(3) / "attempt_0" / "open_lane" / "tools.jsonl").read_text().splitlines()]
    assert "lemmas only" in tools[0]["outcome"]["error"]
    sent = run.round_path(3) / "attempt_0" / "open_lane" / "submissions" / "000"
    assert (sent / "Candidate/Col.lean").read_text() == GENERAL  # the first network again: nothing to rename

    # the prompts
    p1, p2, p3 = (run.read(k, "prompt.md") for k in (1, 2, 3))
    assert "This run is about one network." in p1 and "Keep the checker and the instance in separate modules" in p1
    assert f"- {A} (n2v24d8)" in p1 and B not in p1 and "geometric mean" not in p1
    assert "THIS SESSION: THE SEED CHECK" in p2 and f"- {B} (n2v24d8)" in p2 and "SCOREBOARD" not in p2
    assert f"The best of your scored proofs\nthat could be locked was of {A}: all 576 inputs it answers correctly, at length 20,448" in p2
    assert "LOCKED\n- Candidate/Col.lean (" in p2 and f"({PA})" in p2 and "Candidate/ColRun.lean) is in your workspace" in p2
    assert "THIS SESSION: HOW THE COST GROWS" in p3 and "certified 570 of the 576" in p3 and "576 inputs at 295 each" in p3
    # the scaling claim comes with its conditions, and with what the checker certifies at other sizes
    assert "if the locked checker's run succeeds" in p3 and "the sizes you let vary and the ones you hold fixed" in p3
    assert "A cheap check and a useful accuracy bound are separate" in p3 and "It must be the same method at every size" in p3
    # the proof rounds' prompt: the score as a formula, an instance in one theorem or from parts, what the seed check shows
    assert "F(P) = length(P) + c * (correct - certified(P))" in p1 and "a computed figure, not a proof that was built and checked" in p1
    assert "A submission improves the score when it lowers" in p1 and "any shorter proof raises" not in p1
    assert "A short run: one `decide +kernel`" in p1 and "A long run: memory is the limit" in p1
    # where an instance put together from parts can be seen, and its one trap, in the prompt itself (no doc is pointed to)
    assert "which read_file reads:\n  examples/open_lane/attn_max2_tiny_scored/Candidate/AttnTinyScored.lean" in p1
    assert "never leave it to the kernel to see that two\n  different `CostM.run` terms are equal by unfolding them" in p1 and "COUNTED.md" not in p1
    assert "another seed may compute\n  differently, or with smaller margins" in p1 and "certifies as much there" not in p1
    assert "A real network's weights written out measure more." in p1
    assert not any("{" + name + "}" in p for p in (p2, p3) for name in ("LOCKED", "RENAME", "FREE", "NETWORK", "SEED_CHECK_RESULT"))

    # the score is the proof rounds' alone, and the run is over: a resume adds nothing
    from core.scoring import run_cost_of_finishing, summarize

    assert run_cost_of_finishing(summarize(records, ctx.entries, None)) == pytest.approx(170368 / 15448)
    assert "seed_check" in json.dumps(json.loads((run.round_path(2) / "attempt_0" / "results.json").read_text()))
    loop.status_text(run)
    ctx2 = loop.resume(run.path, log=lines.append)
    loop.drive(ctx2)
    assert len(ctx2.run.read_archive()) == len(records) and ctx2.run.done_rounds() == [0, 1, 2, 3]


def test_the_receipts_say_which_proofs_can_go_to_the_seed_check_and_a_run_without_one_is_told_nothing(tmp_path, monkeypatch):
    """During the proof rounds the agent reads, per scored proof, whether it can be taken to the seed check.
    With two proof rounds and scripts for both, the seed check waits for the round limit; when the backend
    runs out before a stage, the stage is left for a resume."""
    nothing = {"calls": [], "response": "CLAIM: nothing.\nWHY IT HELPS: -\nNOTES: none."}
    ctx = loop.start(pilot_run(tmp_path, monkeypatch, [ROUND_1, nothing, SEED_CHECK], rounds_max=2), log=lambda *a: None)
    loop.drive(ctx)
    run = ctx.run
    p2 = run.read(2, "prompt.md")
    assert "length 15,448 (bill 15,000); finishing from it costs 15,448" in p2 and "not ready for the seed check: the instance theorem" in p2
    assert "length 20,448 (bill 20,000); finishing from it costs 20,448" in p2 and "a ratio of 8.332); ready for the seed check" in p2
    assert "Score: 11.028 (cost of finishing; brute force is 1.000)" in p2
    # the score rests on the proof that cannot go: the aim says so
    assert "The proof your score rests on (length 15,448) cannot be taken to the seed check as it is: the instance theorem" in p2
    assert "submit it again with the checker and its soundness proof in modules apart from the instance" in p2
    state = stages.read_state(run)
    assert state["stages"]["seed_check"]["round"] == 3 and state["stages"]["seed_check"]["result"]["certified"] == 570
    assert state["stages"]["scaling"] == {"round": 4, "result": None} and run.done_rounds() == [0, 1, 2, 3]
    # the run is not over: with a script for the last session, a resume runs it and nothing else
    scripts = json.loads(json.dumps(yaml.safe_load((run.path / "config.yaml").read_text())["open_lane"]["fake_scripts"]))
    extra = tmp_path / "script_scaling.json"
    extra.write_text(json.dumps(SCALING))
    cfg = yaml.safe_load((run.path / "config.yaml").read_text())
    cfg["open_lane"]["fake_scripts"] = scripts + [str(extra)]
    (run.path / "config.yaml").write_text(yaml.safe_dump(cfg))
    ctx2 = loop.resume(run.path, log=lambda *a: None)
    loop.drive(ctx2)
    assert ctx2.run.done_rounds() == [0, 1, 2, 3, 4] and len(stages.read_state(run)["stages"]["scaling"]["result"]["lemmas"]) == 1


def test_a_run_whose_proofs_cannot_be_locked_skips_what_follows_and_says_why(tmp_path, monkeypatch):
    only_one = {"calls": ROUND_1["calls"][:2], "response": ROUND_1["response"]}
    lines = []
    ctx = loop.start(pilot_run(tmp_path, monkeypatch, [only_one, SEED_CHECK, SCALING]), log=lines.append)
    loop.drive(ctx)
    state = stages.read_state(ctx.run)
    assert state["locked"] is None and ctx.run.done_rounds() == [0, 1]
    assert any("no proof to lock" in l and "module of its own" in l for l in lines)


def test_when_lean_cannot_be_asked_nothing_is_decided_and_a_resume_goes_on(tmp_path, monkeypatch):
    """Lean not answering (no Lean, the compiled modules not where the service keeps them) says nothing about
    a proof. It is not a reason to tell the agent its proof cannot be locked, to pass the best proof over for
    a worse one, or to record an accepted proof as unverified: the prompt is silent on that proof and the log
    says why, the run halts before anything is locked, and a halted round asks again on a resume."""
    asked = {"fails": True}

    def lean(lean_project, submission, where=(), closure=()):
        if asked["fails"]:
            raise inspect.InspectError("no lean binary found (install elan)")
        return stand_in_inspect(lean_project, submission, where, closure)

    monkeypatch.setattr(inspect, "inspect_submission", lean)
    nothing = {"calls": [], "response": "CLAIM: nothing.\nWHY IT HELPS: -\nNOTES: none."}
    lines = []
    path = pilot_run(tmp_path, monkeypatch, [ROUND_1, nothing, SEED_CHECK, SCALING], rounds_max=2)
    ctx = loop.start(path, log=lines.append)
    # the proof rounds go on without Lean's account: round 2's prompt says nothing of readiness, the log says why
    with pytest.raises(loop.LoopError, match="could not be read for the lock .*no lean binary found.*can be resumed"):
        loop.drive(ctx)
    run = ctx.run
    p2 = run.read(2, "prompt.md")
    assert "finishing from it costs 15,448" in p2 and "ready for the seed check" not in p2 and "cannot be taken to the seed check" not in p2
    assert sum("could not ask Lean whether this proof can go to the seed check" in l for l in lines) == 2
    assert run.done_rounds() == [0, 1, 2] and stages.read_state(run) is None  # nothing locked, nothing passed over
    # Lean answers again, and goes away once more while the seed check's session runs
    asked["fails"] = False
    real = Session.submit_candidate

    def submit(self, *args, **kwargs):
        asked["fails"] = bool(self.state.get("stage"))  # no answer while a session after the proof rounds submits
        try:
            return real(self, *args, **kwargs)
        finally:
            asked["fails"] = False

    monkeypatch.setattr(Session, "submit_candidate", submit)
    asked_again = {"n": 0}
    from core.open_lane import lock as lock_module

    same = lock_module.same_checker

    def unanswered_once(lock, submission, lean_project, scored=True):
        asked_again["n"] += 1
        if asked_again["n"] == 3:  # the round's first question, after the session's two
            return {"verified": None, "why": "Lean could not be asked what the submission declares: no lean binary found"}
        return same(lock, submission, lean_project, scored=scored)

    monkeypatch.setattr(lock_module, "same_checker", unanswered_once)
    ctx2 = loop.resume(run.path, log=lines.append)
    with pytest.raises(Exception, match="whether it has the locked checker is not known .*the run halts and can be resumed"):
        loop.drive(ctx2)
    state = stages.read_state(run)
    assert state["locked"]["length"] == 20448 and state["stages"]["seed_check"]["result"] is None and run.done_rounds() == [0, 1, 2]
    sub = run.round_path(3) / "attempt_0" / "open_lane" / "submissions"
    assert all("verified" not in json.loads((sub / n / "lock.json").read_text()) for n in ("000", "001"))  # nothing was recorded
    tools = [json.loads(l) for l in (run.round_path(3) / "attempt_0" / "open_lane" / "tools.jsonl").read_text().splitlines()]
    assert [t["outcome"].get("locked_checker", "-") for t in tools[6:]] == [None, None]
    # the session is not run again: its accepted proofs are asked about again, and the run finishes
    ctx3 = loop.resume(run.path, log=lines.append)
    loop.drive(ctx3)
    state = stages.read_state(run)
    assert run.done_rounds() == [0, 1, 2, 3, 4] and state["stages"]["seed_check"]["result"]["outcome"] == "certified"
    check = [r for r in run.read_archive() if r.get("stage") == "seed_check"]
    assert [r["lock"]["verified"] for r in check] == [False, True] and len(tools) == len(
        (run.round_path(3) / "attempt_0" / "open_lane" / "tools.jsonl").read_text().splitlines())


def test_the_seed_check_names_another_development_seed_of_the_same_size(tmp_path, monkeypatch):
    """Refused before a run folder exists: the run's own network, a network of another size, a held-out
    network, a run on several networks, and a setting of the wrong form."""
    for check, why in ((A, "the run's own network"), ("max2_ladder-n2v32d8-s1", "keeps the sizes"),
                       ("max2_ladder-n2v24d8-s1", "not a development network")):
        path = pilot_run(tmp_path, monkeypatch, [], seed_check={"network": check})
        with pytest.raises(loop.LoopError, match=why):
            loop.start(path, log=lambda *a: None)
    path = pilot_run(tmp_path, monkeypatch, [])
    cfg = yaml.safe_load(path.read_text())
    cfg["networks"] = [A, B]
    cfg["open_lane"]["seed_check"] = {"network": "max2_ladder-n2v32d8-s1"}
    path.write_text(yaml.safe_dump(cfg))
    with pytest.raises(loop.LoopError, match="are for a run on one network"):
        loop.start(path, log=lambda *a: None)
    cfg["open_lane"]["seed_check"] = B
    path.write_text(yaml.safe_dump(cfg))
    with pytest.raises(RunConfigError, match="seed_check must be null or"):
        load_run_config(path)
    assert not (tmp_path / "runs").exists()


def test_the_pilot_on_the_linear_max_of_2_network_is_one_network_a_second_seed_and_a_size_no_copy_fits(tmp_path):
    """config/pilot/linear-max2.yaml: the shared base and four lines about the model. One network of vocabulary
    size 64 and width 8, cost of finishing as the score, template v5, the seed check on another development seed of
    the same size, the scaling question on. At this size a copy of the weights is over the Lean service's
    description budget (8192 + 4 E), which the choice of size rests on."""
    from fractions import Fraction

    import numpy as np

    from core.model_folder import load_model_folder
    from core.zoo import load_weights, networks

    raw = read_run_config_file(REPO_ROOT / "config" / "pilot" / "linear-max2.yaml")
    assert set(raw) - set(read_run_config_file(REPO_ROOT / "config" / "pilot" / "base.yaml")) == {"run_id", "model", "networks"}
    project = fake_project(tmp_path)
    raw["open_lane"] = {**raw["open_lane"], "lean_project": str(project)}
    from core.run_config import merge

    cfg = merge(raw)
    ol = cfg["open_lane"]
    assert (cfg["metric"], cfg["prompt_template"], cfg["networks"], ol["scaling"]) == ("cost_of_finishing", "open_lane_v5", ["max2-v64-s0"], True)
    assert ol["seed_check"] == {"network": "max2-v64-s1"} and ol["example"].endswith("Max2TinyScored.lean") and "one theorem" in ol["notes"]
    from core.open_lane import surface

    # the example of a split instance is one of the files the agent can read (here on the stand-in surface, by folder)
    assert "examples/open_lane/attn_max2_tiny_scored/" in surface.of_run(cfg)["prefixes"]
    folder = load_model_folder(REPO_ROOT / cfg["model"])
    entries = loop.select_networks(folder, cfg)
    other = loop.seed_check_entry(cfg, folder, entries)
    assert [e["id"] for e in entries] == ["max2-v64-s0"] and other["id"] == "max2-v64-s1"
    sizes = folder.sizes(entries[0]["setting"])
    assert sizes == folder.sizes(other["setting"]) and sorted(sizes.values()) == [2, 8, 64]
    for e in (entries[0], other):
        bits = 0
        for tensor in load_weights(folder, e["id"]).values():
            fr = [Fraction(float(v)) for v in np.asarray(tensor, dtype=np.float64).reshape(-1)]
            den = max(f.denominator for f in fr)
            bits += sum(max(1, abs(int(f * den)).bit_length()) for f in fr)
        assert bits > 2 * (8192 + 4 * e["E"]), e["id"]
        assert e["split"] == "dev" and e in networks(folder, "dev")


def test_one_input_by_brute_force_has_an_exact_price_on_a_network_with_a_misclassified_input():
    """The pilot's network answers 4,095 of its 4,096 inputs correctly. Brute force still runs a forward pass
    on every input, so one input's price is the single rule's charge over all of them, exactly; a round-0
    proof with other leaves is not brute force and gives only the estimate."""
    from core.scoring import fallback_cost_per_input

    entry = {"id": "n", "n_inputs": 4096, "E": 1088, "B": 2683968}
    brute = {"network": "n", "round": 0, "status": "ok", "certified": 4095, "length_by_rule": {"extract": 1088, "single": 2682880},
             "leaves": {"accepted": 4095, "rejected": 1, "skipped": 0, "total": 4096}}
    assert fallback_cost_per_input(entry, [brute]) == (655.0, "exact: the single rule's charge per input")
    other = {**brute, "length_by_rule": {"extract": 1088, "single": 1000, "interval": 5}}
    skipping = {**brute, "leaves": {"accepted": 4000, "rejected": 0, "skipped": 96, "total": 4096}}
    assert fallback_cost_per_input(entry, [other])[1].startswith("estimate") and fallback_cost_per_input(entry, [skipping])[1].startswith("estimate")


def test_a_run_is_told_only_of_the_sessions_it_has(tmp_path, monkeypatch):
    """Template v5 names the seed check and the scaling question as the run config has them. A run with the
    seed check alone ends after it, and its prompt says one thing follows the rounds; a run on one network
    with neither is told of none and needs no separate modules."""
    from core.open_lane.prompt import after_rounds_text, modules_rule_text

    ctx = loop.start(pilot_run(tmp_path, monkeypatch, [ROUND_1, SEED_CHECK], scaling=False), log=lambda *a: None)
    loop.drive(ctx)
    assert ctx.run.done_rounds() == [0, 1, 2] and list(stages.read_state(ctx.run)["stages"]) == ["seed_check"]
    p1 = ctx.run.read(1, "prompt.md")
    assert "One thing comes after its rounds" in p1 and "- The seed check." in p1 and "The scaling question" not in p1
    assert "Keep the checker and the instance in separate modules" in p1 and "{" + "AFTER_ROUNDS}" not in p1
    assert after_rounds_text({}) == "This run is about one network." and modules_rule_text({}) == ""
    alone = after_rounds_text({"scaling": True})
    assert "- The scaling question. Then you are asked" in alone and "seed check" not in alone
    assert "The scaling question is asked of the first kind, locked." in modules_rule_text({"scaling": True})
    # both sessions are for a run on one network
    path = pilot_run(tmp_path / "two", monkeypatch, [], seed_check=None)
    cfg = yaml.safe_load(path.read_text())
    cfg["networks"] = [A, B]
    path.write_text(yaml.safe_dump(cfg))
    with pytest.raises(loop.LoopError, match="are for a run on one network"):
        loop.start(path, log=lambda *a: None)


def test_a_seed_check_that_did_not_finish_is_no_result_and_a_checked_zero_is_a_result(tmp_path):
    """Two reviews (10 November 2026). First: a session that timed out or never compiled was reported as "the
    locked checker certified nothing". Failing to complete the check is not a measurement. The outcome is
    `no_result`, with what the session's records were and how it ended, and every text says it is not a
    measurement of zero. A claim of 0 accepted under the lock is a result: the checker certifies nothing
    there. Second: an accepted proof counts only when Lean found the locked checker in it. One that was
    accepted without that is `unverified`: reported with the reason, never as what the locked checker
    certifies, and never in place of a verified one."""
    entry = {"id": B, "n_inputs": 576, "E": 448, "B": 170368, "real_correct": 576}
    state = {"locked": {"ratio": 8.332}, "stages": {"seed_check": {"network": B, "round": 5}}}

    def rec(status, **f):
        return {"round": 5, "stage": "seed_check", "network": B, "status": status, "record_id": f"r5/{status}", **f}

    failed = [rec("timeout", error="compiling Candidate.ColRunB exceeded 3600 s"), rec("rejected", error="Candidate.ColRunB does not compile")]
    res = stages.seed_check_result(failed, 5, entry, "the session ran out of time")
    assert res["outcome"] == "no_result" and "certified" not in res and "ratio" not in res
    assert res["note"] == "the session's records: 1 rejected, 1 timeout; the session ran out of time" and len(res["reasons"]) == 2
    state["stages"]["seed_check"]["result"] = res
    line = stages.seed_check_line(state)
    assert "gave no accepted result" in line and "That is not a measurement" in line and "certified nothing" not in line
    nothing = stages.seed_check_result([rec("no_submission", error="the session submitted no candidate")], 5, entry)
    assert nothing["outcome"] == "no_result" and nothing["reasons"] == []
    ok = {"intact": True, "in_receipt": True, "verified": True, "why": None, "fingerprints": {"checker": "c"}}
    zero = stages.seed_check_result(failed + [rec("ok", certified=0, length=20448, lock=ok)], 5, entry)
    assert (zero["outcome"], zero["certified"], zero["finishing_total"]) == ("certified", 0, 20448 + 576 * 295)
    assert zero["lock_verified"] and zero["fingerprints"] == {"checker": "c"}
    state["stages"]["seed_check"]["result"] = zero
    assert "certifies none of the 576 inputs" in stages.seed_check_line(state) and "a checked claim of 0" in stages.seed_check_line(state)
    # accepted, but the locked modules did not reach the service unchanged: not a result
    broken = stages.seed_check_result([rec("ok", certified=570, length=20448, lock={**ok, "intact": False})], 5, entry)
    assert broken["outcome"] == "unverified" and "certified" not in broken and "ratio" not in broken
    assert broken["accepted"] == [{"record_id": "r5/ok", "certified": 570, "length": 20448,
                                   "why": "the locked modules did not reach the service unchanged"}]
    # accepted, the text unchanged, but Lean did not find the locked checker in it: not a result
    why = "the checker's kernel terms differ from the locked checker's"
    other = stages.seed_check_result([rec("ok", certified=570, length=20448, lock={**ok, "verified": False, "why": why})], 5, entry)
    assert other["outcome"] == "unverified" and other["accepted"][0]["why"] == why
    state["stages"]["seed_check"]["result"] = other
    line = stages.seed_check_line(state)
    assert "is unverified" in line and why in line and "not a measurement of how the locked checker transfers" in line
    # a record from before the comparison existed (no `verified`) does not count either
    old = stages.seed_check_result([rec("ok", certified=570, length=20448, lock={"intact": True, "in_receipt": True})], 5, entry)
    assert old["outcome"] == "unverified" and old["accepted"][0]["why"] == "the checker was not compared with the locked one"
    # a verified proof is the result even when a cheaper unverified one stands next to it
    both = stages.seed_check_result([rec("ok", certified=576, length=100, lock={**ok, "verified": False, "why": why}),
                                     rec("ok", certified=570, length=20448, lock=ok)], 5, entry)
    assert (both["outcome"], both["certified"], both["length"]) == ("certified", 570, 20448)
    # the report and the status say of each outcome what it is
    from types import SimpleNamespace

    run = SimpleNamespace(path=tmp_path)
    locked = {"record_id": "r1/ok", "network": A, "certified": 576, "real_correct": 576, "length": 20448, "B": 170368, "ratio": 8.332,
              "modules": ["Candidate/Col.lean"], "checker": "Candidate.Col.D"}
    texts = {}
    for name, result in (("unverified", other), ("no_result", res), ("zero", zero)):
        stages.write_state(run, {"proof_rounds_ended": {"after_round": 4, "why": "the round limit (4)"}, "locked": locked, "passed_over": [],
                                 "stages": {"seed_check": {"network": B, "round": 5, "result": result}}})
        texts[name] = "\n".join(stages.report_lines(run) + stages.status_lines(run))
    assert f"Unverified on {B}" in texts["unverified"] and why in texts["unverified"] and "| Network |" not in texts["unverified"]
    assert "This is not a measurement of how the locked checker transfers" in texts["unverified"]
    assert f"No accepted result on {B}" in texts["no_result"] and "This is not a measurement of zero" in texts["no_result"]
    assert f"| {B} (second seed, checker locked) | 0 of 576 | 20,448 |" in texts["zero"] and "certifies none of the 576 inputs" in texts["zero"]
