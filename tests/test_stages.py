"""After the proof rounds of an open-lane run: the lock, the seed check and the scaling question.

No Lean and no model: the Lean project is a folder of stand-in files, the acceptance service is a function
that accepts what it is handed and writes the receipt the real one would, and the sessions are scripts of
tool calls (the fake backend). What is tested is the pipeline's side: which proof is locked and why, that
the locked modules reach the service unchanged whatever a session does, and what the run records.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path

import pytest
import yaml

from core import loop
from core.open_lane import stages
from core.open_lane.lock import LockError, declaring_module, lockable, protected_name, read_lock, renamed
from core.open_lane.session import Session
from core.run_config import RunConfigError, load_run_config, read_run_config_file
from core.util import REPO_ROOT

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


def test_a_proof_is_locked_by_module_the_checker_apart_from_the_instance(tmp_path):
    """The locked modules are the ones that declare the checker and its soundness theorem, with what they
    import; the instance must be declared outside them. A proof in one module, or one whose constants are
    not named after their modules, cannot be locked, and the reason says what to change."""
    lock = read_lock(submission(tmp_path / "two", {"Candidate/ColRun.lean": INSTANCE, "Candidate/Col.lean": GENERAL}, SCORED))
    assert list(lock["modules"]) == ["Candidate/Col.lean"] and lock["free"] == ["Candidate/ColRun.lean"]
    assert (lock["checker"], lock["sound"], lock["protected"]) == ("Candidate.Col.D", "Candidate.Col.D_sound", PA)
    assert lock["modules"]["Candidate/Col.lean"] == GENERAL and len(lock["digest"]) == 64
    # what the checker's module imports is locked with it
    deep = {"Candidate/Lemmas.lean": "theorem l : True := trivial\n", "Candidate/Col.lean": "import Candidate.Lemmas\n" + GENERAL,
            "Candidate/ColRun.lean": INSTANCE}
    assert sorted(read_lock(submission(tmp_path / "deep", deep, SCORED))["modules"]) == ["Candidate/Col.lean", "Candidate/Lemmas.lean"]
    one = {"checker": "Candidate.One.D", "sound": "Candidate.One.D_sound", "instance": "Candidate.One.D_instance",
           "certificate": [], "claimed_bill": 1}
    assert "the instance belongs in a module of its own" in lockable(submission(tmp_path / "one", {"Candidate/One.lean": ONE_MODULE}, one))
    elsewhere = {**SCORED, "checker": "Candidate.Other.D"}
    assert "name each constant after its module" in lockable(submission(tmp_path / "named", {"Candidate/Col.lean": GENERAL,
                                                                                          "Candidate/ColRun.lean": INSTANCE}, elsewhere))
    with pytest.raises(LockError, match="not a scored proof"):
        read_lock(submission(tmp_path / "plain", {"Candidate/Col.lean": GENERAL}, None))
    assert declaring_module("Candidate.A.B.x", {"Candidate.A": "a", "Candidate.A.B": "b"}) == "Candidate.A.B"
    assert declaring_module("Candidate.x", {"Candidate.A": "a"}) is None


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
    assert [r["status"] for r in check] == ["ok"] and check[0]["network"] == B and check[0]["certified"] == 570
    assert check[0]["lock"] == {"digest": locked["digest"], "of": locked["record_id"], "intact": True, "in_receipt": True}
    tools = [json.loads(l) for l in (run.round_path(2) / "attempt_0" / "open_lane" / "tools.jsonl").read_text().splitlines()]
    errors = [t["outcome"].get("error", "") for t in tools]
    assert "Candidate/Col.lean is locked" in errors[0] and errors[1] == ""
    assert "scored.checker must be Candidate.Col.D" in errors[2] and "scored proofs only" in errors[3]
    assert "is not one of this run's networks" in errors[4] and errors[5] == ""
    sent = run.round_path(2) / "attempt_0" / "open_lane" / "submissions" / "000"
    new = "N_max2_ladder_n2v24d8_s3_c570"
    assert (sent / "Candidate/Col.lean").read_text() == GENERAL.replace(PA, new)  # the locked text, renamed, not the session's
    assert sorted(json.loads((sent / "manifest.json").read_text())["modules"]) == ["Candidate/Col.lean", "Candidate/ColRunB.lean"]
    result = state["stages"]["seed_check"]["result"]
    per_input = (170368 - 448) // 576
    assert (result["certified"], result["real_correct"], result["length"]) == (570, 576, 20448)
    assert result["finishing_total"] == 20448 + 6 * per_input and result["ratio"] == pytest.approx(170368 / (20448 + 6 * per_input))
    assert result["lock_intact"] and result["lock_in_receipt"]
    assert any(f"on {B} the locked checker certified 570 of the 576" in l for l in lines)

    # the scaling question: lemmas only, about the locked checker
    scaling = [r for r in records if r.get("stage") == "scaling"]
    assert [r["status"] for r in scaling] == ["lemma"] and state["stages"]["scaling"]["result"]["lemmas"][0]["theorem"] == "Candidate.Growth.bill_fixed"
    tools = [json.loads(l) for l in (run.round_path(3) / "attempt_0" / "open_lane" / "tools.jsonl").read_text().splitlines()]
    assert "lemmas only" in tools[0]["outcome"]["error"]
    sent = run.round_path(3) / "attempt_0" / "open_lane" / "submissions" / "000"
    assert (sent / "Candidate/Col.lean").read_text() == GENERAL  # the first network again: nothing to rename

    # the prompts
    p1, p2, p3 = (run.read(k, "prompt.md") for k in (1, 2, 3))
    assert "This run is about one network." in p1 and "Keep the checker and the instance in separate modules" in p1
    assert f"- {A} (n2v24d8)" in p1 and B not in p1 and "geometric mean" not in p1
    assert "THIS SESSION: THE SEED CHECK" in p2 and f"- {B} (n2v24d8)" in p2 and "SCOREBOARD" not in p2
    assert f"Your best scored proof was of\n{A}: all 576 inputs it answers correctly, at length 20,448" in p2
    assert "LOCKED\n- Candidate/Col.lean (" in p2 and f"({PA})" in p2 and "Candidate/ColRun.lean) is in your workspace" in p2
    assert "THIS SESSION: HOW THE COST GROWS" in p3 and "certified 570 of the 576" in p3 and "576 inputs at 295 each" in p3
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
    """config/pilot/linear-max2.yaml: the shared base and four lines about the model. One network of 64 tokens
    and width 8, cost of finishing as the score, template v5, the seed check on another development seed of
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
