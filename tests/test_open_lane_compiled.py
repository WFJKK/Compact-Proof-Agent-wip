"""A run whose checker the Lean service runs compiled (open_lane.instance: compiled; the service's policy v15,
scored.run compiled): the agent proves the checker sound and nothing else, and the count and the bill are those
of the service's own run of the compiled checker on the network.

What is tested here is the pipeline's side: the setting and what it needs, the prompts and tool texts of such a
run (nothing of an instance theorem or a claimed count), what a session sends the service and refuses before it
does, the lock of a proof without an instance, the seed check as a session that gives a certificate and proves
nothing, the modules a fresh run is given to start from, and that every record and report line says who ran
the checker. On stand-ins for the Lean project and its service, as tests/test_stages.py; and once against the
real service where it is built. The service's side is tested in the Lean project (scripts/test_accept.py)."""

from __future__ import annotations

import hashlib
import json
import os
import re
from pathlib import Path

import pytest
import yaml

from core import loop
from core.agent.build_prompt import load_template, placeholders
from core.open_lane import inspect, stages, workflow
from core.open_lane.lock import lockable, read_lock
from core.open_lane.session import RESEARCH_TOOLS, Session, ToolError, tool_table
from core.run_config import RunConfigError, load_run_config, merge
from core.util import REPO_ROOT
from tests.test_stages import A, B, IDENT, call, fake_project, stand_in_inspect

PROMPTS = REPO_ROOT / "core" / "agent" / "prompts"
NA, NB = "N_max2_ladder_n2v24d8_s0", "N_max2_ladder_n2v24d8_s3"  # the two networks' own protected modules
EXAMPLE = "examples/open_lane/max2_tiny_run/Candidate/Max2TinyRun.lean"

# a toy proof with no instance: the checker and its soundness theorem, written against the network's module
COL = f"""import Protected.{NA}
import CompactCheck.CountedOps

namespace Candidate.Col

open CompactCheck Protected.{NA}

def D : Checker := fun I => pure I.nzero

theorem D_sound : True := trivial

end Candidate.Col
"""
SCORED = {"checker": "Candidate.Col.D", "sound": "Candidate.Col.D_sound", "certificate": []}
COUNTS = {A: 576, B: 570}  # what the stand-in service's run of the checker certifies on each network


def inspect_run(lean_project, submission, where=(), closure=(), timeout_s=None):
    """tests/test_stages.py's stand-in for Lean's account, for modules that import the network's own protected
    module: as the real account has it, the claim's module (which the service builds for every submission, here
    with a claimed count of 0, and which these modules do not import) and the network's are told apart."""
    info = stand_in_inspect(lean_project, submission, where, closure, timeout_s)
    info["network_module"], info["protected"] = info["protected"], info["protected"] + "_c0"
    return info


def run_service(extract: int = 448, bill: int = 20000):
    """The acceptance service at policy v15, standing in. A development compile with a checker returns the
    preview with the run. A scored submission must say `run: compiled` and may hold no instance, no bill, no
    claimed count and no theorem of its own (as the real service refuses them); it is accepted with the count of
    the run, which nobody claimed."""
    def service(self, args, timeout_s):
        if args[0] == "compile":
            network = args[args.index("--network") + 1]
            short = "N_" + re.sub(r"[^A-Za-z0-9]", "_", network)
            out = {"ok": True, "messages": "", "module": args[2][:-5].replace("/", "."), "seconds": 1.0,
                   "protected_module": f"Protected.{short}_c{args[args.index('--claimed') + 1]}",
                   "network_module": f"Protected.{short}", "protected_modules": [f"Protected.{short}"]}
            if "--checker" in args:
                read = len(json.loads(Path(args[args.index("--certificate") + 1]).read_text())) if "--certificate" in args else 0
                out["scoring_preview"] = {
                    "checker": args[args.index("--checker") + 1], "counted_language": "ok", "offending": [],
                    "description_size": 900, "size_budget": 9984, "within_budget": True, "largest_definitions": [],
                    "last_bits": {"count": COUNTS[network], "bill": bill, "passes": True, "holds_to": 8,
                                  "least_count_on_copies": COUNTS[network], "runs": [], "keep": "9/10"},
                    "run": {"count": COUNTS[network], "bill": bill, "extract": extract, "read": read,
                            "length": bill + extract + read}}
            return out
        cdir = Path(args[1])
        m = json.loads((cdir / "manifest.json").read_text())
        digests = {**IDENT, "modules": {rel[:-5].replace("/", "."): hashlib.sha256((cdir / rel).read_bytes()).hexdigest()
                                        for rel in m["modules"]}}
        receipt = {"network": m["network"], "claim_kind": m["kind"], "candidate_id": m["candidate_id"], "digests": digests,
                   "seconds": 1.0, "receipt_path": str(cdir / "receipt.json"), "isolation": "none"}
        if m["kind"] == "auxiliary":
            return {**receipt, "status": "accepted", "theorem": m["theorem"], "claimed_count": m.get("claimed_count", 0),
                    "statement": "∀ w, bill w = 20000"}
        scored = m.get("scored") or {}
        wrong = [key for key in ("claimed_count", "theorem") if key in m] + [key for key in ("instance", "claimed_bill") if key in scored]
        if scored.get("run") != "compiled" or wrong:
            return {**receipt, "status": "rejected", "reason": f"not a submission whose run the service makes: {wrong or 'no run'}"}
        read = len(scored.get("certificate") or [])
        return {**receipt, "status": "accepted", "run": "compiled", "theorem": scored["sound"], "claimed_count": None,
                "certified_count": COUNTS[m["network"]], "score_eligible": True, "execution_assurance": "compiled_instance",
                "scoring": {"status": "scored", "run": "compiled", "bill": bill, "extract": extract, "read": read,
                            "length": bill + extract + read, "description_size": 900}}
    return service


def project_with_the_example(tmp_path: Path) -> Path:
    project = fake_project(tmp_path)
    (project / EXAMPLE).parent.mkdir(parents=True, exist_ok=True)
    (project / EXAMPLE).write_text("-- brute force, its checker and soundness theorem alone")
    return project


def compiled_run(tmp_path: Path, monkeypatch, scripts: list[dict], rounds_max: int = 1, **open_lane) -> Path:
    """A python_then_lean run on the pilot's base with open_lane.instance compiled, no discovery round, for two
    seeds of a small size: the fake backend plays `scripts` (one per session) and stand-ins answer for Lean and
    its service."""
    project = project_with_the_example(tmp_path)
    paths = []
    for i, script in enumerate(scripts):
        p = tmp_path / f"script_{i}.json"
        p.write_text(json.dumps(script))
        paths.append(str(p))
    cfg = {"extends": str(REPO_ROOT / "config" / "pilot" / "base.yaml"), "run_id": "run", "model": "tests/max2_ladder",
           "networks": [A], "backend": "fake", "rounds_max": rounds_max, "patience": 1, "runs_dir": str(tmp_path / "runs"),
           "workers": 1,
           "open_lane": {"lean_project": str(project), "work_dir": str(tmp_path / "work"), "fake_scripts": paths,
                         "workflow_mode": "python_then_lean", "discovery_rounds": 0, "instance": "compiled", **open_lane}}
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    monkeypatch.setattr(loop, "check_lean_lock", lambda project: {})
    monkeypatch.setattr(loop, "check_inspection", lambda project: None)
    monkeypatch.setattr(loop, "lean_identity", lambda project, knowledge="minimal": dict(IDENT))
    monkeypatch.setattr(Session, "_service", run_service())
    monkeypatch.setattr(inspect, "inspect_submission", inspect_run)
    return path


def tool_log(run, k: int) -> list[dict]:
    p = run.round_path(k) / "attempt_0" / "open_lane" / "tools.jsonl"
    return [json.loads(line) for line in p.read_text().splitlines()]


def answers(run, k: int) -> list[dict]:
    """What each call of the session's script was answered: ok or the refusal (a call the tool table refuses,
    for an argument it does not take, never reaches the tool or its log)."""
    return run.read(k, "attempt_0/response_meta.json")["tool_calls"]


@pytest.fixture(autouse=True)
def _stand_ins(request):
    if request.node.get_closest_marker("real_surface") is None:
        request.getfixturevalue("stand_in_surface")


# the prompts ---------------------------------------------------------------------------------------------
def headings(text: str) -> list[str]:
    return [l for l in text.splitlines() if re.fullmatch(r"[A-Z][A-Z :',-]+", l)]


@pytest.mark.parametrize("was, now", [("open_lane_v6", "open_lane_v7"),
                                      ("open_lane_discovery_v1", "open_lane_discovery_v2"),
                                      ("open_lane_formalization_v1", "open_lane_formalization_v2")])
def test_the_compiled_runs_templates_are_the_kernel_runs_but_for_the_instance(was, now):
    """A compiled run's prompt is the kernel run's with the passages about the instance rewritten and nothing
    else moved: the same sections in the same order, the same second part, the same placeholders but the two
    that only an instance needs. It names no instance theorem, no claimed count and no `Target` (but to say
    that this run has none), and tells the agent what replaces them: the service's run, and lean_check's `run`."""
    old1, old2 = load_template(was)
    new1, new2 = load_template(now)
    assert new2 == old2
    assert placeholders(new1) == placeholders(old1) - {"MODULES_RULE", "SPLIT_EXAMPLE"}
    swapped = {"Getting the instance through the kernel:": "The run, and what is left to the kernel:"}
    assert headings(new1) == headings(old1)
    for gone, there in swapped.items():
        assert gone in old1 and gone not in new1 and there in new1
    flat = " ".join(new1.split())
    assert "in this run there is no instance theorem and no theorem of `Target`" in flat
    rest = flat.replace("there is no instance theorem and no theorem of `Target`", "").replace("An instance of this PyTorch module", "")
    for word in ("D_instance", "instance", "Target", "claimed", "#eval", "decide +kernel", "claim's module"):
        assert word not in rest, (now, word)
    assert "The service runs your compiled checker on the network's weights, with your certificate and plan" in flat
    assert "`run` in its answer is the count, the bill and the length a submission of that checker gets" in flat
    assert "Your submission names D, the soundness theorem and the certificate" in flat
    # what did not change is word for word the kernel run's: most lines of the old first part are still there
    kept = sum(1 for line in old1.splitlines() if line.strip() and line in new1)
    assert kept > 0.6 * sum(1 for line in old1.splitlines() if line.strip()), (was, kept)


def test_the_compiled_runs_prompts_state_the_services_numbers_too():
    """As tests/test_open_lane.py checks of the kernel run's prompts: the numbers in the compiled run's words
    are the Lean service's own."""
    lean = Path(os.environ.get("COMPACT_PROOF_LEAN", "~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck")).expanduser()
    if not (lean / "scripts" / "accept.py").is_file():
        pytest.skip("the Lean project is not at COMPACT_PROOF_LEAN")
    import importlib.util

    spec = importlib.util.spec_from_file_location("lean_accept_policy_run", lean / "scripts" / "accept.py")
    accept = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(accept)
    if "compiled" not in getattr(accept, "RUNS", ()):
        pytest.skip("the Lean project there is from before its policy v15")
    fine, coarse = accept.LAST_BITS_LEVELS
    copies = len(accept.LAST_BITS_LEVELS + accept.LAST_BITS_RECORDED) * accept.LAST_BITS_COPIES
    words = {8: "eight", 9: "nine"}
    for name in ("open_lane_v7.md", "open_lane_formalization_v2.md", "open_lane_discovery_v2.md"):
        text = " ".join((PROMPTS / name).read_text().split())
        assert f"{accept.SIZE_BUDGET_BASE} + {accept.SIZE_BUDGET_PER_PARAM}E" in text, name
        assert f"at most {accept.SIZE_BUDGET_SHARE_CAP:,}; and never above {accept.SIZE_BUDGET_CAP:,}" in text, name
        assert f"moved by about 2^-{fine} or 2^-{coarse} of itself" in text, name
        assert f"at least {accept.LAST_BITS_KEEP} of what it certifies on the network" in text, name
        assert f"within {accept.GENERAL_KERNEL_BUDGET_MS // 1000} s" in text, name
        assert f"The run on the network and the {words[copies]} runs on copies get an hour together" in text and accept.CHECK_TIMEOUT_S == 3600
        assert f"A lean_check preview gives the {words[copies + 1]} runs two minutes" in text and accept.PREVIEW_LAST_BITS_S == 120
        for word in ("noncomputable", "implemented_by", "extern", "export", "csimp", "initialize"):
            assert f"`{word}`" in text, (name, word)


# the setting ----------------------------------------------------------------------------------------------
def _cfg(tmp_path, model: str = "tests/max2_ladder", **open_lane) -> dict:
    project = project_with_the_example(tmp_path)
    return {"run_id": "x", "model": model, "backend": "fake", "rule_set": ["single", "skip"],
            "prompt_template": "open_lane_v6", "rounds_max": 3, "runs_dir": str(tmp_path / "runs"),
            "open_lane": {"enabled": True, "lean_project": str(project), **open_lane}}


def test_the_setting_defaults_to_the_kernel_and_says_what_a_compiled_run_needs(tmp_path):
    """A config that does not say runs as before: an instance theorem, the kernel's templates and tools. A
    compiled run is a python_then_lean run, takes its worked example and notes from the model folder's
    `compiled` block (an example with an instance theorem would contradict its prompt, so a folder without the
    block is refused unless the run config names an example), and has no split example."""
    plain = merge(_cfg(tmp_path), source="plain")
    assert plain["open_lane"]["instance"] == "kernel" and not workflow.is_compiled(plain)
    assert plain["open_lane"]["example"].endswith("Max2TinyScored.lean") and "its instance is one theorem" in plain["open_lane"]["notes"]
    assert workflow.general_template(plain) == "open_lane_v6" and workflow.templates(plain) == workflow.TEMPLATES
    assert "instance" not in workflow.schedule(merge(_cfg(tmp_path, workflow_mode="python_then_lean", discovery_rounds=1), source="p"))
    with pytest.raises(RunConfigError, match="instance must be one of kernel, compiled"):
        merge(_cfg(tmp_path, instance="native"), source="bad")
    with pytest.raises(RunConfigError, match="compiled is for a python_then_lean run"):
        merge(_cfg(tmp_path, instance="compiled"), source="interleaved")
    cfg = merge(_cfg(tmp_path, instance="compiled", workflow_mode="python_then_lean", discovery_rounds=1,
                     split_example="examples/open_lane/attn_max2_tiny_scored/Candidate/AttnTinyScored.lean"), source="run")
    ol = cfg["open_lane"]
    assert ol["example"] == EXAMPLE and "its instance" not in ol["notes"] and "hold for any size" in " ".join(ol["notes"].split())
    assert ol["split_example"] is None
    assert workflow.is_compiled(cfg) and workflow.general_template(cfg) == "open_lane_v7"
    sched = workflow.schedule(cfg)
    assert sched["instance"] == "compiled" and sched["templates"] == {"discovery": "open_lane_discovery_v2",
                                                                        "formalization": "open_lane_formalization_v2"}
    # a model folder that names no example for such a run
    with pytest.raises(RunConfigError, match="needs a worked example without an instance theorem"):
        merge(_cfg(tmp_path, model="tests/max2_tiny", instance="compiled", workflow_mode="python_then_lean", discovery_rounds=1),
              source="no block")
    own = merge(_cfg(tmp_path, model="tests/max2_tiny", instance="compiled", workflow_mode="python_then_lean",
                     discovery_rounds=1, example=EXAMPLE), source="own example")
    assert own["open_lane"]["example"] == EXAMPLE and own["open_lane"]["notes"] == ""


def test_the_models_of_the_pilots_name_an_example_without_an_instance(tmp_path):
    """The two models a pilot has run on carry the block, and the example each names is one of the Lean
    project's examples of a proof whose run the service makes (checked against the project where it is)."""
    lean = Path(os.environ.get("COMPACT_PROOF_LEAN", "~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck")).expanduser()
    for model in ("models/max2", "models/attn-min2"):
        block = yaml.safe_load((REPO_ROOT / model / "config.yaml").read_text())["open_lane"]["compiled"]
        assert block["example"].startswith("examples/open_lane/") and block["example"].endswith("Run.lean")
        assert "instance" not in block["notes"] and "kernel" not in block["notes"]
        if (lean / block["example"]).is_file():
            text = (lean / block["example"]).read_text()
            assert "theorem D_sound" in text and "D_instance" not in text.split("-/", 1)[1] and "Target" not in text.split("-/", 1)[1]
            manifest = json.loads((lean / block["example"]).parents[1].joinpath("manifest.json").read_text())
            assert manifest["scored"]["run"] == "compiled" and "claimed_count" not in manifest and "instance" not in manifest["scored"]


def test_start_drafts_are_checked_when_the_config_is_read(tmp_path):
    (tmp_path / "Given.lean").write_text(COL)
    ok = {"path": "Candidate/Col.lean", "with": str(tmp_path / "Given.lean"), "note": "from an earlier run"}
    base = dict(workflow_mode="python_then_lean", discovery_rounds=1)
    assert merge(_cfg(tmp_path, start_drafts=[ok], **base), source="ok")["open_lane"]["start_drafts"] == [ok]
    for bad, why in (([{**ok, "path": "Col.lean"}], "must be a list of"), ([ok, ok], "names a module twice"),
                     ([{**ok, "scored": {"checker": "Candidate.Col.D"}}], "must be a list of"),
                     ([{**ok, "scored": {**SCORED, "claimed_bill": 1}}], "must be a list of")):
        with pytest.raises(RunConfigError, match=why):
            merge(_cfg(tmp_path, start_drafts=bad, instance="compiled", **base), source="bad")
    with pytest.raises(RunConfigError, match="`scored` names a checker for the service to run"):
        merge(_cfg(tmp_path, start_drafts=[{**ok, "scored": SCORED}], **base), source="kernel")
    with pytest.raises(RunConfigError, match="is for a run that starts afresh"):
        merge(_cfg(tmp_path, start_drafts=[ok], continue_from="earlier", **base), source="continues")
    merge(_cfg(tmp_path, start_drafts=[{**ok, "scored": {**SCORED, "plan": [1, 2]}}], instance="compiled", **base), source="scored")


# the tools ------------------------------------------------------------------------------------------------
def test_the_tools_of_a_compiled_run_take_no_claimed_count_and_no_instance():
    """The same tools under the same names. In a compiled run lean_check needs a path and a network, and
    submit_candidate a network and modules: a checker with its soundness theorem in `scored`, or a lemma. Their
    texts speak of the run and of no claim; the kernel run's tables are untouched."""
    assert tool_table(False, False) is Session.TOOLS and tool_table(True, False) is RESEARCH_TOOLS
    for research in (False, True):
        t, was = tool_table(research, True), tool_table(research, False)
        assert list(t) == list(was)
        check, submit = t["lean_check"], t["submit_candidate"]
        assert "claimed_count" not in check["schema"]["properties"] and check["schema"]["required"] == ["path", "network"]
        assert set(was["lean_check"]["schema"]["properties"]) - set(check["schema"]["properties"]) == {"claimed_count"}
        assert "`run`: the count the compiled D certifies on the network" in check["description"]
        assert "claimed" not in check["description"] and "Protected.N_<network>:" in check["description"]
        assert submit["schema"]["required"] == ["network", "modules"] and "claimed_count" not in submit["schema"]["properties"]
        assert "you claim no count and prove nothing about the run" in submit["description"]
        assert "Target" not in json.dumps(submit) and "instance" not in json.dumps(submit) and "claimed_bill" not in json.dumps(submit)
        for name in set(t) - {"lean_check", "submit_candidate"}:
            assert t[name] == was[name]
        assert "claimed_count" in was["lean_check"]["schema"]["required"] and "theorem : Target" in was["submit_candidate"]["description"]
    assert "In the discovery phase only lemmas" in tool_table(True, True)["submit_candidate"]["description"]


# the lock -------------------------------------------------------------------------------------------------
def submission(path: Path, modules: dict, scored: dict) -> Path:
    for rel, text in modules.items():
        (path / rel).parent.mkdir(parents=True, exist_ok=True)
        (path / rel).write_text(text)
    (path / "manifest.json").write_text(json.dumps({"schema": "open-lane-candidate-v1", "kind": "performance",
                                                    "model": "tests/max2_ladder", "network": A, "modules": list(modules),
                                                    "scored": scored}))
    return path


def test_a_proof_without_an_instance_is_locked_whole(tmp_path, monkeypatch):
    """A proof the service ran has no instance to keep apart: its checker's module, and what that imports, is
    the lock, in one module as well as in several (a kernel proof in one module cannot be locked). A module the
    checker does not use stays free. The lock says which kind of proof it is and names no instance."""
    monkeypatch.setattr(inspect, "inspect_submission", inspect_run)
    scored = {**SCORED, "run": "compiled"}
    lock = read_lock(submission(tmp_path / "one", {"Candidate/Col.lean": COL}, scored), Path("/nowhere"))
    assert list(lock["modules"]) == ["Candidate/Col.lean"] and lock["free"] == [] and lock["instance"] is None and lock["run"] == "compiled"
    assert lock["protected_modules"] == {"claim": NA + "_c0", "network": NA, "certificate": None, "plan": None}
    deep = {"Candidate/Lemmas.lean": "theorem l : True := trivial\n", "Candidate/Col.lean": "import Candidate.Lemmas\n" + COL,
            "Candidate/Notes.lean": "theorem aside : True := trivial\n"}
    lock = read_lock(submission(tmp_path / "deep", deep, scored), Path("/nowhere"))
    assert sorted(lock["modules"]) == ["Candidate/Col.lean", "Candidate/Lemmas.lean"] and lock["free"] == ["Candidate/Notes.lean"]
    assert lockable(tmp_path / "deep", Path("/nowhere")) is None
    # the same modules as a kernel proof need an instance, declared apart
    assert "does not name a checker, a soundness theorem and an instance" in lockable(
        submission(tmp_path / "kernel", {"Candidate/Col.lean": COL}, SCORED), Path("/nowhere"))


# a whole run ----------------------------------------------------------------------------------------------
NOTE = "accepted by an earlier version of the service, adapted to today's library"
ROUND_1 = {"calls": [
    call("lean_check", path="Candidate/Col.lean", edits=[], network=A, checker="Candidate.Col.D"),
    # the kernel run's submission, three ways: each refused before a submission is spent
    call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.Col.performance", modules=["Candidate/Col.lean"],
         scored=SCORED),
    call("submit_candidate", network=A, modules=["Candidate/Col.lean"],
         scored={**SCORED, "instance": "Candidate.Col.D_instance", "claimed_bill": 20000}),
    call("submit_candidate", network=A, modules=["Candidate/Col.lean"], theorem="Candidate.Col.performance", scored=SCORED),
    call("submit_candidate", network=A, modules=["Candidate/Col.lean"]),
    call("submit_candidate", network=A, modules=["Candidate/Col.lean"], scored=SCORED),
    call("submit_candidate", network=A, modules=["Candidate/Col.lean"], theorem="Candidate.Col.D_sound", kind="auxiliary"),
], "response": "CLAIM: 576 of 576.\nWHY IT HELPS: columns.\nNOTES: none."}
SEED_CHECK = {"calls": [
    call("lean_check", path="Candidate/Col.lean", source=COL.replace("pure I.nzero", "pure (I.nofNat 576)"), network=B),
    call("lean_check", path="Candidate/Col.lean", edits=[], network=B, checker="Candidate.Col.D", certificate=[1, 2]),
    call("submit_candidate", network=B, modules=["Candidate/Col.lean"], scored={**SCORED, "checker": "Candidate.Other.D"}),
    call("submit_candidate", network=B, modules=["Candidate/Col.lean"], scored={**SCORED, "certificate": [1, 2]}),
], "response": "CLAIM: 570 of 576.\nWHY IT HELPS: six inputs differ.\nNOTES: none."}
SCALING = {"calls": [
    call("submit_candidate", network=A, modules=["Candidate/Col.lean"], scored=SCORED),
    call("lean_check", path="Candidate/Growth.lean", source="import Candidate.Col\nnamespace Candidate.Growth\ntheorem bill_fixed : True := trivial\nend Candidate.Growth\n", network=A),
    call("submit_candidate", network=A, modules=["Candidate/Growth.lean"], theorem="Candidate.Growth.bill_fixed", kind="auxiliary"),
], "response": "CLAIM: quadratic against cubic.\nWHY IT HELPS: bill_fixed proves a.\nNOTES: none."}


def test_a_compiled_run_from_a_given_module_through_the_seed_check(tmp_path, monkeypatch):
    """One formalization round, the seed check and the scaling question, on stand-ins.

    The run starts from a module it is given (open_lane.start_drafts): the first session finds it in its
    workspace, listed apart with the person's note, and compiles it as saved; lean_check's answer holds the run.
    A submission worded as a kernel run's (a claimed count, a theorem, an instance, a bill) is refused by the
    session, with the reason, before the service is asked; the run's own submission goes out with `run:
    compiled` and without a claimed count or a theorem, and comes back with the count the service's run gave.
    The record says who ran the checker. The proof is locked whole. The seed check's session writes no Lean: it
    cannot save over the checker, compiles it as it is to see the run on the second network, and submits a
    certificate; the locked text reaches the service with the network's module renamed and nothing else. The
    report says how the count was established. A resumed run adds nothing."""
    (tmp_path / "Given.lean").write_text(COL)
    path = compiled_run(tmp_path, monkeypatch, [ROUND_1, SEED_CHECK, SCALING], seed_check={"network": B}, scaling=True,
                        start_drafts=[{"path": "Candidate/Col.lean", "with": str(tmp_path / "Given.lean"), "note": NOTE,
                                       "scored": SCORED}])
    lines: list[str] = []
    ctx = loop.start(path, log=lines.append)
    loop.drive(ctx)
    run = ctx.run
    assert run.done_rounds() == [0, 1, 2, 3], lines[-8:]
    # the first session: a compiled run's, with the given module as a draft and the prompt of its kind
    first = json.loads((run.round_path(1) / "attempt_0" / "open_lane" / "session.json").read_text())
    assert first["instance"] == "compiled" and first["workflow"]["phase"] == "formalization"
    assert [(d["path"], d["given"], d["note"], d["set_apart"]) for d in first["drafts"]] == [("Candidate/Col.lean", True, NOTE, False)]
    p1 = run.read(1, "prompt.md")
    assert run.read(1, "meta.json")["prompt"]["template"] == "open_lane_formalization_v2"
    assert "Modules this run was given to start from." in p1 and f"- Candidate/Col.lean ({len(COL.splitlines())} lines): {NOTE}" in p1
    assert "Your unfinished work, as your last session left it" not in p1
    for word in ("D_instance", "claimed_count", "theorem : Target", "claimed_bill"):
        assert word not in p1, word
    assert "-- brute force, its checker and soundness theorem alone" in p1 and "You then give only a new certificate and plan" in p1
    assert "namespace Protected.N_<network>     -- for example" in p1 and "_c<claimed>" not in p1
    assert workflow.recorded(run.path)["schedule"]["instance"] == "compiled"
    # its tools
    log, said = tool_log(run, 1), answers(run, 1)
    seen = log[0]["outcome"]
    assert seen["ok"] and seen["scoring_preview"]["run"] == {"count": 576, "bill": 20000, "length": 20448}, seen
    assert "submit_candidate does not take ['claimed_count']" in said[1]["error"]
    assert "scored does not take ['claimed_bill', 'instance'] in this run" in said[2]["error"]
    assert "a submission's theorem is its soundness theorem" in said[3]["error"]
    assert "a submission names your checker and its soundness theorem" in said[4]["error"]
    assert [a["ok"] for a in said] == [True, False, False, False, False, True, True]
    assert (log[4]["outcome"]["status"], log[4]["outcome"]["certified"], log[4]["outcome"]["length"]) == ("accepted", 576, 20448)
    assert log[5]["outcome"]["status"] == "accepted" and len(log) == 6
    assert run.read(1, "attempt_0/response_meta.json")["tools_used"]["submit_candidate"] == 2  # the refusals cost none
    sub = run.round_path(1) / "attempt_0" / "open_lane" / "submissions"
    manifest = json.loads((sub / "000" / "manifest.json").read_text())
    assert manifest["scored"] == {**SCORED, "run": "compiled"} and "claimed_count" not in manifest and "theorem" not in manifest
    lemma = json.loads((sub / "001" / "manifest.json").read_text())
    assert lemma["theorem"] == "Candidate.Col.D_sound" and "scored" not in lemma and "claimed_count" not in lemma
    # the records
    records = run.read_archive()
    ok = [r for r in records if r["status"] == "ok" and r.get("lane") == "open" and not r.get("stage")]
    assert len(ok) == 1 and (ok[0]["run"], ok[0]["claimed_count"], ok[0]["certified"], ok[0]["length"]) == ("compiled", None, 576, 20448)
    assert ok[0]["theorem"] == "Candidate.Col.D_sound"
    # the lock: the whole proof
    state = stages.read_state(run)
    locked = state["locked"]
    assert locked["record_id"] == ok[0]["record_id"] and locked["modules"] == ["Candidate/Col.lean"] and locked["free"] == []
    # the seed check: nothing to write, the checker as it was, renamed for the second network
    p2 = run.read(2, "prompt.md")
    assert run.read(2, "meta.json")["prompt"]["template"] == "open_lane_v7"
    assert "YOURS TO GIVE" in p2 and "there is nothing to prove here and no count to claim" in p2 and "D_instance" not in p2
    assert "to read and adapt" not in p2 and f"scored.checker\nCandidate.Col.D and scored.sound Candidate.Col.D_sound" in p2
    second = json.loads((run.round_path(2) / "attempt_0" / "open_lane" / "session.json").read_text())
    assert second["instance"] == "compiled" and second["stage"]["name"] == "seed_check" and "workflow" not in second
    log2 = tool_log(run, 2)
    assert "Candidate/Col.lean is locked" in log2[0]["outcome"]["error"] and "give `edits: []`" in log2[0]["outcome"]["error"]
    assert log2[1]["outcome"]["ok"] and log2[1]["outcome"]["scoring_preview"]["run"] == {"count": 570, "bill": 20000, "length": 20450}
    assert "scored.checker must be Candidate.Col.D" in log2[2]["outcome"]["error"]
    assert log2[3]["outcome"]["status"] == "accepted" and log2[3]["outcome"]["locked_checker"] is True
    sent = run.round_path(2) / "attempt_0" / "open_lane" / "submissions" / "000"
    assert (sent / "Candidate" / "Col.lean").read_text() == COL.replace(NA, NB)
    assert json.loads((sent / "manifest.json").read_text())["scored"] == {**SCORED, "certificate": [1, 2], "run": "compiled"}
    result = state["stages"]["seed_check"]["result"]
    assert (result["outcome"], result["certified"], result["length"], result["lock_verified"]) == ("certified", 570, 20450, True)
    # the scaling question: lemmas only, in the compiled run's words
    p3 = run.read(3, "prompt.md")
    assert "its bill is the number the service's run gave" in " ".join(p3.split()) and "your instance" not in p3
    said3 = answers(run, 3)
    assert "this session takes lemmas only" in said3[0]["error"] and said3[2]["status"] == "accepted", said3
    # what a person reads
    from core.report import build_report

    report = build_report(run.path).read_text()
    assert "the count and the bill of a scored proof are those of the service's own run of the compiled checker" in report
    assert "`Candidate.Col.D_sound` on " + A in report and "run by the service with compiled code" in report
    # the next session's list of what was submitted names no claim
    from core.open_lane.prompt import receipts_text

    listed = receipts_text(records, loop.select_networks(ctx.folder, ctx.cfg), ctx.cfg["metric"])
    assert f"- round 1 submission 0: {A}: ok, certified 576, length 20,448 (bill 20,000)" in listed and "claimed" not in listed
    before = len(records)
    ctx2 = loop.resume(run.path, log=lines.append)
    loop.drive(ctx2)
    assert len(run.read_archive()) == before


def test_a_kernel_run_is_as_it_was(tmp_path, monkeypatch):
    """The same stand-in run without the setting: the kernel's template and tools, a claimed count in the
    manifest, no `instance` in the session and no `run` asked of the service."""
    from tests.test_stages import GENERAL, INSTANCE
    from tests.test_stages import SCORED as KERNEL_SCORED
    from tests.test_stages import fake_service

    round_1 = {"calls": [
        call("lean_check", path="Candidate/Col.lean", source=GENERAL, network=A, claimed_count=576),
        call("lean_check", path="Candidate/ColRun.lean", source=INSTANCE, network=A, claimed_count=576),
        call("lean_check", path="Candidate/ColRun.lean", edits=[], network=A),
        call("submit_candidate", network=A, modules=["Candidate/ColRun.lean"], scored=KERNEL_SCORED),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.ColRun.performance",
             modules=["Candidate/ColRun.lean"], scored=KERNEL_SCORED),
    ], "response": "CLAIM: 576.\nWHY IT HELPS: -\nNOTES: none."}
    discovery = {"calls": [], "response": "CLAIM: -\nWHY IT HELPS: -\nNOTES: none."}
    path = compiled_run(tmp_path, monkeypatch, [discovery, round_1], rounds_max=2, discovery_rounds=1, instance="kernel")
    monkeypatch.setattr(Session, "_service", fake_service(448))
    ctx = loop.start(path, log=lambda *a: None)
    loop.drive(ctx)
    run = ctx.run
    session = json.loads((run.round_path(2) / "attempt_0" / "open_lane" / "session.json").read_text())
    assert "instance" not in session and run.read(2, "meta.json")["prompt"]["template"] == "open_lane_formalization_v1"
    assert run.read(1, "meta.json")["prompt"]["template"] == "open_lane_discovery_v1"
    assert "instance" not in workflow.recorded(run.path)["schedule"]
    said = answers(run, 2)
    assert "lean_check needs ['claimed_count']" in said[2]["error"]
    assert "submit_candidate needs ['claimed_count', 'theorem']" in said[3]["error"]
    manifest = json.loads((run.round_path(2) / "attempt_0" / "open_lane" / "submissions" / "000" / "manifest.json").read_text())
    assert manifest["claimed_count"] == 576 and manifest["theorem"] == "Candidate.ColRun.performance" and "run" not in manifest["scored"]
    ok = [r for r in run.read_archive() if r["status"] == "ok" and r.get("lane") == "open"]
    assert len(ok) == 1 and "run" not in ok[0] and ok[0]["claimed_count"] == 576


# the dry start --------------------------------------------------------------------------------------------
def test_a_dry_start_compiles_runs_and_submits_what_the_run_is_given(tmp_path, monkeypatch):
    """Before a run that starts from a given module: the dry start compiles it in the first round's workspace,
    reports the run the service makes of the checker the config names, and with --check submits it. A module
    that does not compile, or a checker the service refuses to score, is NOT READY. The session is one that
    takes proofs whatever the run's first round is (here a discovery round)."""
    from core.open_lane import dry_start

    (tmp_path / "Given.lean").write_text(COL)
    start = [{"path": "Candidate/Col.lean", "with": str(tmp_path / "Given.lean"), "note": NOTE, "scored": SCORED}]
    path = compiled_run(tmp_path, monkeypatch, [], rounds_max=2, discovery_rounds=1, start_drafts=start)

    def go(check: bool, **over) -> tuple[int, str]:
        lines: list[str] = []
        cfg = load_run_config(path, overrides=over or None)
        return dry_start.run(cfg, check, False, lines.append), "\n".join(lines)

    status, text = go(False)
    assert status == 0, text
    assert "the run starts from the 1 module(s) it is given (open_lane.start_drafts)" in text
    assert "the start draft Candidate/Col.lean compiles" in text and "its checker's run: 576 inputs, bill 20,000, length 20,448" in text
    assert "the last-bits test passes" in text and "submitting" not in text
    assert "READY: the modules the run is given to start from compile in the first round's workspace" in text
    status, text = go(True)
    assert status == 0, text
    assert "submitting Candidate.Col.D, as the agent would" in text
    assert "accepted and scored: 576 inputs, length 20,448" in text and "the run made by the service with compiled code" in text
    assert "and the checker among them is accepted and scored" in text
    assert not (tmp_path / "runs" / dry_start.FOLDER).exists()

    def broken(self, args, timeout_s):
        if args[0] == "compile":
            return {"ok": False, "messages": "Candidate/Col.lean:3:0: error: unknown constant", "seconds": 2.0}
        raise AssertionError("nothing is submitted when the module does not compile")

    monkeypatch.setattr(Session, "_service", broken)
    status, text = go(True)
    assert status == 1 and "NOT READY: the start draft Candidate/Col.lean does not compile" in text and "unknown constant" in text
    assert "READY: " not in text.replace("NOT READY: ", "")


# against the real Lean service, where it is built ------------------------------------------------------------
LEAN = Path(os.environ.get("COMPACT_PROOF_LEAN", "~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck")).expanduser()
HAVE_LEAN = ((LEAN / "scripts" / "accept.py").is_file() and (LEAN / ".lake" / "build" / "bin" / "acceptcheck").is_file()
             and (LEAN / EXAMPLE).is_file())


@pytest.mark.real_surface
@pytest.mark.skipif(not HAVE_LEAN, reason="the Lean project at policy v15 with a built acceptcheck is not at COMPACT_PROOF_LEAN")
def test_a_compiled_run_against_the_real_lean_service(tmp_path, monkeypatch):
    """The real service and Lean's real account of what was compiled. The run is given brute force written
    against the first network's module (the Lean project's example of a proof whose run the service makes, with
    the network's name put in). Round 1 compiles it as saved, sees the run in lean_check's answer, and submits:
    accepted, scored, the count and the bill those of the service's run, which nobody claimed. The seed check
    locks the whole proof, compiles it for the second seed and submits with no Lean written; Lean finds the
    locked checker in what the service compiled there."""
    given = (LEAN / EXAMPLE).read_text().replace("N_max2_tiny_v8_s0", NA).replace("Max2TinyRun", "Brute")
    (tmp_path / "Brute.lean").write_text(given)
    scored = {"checker": "Candidate.Brute.D", "sound": "Candidate.Brute.D_sound", "certificate": []}
    round_1 = {"calls": [
        call("lean_check", path="Candidate/Brute.lean", edits=[], network=A, checker="Candidate.Brute.D"),
        call("submit_candidate", network=A, modules=["Candidate/Brute.lean"], scored=scored),
    ], "response": "CLAIM: 576.\nWHY IT HELPS: -\nNOTES: -"}
    seed_check = {"calls": [
        call("lean_check", path="Candidate/Brute.lean", edits=[], network=B, checker="Candidate.Brute.D"),
        call("submit_candidate", network=B, modules=["Candidate/Brute.lean"], scored=scored),
    ], "response": "CLAIM: all of them.\nWHY IT HELPS: -\nNOTES: -"}
    paths = []
    for i, sc in enumerate((round_1, seed_check)):
        p = tmp_path / f"s{i}.json"
        p.write_text(json.dumps(sc))
        paths.append(str(p))
    cfg = {"run_id": "run-lean", "model": "tests/max2_ladder", "networks": [A], "backend": "fake", "rule_set": ["single", "skip"],
           "prompt_template": "open_lane_v6", "baselines": False, "rounds_max": 1, "patience": 1,
           "runs_dir": str(tmp_path / "runs"), "sandbox": "auto", "workers": 1,
           "open_lane": {"enabled": True, "lean_project": str(LEAN), "work_dir": str(tmp_path / "work"), "fake_scripts": paths,
                         "workflow_mode": "python_then_lean", "discovery_rounds": 0, "instance": "compiled",
                         "seed_check": {"network": B},
                         "start_drafts": [{"path": "Candidate/Brute.lean", "with": str(tmp_path / "Brute.lean"), "scored": scored}]}}
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    lines: list[str] = []
    ctx = loop.start(path, log=lines.append)
    loop.drive(ctx)
    run = ctx.run
    assert run.done_rounds() == [0, 1, 2], lines[-8:]
    log = tool_log(run, 1)
    seen = log[0]["outcome"]
    assert seen["ok"] and seen["scoring_preview"]["counted_language"] == "ok", seen
    assert seen["scoring_preview"]["run"]["count"] == 576 and seen["scoring_preview"]["last_bits"]["passes"] is True, seen
    assert log[1]["outcome"]["status"] == "accepted" and log[1]["outcome"]["scoring"] == "scored", log[1]
    receipt = json.loads((run.round_path(1) / "attempt_0" / "open_lane" / "submissions" / "000" / "receipt.json").read_text())
    assert (receipt["run"], receipt["execution_assurance"], receipt["certified_count"]) == ("compiled", "compiled_instance", 576)
    assert receipt["scoring"]["bill"] == seen["scoring_preview"]["run"]["bill"]
    assert receipt["scoring"]["length"] == seen["scoring_preview"]["run"]["length"] and receipt["scoring"]["last_bits"]["passed"] is True
    ok = [r for r in run.read_archive() if r["status"] == "ok" and r.get("lane") == "open" and not r.get("stage")]
    assert len(ok) == 1 and ok[0]["run"] == "compiled" and ok[0]["certified"] == 576 and ok[0]["claimed_count"] is None
    state = stages.read_state(run)
    assert state["locked"]["modules"] == ["Candidate/Brute.lean"] and state["locked"]["free"] == []
    sent = run.round_path(2) / "attempt_0" / "open_lane" / "submissions" / "000"
    assert (sent / "Candidate" / "Brute.lean").read_text() == given.replace(NA, NB)
    log2 = tool_log(run, 2)
    assert log2[0]["outcome"]["ok"] and log2[0]["outcome"]["scoring_preview"]["run"]["count"] > 0, log2[0]
    assert log2[1]["outcome"]["status"] == "accepted" and log2[1]["outcome"]["locked_checker"] is True, log2[1]
    result = state["stages"]["seed_check"]["result"]
    assert result["outcome"] == "certified" and result["lock_verified"] is True
    assert result["certified"] == log2[0]["outcome"]["scoring_preview"]["run"]["count"]


def test_a_dry_start_submits_a_carried_kernel_proof_without_its_instance(tmp_path, monkeypatch):
    """A compiled run that continues a kernel run: the best carried proof was accepted with an instance theorem,
    in modules of its own. The dry start submits what a compiled run submits of it: the modules its lock holds
    (the checker and its soundness proof), with the checker, the soundness theorem and the certificate. The
    service runs the checker; the instance modules stay behind."""
    from core.open_lane import dry_start
    from tests.test_continuation import CHILD, child_config, parent_run
    from tests.test_stages import fake_service

    monkeypatch.setattr(inspect, "inspect_submission", stand_in_inspect)
    parent_run(tmp_path, monkeypatch)
    monkeypatch.setattr(Session, "_service", fake_service(448))
    loop.drive(loop.start(child_config(tmp_path, "ptl-2", CHILD, "ptl", 2), log=lambda *a: None))  # a scored kernel proof to carry
    (tmp_path / "lean" / EXAMPLE).parent.mkdir(parents=True, exist_ok=True)
    (tmp_path / "lean" / EXAMPLE).write_text("-- brute force, its checker and soundness theorem alone")
    sent = []

    def service(self, args, timeout_s):
        if args[0] == "submit":
            sent.append(json.loads((Path(args[1]) / "manifest.json").read_text()))
        return run_service()(self, args, timeout_s)

    monkeypatch.setattr(Session, "_service", service)
    end = {"calls": [], "response": "CLAIM: none.\nWHY IT HELPS: -\nNOTES: none."}
    lines: list[str] = []
    cfg = load_run_config(child_config(tmp_path, "ptl-3", [end], "ptl-2", 1, instance="compiled"))
    status = dry_start.run(cfg, True, False, lines.append)
    text = "\n".join(lines)
    assert status == 0, text
    assert "the best carried scored proof: Candidate.ColRun.performance (576 inputs" in text
    assert "without its instance: the 1 modules of its checker and soundness proof" in text
    assert "accepted and scored: 576 inputs, length 20,448" in text and "the run made by the service with compiled code" in text
    assert len(sent) == 1 and sent[0]["modules"] == ["Candidate/Col.lean"] and "claimed_count" not in sent[0]
    assert sent[0]["scored"] == {"checker": "Candidate.Col.D", "sound": "Candidate.Col.D_sound", "certificate": [], "run": "compiled"}
