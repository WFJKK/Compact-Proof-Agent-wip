"""The linear networks on four tokens (models/max4 and models/min4, 18 November 2026): the max2 model on four
positions, at a size where brute force can be run (v16) and at the max2 model's v64 sizes, where it cannot
(16,777,216 inputs). The model folders, their zoos, the run configs and the probe the dry start is given."""

from __future__ import annotations

import json
from pathlib import Path

import numpy as np
import pytest
import yaml

from core import loop
from core.model_folder import load_model_folder
from core.open_lane import workflow
from core.open_lane.session import Session
from core.run_config import load_run_config
from core.util import REPO_ROOT, sha256_file
from core.zoo import networks, split_assignment
from tests.test_open_lane_compiled import project_with_the_example
from tests.test_stages import IDENT, call

MODELS = (("max4", "largest", np.max), ("min4", "smallest", np.min))
PILOT = REPO_ROOT / "config" / "pilot"


@pytest.mark.parametrize("name, what, fn", MODELS)
def test_the_model_is_the_max2_model_on_four_tokens(name, what, fn):
    """The same module as models/max2 (the tokens' one-hot vectors summed, three linear maps), four positions,
    two sizes; the label is the largest or the smallest token; max2's training but for the number of steps."""
    folder = load_model_folder(REPO_ROOT / "models" / name)
    assert (folder.path / "model.py").read_text() == (REPO_ROOT / "models" / "max2" / "model.py").read_text()
    assert folder.setting_names() == ["v16", "v64"]
    assert folder.sizes("v16") == {"n_ctx": 4, "d_vocab": 16, "d_model": 4} and folder.sizes("v64") == {"n_ctx": 4, "d_vocab": 64, "d_model": 8}
    assert folder.n_inputs("v16") == 65_536 and folder.n_inputs("v64") == 16_777_216
    assert f"the correct output is the {what} token" in folder.task.DESCRIPTION
    tokens = np.array([[3, 9, 1, 9], [0, 0, 0, 0], [15, 2, 7, 4]])
    assert list(folder.task.label(tokens, folder.sizes("v16"))) == list(fn(tokens, axis=1))
    max2 = yaml.safe_load((REPO_ROOT / "models" / "max2" / "config.yaml").read_text())
    own = folder.config
    assert {**own["training"], "steps": max2["training"]["steps"]} == max2["training"] and own["training"]["steps"] > max2["training"]["steps"]
    assert own["split"] == max2["split"] and own["seeds"] == max2["seeds"] and own["hygiene"] == max2["hygiene"]
    assert [p.name for p in sorted((folder.path / "baselines").glob("*.md"))] == ["01_brute_force.md"]


@pytest.mark.parametrize("name, what, fn", MODELS)
def test_its_zoo_is_trained_and_costed(name, what, fn):
    """Ten seeds at each size, every file as the manifest says. At v64 the networks are right on more than 99.7%
    of their 16,777,216 inputs and wrong on thousands, the mask is stored compressed, and brute force's length
    comes from the shapes: the max2 model's 1,088 weights, and a forward pass of 671 for every input. The two
    seeds the pilot names are development networks."""
    folder = load_model_folder(REPO_ROOT / "models" / name)
    manifest = json.loads(folder.manifest_path().read_text())
    entries = {n["id"]: n for n in manifest["networks"]}
    assert sorted(entries) == sorted(f"{name}-{s}-s{k}" for s in ("v16", "v64") for k in range(10))
    split = split_assignment(folder)
    for nid, e in entries.items():
        assert e["split"] == split[(e["setting"], e["seed"])]
        assert sha256_file(folder.zoo_dir() / e["weights"]) == e["sha256"] and (folder.zoo_dir() / e["correct"]).is_file()
        assert e["n_inputs"] == folder.n_inputs(e["setting"]) and e["real_correct"] == round(e["real_accuracy"] * e["n_inputs"])
        if e["setting"] == "v64":
            assert e["correct"].endswith(".correct.npz") and 0.997 < e["real_accuracy"] < 1 and e["n_inputs"] - e["real_correct"] > 1000
            assert (e["E"], e["B"]) == (1088, 1088 + 671 * 16_777_216)
        else:
            assert e["real_accuracy"] > 0.999 and e["E"] == 144 and e["B"] == e["E"] + e["n_inputs"] * ((e["B"] - e["E"]) // e["n_inputs"])
    assert entries[f"{name}-v64-s0"]["split"] == entries[f"{name}-v64-s1"]["split"] == "dev"
    assert len([e for e in networks(folder) if e["setting"] == "v64"]) == 6


@pytest.mark.parametrize("name, what, fn", MODELS)
def test_the_first_run_is_from_nothing_in_compiled_mode_and_its_dry_start_has_a_probe(name, what, fn, tmp_path):
    """config/pilot/linear-<name>-ptl-1.yaml: one network at v64, no baselines replayed, one discovery round and
    four formalization rounds, the checker's run made by the service, the reading on, nothing given to start
    from. Its dry start is a config of its own, which gives the same run a probe module: a file of this
    repository written for this network, with the checker and the soundness theorem the config names."""
    project = project_with_the_example(tmp_path)
    over = {"open_lane.lean_project": str(project)}
    cfg = load_run_config(PILOT / f"linear-{name}-ptl-1.yaml", overrides=over)
    ol = cfg["open_lane"]
    assert (cfg["run_id"], cfg["model"], cfg["networks"], cfg["baselines"]) == (f"linear-{name}-ptl-1", f"models/{name}", [f"{name}-v64-s0"], False)
    assert (cfg["metric"], cfg["rounds_max"], cfg["memory_limit_mb"]) == ("cost_of_finishing", 5, 4096)
    assert (ol["workflow_mode"], ol["instance"], ol["code_review"], ol["seed_check"], ol["scaling"], ol["start_drafts"]) == (
        "python_then_lean", "compiled", True, None, False, [])
    sched = workflow.schedule(cfg)
    assert sched["discovery_rounds"] == [1, 1] and sched["formalization_rounds"] == [2, 5] and sched["instance"] == "compiled"
    assert ol["example"].endswith("Max2TinyRun.lean") and "instance" not in ol["notes"] and "kernel" not in ol["notes"]
    assert "16,777,216" in ol["notes"] and "allInputs task.space" in ol["notes"]
    base = load_run_config(PILOT / f"linear-{name}.yaml", overrides=over)
    assert base["open_lane"]["seed_check"] == {"network": f"{name}-v64-s1"} and base["open_lane"]["instance"] == "kernel"
    assert "one theorem" in base["open_lane"]["notes"]

    dry = load_run_config(PILOT / f"linear-{name}-dry.yaml", overrides=over)
    (draft,) = dry["open_lane"]["start_drafts"]
    assert draft["path"] == "Candidate/Probe.lean" and draft["scored"] == {
        "checker": "Candidate.Probe.D", "sound": "Candidate.Probe.D_sound", "certificate": []}
    same = {k: v for k, v in dry["open_lane"].items() if k != "start_drafts"}
    assert same == {k: v for k, v in ol.items() if k != "start_drafts"} and dry["run_id"] == f"linear-{name}-dry"
    text = (REPO_ROOT / draft["with"]).read_text()
    module = f"N_{name}_v64_s0"
    assert text.startswith(f"import Protected.{module}\n") and f"open CompactCheck Protected.{module}" in text
    assert "def D : Checker" in text and "theorem D_sound" in text and "sorry" not in text
    assert "allInputs task.space" not in text.split("-/", 1)[1].split("theorem", 1)[0]  # the checker never builds the list of all inputs
    other = "min4" if name == "max4" else "max4"
    assert text.replace(module, f"N_{other}_v64_s0") == (PILOT / "start" / "linear4-probe" / other / "Probe.lean").read_text()


@pytest.mark.parametrize("name, what, fn", MODELS)
def test_a_run_on_the_large_network_starts_without_baselines(name, what, fn, tmp_path, monkeypatch, stand_in_surface):
    """The first run's config with the fake backend and stand-ins for Lean: round 0 replays nothing, the first
    session is a discovery session on the network of 16,777,216 inputs, its prompt gives the sizes and brute
    force's length and never names the paper, and the agent's Python has the network's weights. The run goes on
    to the first formalization round, and the report is written."""
    project = project_with_the_example(tmp_path)
    r1 = {"calls": [call("run_python", network=f"{name}-v64-s0", code=(
        "import numpy as np\n"
        "print(sorted((k, tuple(v.shape)) for k, v in weights.items()))\n"
        "print(info['sizes'], info['input_space'])\n"))],
        "response": "CLAIM: none yet.\nWHY IT HELPS: -\nNOTES: looked at the weights."}
    r2 = {"calls": [], "response": "CLAIM: nothing.\nWHY IT HELPS: -\nNOTES: none."}
    scripts = []
    for i, script in enumerate((r1, r2)):
        p = tmp_path / f"script_{i}.json"
        p.write_text(json.dumps(script))
        scripts.append(str(p))
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump({
        "extends": str(PILOT / f"linear-{name}-ptl-1.yaml"), "run_id": "run", "backend": "fake", "rounds_max": 2, "patience": 1,
        "runs_dir": str(tmp_path / "runs"), "workers": 1,
        "open_lane": {"lean_project": str(project), "work_dir": str(tmp_path / "work"), "fake_scripts": scripts}}))
    monkeypatch.setattr(loop, "check_lean_lock", lambda project: {})
    monkeypatch.setattr(loop, "check_inspection", lambda project: None)
    monkeypatch.setattr(loop, "lean_identity", lambda project, knowledge="minimal": dict(IDENT))
    monkeypatch.setattr(Session, "_service", lambda self, args, timeout_s: {"ok": True, "messages": ""})
    lines: list[str] = []
    ctx = loop.start(path, log=lines.append)
    loop.drive(ctx)
    run = ctx.run
    assert run.done_rounds() == [0, 1, 2], lines[-8:]
    assert [r for r in run.read_archive() if r.get("round") == 0] == []
    prompt = run.read(1, "prompt.md")
    assert run.read(1, "meta.json")["prompt"]["template"] == "open_lane_discovery_v2"
    assert "16,777,216" in prompt and "11,257,513,024" in prompt and f"the correct output is the {what} token" in prompt
    assert "allInputs task.space" in prompt and "Gross" not in prompt and "Compact Proofs" not in prompt
    session = json.loads((run.round_path(1) / "attempt_0" / "open_lane" / "session.json").read_text())
    assert session["networks"] == {f"{name}-v64-s0": {"setting": "v64", "n_inputs": 16_777_216}}
    assert session["instance"] == "compiled" and session["workflow"]["phase"] == "discovery"
    log = [json.loads(line) for line in (run.round_path(1) / "attempt_0" / "open_lane" / "tools.jsonl").read_text().splitlines()]
    out = json.dumps(log[0])
    assert "('embedding.weight', (8, 64))" in out and "('unembedding.weight', (64, 8))" in out, out
    assert "'n_ctx': 4" in out and "[64, 64, 64, 64]" in out
    from core.report import build_report

    report = Path(build_report(run.path)).read_text()
    assert f"- Model: `models/{name}`" in report and "metric cost_of_finishing" in report


@pytest.mark.parametrize("name, what, fn", MODELS)
def test_the_reference_script_counts_what_convexity_certifies(name, what, fn):
    """scripts/linear4_reference.py on a small network (65,536 inputs, every one right): the pure inputs certify
    every input there, at about a thousandth of brute force's length, and no argument certifies a wrong input
    (the script raises if one does). The numbers of docs/decisions/linear-four-tokens.md come from it at v64."""
    import importlib.util

    spec = importlib.util.spec_from_file_location("linear4_reference", REPO_ROOT / "scripts" / "linear4_reference.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    r = module.reference(load_model_folder(REPO_ROOT / "models" / name), f"{name}-v16-s3")
    assert (r["inputs"], r["right"], r["E"], r["B"], r["forward_pass"]) == (65_536, 65_536, 144, 7_274_640, 111)
    rows = {row["proof"]: row for row in r["rows"]}
    assert rows["pure inputs"]["certified"] == rows["doubled inputs"]["certified"] == 65_536 and r["left_multisets"] == 0
    assert rows["pure inputs"]["length"] == 16 * 4 * (4 + 16) + 120 * 15 * 3 + 16 * 15 + 144 == 7_064
    assert 1000 < rows["pure inputs"]["B_over_length"] < 1100 and rows["every multiset"]["length"] > rows["doubled inputs"]["length"]

