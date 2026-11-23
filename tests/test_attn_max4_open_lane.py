"""The attention max-of-4 network at the paper's own size in the open lane (23 November 2026): models/attn-max4 at
v64 (one layer, one head, attention only, vocabulary size 64, width 32, four positions, 16,777,216 inputs), the
first run's config and its dry start's probe."""

from __future__ import annotations

import json
from pathlib import Path

import yaml

from core import loop
from core.model_folder import load_model_folder
from core.open_lane import workflow
from core.open_lane.session import Session
from core.run_config import load_run_config
from core.util import REPO_ROOT
from core.zoo import network_entry
from tests.test_open_lane_compiled import project_with_the_example
from tests.test_stages import IDENT, call

PILOT = REPO_ROOT / "config" / "pilot"
NAME = "attn-max4"
ATTENTION_FILES = ("examples/open_lane/attn_max2_tiny_run/Candidate/AttnTinyRun.lean",
                   "examples/open_lane/attn_max2_tiny_scored/Candidate/AttnTinyScored.lean",
                   "CompactCheck/CountedGeneral.lean", "CompactCheck/CountedGeneralSound.lean", "CompactCheck/ExpSound.lean")


def project_with_attention(tmp_path: Path) -> Path:
    """The stand-in Lean project with the files an attention run names (its worked examples and the general
    rule's sources), as placeholders."""
    project = project_with_the_example(tmp_path)
    for rel in ATTENTION_FILES:
        (project / rel).parent.mkdir(parents=True, exist_ok=True)
        (project / rel).write_text(f"-- {rel}, standing in")
    return project


def test_the_paper_size_run_is_from_nothing_in_compiled_mode_and_its_dry_start_has_a_probe(tmp_path):
    """config/pilot/attn-max4-ptl-1.yaml: the paper's size, one network, no baselines replayed, one discovery round
    and four formalization rounds of 90 minutes, the checker's run made by the service, the reading on, nothing
    given to start from. The base config's seed check is on a development seed. The dry start is a config of its
    own that gives the same run a probe module: the general single rule (`I.gsingle`) on 64 inputs, written for
    this network, which never builds the list of all inputs."""
    project = project_with_attention(tmp_path)
    over = {"open_lane.lean_project": str(project)}
    folder = load_model_folder(REPO_ROOT / "models" / NAME)
    assert folder.sizes("v64") == {"n_ctx": 4, "d_vocab": 64, "d_model": 32, "d_head": 32} and folder.n_inputs("v64") == 16_777_216
    cfg = load_run_config(PILOT / f"{NAME}-ptl-1.yaml", overrides=over)
    ol = cfg["open_lane"]
    assert (cfg["run_id"], cfg["model"], cfg["networks"], cfg["baselines"]) == (f"{NAME}-ptl-1", f"models/{NAME}", [f"{NAME}-v64-s0"], False)
    assert (cfg["metric"], cfg["rounds_max"], cfg["memory_limit_mb"], cfg["api_budget"]) == (
        "cost_of_finishing", 5, 4096, {"run_usd": 200, "round_usd": 40})
    assert (ol["workflow_mode"], ol["instance"], ol["worker_seconds"], ol["code_review"], ol["seed_check"], ol["scaling"], ol["start_drafts"]) == (
        "python_then_lean", "compiled", 5400, True, None, False, [])
    sched = workflow.schedule(cfg)
    assert sched["discovery_rounds"] == [1, 1] and sched["formalization_rounds"] == [2, 5] and sched["instance"] == "compiled"
    assert ol["example"].endswith("AttnTinyRun.lean") and "instance" not in ol["notes"] and "kernel" not in ol["notes"]
    assert "16,777,216" in ol["notes"] and "allInputs task.space" in ol["notes"] and "width 32" in ol["notes"]
    assert "CompactCheck/CountedGeneralSound.lean" in ol["extra_sources"]
    base = load_run_config(PILOT / f"{NAME}.yaml", overrides=over)
    assert base["open_lane"]["seed_check"] == {"network": f"{NAME}-v64-s2"} and base["open_lane"]["instance"] == "kernel"
    assert "one theorem" in base["open_lane"]["notes"] and base["open_lane"]["example"].endswith("AttnTinyScored.lean")
    for nid in (f"{NAME}-v64-s0", f"{NAME}-v64-s2"):
        assert network_entry(folder, nid)["split"] == "dev"

    dry = load_run_config(PILOT / f"{NAME}-dry.yaml", overrides=over)
    (draft,) = dry["open_lane"]["start_drafts"]
    assert draft["path"] == "Candidate/Probe.lean" and draft["scored"] == {
        "checker": "Candidate.Probe.D", "sound": "Candidate.Probe.D_sound", "certificate": []}
    same = {k: v for k, v in dry["open_lane"].items() if k != "start_drafts"}
    assert same == {k: v for k, v in ol.items() if k != "start_drafts"} and dry["run_id"] == f"{NAME}-dry"
    text = (REPO_ROOT / draft["with"]).read_text()
    module = "N_attn_max4_v64_s0"
    assert text.startswith(f"import Protected.{module}\n") and f"open CompactCheck Protected.{module}" in text
    assert "import CompactCheck.CountedGeneralSound" in text and "I.gsingle g task x" in text and "CostM.gsingle_correct hs" in text
    assert "def D : Checker" in text and "theorem D_sound" in text and "sorry" not in text
    assert "allInputs task.space" not in text.split("-/", 1)[1].split("theorem", 1)[0]  # the checker never builds the list of all inputs


def test_a_run_on_the_paper_size_network_starts_without_baselines(tmp_path, monkeypatch, stand_in_surface):
    """The first run's config with the fake backend and stand-ins for Lean: round 0 replays nothing, the first
    session is a discovery session, its prompt gives the sizes, the task and brute force's length and never names
    the paper, and the agent's Python has the network's seven weight matrices. The run goes on to the first
    formalization round, and the report is written."""
    project = project_with_attention(tmp_path)
    r1 = {"calls": [call("run_python", network=f"{NAME}-v64-s0", code=(
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
        "extends": str(PILOT / f"{NAME}-ptl-1.yaml"), "run_id": "run", "backend": "fake", "rounds_max": 2, "patience": 1,
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
    assert "16,777,216" in prompt and "220,771,393,664" in prompt and "the correct output is the largest token" in prompt
    assert "allInputs task.space" in prompt and "Gross" not in prompt and "Compact Proofs" not in prompt
    session = json.loads((run.round_path(1) / "attempt_0" / "open_lane" / "session.json").read_text())
    assert session["networks"] == {f"{NAME}-v64-s0": {"setting": "v64", "n_inputs": 16_777_216}}
    assert session["instance"] == "compiled" and session["workflow"]["phase"] == "discovery"
    log = [json.loads(line) for line in (run.round_path(1) / "attempt_0" / "open_lane" / "tools.jsonl").read_text().splitlines()]
    out = json.dumps(log[0])
    for name, shape in (("E", (64, 32)), ("P", (4, 32)), ("WQ", (32, 32)), ("WO", (32, 32)), ("U", (32, 64))):
        assert f"('{name}', {shape})" in out, out
    assert "'d_model': 32" in out and "[64, 64, 64, 64]" in out
    from core.report import build_report

    report = Path(build_report(run.path)).read_text()
    assert f"- Model: `models/{NAME}`" in report and "metric cost_of_finishing" in report
