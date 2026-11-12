"""The python_then_lean workflow (core/open_lane/workflow.py): a fixed schedule of discovery rounds (Python and
arguments, a research folder, a small Lean allowance) and formalization rounds, on stand-ins for the Lean
project and its service, with the fake backend; and once against the real Lean service where it is built.

Each test names the case of the specification it shows (docs/OPEN_LANE.md, "Choosing a workflow")."""

from __future__ import annotations

import copy
import json
import os
from pathlib import Path

import pytest
import yaml

from core import loop
from core.archive import RunDir
from core.open_lane import research, stages, workflow
from core.open_lane.session import RESEARCH_TOOLS, Session, ToolError
from core.run_config import RunConfigError, load_run_config, merge
from core.util import REPO_ROOT
from tests.test_stages import (A, GENERAL, IDENT, INSTANCE, SCALING, SCORED, SEED_CHECK, call, fake_project, fake_service,
                               stand_in_inspect)

NET = "max2_tiny-v8-s0"


@pytest.fixture(autouse=True)
def _stand_ins(request, monkeypatch):
    if request.node.get_closest_marker("real_surface") is None:
        request.getfixturevalue("stand_in_surface")
    from core.open_lane import inspect

    monkeypatch.setattr(inspect, "inspect_submission", stand_in_inspect)


CANDIDATE = {"id": "c001", "title": "The larger token's column decides", "mechanism_claim": "logits are column sums",
             "proof_sketch": "bound the gap per pair of columns", "predictions": ["gap > 0 off the diagonal"],
             "experiment_refs": ["Research/results/margins.json"], "counterexamples": [], "estimated_coverage": 4096,
             "estimated_cost": 1, "cost_estimation_method": "a guess", "unresolved_questions": [], "agent_assessment": "promising"}
PROBE = """import Protected.N_max2_ladder_n2v24d8_s0_c576

namespace Candidate.Probe

theorem gap_def : True := trivial

end Candidate.Probe
"""


def ptl_run(tmp_path: Path, monkeypatch, scripts: list[dict], rounds_max: int, discovery_rounds: int, service=None,
            **open_lane) -> Path:
    """A python_then_lean run on the pilot's base, for two seeds of a small size, as tests/test_stages.py's
    pilot_run: the fake backend plays `scripts` (one per session), stand-ins answer for Lean and its service."""
    project = fake_project(tmp_path)
    paths = []
    for i, script in enumerate(scripts):
        p = tmp_path / f"script_{i}.json"
        p.write_text(json.dumps(script))
        paths.append(str(p))
    cfg = {"extends": str(REPO_ROOT / "config" / "pilot" / "base.yaml"), "run_id": "ptl", "model": "tests/max2_ladder",
           "networks": [A], "backend": "fake", "rounds_max": rounds_max, "patience": 1, "runs_dir": str(tmp_path / "runs"),
           "workers": 1,
           "open_lane": {"lean_project": str(project), "work_dir": str(tmp_path / "work"), "fake_scripts": paths,
                         "seed_check": {"network": "max2_ladder-n2v24d8-s3"}, "workflow_mode": "python_then_lean",
                         "discovery_rounds": discovery_rounds, **open_lane}}
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    monkeypatch.setattr(loop, "check_lean_lock", lambda project: {})
    monkeypatch.setattr(loop, "check_inspection", lambda project: None)
    monkeypatch.setattr(loop, "lean_identity", lambda project, knowledge="minimal": dict(IDENT))
    monkeypatch.setattr(Session, "_service", service or fake_service(448))
    return path


def read_only(p: Path) -> bool:
    """No write permission for anyone (os.access says yes to root whatever the mode)."""
    return os.stat(p).st_mode & 0o222 == 0


def tool_log(run: RunDir, k: int) -> list[dict]:
    p = run.round_path(k) / "attempt_0" / "open_lane" / "tools.jsonl"
    return [json.loads(line) for line in p.read_text().splitlines()]


# 1, 3, 18: the modes, their settings and their tools ------------------------------------------------------
def _cfg(tmp_path, **open_lane) -> dict:
    project = fake_project(tmp_path)
    return {"run_id": "x", "model": "tests/max2_tiny", "backend": "fake", "rule_set": ["single", "skip"],
            "prompt_template": "open_lane_v6", "rounds_max": 7, "runs_dir": str(tmp_path / "runs"),
            "open_lane": {"enabled": True, "lean_project": str(project), **open_lane}}


def test_a_config_without_the_setting_is_interleaved_with_the_five_tools(tmp_path):
    """Case 1 and 18: an old configuration behaves as interleaved: no phase, its own template, the five tools."""
    cfg = merge(_cfg(tmp_path))
    assert cfg["open_lane"]["workflow_mode"] == "interleaved" and workflow.mode(cfg) == "interleaved"
    assert workflow.phase(cfg, 1) is None and workflow.template(cfg, 3) == "open_lane_v6"
    old = copy.deepcopy(cfg)
    for key in ("workflow_mode", "discovery_rounds", "probe_compile_calls", "probe_auxiliary_submissions", "probe_seconds",
                "research_workspace_mb", "research_workspace_files"):
        old["open_lane"].pop(key)  # a run saved before the setting existed
    assert workflow.mode(old) == "interleaved" and workflow.phase(old, 2) is None
    s = Session.create(tmp_path / "run" / "round_001" / "attempt_0" / "open_lane", cfg, "tests/max2_tiny",
                       [{"id": NET, "setting": "v8", "n_inputs": 64}], tmp_path / "run")
    assert s.phase() is None and s.tools is Session.TOOLS
    assert list(Session.TOOLS) == ["lean_check", "run_python", "search_library", "read_file", "submit_candidate"]
    with pytest.raises(ToolError, match="does not take"):
        s.call("lean_check", {"path": "Candidate/A.lean", "source": "", "network": NET, "claimed_count": 1, "candidate_id": "c001"})
    with pytest.raises(ToolError, match="no tool 'research_write'"):
        s.call("research_write", {"path": "Research/a.md", "text": "x"})


def test_the_new_mode_validates_its_phase_boundary_and_budgets(tmp_path):
    """Case 3."""
    ok = merge(_cfg(tmp_path, workflow_mode="python_then_lean", discovery_rounds=4))
    assert workflow.schedule(ok)["discovery_rounds"] == [1, 4] and workflow.schedule(ok)["formalization_rounds"] == [5, 7]
    assert [workflow.phase(ok, k) for k in range(0, 9)] == [None, "discovery", "discovery", "discovery", "discovery",
                                                           "formalization", "formalization", "formalization", None]
    assert workflow.template(ok, 4) == "open_lane_discovery_v1" and workflow.template(ok, 5) == "open_lane_formalization_v1"
    bad = [({"discovery_rounds": 0}, "at least 1 and less than rounds_max"),
           ({"discovery_rounds": 7}, "at least 1 and less than rounds_max"),
           ({"discovery_rounds": 2, "probe_compile_calls": -1}, "probe_compile_calls must be at least 0"),
           ({"discovery_rounds": 2, "probe_seconds": -5}, "probe_seconds must be at least 0"),
           ({"discovery_rounds": 2, "probe_auxiliary_submissions": 1.5}, "must be an integer"),
           ({"discovery_rounds": 2, "enabled": False}, "needs open_lane.enabled: true")]
    for extra, why in bad:
        with pytest.raises(RunConfigError, match=why):
            merge(_cfg(tmp_path, workflow_mode="python_then_lean", **extra))
    with pytest.raises(RunConfigError, match="workflow_mode must be one of interleaved, python_then_lean"):
        merge(_cfg(tmp_path, workflow_mode="lean_first"))
    # all probe limits zero: no Lean in discovery (said in the prompt; the tools refuse)
    zero = merge(_cfg(tmp_path, workflow_mode="python_then_lean", discovery_rounds=1, probe_compile_calls=0,
                      probe_auxiliary_submissions=0, probe_seconds=0))
    assert workflow.schedule(zero)["probe"] == {"compile_calls": 0, "auxiliary_submissions": 0, "seconds": 0.0}
    # the separate pilot config: the linear pilot with the new mode on top
    pilot = load_run_config(REPO_ROOT / "config" / "pilot" / "linear-max2-python-then-lean.yaml",
                            overrides={"open_lane.lean_project": str(fake_project(tmp_path / "p"))})
    assert pilot["run_id"] == "pilot-linear-max2-python-then-lean" and pilot["rounds_max"] == 7
    assert workflow.schedule(pilot)["discovery_rounds"] == [1, 4] and pilot["open_lane"]["seed_check"] == {"network": "max2-v64-s1"}
    assert workflow.schedule(pilot)["probe"] == {"compile_calls": 3, "auxiliary_submissions": 1, "seconds": 600.0}


def test_the_research_inventory_passes_the_backends_context_checks_and_the_five_still_do(tmp_path):
    """Case 18: the CLI is told the session's tools, and its init event is checked against them."""
    from core.agent.backends.claude_code import isolation_problems
    from core.open_lane import backends
    from core.open_lane.mcp_server import tool_list

    cfg = merge(_cfg(tmp_path, workflow_mode="python_then_lean", discovery_rounds=2))
    run = tmp_path / "run"
    workflow.record(run, cfg)
    s = Session.create(run / "round_001" / "attempt_0" / "open_lane", cfg, "tests/max2_tiny", [{"id": NET, "setting": "v8", "n_inputs": 64}], run)
    names = [t["name"] for t in tool_list(s)]
    assert names == list(RESEARCH_TOOLS) and names[:5] == list(Session.TOOLS) and names[5:] == ["research_write", "research_list"]
    tools, system = backends.inventory(s)
    assert tools == tuple(f"mcp__cpl__{n}" for n in names) and system == backends.RESEARCH_SYSTEM_PROMPT
    assert "no files of your own" not in system and "Research/" in system
    init = {"type": "system", "subtype": "init", "session_id": "s", "tools": list(tools), "skills": [], "slash_commands": [],
            "mcp_servers": [{"name": "cpl", "status": "connected"}], "model": "m"}
    assert isolation_problems(init, tools, {"cpl"}, required="cpl") == []
    assert backends._init_problem(json.dumps(init), tools) is None
    assert backends._init_problem(json.dumps(init)) is not None  # the five alone would not be what this session runs
    legacy = Session.create(tmp_path / "other" / "round_001" / "attempt_0" / "open_lane", merge(_cfg(tmp_path)), "tests/max2_tiny",
                            [{"id": NET, "setting": "v8", "n_inputs": 64}], tmp_path / "other")
    assert backends.inventory(legacy) == (backends.MCP_TOOLS, backends.SYSTEM_PROMPT)
    assert [t["name"] for t in tool_list(legacy)] == list(Session.TOOLS)
    b = backends.ClaudeCodeToolBackend.__new__(backends.ClaudeCodeToolBackend)
    b.cfg, b.command = {**cfg, "agent_model": "m", "effort": None}, "claude"
    cmd = b.command_line(Path("mcp.json"), s)
    assert cmd[cmd.index("--allowedTools") + 1] == ",".join(tools) and cmd[cmd.index("--system-prompt") + 1] == system
    cmd = b.command_line(Path("mcp.json"), legacy)
    assert cmd[cmd.index("--allowedTools") + 1] == ",".join(backends.MCP_TOOLS)


# 4, 5, 8, 10, 14, 15, 16: a whole run ---------------------------------------------------------------------
def test_discovery_then_formalization_then_the_seed_check_on_stand_ins(tmp_path, monkeypatch):
    """Discovery rounds 1 to 3 with patience 1: round 1 has no Lean at all, round 2 one Lean check of a candidate
    and an auxiliary lemma, round 3 the shortlist. Formalization rounds 4 and 5: a scored proof naming the
    candidate. Then the seed check and the scaling question, with their locks, as before."""
    cand = json.dumps(CANDIDATE)
    r1 = {"calls": [
        call("research_write", path="Research/candidates/c001.json", text=cand),
        call("run_python", code="import json\njson.dump({'min_gap': 0.5}, open('out/Research/results/margins.json', 'w'))\nprint('ok')",
             network=A, outputs=["Research/results/margins.json"]),
        call("research_write", path="Research/notes.md", text="columns decide"),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.X.performance", modules=["Candidate/X.lean"]),
    ], "response": "CLAIM: c001.\nWHY IT HELPS: columns.\nNOTES: test the gap."}
    r2 = {"calls": [
        call("lean_check", path="Candidate/Probe.lean", source=PROBE, network=A, claimed_count=576),  # no candidate: refused
        call("lean_check", path="Candidate/Probe.lean", source=PROBE, network=A, claimed_count=576, candidate_id="c001",
             question="Can the gap be stated with the specification's own definitions?"),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.Probe.gap_def", modules=["Candidate/Probe.lean"],
             kind="auxiliary", candidate_id="c001", question="Is the gap statement provable as stated?"),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.Probe.gap_def", modules=["Candidate/Probe.lean"],
             kind="performance", candidate_id="c001", question="x" * 20),
    ], "response": "CLAIM: the gap is stated.\nWHY IT HELPS: -\nNOTES: none."}
    r3 = {"calls": [call("research_write", path="Research/shortlist.json", text=json.dumps([{"id": "c001", "reason": "the only one"}]))],
          "response": "CLAIM: shortlist.\nWHY IT HELPS: -\nNOTES: none."}
    r4 = {"calls": [
        call("lean_check", path="Candidate/Col.lean", source=GENERAL, network=A, claimed_count=576),
        call("lean_check", path="Candidate/ColRun.lean", source=INSTANCE, network=A, claimed_count=576),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.ColRun.performance", modules=["Candidate/ColRun.lean"],
             scored=SCORED, candidate_id="c001"),
    ], "response": "CLAIM: 576 of 576.\nWHY IT HELPS: columns.\nNOTES: none."}
    r5 = {"calls": [], "response": "CLAIM: nothing more.\nWHY IT HELPS: -\nNOTES: none."}
    path = ptl_run(tmp_path, monkeypatch, [r1, r2, r3, r4, r5, SEED_CHECK, SCALING], rounds_max=5, discovery_rounds=3)
    lines: list[str] = []
    ctx = loop.start(path, log=lines.append)
    loop.drive(ctx)
    run = ctx.run
    # case 4: every discovery round ran, though rounds 1 and 3 submitted nothing and patience is 1
    assert run.done_rounds()[:6] == [0, 1, 2, 3, 4, 5] and not any("patience" in l for l in lines), lines
    assert any("round 1: discovery" in l for l in lines) and any("round 4: formalization" in l for l in lines)
    r1_records = [r for r in run.read_archive() if r["round"] == 1]
    assert [r["status"] for r in r1_records] == ["no_submission"] and "the plan in this phase" in r1_records[0]["error"]
    sched = workflow.recorded(run.path)["schedule"]
    assert sched["discovery_rounds"] == [1, 3] and sched["formalization_rounds"] == [4, 5]
    # case 5: no score pressure and no change-of-approach warning in discovery; the shortlist asked for in its last round
    for k in (1, 2, 3):
        p = run.read(k, "prompt.md")
        stats = run.read(k, "meta.json")["prompt"]
        assert stats["template"] == "open_lane_discovery_v1" and stats["phase"] == "discovery"
        assert "Raise the score" not in p and "No submission of the last" not in p and "cannot be taken to the seed check" not in p
        assert "Your current task is to develop promising explanations and verification methods" in " ".join(p.split())
        assert "All Python coverage and cost estimates remain provisional" in " ".join(p.split())
        assert "THE VERIFIED BASELINE (accepted by the service; not an estimate)" in p
        assert ("write Research/shortlist.json" in p) == (k == 3)
    assert "c001: The larger token's column decides; your assessment: promising; estimated coverage 4,096" in run.read(2, "prompt.md")
    p4 = run.read(4, "prompt.md")
    assert run.read(4, "meta.json")["prompt"]["template"] == "open_lane_formalization_v1"
    assert "Your current task is to turn the strongest saved candidates into accepted Lean results" in " ".join(p4.split())
    assert "1. c001: the only one" in p4 and "Raise the score" in p4 and "mechanism: logits are column sums" in p4
    # the transition, once, with a read-only copy of the research folder as discovery left it
    tr = workflow.transition(run.path)
    assert tr["round"] == 4 and tr["ranked"] and [x["id"] for x in tr["shortlist"]] == ["c001"] and tr["missing"] == []
    snap = run.path / tr["snapshot"]
    assert (snap / "candidates" / "c001.json").is_file() and read_only(snap / "candidates" / "c001.json") and read_only(snap)
    assert set(tr["files"]) == {"Research/candidates/c001.json", "Research/notes.md", "Research/results/margins.json",
                                "Research/shortlist.json"}
    # the discovery phase's tools: refusals, one Lean check, one lemma
    log1, log2 = tool_log(run, 1), tool_log(run, 2)
    assert "the discovery phase takes lemmas only" in log1[3]["outcome"]["error"]
    assert "candidate_id must name a candidate record" in log2[0]["outcome"]["error"]
    assert log2[1]["outcome"]["discovery_check"]["outcome"] == "compiled"
    assert log2[2]["outcome"]["status"] == "accepted" and log2[2]["outcome"]["candidate_id"] == "c001"
    assert "the discovery phase takes lemmas only" in log2[3]["outcome"]["error"]
    probes = workflow.probe_entries(run.path)
    assert [(e["kind"], e["outcome"], e["round"]) for e in probes] == [("compile", "compiled", 2), ("auxiliary", "accepted", 2)]
    records = run.read_archive()
    lemma = [r for r in records if r["round"] == 2 and r["status"] == "lemma"]
    assert len(lemma) == 1 and lemma[0]["phase"] == "discovery" and lemma[0]["research_candidate"] == "c001" and "stage" not in lemma[0]
    # case 8: formalization kept its rounds and its own budgets: round 4 compiled and submitted with the full session budgets
    assert run.read(4, "attempt_0/response_meta.json")["tools_used"] == {"lean_check": 2, "submit_candidate": 1, "run_python": 0}
    # case 10: the lemma accepted in discovery is in formalization's workspace, compiled there
    carried = json.loads((run.round_path(4) / "attempt_0" / "open_lane" / "session.json").read_text())["carried"]
    assert [m["path"] for m in carried] == ["Candidate/Probe.lean"] and carried[0]["compiled"]
    # case 15: the formalization proof is an ordinary scored record and enters the frontier and the score
    ok = [r for r in records if r["status"] == "ok" and r.get("lane") == "open" and not r.get("stage")]
    assert len(ok) == 1 and ok[0]["round"] == 4 and ok[0]["phase"] == "formalization" and ok[0]["research_candidate"] == "c001"
    from core.scoring import frontier, summarize

    assert ok[0]["record_id"] in {p["record_id"] for pts in frontier(records).values() for p in pts}
    entries = loop.select_networks(ctx.folder, ctx.cfg)
    finishing = summarize(records, entries)[entries[0]["setting"]]["cost_of_finishing_median"]
    assert finishing > 1
    # case 14: the agent's estimates (coverage 4,096 at cost 1) touch nothing verified: the score is the records'
    assert not any("estimated" in json.dumps(r) for r in records)
    assert summarize([r for r in records if r["status"] != "lemma"], entries)[entries[0]["setting"]]["cost_of_finishing_median"] == finishing
    # case 16: the seed check and the scaling question ran after, with the proof of round 4 locked
    state = stages.read_state(run)
    assert state["locked"]["record_id"] == ok[0]["record_id"] and state["stages"]["seed_check"]["result"]["outcome"] == "certified"
    assert state["stages"]["seed_check"]["round"] == 6 and state["stages"]["scaling"]["round"] == 7
    stage_session = json.loads((run.round_path(6) / "attempt_0" / "open_lane" / "session.json").read_text())
    assert "workflow" not in stage_session and stage_session["stage"]["name"] == "seed_check"
    assert all(r.get("stage") and "phase" not in r for r in records if r["round"] >= 6)
    # the report and the status say what the phases did, estimates apart from verified results
    status = loop.status_text(run)
    assert "Workflow (python_then_lean):" in status and "discovery: rounds 1 to 3 configured, 3 done" in status
    assert "formalization: rounds 4 to 5 configured, 2 done" in status
    assert "1 of 3 compiles, 1 of 1 auxiliary submissions" in status and "transition before round 4: shortlist c001" in status
    assert "research candidates (agent-written; estimates are provisional, never scored)" in status
    assert "c001: The larger token's column decides; estimated coverage 4,096, estimated cost 1; agent's assessment promising; accepted: 576 certified" in status
    # resume: nothing redone, the transition not recorded again
    before, at = len(records), tr["at"]
    ctx2 = loop.resume(run.path, log=lines.append)
    loop.drive(ctx2)
    assert len(run.read_archive()) == before and workflow.transition(run.path)["at"] == at


def test_without_a_shortlist_formalization_lists_the_candidates_unranked(tmp_path, monkeypatch):
    """Case 17: the last discovery session ran out of time before the shortlist; nothing is invented or lost."""
    r1 = {"calls": [call("research_write", path="Research/candidates/c001.json", text=json.dumps(CANDIDATE)),
                    call("research_write", path="Research/candidates/c002.json",
                         text=json.dumps({**CANDIDATE, "id": "c002", "title": "Second", "agent_assessment": "weak"}))],
          "response": "(the session ran out of time)"}
    r2 = {"calls": [], "response": "CLAIM: none.\nWHY IT HELPS: -\nNOTES: none."}
    path = ptl_run(tmp_path, monkeypatch, [r1, r2], rounds_max=2, discovery_rounds=1, seed_check=None, scaling=False)
    ctx = loop.start(path, log=lambda *a: None)
    loop.drive(ctx)
    tr = workflow.transition(ctx.run.path)
    assert tr["ranked"] is False and tr["shortlist"] is None and [c["id"] for c in tr["candidates"]] == ["c001", "c002"]
    p2 = ctx.run.read(2, "prompt.md")
    assert "Discovery left no shortlist. The saved candidates, unranked: choose among them." in p2
    assert "- c001: The larger token's column decides" in p2 and "- c002: Second" in p2
    assert (research.root(ctx.run.path) / "candidates" / "c002.json").is_file()


# 6, 7, 9, 11, 12, 13: the session's tools ------------------------------------------------------------------
def _phased(tmp_path, k: int = 1, run: Path | None = None, **open_lane) -> Session:
    cfg = merge(_cfg(tmp_path, workflow_mode="python_then_lean", discovery_rounds=2, **open_lane))
    cfg["open_lane"]["work_dir"] = str(tmp_path / "work")
    run = run or tmp_path / "run"
    workflow.record(run, cfg)
    return Session.create(run / f"round_{k:03d}" / "attempt_0" / "open_lane", cfg, "tests/max2_tiny",
                          [{"id": NET, "setting": "v8", "n_inputs": 64}], run)


SRC = "namespace Candidate.P\ntheorem t : True := trivial\nend Candidate.P\n"
Q = "Does the gap statement typecheck against the definitions?"


def test_the_lean_allowance_is_one_total_over_discovery_and_survives_rounds_resumes_and_crashes(tmp_path, monkeypatch):
    """Case 6, 7 and 9. The allowance is the run's (three compiles, one lemma, 600 s): taken before a call,
    settled after it; a call that never settled counts whole; a timed-out compile is inconclusive and Python
    goes on; a compile is never reported as an acceptance; once it is used up the source is saved, not
    compiled, and formalization is not touched."""
    answers = iter([{"ok": True, "messages": ""},
                    {"status": "timeout", "ok": False, "timed_out": True, "error": "the service did not answer within 5 s"},
                    {"ok": False, "messages": "error: unknown identifier"}])
    monkeypatch.setattr(Session, "_service", lambda self, args, timeout_s: next(answers))
    s = _phased(tmp_path)
    s.call("research_write", {"path": "Research/candidates/c001.json", "text": json.dumps(CANDIDATE)})
    out = s.call("lean_check", {"path": "Candidate/P.lean", "source": SRC, "network": NET, "claimed_count": 64,
                                "candidate_id": "c001", "question": Q})
    assert out["discovery_check"]["outcome"] == "compiled" and "not an acceptance" in out["discovery_check"]["note"]
    assert out["remaining"]["discovery_lean_allowance"]["compile_calls"] == 2
    # the next round's session: the allowance goes on, it does not start again
    s2 = _phased(tmp_path, k=2)
    assert workflow.probe_left(s2.run_dir())["compile_calls"] == 2
    out = s2.call("lean_check", {"path": "Candidate/P.lean", "source": SRC, "network": NET, "claimed_count": 64,
                                 "candidate_id": "c001", "question": Q})
    assert out["timed_out"] and out["discovery_check"]["outcome"] == "timeout" and "Inconclusive" in out["discovery_check"]["note"]
    assert s2.run_python("print(1 + 1)", NET)["output"] == "2\n"  # Python goes on
    # a call that crashed between its share and its settling (the tools' server killed): its share counts whole
    workflow.probe_reserve(s2.run_dir(), "compile", 100.0, {"round": 2, "candidate_id": "c001"})
    used = workflow.probe_usage(s2.run_dir())
    assert used["compile_calls"] == 3 and used["seconds"] >= 100
    # a resumed session (the same folder opened again) sees the same
    again = Session(s2.path)
    assert again.remaining()["discovery_lean_allowance"]["compile_calls"] == 0
    with pytest.raises(ToolError, match="allowance of 3 compiles is used up.*Candidate/Q.lean is saved, not compiled"):
        again.call("lean_check", {"path": "Candidate/Q.lean", "source": SRC.replace("P", "Q"), "network": NET, "claimed_count": 64,
                                  "candidate_id": "c001", "question": Q})
    assert (again.workspace / "Candidate" / "Q.lean").read_text() == SRC.replace("P", "Q")
    assert again.state["used"]["lean_check"] == 1  # the refused call spent nothing of the session either
    # no outcome is ever "accepted" for a compile, and a compiled module made no record
    assert [e.get("outcome") for e in workflow.probe_entries(s2.run_dir())] == ["compiled", "timeout", None]
    assert s.receipts() == [] and s2.receipts() == []
    # formalization: no allowance, the session's own budgets
    f = _phased(tmp_path, k=3)
    assert f.phase() == "formalization" and "discovery_lean_allowance" not in f.remaining()
    out = f.call("lean_check", {"path": "Candidate/P.lean", "source": SRC, "network": NET, "claimed_count": 64})
    assert out["ok"] is False and "discovery_check" not in out
    assert workflow.probe_usage(f.run_dir())["compile_calls"] == 3


def test_all_limits_zero_means_no_lean_in_discovery(tmp_path, monkeypatch):
    monkeypatch.setattr(Session, "_service", lambda self, args, timeout_s: pytest.fail("no Lean in this discovery"))
    s = _phased(tmp_path, probe_compile_calls=0, probe_auxiliary_submissions=0, probe_seconds=0)
    s.call("research_write", {"path": "Research/candidates/c001.json", "text": json.dumps(CANDIDATE)})
    with pytest.raises(ToolError, match="allowance of 0 compiles is used up"):
        s.call("lean_check", {"path": "Candidate/P.lean", "source": SRC, "network": NET, "claimed_count": 64,
                              "candidate_id": "c001", "question": Q})


def test_research_files_and_declared_outputs_survive_the_sandbox_and_a_resume(tmp_path):
    """Case 11 and 12: declared inputs are read-only copies; declared outputs are kept when the code completes;
    every call is kept as a record; a raised exception marks the experiment incomplete and keeps nothing."""
    s = _phased(tmp_path)
    s.call("research_write", {"path": "Research/experiments/helper.py", "text": "def double(x):\n    return 2 * x\n"})
    out = s.call("run_python", {"code": "import helper, json, os\nprint(helper.double(21))\n"
                                        "json.dump({'m': helper.double(1)}, open('out/Research/results/m.json', 'w'))\n"
                                        "print(os.stat('Research/experiments/helper.py').st_mode & 0o222 == 0)",
                                "network": NET, "files": ["Research/experiments/helper.py"], "outputs": ["Research/results/m.json"]})
    assert out["output"] == "42\nTrue\n" and out["python"] == {"ok": True, "raised": None}  # 42, and the input is read-only
    assert out["experiment"]["status"] == "complete" and out["experiment"]["outputs"][0]["kept"] is True
    assert json.loads(research.read_bytes(s.run_dir(), "Research/results/m.json")) == {"m": 2}
    rec_dir = s.path / "experiments" / "001"
    rec = json.loads((rec_dir / "record.json").read_text())
    assert rec["complete"] and rec["inputs"][0]["path"] == "Research/experiments/helper.py" and rec["outputs"][0]["kept"]
    assert (rec_dir / "code.py").is_file() and read_only(rec_dir / "record.json") and read_only(rec_dir / "code.py")
    # the record keeps what was, whatever the working file becomes
    s.call("research_write", {"path": "Research/experiments/helper.py", "text": "def double(x):\n    return 3 * x\n"})
    assert (rec_dir / "inputs" / "Research" / "experiments" / "helper.py").read_text().endswith("2 * x\n")
    # a raised exception: the experiment failed, explicitly; its output is in its record only
    out = s.call("run_python", {"code": "open('out/Research/results/m.json', 'w').write('partial')\nraise ValueError('no gap')",
                                "network": NET, "outputs": ["Research/results/m.json"]})
    assert out["status"] == "ok" and out["python"] == {"ok": False, "raised": "ValueError: no gap"}
    assert out["experiment"]["status"] == "python_error" and out["experiment"]["complete"] is False
    assert out["experiment"]["outputs"][0]["kept"] is False and "kept in its record only" in out["experiment"]["outputs"][0]["not_kept"]
    assert json.loads(research.read_bytes(s.run_dir(), "Research/results/m.json")) == {"m": 2}
    # a declared output the code did not write is said to be missing
    out = s.call("run_python", {"code": "print('nothing')", "network": NET, "outputs": ["Research/results/none.json"]})
    assert out["experiment"]["missing"] == ["Research/results/none.json"]
    # the next round, and a resumed session, read the same folder
    s2 = _phased(tmp_path, k=2)
    assert s2.call("read_file", {"path": "Research/results/m.json"})["text"] == '1: {"m": 2}'
    listed = s2.call("research_list", {"prefix": "Research/results"})["files"]
    assert [(f["path"], f["round"], f["via"]) for f in listed] == [("Research/results/m.json", 1, "run_python")]


def test_research_paths_cannot_escape_or_follow_links(tmp_path):
    """Case 13."""
    s = _phased(tmp_path)
    for bad in ("Research/../x.md", "Research/.hidden", "notes.md", "Research/a/../../b", "/Research/x", "Research/",
                "Research/" + "/".join(["d"] * 7) + "/x"):
        with pytest.raises(ToolError, match="Research"):
            s.call("research_write", {"path": bad, "text": "x"})
    outside = tmp_path / "outside"
    outside.mkdir()
    research.root(s.run_dir()).mkdir(parents=True, exist_ok=True)
    os.symlink(outside, research.root(s.run_dir()) / "linked")
    with pytest.raises(ToolError, match="not a plain folder"):
        s.call("research_write", {"path": "Research/linked/x.md", "text": "x"})
    with pytest.raises(ToolError, match="not a plain folder|no file"):
        s.call("read_file", {"path": "Research/linked/x.md"})
    assert not (outside / "x.md").exists()
    for bad in (["Research/../etc/passwd"], ["/etc/passwd"], "Research/x"):
        with pytest.raises(ToolError, match="files"):
            s.call("run_python", {"code": "print(1)", "network": NET, "files": bad})
    # a program that writes a link where an output was declared: nothing is taken through it
    (outside / "secret.txt").write_text("secret")
    out = s.call("run_python", {"code": f"import os\nos.symlink({str(outside / 'secret.txt')!r}, 'out/Research/r/s.txt')",
                                "network": NET, "outputs": ["Research/r/s.txt"]})
    assert out["experiment"]["missing"] == ["Research/r/s.txt"]
    # a candidate record may not say that it is proved
    with pytest.raises(ToolError, match="only the acceptance service's receipts"):
        s.call("research_write", {"path": "Research/candidates/c001.json", "text": json.dumps({**CANDIDATE, "verified": True})})
    with pytest.raises(ToolError, match="never that it is proved"):
        s.call("research_write", {"path": "Research/candidates/c001.json", "text": json.dumps({**CANDIDATE, "agent_assessment": "proved"})})
    with pytest.raises(ToolError, match="its id must be 'c009'"):
        s.call("research_write", {"path": "Research/candidates/c009.json", "text": json.dumps(CANDIDATE)})
    with pytest.raises(ToolError, match="shortlist"):
        s.call("research_write", {"path": "Research/shortlist.json", "text": json.dumps(["c001"])})
    # the folder's limits
    small = _phased(tmp_path / "small", research_workspace_mb=0.001, research_workspace_files=2)
    small.call("research_write", {"path": "Research/a.md", "text": "a"})
    with pytest.raises(ToolError, match="over its limit"):
        small.call("research_write", {"path": "Research/b.md", "text": "b" * 2000})


# 2: a run saved before the setting ------------------------------------------------------------------------
def test_a_saved_run_without_the_new_fields_resumes_as_it_was(tmp_path, monkeypatch):
    """Case 2: a run whose saved config has none of the workflow keys (made before them) resumes interleaved:
    its template, its five tools, patience as before, no workflow record."""
    from core.open_lane.backends import FakeToolBackend

    project = fake_project(tmp_path)
    scripts = []
    for i in range(2):
        p = tmp_path / f"s{i}.json"
        p.write_text(json.dumps({"calls": [call("run_python", code="print(7)", network=A)], "response": "CLAIM: -\nWHY IT HELPS: -\nNOTES: -"}))
        scripts.append(str(p))
    cfg = {"extends": str(REPO_ROOT / "config" / "pilot" / "base.yaml"), "run_id": "old", "model": "tests/max2_ladder",
           "networks": [A], "backend": "fake", "rounds_max": 2, "patience": 5, "runs_dir": str(tmp_path / "runs"), "workers": 1,
           "open_lane": {"lean_project": str(project), "work_dir": str(tmp_path / "work"), "fake_scripts": scripts, "scaling": False}}
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    monkeypatch.setattr(loop, "check_lean_lock", lambda project: {})
    monkeypatch.setattr(loop, "check_inspection", lambda project: None)
    monkeypatch.setattr(loop, "lean_identity", lambda project, knowledge="minimal": dict(IDENT))
    real = FakeToolBackend.respond
    calls = {"n": 0}

    def interrupted(self, prompt, index, where=None):
        calls["n"] += 1
        if index == 1 and calls["n"] == 2:
            raise loop.StopRun("the machine went to sleep")
        return real(self, prompt, index, where)

    monkeypatch.setattr(FakeToolBackend, "respond", interrupted)
    ctx = loop.start(path, log=lambda *a: None)
    with pytest.raises(loop.StopRun):
        loop.drive(ctx)
    saved = yaml.safe_load((ctx.run.path / "config.yaml").read_text())
    for key in ("workflow_mode", "discovery_rounds", "probe_compile_calls", "probe_auxiliary_submissions", "probe_seconds",
                "research_workspace_mb", "research_workspace_files"):
        saved["open_lane"].pop(key)
    (ctx.run.path / "config.yaml").write_text(yaml.safe_dump(saved, sort_keys=True))
    ctx2 = loop.resume(ctx.run.path, log=lambda *a: None)
    loop.drive(ctx2)
    assert ctx2.run.done_rounds() == [0, 1, 2] and workflow.recorded(ctx2.run.path) is None
    assert ctx2.run.read(2, "meta.json")["prompt"]["template"] == "open_lane_v6" and "phase" not in ctx2.run.read(2, "meta.json")["prompt"]
    s2 = json.loads((ctx2.run.round_path(2) / "attempt_0" / "open_lane" / "session.json").read_text())
    assert "workflow" not in s2 and "Raise the score" in ctx2.run.read(2, "prompt.md")
    # a python_then_lean run that lost its schedule record, or whose config was changed, does not resume
    p2 = ptl_run(tmp_path / "b", monkeypatch, [{"calls": [], "response": "x"}] * 2, rounds_max=2, discovery_rounds=1,
                 seed_check=None, scaling=False)
    ctx3 = loop.start(p2, log=lambda *a: None)
    changed = yaml.safe_load((ctx3.run.path / "config.yaml").read_text())
    changed["open_lane"]["probe_seconds"] = 9999
    (ctx3.run.path / "config.yaml").write_text(yaml.safe_dump(changed, sort_keys=True))
    with pytest.raises(loop.LoopError, match="differs from the one it started with"):
        loop.resume(ctx3.run.path, log=lambda *a: None)


# against the real Lean service, where it is built ------------------------------------------------------------
LEAN = Path(os.environ.get("COMPACT_PROOF_LEAN", "~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck")).expanduser()
HAVE_LEAN = (LEAN / "scripts" / "accept.py").is_file() and (LEAN / ".lake" / "build" / "bin" / "acceptcheck").is_file()


@pytest.mark.skipif(not HAVE_LEAN, reason="the Lean project with a built acceptcheck is not at COMPACT_PROOF_LEAN")
def test_discovery_probe_then_formalization_against_the_real_lean_service(tmp_path, monkeypatch):
    """The real service: in discovery a candidate's Lean check compiles the scored example and its central lemma
    is accepted as an auxiliary lemma (the allowance spent and settled); in formalization the lemma's module is
    carried and compiled, and the scored proof naming the candidate is accepted and scored."""
    monkeypatch.undo()  # the real inspection and service
    ex = "examples/open_lane/max2_tiny_scored/Candidate/Max2TinyScored.lean"
    cand = {**CANDIDATE, "title": "Brute force through the single rule"}
    disc = {"calls": [
        {"tool": "research_write", "args": {"path": "Research/candidates/c001.json", "text": json.dumps(cand)}},
        {"tool": "lean_check", "args": {"path": "Candidate/Max2TinyScored.lean", "network": NET, "claimed_count": 64,
                                        "source": {"$project_file": ex}, "candidate_id": "c001",
                                        "question": "Does the counted single rule give a checker whose count lemma can be proved?"}},
        {"tool": "submit_candidate", "args": {"network": NET, "claimed_count": 64, "kind": "auxiliary", "theorem": "Candidate.Max2TinyScored.countSingles_le",
                                              "modules": ["Candidate/Max2TinyScored.lean"], "candidate_id": "c001",
                                              "question": "Is the count lemma accepted as stated?"}},
        {"tool": "research_write", "args": {"path": "Research/shortlist.json", "text": json.dumps([{"id": "c001", "reason": "it compiles"}])}}],
        "response": "CLAIM: c001.\nWHY IT HELPS: -\nNOTES: -"}
    form = {"calls": [
        {"tool": "submit_candidate", "args": {"network": NET, "claimed_count": 64, "theorem": "Candidate.Max2TinyScored.performance",
                                              "modules": ["Candidate/Max2TinyScored.lean"], "candidate_id": "c001",
                                              "scored": {"checker": "Candidate.Max2TinyScored.D", "sound": "Candidate.Max2TinyScored.D_sound",
                                                         "instance": "Candidate.Max2TinyScored.D_instance", "certificate": [], "claimed_bill": 4032}}}],
        "response": "CLAIM: 64 of 64.\nWHY IT HELPS: -\nNOTES: -"}
    paths = []
    for i, sc in enumerate((disc, form)):
        p = tmp_path / f"s{i}.json"
        p.write_text(json.dumps(sc))
        paths.append(str(p))
    cfg = {"run_id": "ptl-lean", "model": "tests/max2_tiny", "backend": "fake", "rule_set": ["single", "skip"],
           "prompt_template": "open_lane_v6", "baselines": False, "rounds_max": 2, "patience": 1, "runs_dir": str(tmp_path / "runs"),
           "sandbox": "auto", "workers": 1,
           "open_lane": {"enabled": True, "lean_project": str(LEAN), "work_dir": str(tmp_path / "work"), "fake_scripts": paths,
                         "workflow_mode": "python_then_lean", "discovery_rounds": 1, "probe_seconds": 3000}}
    path = tmp_path / "run.yaml"
    path.write_text(yaml.safe_dump(cfg))
    lines: list[str] = []
    ctx = loop.start(path, log=lines.append)
    loop.drive(ctx)
    run = ctx.run
    log = tool_log(run, 1)
    assert log[1]["outcome"]["ok"] and log[1]["outcome"]["discovery_check"]["outcome"] == "compiled", log[1]
    assert log[2]["outcome"]["status"] == "accepted", log[2]
    entries = workflow.probe_entries(run.path)
    assert [(e["kind"], e["outcome"], e["settled"]) for e in entries] == [("compile", "compiled", True), ("auxiliary", "accepted", True)]
    assert all(0 < e["seconds"] <= e["reserved_s"] for e in entries)
    records = run.read_archive()
    lemma = [r for r in records if r["status"] == "lemma"]
    ok = [r for r in records if r["status"] == "ok"]
    assert len(lemma) == 1 and lemma[0]["phase"] == "discovery" and "countP" in lemma[0]["statement"]
    assert len(ok) == 1 and ok[0]["phase"] == "formalization" and ok[0]["certified"] == 64 and ok[0]["length"] == 4112
    assert ok[0]["research_candidate"] == "c001"
    carried = json.loads((run.round_path(2) / "attempt_0" / "open_lane" / "session.json").read_text())["carried"]
    assert carried and carried[0]["compiled"]
    assert "1. c001: it compiles" in run.read(2, "prompt.md")
