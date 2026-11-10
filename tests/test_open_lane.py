"""The open lane in the loop: the MCP server's protocol, and a fake-backend run that submits the scored
brute-force example through the Lean project's acceptance service and records its receipt.

The run test needs the Lean project built (at COMPACT_PROOF_LEAN, else next to this repository, else at the
pilots' path, where scripts/server_setup.sh puts it) and takes a few minutes; it is skipped otherwise.
"""

from __future__ import annotations

import io
import json
import os
from pathlib import Path

import pytest

from core import loop
from core.open_lane.mcp_server import serve
from core.open_lane.session import Session, ToolError
from core.run_config import merge
from core.util import REPO_ROOT

def _lean_project() -> Path:
    if os.environ.get("COMPACT_PROOF_LEAN"):
        return Path(os.environ["COMPACT_PROOF_LEAN"]).expanduser()
    for name in ("Compact-Proof-Checker", "auto-research-compact-proof-in-lean"):  # its name, or a clone under its old name
        if (REPO_ROOT.parent / name).is_dir():
            return REPO_ROOT.parent / name
    return Path("~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck").expanduser()


LEAN = _lean_project()
HAVE_LEAN = (LEAN / "scripts" / "accept.py").is_file() and (LEAN / ".lake" / "build" / "bin" / "acceptcheck").is_file()


def base_config(tmp_path: Path, scripts: list[str], **extra) -> dict:
    return {
        "run_id": "open-lane-test", "model": "tests/max2_tiny", "backend": "fake", "rule_set": ["single", "skip"],
        "prompt_template": "open_lane_v1", "baselines": False, "rounds_max": max(1, len(scripts)), "patience": 10,
        "runs_dir": str(tmp_path / "runs"), "sandbox": "auto", "workers": 1,
        "open_lane": {"enabled": True, "lean_project": str(LEAN), "work_dir": str(tmp_path / "work"),
                      "fake_scripts": scripts, "compile_calls": 3, "submissions": 3, "python_calls": 2, "stall_rounds": 1},
        **extra,
    }


def test_the_mcp_server_speaks_the_protocol(tmp_path):
    cfg = merge(base_config(tmp_path, [], open_lane={"enabled": False}))
    cfg["open_lane"].update(lean_project=str(LEAN) if HAVE_LEAN else str(tmp_path), work_dir=str(tmp_path / "work"))
    entries = [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64}]
    session = Session.create(tmp_path / "attempt" / "open_lane", cfg, "tests/max2_tiny", entries, tmp_path / "run")
    (tmp_path / "docs").mkdir(exist_ok=True)
    requests = [
        {"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2025-06-18", "capabilities": {}}},
        {"jsonrpc": "2.0", "method": "notifications/initialized"},
        {"jsonrpc": "2.0", "id": 2, "method": "tools/list"},
        {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {"name": "search_library", "arguments": {"query": "numCorrect"}}},
        {"jsonrpc": "2.0", "id": 4, "method": "tools/call", "params": {"name": "lean_check", "arguments": {"path": "x"}}},
        {"jsonrpc": "2.0", "id": 5, "method": "nothing"},
        {"jsonrpc": "2.0", "id": 6, "method": "tools/call", "params": {"name": "read_file", "arguments": {"path": "docs/COUNTED.md", "start": 1, "lines": 5}}},
        {"jsonrpc": "2.0", "id": 7, "method": "tools/call", "params": {"name": "read_file", "arguments": {"path": "../etc/passwd"}}},
    ]
    out = io.StringIO()
    serve(session, io.StringIO("\n".join(json.dumps(r) for r in requests) + "\n"), out)
    replies = [json.loads(line) for line in out.getvalue().splitlines()]
    assert [r["id"] for r in replies] == [1, 2, 3, 4, 5, 6, 7]
    if HAVE_LEAN:
        assert replies[5]["result"]["isError"] is False and "1: # The counted language" in replies[5]["result"]["content"][0]["text"]
    assert replies[6]["result"]["isError"] is True
    assert replies[0]["result"]["protocolVersion"] == "2025-06-18" and "tools" in replies[0]["result"]["capabilities"]
    assert {t["name"] for t in replies[1]["result"]["tools"]} == {"lean_check", "run_python", "search_library", "read_file", "submit_candidate"}
    assert replies[2]["result"]["isError"] is False
    assert replies[3]["result"]["isError"] is True and "needs" in replies[3]["result"]["content"][0]["text"]
    assert "error" in replies[4]
    log = [json.loads(l) for l in (session.path / "tools.jsonl").read_text().splitlines()]
    assert [l["tool"] for l in log] == ["search_library", "read_file", "read_file"]  # a malformed call is refused before it is a tool call


def test_the_mcp_server_runs_as_the_cli_would_start_it(tmp_path):
    """The server as a subprocess, started with the command the Claude Code backend writes into mcp.json."""
    import subprocess

    from core.open_lane.backends import ClaudeCodeToolBackend

    cfg = merge(base_config(tmp_path, [], open_lane={"enabled": False}))
    cfg["open_lane"].update(lean_project=str(LEAN) if HAVE_LEAN else str(tmp_path), work_dir=str(tmp_path / "work"))
    entries = [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64}]
    where = tmp_path / "attempt_0"
    session = Session.create(where / "open_lane", cfg, "tests/max2_tiny", entries, tmp_path / "run")
    backend = ClaudeCodeToolBackend(cfg, runner=lambda *a, **k: None, check_login=False)
    backend.bind(cfg, "tests/max2_tiny", entries, tmp_path / "run")
    mcp = json.loads(backend.mcp_config(session, where).read_text())["mcpServers"]["cpl"]
    cmd = backend.command_line(where / "mcp.json")
    assert "--mcp-config" in cmd and "--allowedTools" in cmd and "--max-turns" in cmd and "--tools" in cmd
    assert cmd[cmd.index("--allowedTools") + 1].split(",") == [f"mcp__cpl__{t}" for t in ("lean_check", "run_python", "search_library", "read_file", "submit_candidate")]
    requests = [{"jsonrpc": "2.0", "id": 1, "method": "initialize", "params": {"protocolVersion": "2024-11-05"}},
                {"jsonrpc": "2.0", "id": 2, "method": "tools/list"}]
    r = subprocess.run([mcp["command"]] + mcp["args"], input="\n".join(json.dumps(q) for q in requests) + "\n",
                       capture_output=True, text=True, timeout=120, env={**os.environ, **mcp["env"]})
    assert r.returncode == 0, r.stderr
    replies = [json.loads(line) for line in r.stdout.splitlines()]
    assert replies[0]["result"]["protocolVersion"] == "2024-11-05"
    assert len(replies[1]["result"]["tools"]) == 5


def test_the_lean_lock_is_checked(tmp_path):
    """preflight refuses a Lean project at another commit than lean-checker.lock names."""
    import subprocess

    if not HAVE_LEAN:
        pytest.skip("no Lean project")
    lock = json.loads((REPO_ROOT / "lean-checker.lock").read_text())
    head = subprocess.run(["git", "-C", str(LEAN), "rev-parse", "HEAD"], capture_output=True, text=True).stdout.strip()
    if head == lock["commit"]:
        assert loop.check_lean_lock(LEAN)["commit"] == head
    else:
        with pytest.raises(loop.LoopError, match="lean-checker.lock"):
            loop.check_lean_lock(LEAN)
    with pytest.raises(loop.LoopError):
        loop.check_lean_lock(tmp_path)


def test_budgets_persist_across_sessions(tmp_path):
    cfg = merge(base_config(tmp_path, [], open_lane={"enabled": False}))
    cfg["open_lane"].update(lean_project=str(tmp_path), work_dir=str(tmp_path / "work"), compile_calls=1)
    entries = [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64}]
    s = Session.create(tmp_path / "a" / "open_lane", cfg, "tests/max2_tiny", entries, tmp_path / "run")
    s._spend("lean_check")
    again = Session.create(tmp_path / "a" / "open_lane", cfg, "tests/max2_tiny", entries, tmp_path / "run")
    assert again.remaining()["lean_check"] == 0
    with pytest.raises(Exception, match="budget"):
        again._spend("lean_check")


@pytest.mark.skipif(not HAVE_LEAN, reason="the Lean project with a built acceptcheck is not next to this repository")
def test_a_fake_session_submits_the_scored_example_and_the_receipt_becomes_a_record(tmp_path):
    scripts = [str(REPO_ROOT / "tests" / "open_lane" / "scored_brute.json"), str(REPO_ROOT / "tests" / "open_lane" / "nothing.json")]
    cfg_path = tmp_path / "run.yaml"
    import yaml

    cfg_path.write_text(yaml.safe_dump(base_config(tmp_path, scripts)))
    lines = []
    ctx = loop.start(cfg_path, log=lines.append)
    loop.drive(ctx)
    records = ctx.run.read_archive()
    ok = [r for r in records if r["status"] == "ok"]
    assert len(ok) == 1 and ok[0]["lane"] == "open" and ok[0]["certified"] == 64 and ok[0]["length"] == 4112
    assert ok[0]["checked_by"] == "lean" and ok[0]["network"] == "max2_tiny-v8-s0" and ok[0]["round"] == 1
    assert "reference_warning" not in ok[0]
    lemma = [r for r in records if r["status"] == "lemma"]
    assert len(lemma) == 1 and "countP" in lemma[0]["statement"] and lemma[0]["certified"] is None
    assert [r["status"] for r in records if r["round"] == 2] == ["no_submission"]
    meta = ctx.run.read(1, "attempt_0/response_meta.json")
    assert meta["submissions"] == 2 and meta["tools_used"] == {"lean_check": 1, "submit_candidate": 2, "run_python": 1}
    log = [json.loads(l) for l in (ctx.run.round_path(1) / "attempt_0" / "open_lane" / "tools.jsonl").read_text().splitlines()]
    assert [l["tool"] for l in log] == ["search_library", "run_python", "lean_check", "submit_candidate", "submit_candidate"]
    assert "M (8, 8)" in log[1]["outcome"]["output"] and log[2]["outcome"]["ok"]
    # the prompt of round 2 shows the receipt, the lemma, the accepted sources and the notes
    prompt = ctx.run.read(2, "prompt.md")
    assert "length 4,112" in prompt and "countSingles" in prompt and "column sums" in prompt and "auxiliary lemma accepted" in prompt
    assert "{COUNTED}" not in prompt and "def qadd" in prompt and "Correct" in prompt
    summary = loop.status_text(ctx.run)
    assert "Q" in summary
    # patience for the open lane: round 1 accepted new artifacts, round 2 none
    assert loop.rounds_without_new_artifact(ctx.run) == 1
    # the final evaluation refuses an open-lane run until frozen transfer exists
    from core import final

    with pytest.raises(final.FinalError, match="frozen"):
        final.evaluate(ctx.run.path, log=lines.append)
    # the run recorded the Lean service's identity, and every receipt carries the same digests
    started = json.loads((ctx.run.path / "versions.json").read_text())
    ident = started["lean_checker"]
    assert set(ident) == set(loop.LEAN_IDENTITY_KEYS) and ident["commit"] == json.loads(loop.LEAN_LOCK.read_text())["commit"]
    digests = ok[0]["receipt"]["digests"]
    assert all(digests[k] == ident[k] for k in loop.LEAN_IDENTITY_KEYS)
    # resume refuses a service that is not the one the run started with, whatever today's lock says
    import pytest as _pytest

    real_identity, real_lock = loop.lean_identity, loop.LEAN_LOCK
    try:
        loop.lean_identity = lambda project, **kw: {**ident, "policy": "0000000000000000"}
        with _pytest.raises(loop.LoopError, match="policy"):
            loop.resume(ctx.run.path, log=lines.append)
        loop.lean_identity = real_identity
        moved = tmp_path / "moved.lock"
        moved.write_text(json.dumps({**json.loads(real_lock.read_text()), "commit": "f" * 40}))
        loop.LEAN_LOCK = moved
        with _pytest.raises(loop.LoopError, match="moved"):
            loop.resume(ctx.run.path, log=lines.append)
    finally:
        loop.lean_identity, loop.LEAN_LOCK = real_identity, real_lock
    # resume: nothing is redone, nothing is added
    before = len(records)
    ctx2 = loop.resume(ctx.run.path, log=lines.append)
    loop.drive(ctx2)
    assert len(ctx2.run.read_archive()) == before


def test_patience_counts_claims_not_files(tmp_path):
    """Progress detection for the open lane, with no Lean: a run folder with synthetic archive records.
    Round 1 accepts a scored proof and a lemma; round 2 resubmits both from files with a changed comment
    (new digests, same claims): not progress; round 3 proves a second theorem already present in the same
    unchanged file (same digests, new statement): progress; round 4 improves the length: progress; round 5
    repeats round 4's claim under another theorem name, adds a verified-only proof of a count that has a
    scored one, and a rejection: not progress."""
    from core.archive import RunDir

    run = RunDir(tmp_path / "runs", "patience-test")
    run.create({"run_id": "patience-test"})
    base = {"run_id": "patience-test", "lane": "open", "network": "n1", "attempt": 0}

    def rec(k, i, **f):
        return {**base, "round": k, "record_id": f"patience-test/r{k:03d}/a0/n1/open{i:03d}",
                "receipt": {"digests": {"modules": f.pop("digest")}}, **f}

    rounds = {
        1: [rec(1, 0, status="ok", certified=23, length=642, theorem="A.performance", digest="d1"),
            rec(1, 1, status="lemma", statement="∀ x, p x", theorem="A.lemma1", digest="d1")],
        2: [rec(2, 0, status="ok", certified=23, length=642, theorem="A.performance", digest="d2"),
            rec(2, 1, status="lemma", statement="∀ x,  p x", theorem="A.lemma1", digest="d2")],
        3: [rec(3, 0, status="lemma", statement="∀ x, q x", theorem="A.lemma2", digest="d2")],
        4: [rec(4, 0, status="ok", certified=23, length=600, theorem="A.performance", digest="d4")],
        5: [rec(5, 0, status="ok", certified=23, length=600, theorem="A.performance2", digest="d5"),
            rec(5, 1, status="verified", certified=23, theorem="A.performance3", digest="d5"),
            rec(5, 2, status="rejected", theorem="A.performance4", digest="d6")],
    }
    expected = {1: 0, 2: 1, 3: 0, 4: 0, 5: 1}
    for k in range(1, 6):
        run.round_path(k).mkdir(parents=True)
        run.append_archive(rounds[k])
        run.mark_done(k)
        assert loop.rounds_without_new_artifact(run) == expected[k], k
    assert loop.claim_identity(rounds[5][2]) is None


@pytest.mark.parametrize("metric,B,plan", [("Q_above", 12571, {"read": 138, "tree": 73}), ("cost_of_finishing", 12360, {})])
def test_patience_under_q_above_needs_a_gain_or_a_new_lemma(tmp_path, metric, B, plan):
    """Under the metric Q_above (26 October 2026) a scored proof keeps the loop alive only if it raised
    Q_above: a brute-force subset (a new count and length at the line) is not progress, nor is a proof
    worse than an earlier one; a new lemma still is, and a proof above the line is. The same under cost of
    finishing (10 November 2026), where finishing from a brute-force subset costs exactly B (cost-v4's B,
    E plus one forward pass per input; the Q_above case keeps its cost-v3 record, plan charges and all)."""
    from core.archive import RunDir

    run = RunDir(tmp_path / "runs", "patience-q")
    run.create({"run_id": "patience-q"})
    base = {"run_id": "patience-q", "lane": "open", "network": "n1", "attempt": 0, "n_inputs": 64, "knob": 1.0,
            "length_by_rule": {"bill": 0, "extract": 136, "read": 0}}
    entries = [{"id": "n1", "setting": "v8", "n_inputs": 64, "E": 136, "B": B, "real_correct": 64}]
    round0 = {"run_id": "patience-q", "round": 0, "attempt": 0, "network": "n1", "status": "ok", "certified": 64, "n_inputs": 64,
              "length": B, "knob": 0.0, "record_id": "patience-q/r000/a0/n1/k0", "source": "baseline",
              "length_by_rule": {"extract": 136, "single": 12224, **plan},
              "leaves": {"accepted": 64, "rejected": 0, "skipped": 0, "total": 64}}
    run.round_path(0).mkdir(parents=True)
    run.append_archive([round0])
    run.mark_done(0)

    def rec(k, i, **f):
        return {**base, "round": k, "record_id": f"patience-q/r{k:03d}/a0/n1/open{i:03d}",
                "receipt": {"digests": {"modules": f"d{k}{i}"}}, **f}

    rounds = {
        1: [rec(1, 0, status="ok", certified=10, length=191 * 10 + 136, theorem="A.p")],  # a subset: at the line
        2: [rec(2, 0, status="ok", certified=32, length=191 * 32 + 136, theorem="B.p")],  # another: still nothing
        3: [rec(3, 0, status="lemma", statement="∀ x, p x", theorem="C.l")],  # a new lemma: progress
        4: [rec(4, 0, status="ok", certified=20, length=2000, theorem="D.p")],  # above the line: progress
        5: [rec(5, 0, status="ok", certified=20, length=2500, theorem="E.p")],  # worse than round 4: nothing
    }
    expected = {1: 1, 2: 2, 3: 0, 4: 0, 5: 1}
    for k in range(1, 6):
        run.round_path(k).mkdir(parents=True)
        run.append_archive(rounds[k])
        run.mark_done(k)
        assert loop.rounds_without_new_artifact(run, entries, metric) == expected[k], k
    # under the claim rule alone, round 5's new length would have counted as progress
    assert loop.rounds_without_new_artifact(run) == 0


def test_the_tool_backend_reports_the_counters_the_tools_saved(tmp_path):
    """The tools run in the MCP server's process and save their counters to the session; the backend's
    metadata must come from that saved state, not from the session it loaded before the CLI ran. A fake
    CLI that bumps the saved counters (as the server would) and answers; no Lean, no model."""
    from core.open_lane.backends import ClaudeCodeToolBackend

    def result_json(text):
        """What the CLI prints with --output-format stream-json --verbose: one JSON object per line."""
        events = [
            {"type": "system", "subtype": "init", "session_id": "sess_1"},
            {"type": "assistant", "session_id": "sess_1",
             "message": {"role": "assistant", "content": [{"type": "text", "text": text}], "stop_reason": "end_turn"}},
            {"type": "result", "subtype": "success", "is_error": False, "result": text, "session_id": "sess_1",
             "total_cost_usd": 0.1, "num_turns": 1, "usage": {"input_tokens": 10, "output_tokens": 5}},
        ]
        return "\n".join(json.dumps(e) for e in events) + "\n"

    cfg = merge(base_config(tmp_path, [], backend="claude_code", agent_model="m"))
    where = tmp_path / "runs" / "r" / "round_001" / "attempt_0"
    where.mkdir(parents=True)

    def cli(cmd, prompt_text, env, cwd, timeout_s):
        state_path = where / "open_lane" / "session.json"
        state = json.loads(state_path.read_text())
        state["used"] = {"lean_check": 2, "submit_candidate": 1, "run_python": 3}
        state_path.write_text(json.dumps(state))

        class Done:
            stdout, stderr, returncode = result_json("CLAIM: nothing"), "", 0

        return Done()

    b = ClaudeCodeToolBackend(cfg, log=lambda *a: None, runner=cli, sleep=lambda s: None, environ={"PATH": "/usr/bin"})
    b.bind(cfg, "max2_tiny", [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64}], where.parent.parent)
    from core.agent.build_prompt import Prompt

    r = b.respond(Prompt("one", "two", {}), 0, where=where)
    assert r.meta["tools_used"] == {"lean_check": 2, "submit_candidate": 1, "run_python": 3}


def test_a_receipt_is_evidence_only_with_the_whole_identity_of_the_service_the_run_started_with():
    """No Lean: the receipt check alone. An accepted receipt must carry all five digests of the service
    (commit, toolchain, trusted sources, policy, the acceptcheck binary) and each must equal what the run
    recorded; a missing field or a changed binary halts the run; a receipt rejected before its digests were
    complete is checked on what it has."""
    from core.open_lane.records import check_receipt_identity

    ident = {"commit": "c" * 40, "toolchain": "lean:aaaa", "lean_project": "bbbb", "policy": "cccc", "acceptcheck": "dddd"}
    accepted = {"status": "accepted", "receipt_path": "r.json", "digests": {**ident, "modules": {"Candidate.X": "ee"}}}
    check_receipt_identity(accepted, ident)
    for k in ident:
        incomplete = {**accepted, "digests": {kk: v for kk, v in accepted["digests"].items() if kk != k}}
        with pytest.raises(RuntimeError, match=k):
            check_receipt_identity(incomplete, ident)
    rebuilt = {**accepted, "digests": {**accepted["digests"], "acceptcheck": "ffff"}}
    with pytest.raises(RuntimeError, match="acceptcheck"):
        check_receipt_identity(rebuilt, ident)
    with pytest.raises(RuntimeError, match="no Lean checker identity"):
        check_receipt_identity(accepted, None)
    rejected_early = {"status": "rejected", "receipt_path": "r.json", "digests": {"commit": ident["commit"], "toolchain": ident["toolchain"]}}
    check_receipt_identity(rejected_early, ident)
    rejected_elsewhere = {**rejected_early, "digests": {**rejected_early["digests"], "toolchain": "lean:zzzz"}}
    with pytest.raises(RuntimeError, match="toolchain"):
        check_receipt_identity(rejected_elsewhere, ident)


def test_the_identity_command_must_succeed_and_report_every_field():
    """No Lean: what the pipeline accepts from `accept.py identity` at the start of a run."""
    full = {"commit": "c" * 40, "dirty": False, "toolchain": "lean:aaaa", "lean_project": "bbbb", "policy": "cccc", "acceptcheck": "dddd"}
    assert loop.parse_identity(0, json.dumps(full), "", "P") == {k: full[k] for k in loop.LEAN_IDENTITY_KEYS}
    with pytest.raises(loop.LoopError, match="exit 1"):
        loop.parse_identity(1, json.dumps(full), "boom", "P")
    with pytest.raises(loop.LoopError, match="did not report"):
        loop.parse_identity(0, "not json", "", "P")
    with pytest.raises(loop.LoopError, match="acceptcheck"):
        loop.parse_identity(0, json.dumps({**full, "acceptcheck": None}), "", "P")
    with pytest.raises(loop.LoopError, match="uncommitted"):
        loop.parse_identity(0, json.dumps({**full, "dirty": True}), "", "P")


def test_read_file_reaches_the_sources_and_the_prompts_examples_only(tmp_path):
    """No Lean: a fake project folder. The agent may read the Lean sources, the docs and the two examples
    its prompt shows, not the other examples (earlier proofs of the same networks: reading one would be
    copying, not research), and nothing outside the project."""
    project = tmp_path / "lean"
    for rel in ("CompactCheck/Spec.lean", "docs/COUNTED.md", "examples/open_lane/max2_tiny_scored/Candidate/X.lean",
                "examples/open_lane/max2_tiny_brute/Candidate/X.lean", "examples/open_lane/max2_tiny_cols23_v3/Candidate/X.lean",
                "examples/open_lane/max2_tiny_cols23_v3/manifest.json", "examples/open_lane/max2_tiny_agent_cols23/README.md",
                "scripts/accept.py", "accept/allowlist.txt"):
        (project / rel).parent.mkdir(parents=True, exist_ok=True)
        (project / rel).write_text("line one\nline two\n")
    (tmp_path / "secret.txt").write_text("no")
    cfg = merge(base_config(tmp_path, []))
    cfg["open_lane"]["lean_project"] = str(project)
    session = Session.create(tmp_path / "attempt" / "open_lane", cfg, "max2_tiny",
                             [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64}], tmp_path / "run")
    for ok in ("CompactCheck/Spec.lean", "docs/COUNTED.md", "examples/open_lane/max2_tiny_scored/Candidate/X.lean",
               "examples/open_lane/max2_tiny_brute/Candidate/X.lean", "accept/allowlist.txt"):
        assert session.read_file(ok)["total_lines"] == 2, ok
    from core.open_lane.session import ToolError

    for refused in ("examples/open_lane/max2_tiny_cols23_v3/Candidate/X.lean", "examples/open_lane/max2_tiny_cols23_v3/manifest.json",
                    "examples/open_lane/max2_tiny_agent_cols23/README.md", "examples/open_lane/", "scripts/accept.py",
                    "../secret.txt", "/etc/passwd", "examples/open_lane/max2_tiny_scored/../max2_tiny_cols23_v3/Candidate/X.lean"):
        with pytest.raises(ToolError):
            session.read_file(refused)


def fake_project(tmp_path: Path, files: dict) -> Path:
    project = tmp_path / "lean"
    for rel, text in files.items():
        (project / rel).parent.mkdir(parents=True, exist_ok=True)
        (project / rel).write_text(text)
    return project


def test_read_file_reaches_the_runs_worked_example_and_no_other(tmp_path):
    """A run on attention networks shows another worked example (open_lane.example); read_file reaches its
    folder too, and still no other example."""
    attn = "examples/open_lane/attn_max2_tiny_scored/Candidate/AttnTinyScored.lean"
    project = fake_project(tmp_path, {attn: "a\nb\n", "examples/open_lane/attn_max2_tiny_scored/manifest.json": "{}\n",
                                      "examples/open_lane/pilot2_max2_tiny/Candidate/X.lean": "x\n"})
    cfg = merge(base_config(tmp_path, []))
    cfg["open_lane"].update(lean_project=str(project), example=attn)
    session = Session.create(tmp_path / "attempt" / "open_lane", cfg, "attn_max2_tiny",
                             [{"id": "attn_max2_tiny-v8d4-s1", "setting": "v8d4", "n_inputs": 64}], tmp_path / "run")
    assert session.read_file(attn)["total_lines"] == 2
    assert session.read_file("examples/open_lane/attn_max2_tiny_scored/manifest.json")["total_lines"] == 1
    from core.open_lane.session import ToolError

    with pytest.raises(ToolError):
        session.read_file("examples/open_lane/pilot2_max2_tiny/Candidate/X.lean")


def test_the_prompt_shows_the_configured_example_shortened_and_the_further_sources(tmp_path):
    """open_lane.example and open_lane.extra_sources choose what part 1 shows; a run of facts that differ only
    in their numbers (an instance split into one decided fact per input) is shortened to its first two and
    its last, with a count; template v2 has a place for the further sources."""
    from core.agent.build_prompt import load_template, placeholders
    from core.model_folder import load_model_folder
    from core.open_lane.prompt import elide_repeats, static_values

    facts = "\n\n".join(f"theorem in_{a}_{b} : run1 [{a}, {b}] = some (true, 191) := by\n  decide +kernel"
                        for a in range(3) for b in range(3))
    example = "import X\n\ndef D := 1\n\n" + facts + "\n\ntheorem D_instance : True := trivial\n"
    short = elide_repeats(example)
    assert "theorem in_0_0" in short and "theorem in_0_1" in short and "theorem in_2_2" in short
    assert "theorem in_1_1" not in short and "-- ... 6 more of the same form, one per input ..." in short
    assert "theorem D_instance" in short and elide_repeats("a\n\nb\n\nc") == "a\n\nb\n\nc"
    files = {"scripts/accept.py": "", "CompactCheck/Spec.lean": "-- spec", "CompactCheck/Counted.lean": "-- counted",
             "CompactCheck/CountedOps.lean": "-- ops", "CompactCheck/CountedGeneral.lean": "-- general single rule",
             "examples/open_lane/attn/Candidate/A.lean": example}
    project = fake_project(tmp_path, files)
    cfg = merge(base_config(tmp_path, [], model="tests/attn_max2_tiny", prompt_template="open_lane_v3"))
    cfg["open_lane"].update(lean_project=str(project), example="examples/open_lane/attn/Candidate/A.lean",
                            extra_sources=["CompactCheck/CountedGeneral.lean"])
    folder = load_model_folder(REPO_ROOT / "tests" / "attn_max2_tiny")
    entries = [{"id": "attn_max2_tiny-v8d4-s1", "setting": "v8d4", "n_inputs": 64, "E": 136, "B": 12571, "real_correct": 64}]
    values = static_values(cfg, folder, entries)
    assert "more of the same form" in values["EXAMPLE"] and "theorem in_1_1" not in values["EXAMPLE"]
    assert values["EXTRA_SOURCES"].startswith("From CompactCheck/CountedGeneral.lean:") and "general single rule" in values["EXTRA_SOURCES"]
    part1, part2 = load_template("open_lane_v3")
    assert "{EXTRA_SOURCES}" in part1 and placeholders(part1) <= set(values)
    assert "CostM.gsingle_run_of" in part1
    # the instance is one decide with Lean's recursion limit raised (a few thousand charges stop the default)
    assert "set_option maxRecDepth 1000000 in\n    theorem D_instance" in part1
    # the accepted modules are in the workspace, listed; their sources are no longer pasted
    assert "{WORKSPACE}" in part2 and "{LEMMAS}" not in part2


def test_the_open_lane_config_names_its_example_and_sources_in_the_lean_project(tmp_path):
    from core.run_config import RunConfigError

    project = fake_project(tmp_path, {"scripts/accept.py": "", "examples/open_lane/max2_tiny_scored/Candidate/Max2TinyScored.lean": "x"})
    good = base_config(tmp_path, [])
    good["open_lane"]["lean_project"] = str(project)
    assert merge(good)["open_lane"]["extra_sources"] == []
    for bad, match in (({"example": "examples/none.lean"}, "has no examples/none.lean"),
                       ({"extra_sources": ["CompactCheck/None.lean"]}, "has no CompactCheck/None.lean"),
                       ({"extra_sources": "CompactCheck/X.lean"}, "extra_sources must be a list")):
        cfg = base_config(tmp_path, [])
        cfg["open_lane"].update(lean_project=str(project), **bad)
        with pytest.raises(RunConfigError, match=match):
            merge(cfg)


@pytest.mark.parametrize("metric", ["Q", "Q_grid", "Q_exact", "Q_above", "cost_of_finishing"])
def test_the_open_lane_prompt_builds_for_every_metric(tmp_path, monkeypatch, metric):
    """Review of 23 October: the open-lane aim had no entry for Q_exact, so the first prompt of a Q_exact run
    raised KeyError. The whole prompt, both parts, for each metric the run config accepts, from a fake Lean
    project and an archive with round 0's brute-force record. Part 2 lists the module round 1 had accepted,
    carried into the workspace (the service's compile replaced), without pasting its source."""
    from core.archive import RunDir
    from core.model_folder import load_model_folder
    from core.open_lane.prompt import build_open_lane_prompt
    from core.run_config import METRICS

    assert metric in METRICS
    files = {"scripts/accept.py": "", "CompactCheck/Spec.lean": "-- spec", "CompactCheck/Counted.lean": "-- counted",
             "CompactCheck/CountedOps.lean": "-- ops", "CompactCheck/CountedGeneral.lean": "-- general",
             "CompactCheck/CountedGeneralSound.lean": "-- sound",
             "examples/open_lane/attn_max2_tiny_scored/Candidate/AttnTinyScored.lean": "-- example"}
    project = fake_project(tmp_path, files)
    cfg = merge(base_config(tmp_path, [], model="tests/attn_max2_tiny", prompt_template="open_lane_v3", metric=metric))
    cfg["open_lane"].update(lean_project=str(project),
                            example="examples/open_lane/attn_max2_tiny_scored/Candidate/AttnTinyScored.lean",
                            extra_sources=["CompactCheck/CountedGeneral.lean", "CompactCheck/CountedGeneralSound.lean"])
    folder = load_model_folder(REPO_ROOT / "tests" / "attn_max2_tiny")
    from core.zoo import networks

    entries = [e for e in networks(folder) if e["split"] == "dev"]
    run = RunDir(tmp_path / "runs", "prompt-" + metric)
    run.create(cfg)
    e = entries[0]
    run.append_archive([{"run_id": run.run_id, "round": 0, "attempt": 0, "record_id": "r0", "network": e["id"],
                         "setting": e["setting"], "status": "ok", "certified": e["n_inputs"], "n_inputs": e["n_inputs"],
                         "length": e["B"], "length_by_rule": {"single": 64 * 191, "tree": e["B"] - 64 * 191 - e["E"],
                                                              "extract": e["E"]}, "knob": 1.0,
                         "leaves": {"accepted": 64, "rejected": 0, "skipped": 0, "total": 64}}])
    # a brute-force subset and a proof above the line, as the agent's receipts
    run.round_path(1).mkdir(parents=True)
    run.append_archive([{"run_id": run.run_id, "round": 1, "attempt": 0, "record_id": "r1a", "network": e["id"], "lane": "open",
                         "submission": 0, "claimed_count": 10, "setting": e["setting"], "status": "ok", "certified": 10,
                         "n_inputs": 64, "length": 191 * 10 + e["E"], "length_by_rule": {"bill": 1910, "extract": e["E"], "read": 0},
                         "knob": 1.0},
                        {"run_id": run.run_id, "round": 1, "attempt": 0, "record_id": "r1b", "network": e["id"], "lane": "open",
                         "submission": 1, "claimed_count": 20, "setting": e["setting"], "status": "ok", "certified": 20,
                         "n_inputs": 64, "length": 2000, "length_by_rule": {"bill": 1864, "extract": e["E"], "read": 0}, "knob": 1.0}])
    _submission(run.path, 1, 2, {"Candidate/Tables.lean": "theorem tables_ok : 2 + 2 = 4 := rfl\n"})
    monkeypatch.setattr(Session, "_service", lambda self, args, timeout_s: {"ok": True, "messages": ""})
    run.mark_done(1)
    p = build_open_lane_prompt(cfg, folder, entries, run, 2)
    assert "YOUR WORKSPACE" in p.part2 and "- Candidate/Tables.lean (1 lines; round 1, submission 2" in p.part2
    assert "tables_ok" not in p.part2 and "ACCEPTED LEMMAS" not in p.part2
    assert "Raise the score. It stands at: " + metric in p.part2
    assert (" mean " in p.part2.split("Raise the score", 1)[1]) == (metric in ("Q_exact", "Q_above", "cost_of_finishing"))
    assert "-- general" in p.part1 and "{" + "EXTRA_SOURCES}" not in p.part1
    if metric == "cost_of_finishing":
        # one score and nothing else; per network the cheapest way to finish; the receipts say what finishing
        # from each proof costs (a brute-force subset: exactly B, so nothing)
        assert "Score: 1.188 (cost of finishing, the geometric mean over the 1 network of the run" in p.part2
        assert not any(other in p.part2 for other in ("Q_above", "Q_exact", "Q median", "brute-force line"))
        assert ("Cheapest way to finish: 10,404 = a proof of length 2,000 certifying 20 of the 64 correct inputs, plus 44 "
                "inputs by brute force at 191 each (B = 12,360)") in p.part2
        assert "finishing from it costs 12,360, no less than brute force (12,360): it adds nothing to the score" in p.part2
        assert "finishing from it costs 10,404, against 12,360 for brute force (a ratio of 1.188)" in p.part2
        assert "It stands at: cost_of_finishing: 1.188, the geometric mean over the run's 1 network." in p.part2
        assert "geometric mean over the networks of the run" in p.part1 and "There are no budgets to aim at." in p.part1
        return
    # the receipts say which proofs beat brute force; the scoreboard shows the line
    assert "not above the brute-force line (which certifies 10 at this length): scores nothing" in p.part2
    assert "above the brute-force line (which certifies 9 at this length)" in p.part2
    assert "1 above the brute-force line (k inputs for 191 k + 136, up to 64)" in p.part2
    if metric == "Q_above":
        assert "brute force on any subset of the inputs scores exactly 0" in p.part1



LADDER_FILES = {"scripts/accept.py": "", "CompactCheck/Spec.lean": "-- spec", "CompactCheck/Counted.lean": "-- counted",
                "CompactCheck/CountedOps.lean": "-- ops", "CompactCheck/CountedGeneral.lean": "-- general",
                "CompactCheck/CountedGeneralSound.lean": "-- sound",
                "examples/open_lane/attn_max2_tiny_scored/Candidate/AttnTinyScored.lean": "-- example",
                "examples/open_lane/pilot2_max2_tiny/r1_ColFull/Candidate/ColFull.lean": "-- the column proof",
                "examples/open_lane/pilot2_max2_tiny/r4_Full64/Candidate/Full64.lean": "-- another proof"}


def ladder_pilot_config(tmp_path: Path, project: Path) -> dict:
    """config/open-lane-pilot-attn-maxn-tiny.yaml as a run would read it, with this machine's paths and the
    fake backend (no model is called)."""
    import yaml

    raw = yaml.safe_load((REPO_ROOT / "config" / "open-lane-pilot-attn-maxn-tiny.yaml").read_text())
    raw.update(backend="fake", runs_dir=str(tmp_path / "runs"), sandbox="auto")
    raw["open_lane"].update(lean_project=str(project), work_dir=str(tmp_path / "work"), fake_scripts=[])
    return raw


def test_the_ladder_pilot_scores_six_networks_on_cost_of_finishing_with_prompt_v4(tmp_path, monkeypatch):
    """The pilot of 10 November 2026: three sizes of the tiny attention network (context lengths 2, 3, 4),
    two development seeds each, scored on cost of finishing as the geometric mean over the six; prompt
    template v4. Part 1 puts the score before the rules and says what is wanted (the mechanism: one checker
    for every size and seed); part 2 shows that one score, each network's cheapest way to finish, and how
    many networks no proof has reached. From a fake Lean project; no service and no model."""
    from core.archive import RunDir
    from core.loop import select_networks
    from core.model_folder import load_model_folder
    from core.open_lane.prompt import build_open_lane_prompt

    project = fake_project(tmp_path, LADDER_FILES)
    cfg = merge(ladder_pilot_config(tmp_path, project))
    assert (cfg["metric"], cfg["prompt_template"], cfg["open_lane"]["knowledge"], cfg["open_lane"]["second_example"]) == (
        "cost_of_finishing", "open_lane_v4", "minimal", None)
    folder = load_model_folder(REPO_ROOT / cfg["model"])
    entries = select_networks(folder, cfg)
    assert [(e["setting"], e["seed"], e["split"]) for e in entries] == [
        ("n2v8d4", 1, "dev"), ("n2v8d4", 2, "dev"), ("n3v4d4", 0, "dev"), ("n3v4d4", 2, "dev"), ("n4v4d4", 0, "dev"), ("n4v4d4", 2, "dev")]
    assert cfg["open_lane"]["submissions"] >= len(entries)  # a submission per network each round
    run = RunDir(tmp_path / "runs", cfg["run_id"])
    run.create(cfg)
    run.round_path(0).mkdir(parents=True)
    run.append_archive([{"run_id": run.run_id, "round": 0, "attempt": 0, "record_id": f"r0/{e['id']}", "network": e["id"],
                         "setting": e["setting"], "status": "ok", "certified": e["n_inputs"], "n_inputs": e["n_inputs"],
                         "length": e["B"], "length_by_rule": {"single": e["B"] - e["E"], "extract": e["E"]}, "knob": 1.0,
                         "leaves": {"accepted": e["n_inputs"], "rejected": 0, "skipped": 0, "total": e["n_inputs"]}} for e in entries])
    run.mark_done(0)
    monkeypatch.setattr(Session, "_service", lambda self, args, timeout_s: {"ok": True, "messages": ""})
    first = build_open_lane_prompt(cfg, folder, entries, run, 1)
    p1 = first.part1
    assert first.stats["template"] == "open_lane_v4" and "{" + "SECOND_EXAMPLE}" not in p1 and "second worked example" not in p1
    order = [p1.index(h) for h in ("GOAL", "What we are after is the mechanism", "THE NETWORKS", "SCORING", "WHAT A PROOF IS",
                                   "WHAT A PROOF COSTS", "What a checker may use.", "Limits on the general layer",
                                   "Getting the instance through the kernel:", "YOUR TOOLS", "HOW TO WORK", "HOW TO ANSWER")]
    assert order == sorted(order)
    assert "the geometric mean over the networks of the run" in p1 and "Q_above" not in p1 and "budget grid" not in p1
    assert "set_option maxRecDepth 1000000 in\n    theorem D_instance" in p1 and "8192 + 4E" in p1
    assert "read the sizes with `I.weightShape`" in p1 and "Get a scored proof through the service early" in p1
    for e in entries:
        assert f"- {e['id']} ({e['setting']}): correct" in p1
    assert "Score: 1.000 (cost of finishing, the geometric mean over the 6 networks of the run" in first.part2
    assert "6 of the 6 networks still stand at 1.000" in first.part2
    # round 1: a complete proof on one network, a partial one on its sibling seed
    def scored(i, e, certified, length):
        return {"run_id": run.run_id, "round": 1, "attempt": 0, "record_id": f"r1/{i}", "network": e["id"], "lane": "open",
                "submission": i, "claimed_count": certified, "setting": e["setting"], "status": "ok", "certified": certified,
                "n_inputs": e["n_inputs"], "length": length, "length_by_rule": {"bill": length - e["E"], "extract": e["E"], "read": 0},
                "knob": 1.0}

    run.round_path(1).mkdir(parents=True, exist_ok=True)  # the first prompt opened round 1's session there
    run.append_archive([scored(0, entries[0], 64, 3090), scored(1, entries[1], 40, 1800)])
    run.mark_done(1)
    p2 = build_open_lane_prompt(cfg, folder, entries, run, 2).part2
    sibling = 12360 / (1800 + 24 * 191)
    assert f"Score: {(4.0 * sibling) ** (1 / 6):.3f} (cost of finishing" in p2
    assert f"n2v8d4: geometric mean {(4.0 * sibling) ** 0.5:.3f}" in p2 and "n4v4d4: geometric mean 1.000" in p2
    assert f"{entries[0]['id']}: 4.000. Cheapest complete proof: length 3,090, certifying all 64 correct inputs" in p2
    assert "plus 24 inputs by brute force at 191 each" in p2 and "4 of the 6 networks still stand at 1.000" in p2
    assert not any(other in p2 for other in ("Q_above", "Q_exact", "Q median", "brute-force line"))


def test_a_second_worked_example_is_named_and_readable_only_when_the_run_config_says_so(tmp_path):
    """open_lane.second_example (off by default): a scored proof that is not brute force, named in prompt v4
    and readable with read_file, its source not pasted. Only that proof's folder becomes readable; its
    neighbours (other proofs of the same pilot) stay out of reach. It must be a file under examples/."""
    from core.model_folder import load_model_folder
    from core.open_lane.prompt import static_values
    from core.open_lane.session import readable_paths
    from core.run_config import RunConfigError

    project = fake_project(tmp_path, LADDER_FILES)
    second = "examples/open_lane/pilot2_max2_tiny/r1_ColFull/Candidate/ColFull.lean"
    off = merge(ladder_pilot_config(tmp_path, project))
    on = ladder_pilot_config(tmp_path, project)
    on["open_lane"]["second_example"] = second
    on = merge(on)
    folder = load_model_folder(REPO_ROOT / on["model"])
    entries = [{"id": "attn_maxn_tiny-n2v8d4-s1", "setting": "n2v8d4", "n_inputs": 64, "E": 136, "B": 12360, "real_correct": 64}]
    assert static_values(off, folder, entries)["SECOND_EXAMPLE"] == ""
    text = static_values(on, folder, entries)["SECOND_EXAMPLE"]
    assert second in text and "read it with read_file" in text and "the column proof" not in text
    example = on["open_lane"]["example"]
    assert "examples/open_lane/pilot2_max2_tiny/r1_ColFull/" not in readable_paths(example)
    readable = readable_paths(example, second)
    assert "examples/open_lane/pilot2_max2_tiny/r1_ColFull/" in readable
    assert not "examples/open_lane/pilot2_max2_tiny/r4_Full64/Candidate/Full64.lean".startswith(tuple(readable))
    session = Session.create(tmp_path / "attempt" / "open_lane", on, on["model"], entries, tmp_path / "run")
    assert "the column proof" in session.read_file(second)["text"]
    from core.open_lane.session import ToolError

    with pytest.raises(ToolError):
        session.read_file("examples/open_lane/pilot2_max2_tiny/r4_Full64/Candidate/Full64.lean")
    for bad, match in (("CompactCheck/Spec.lean", "under examples/"), ("examples/open_lane/none/Candidate/X.lean", "has no examples/open_lane/none"),
                       ("examples/../scripts/accept.py", "under examples/")):
        cfg = ladder_pilot_config(tmp_path, project)
        cfg["open_lane"]["second_example"] = bad
        with pytest.raises(RunConfigError, match=match):
            merge(cfg)


def test_the_knowledge_condition_reaches_every_service_call_and_the_prompt(tmp_path):
    """open_lane.knowledge chooses the experimental condition (minimal: the base counted language; maximum: plus
    the fixed rules lane's rules for groups of inputs as operations). The session passes it to every call of the
    service, which checks a checker against that condition's allowlist; the prompt says which condition the
    run is; the config refuses anything else."""
    from core.open_lane.prompt import static_values
    from core.model_folder import load_model_folder
    from core.run_config import RunConfigError

    files = {"scripts/accept.py": "import json, sys\nprint(json.dumps({'ok': True, 'messages': ' '.join(sys.argv[1:])}))\n",
             "CompactCheck/Spec.lean": "-- spec", "CompactCheck/Counted.lean": "-- counted", "CompactCheck/CountedOps.lean": "-- ops",
             "examples/open_lane/max2_tiny_scored/Candidate/Max2TinyScored.lean": "-- example"}
    project = fake_project(tmp_path, files)
    folder = load_model_folder(REPO_ROOT / "tests" / "max2_tiny")
    entries = [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64, "E": 80, "B": 4323, "real_correct": 64}]
    for knowledge in ("minimal", "maximum"):
        cfg = merge(base_config(tmp_path, [], prompt_template="open_lane_v2"))
        cfg["open_lane"].update(lean_project=str(project), knowledge=knowledge)
        session = Session.create(tmp_path / knowledge / "open_lane", cfg, "tests/max2_tiny",
                                 [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64}], tmp_path / "run")
        out = session.lean_check("Candidate/X.lean", "-- x", "max2_tiny-v8-s0", 64)
        assert f"--knowledge {knowledge}" in out["messages"], out
        text = static_values(cfg, folder, entries)["KNOWLEDGE"]
        assert f"{knowledge}-knowledge condition" in text and "ginterval" in text and "gtokenIntervals" in text
    cfg = base_config(tmp_path, [])
    cfg["open_lane"].update(lean_project=str(project), knowledge="everything")
    with pytest.raises(RunConfigError, match="knowledge must be one of"):
        merge(cfg)


def test_the_tool_backend_never_records_another_models_session(tmp_path):
    """No Lean, no model: a fake CLI whose session was answered by another model must stop the run."""
    from core.agent.backends.api import StopRun
    from core.agent.build_prompt import Prompt
    from core.open_lane.backends import ClaudeCodeToolBackend

    cfg = merge(base_config(tmp_path, [], backend="claude_code", agent_model="m"))
    where = tmp_path / "runs" / "r" / "round_001" / "attempt_0"
    where.mkdir(parents=True)
    seen = []

    def cli(cmd, prompt_text, env, cwd, timeout_s):
        seen.append(env)
        events = [{"type": "system", "subtype": "model_fallback", "original_model": "m", "fallback_model": "other"},
                  {"type": "assistant", "session_id": "s",
                   "message": {"role": "assistant", "content": [{"type": "text", "text": "x"}], "stop_reason": "end_turn"}},
                  {"type": "result", "subtype": "success", "is_error": False, "result": "x", "session_id": "s", "usage": {}}]

        class Done:
            stdout, stderr, returncode = "\n".join(json.dumps(e) for e in events) + "\n", "", 0

        return Done()

    b = ClaudeCodeToolBackend(cfg, log=lambda *a: None, runner=cli, sleep=lambda s: None, environ={"PATH": "/usr/bin"})
    b.bind(cfg, "max2_tiny", [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64}], where.parent.parent)
    with pytest.raises(StopRun, match="other instead of m"):
        b.respond(Prompt("one", "two", {}), 0, where=where)
    assert seen[0]["CLAUDE_CODE_NO_MODEL_FALLBACK"] == "1"


def _submission(run: Path, k: int, n: int, modules: dict, kind: str = "auxiliary", status: str = "accepted") -> None:
    """A submission folder as a session leaves it: the modules as submitted, the manifest, the receipt."""
    d = run / f"round_{k:03d}" / "attempt_0" / "open_lane" / "submissions" / f"{n:03d}"
    for rel, text in modules.items():
        (d / rel).parent.mkdir(parents=True, exist_ok=True)
        (d / rel).write_text(text)
    (d / "manifest.json").write_text(json.dumps({
        "schema": "open-lane-candidate-v1", "kind": kind, "network": "max2_tiny-v8-s0", "model": "tests/max2_tiny",
        "claimed_count": 64 if kind == "performance" else 0, "theorem": "Candidate.A.t", "modules": list(modules)}))
    (d / "receipt.json").write_text(json.dumps({"status": status, "claim_kind": kind, "statement": "1 = 1"}))


def test_a_new_round_starts_with_the_accepted_modules_of_earlier_rounds_compiled(tmp_path, monkeypatch):
    """No Lean: the service's compile is replaced. What is carried, in which order, and what the tools do with it."""
    run = tmp_path / "run"
    _submission(run, 1, 0, {"Candidate/A.lean": "theorem t : 1 = 1 := rfl\n"})
    _submission(run, 1, 1, {"Candidate/R.lean": "theorem r : 1 = 2 := sorry\n"}, status="rejected")
    _submission(run, 2, 0, {"Candidate/B.lean": "import Candidate.A\n\ntheorem u : 2 = 2 := rfl\n",
                            "Candidate/A.lean": "theorem t : 1 = 1 := rfl\ntheorem t2 : 3 = 3 := rfl\n"})
    calls = []

    def fake_service(self, args, timeout_s):
        calls.append(args)
        return {"ok": args[2] != "Candidate/B.lean", "messages": "B.lean:3:0: error: something" if args[2] == "Candidate/B.lean" else ""}

    monkeypatch.setattr(Session, "_service", fake_service)
    cfg = merge(base_config(tmp_path, [], open_lane={"enabled": False}))
    cfg["open_lane"].update(lean_project=str(tmp_path), work_dir=str(tmp_path / "work"))
    entries = [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64}]
    where = run / "round_003" / "attempt_0" / "open_lane"
    s = Session.create(where, cfg, "tests/max2_tiny", entries, run)
    assert [c[2] for c in calls] == ["Candidate/A.lean", "Candidate/B.lean"]  # a module after the ones it imports
    assert all(c[0] == "compile" and "--claimed" in c for c in calls)
    assert s.remaining()["lean_check"] == cfg["open_lane"]["compile_calls"]  # not charged
    assert "t2" in (s.workspace / "Candidate/A.lean").read_text()  # the latest accepted version
    assert not (s.workspace / "Candidate/R.lean").exists()  # a rejected submission carries nothing
    carried = s.state["carried"]
    assert [(m["path"], m["round"], m["compiled"]) for m in carried] == [("Candidate/A.lean", 2, True), ("Candidate/B.lean", 2, False)]
    assert "something" in carried[1]["errors"][0]
    from core.open_lane.prompt import workspace_text

    text = workspace_text(carried)
    assert "Candidate/A.lean (2 lines; round 2, submission 0, accepted lemma Candidate.A.t): compiled" in text
    assert "Candidate/B.lean" in text and "did not compile here" in text
    assert workspace_text([]) == "none yet"
    # reopening the session (the backend does, after the prompt did) carries nothing again
    calls.clear()
    Session.create(where, cfg, "tests/max2_tiny", entries, run)
    assert calls == []
    # the agent reads its own modules, and a submission takes the modules its modules import
    assert "t2" in s.read_file("Candidate/A.lean")["text"]
    with pytest.raises(ToolError, match="no module"):
        s.read_file("Candidate/Missing.lean")
    assert s.with_imports(["Candidate/B.lean"]) == ["Candidate/B.lean", "Candidate/A.lean"]
    # an interrupted carry is done again when the session is reopened
    state = json.loads((where / "session.json").read_text())
    state["carried"] = "pending"
    (where / "session.json").write_text(json.dumps(state))
    Session.create(where, cfg, "tests/max2_tiny", entries, run)
    assert len(calls) == 2
    # round 1 has nothing to carry
    assert Session.create(run / "round_001" / "attempt_1" / "open_lane", cfg, "tests/max2_tiny", entries, run).state["carried"] == []


@pytest.mark.skipif(not HAVE_LEAN, reason="the Lean project with a built acceptcheck is not next to this repository")
def test_a_lemma_accepted_in_one_round_is_imported_in_the_next_without_being_pasted(tmp_path):
    lib = ("import CompactCheck.Spec\n\nnamespace Candidate.Lib\n\ntheorem two_eq : (2 : Nat) = 1 + 1 := rfl\n\n"
           "end Candidate.Lib\n")
    use = ("import Candidate.Lib\n\nnamespace Candidate.Use\n\ntheorem three_eq : (2 : Nat) + 1 = 3 := by\n"
           "  rw [Candidate.Lib.two_eq]\n\nend Candidate.Use\n")
    net = "max2_tiny-v8-s0"
    r1 = {"calls": [{"tool": "lean_check", "args": {"path": "Candidate/Lib.lean", "source": lib, "network": net, "claimed_count": 0}},
                    {"tool": "submit_candidate", "args": {"network": net, "claimed_count": 0, "kind": "auxiliary",
                                                          "theorem": "Candidate.Lib.two_eq", "modules": ["Candidate/Lib.lean"]}}],
          "response": "CLAIM: a lemma.\nWHY IT HELPS: to be imported.\nNOTES: import it next round."}
    r2 = {"calls": [{"tool": "lean_check", "args": {"path": "Candidate/Use.lean", "source": use, "network": net, "claimed_count": 0}},
                    {"tool": "submit_candidate", "args": {"network": net, "claimed_count": 0, "kind": "auxiliary",
                                                          "theorem": "Candidate.Use.three_eq", "modules": ["Candidate/Use.lean"]}}],
          "response": "CLAIM: a lemma that uses the last one.\nWHY IT HELPS: no pasting.\nNOTES: none."}
    scripts = []
    for i, s in enumerate((r1, r2)):
        p = tmp_path / f"r{i + 1}.json"
        p.write_text(json.dumps(s))
        scripts.append(str(p))
    import yaml

    cfg_path = tmp_path / "run.yaml"
    cfg_path.write_text(yaml.safe_dump(base_config(tmp_path, scripts)))
    ctx = loop.start(cfg_path, log=lambda *a: None)
    loop.drive(ctx)
    lemmas = [r for r in ctx.run.read_archive() if r["status"] == "lemma"]
    assert [(r["round"], r["theorem"]) for r in lemmas] == [(1, "Candidate.Lib.two_eq"), (2, "Candidate.Use.three_eq")]
    s2 = ctx.run.round_path(2) / "attempt_0" / "open_lane"
    carried = json.loads((s2 / "session.json").read_text())["carried"]
    assert [(m["path"], m["compiled"]) for m in carried] == [("Candidate/Lib.lean", True)]
    assert (s2 / "workspace" / "out" / "Candidate" / "Lib.olean").is_file()
    assert (s2 / "submissions" / "000" / "Candidate" / "Lib.lean").read_text() == lib  # added to the submission
    assert "Candidate/Lib.lean" in ctx.run.read(2, "prompt.md") or "Lib" in ctx.run.read(2, "prompt.md")
