"""The workflow of an open-lane run's proof rounds, chosen before the run starts (open_lane.workflow_mode).

- interleaved (the default, and every run made before the setting): the agent explores in Python and develops
  and submits Lean proofs in every round; prompt_template and patience as they were. Nothing here applies.
- python_then_lean: a fixed schedule of two phases, recorded when the run starts and kept on resume:

      round 0                        the baselines, as before
      rounds 1 .. discovery_rounds   discovery: Python experiments and mathematical arguments, written to the
                                     run's research folder (core/open_lane/research.py); a small Lean allowance
      the rounds after, to rounds_max  formalization: the strongest saved candidates into accepted Lean results
      then                           the seed check and the scaling question, as before (core/open_lane/stages.py)

  Patience does not apply in either phase (a discovery round without a submission is the plan, and its history
  must not use up formalization's rounds); the hard limits, a stop by the user, a backend's failure and the
  model declining stop a run as before. Each phase has its prompt template (TEMPLATES), recorded in each
  round's meta.

`phase` is a field of its own. It is not `stage`: a stage is a session after the proof rounds, under a lock,
whose records never count; a phase is a part of the proof rounds, and a formalization round's scored proofs
enter the frontier and the score as any proof round's.

The discovery phase's Lean allowance (probe_compile_calls, probe_auxiliary_submissions, probe_seconds) is a
total over the phase, kept in <run>/workflow/probes.json, which only the pipeline writes. A call takes its
share before it starts (the seconds it may run for), under the workflow lock, and settles it when it ends
with the seconds it took; a call that never settles (its process was killed) keeps the whole share. So a
crash, a resume or a new round never gives back what was spent.

The transition into formalization is recorded once (<run>/workflow/transition.json, with a read-only copy of
the whole research folder in <run>/workflow/discovery/): the shortlist the last discovery session left (or the
latest one there is), or, without one, the saved candidates unranked. Nothing is ranked for the agent.
"""

from __future__ import annotations

import json
import time
from pathlib import Path

from . import research

INTERLEAVED, PYTHON_THEN_LEAN = "interleaved", "python_then_lean"
MODES = (INTERLEAVED, PYTHON_THEN_LEAN)
DISCOVERY, FORMALIZATION = "discovery", "formalization"
TEMPLATES = {DISCOVERY: "open_lane_discovery_v1", FORMALIZATION: "open_lane_formalization_v1"}
STATE_FILE = "workflow.json"
PROBES_FILE = "probes.json"
TRANSITION_FILE = "transition.json"
SNAPSHOT_DIR = "discovery"
OUTCOMES = ("compiled", "compiler_error", "timeout", "infrastructure_error", "accepted", "rejected")


class WorkflowError(RuntimeError):
    pass


class ProbeRefused(ValueError):
    pass


# the mode and the phase -----------------------------------------------------------------------
def mode(cfg: dict) -> str:
    ol = cfg.get("open_lane") or {}
    return ol.get("workflow_mode", INTERLEAVED) if ol.get("enabled") else INTERLEAVED


def is_phased(cfg: dict) -> bool:
    return mode(cfg) == PYTHON_THEN_LEAN


def phase(cfg: dict, k: int) -> str | None:
    """The phase of proof round k (1 to rounds_max) in a python_then_lean run; None otherwise."""
    if not is_phased(cfg) or not 1 <= k <= int(cfg["rounds_max"]):
        return None  # round 0, and the sessions after the proof rounds, have no phase
    return DISCOVERY if k <= int(cfg["open_lane"]["discovery_rounds"]) else FORMALIZATION


def schedule(cfg: dict) -> dict:
    """What the run fixes when it starts: the mode, the phases' rounds and the discovery allowance."""
    ol = cfg["open_lane"]
    n, total = int(ol.get("discovery_rounds", 0)), int(cfg["rounds_max"])
    out = {"mode": mode(cfg), "rounds_max": total}
    if out["mode"] == PYTHON_THEN_LEAN:
        out.update(discovery_rounds=[1, n], formalization_rounds=[n + 1, total], templates=dict(TEMPLATES),
                   probe={"compile_calls": int(ol["probe_compile_calls"]), "auxiliary_submissions": int(ol["probe_auxiliary_submissions"]),
                          "seconds": float(ol["probe_seconds"])},
                   research={"mb": float(ol["research_workspace_mb"]), "files": int(ol["research_workspace_files"])})
    return out


def template(cfg: dict, k: int) -> str:
    """The prompt template of round k: the phase's in a python_then_lean run, prompt_template otherwise."""
    p = phase(cfg, k)
    return TEMPLATES[p] if p else cfg["prompt_template"]


def recorded(run_dir: Path) -> dict | None:
    p = Path(run_dir) / research.STATE_DIR / STATE_FILE
    return json.loads(p.read_text()) if p.is_file() else None


def record(run_dir: Path, cfg: dict) -> dict:
    """At the start of a python_then_lean run: the schedule, written once."""
    have = recorded(run_dir)
    if have is not None:
        return have
    data = {"schedule": schedule(cfg), "created": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    research._write_json(research.state_dir(run_dir) / STATE_FILE, data)
    return data


def check_resume(run_dir: Path, cfg: dict) -> None:
    """On resume: the schedule is the one the run started with. A run made before workflows has none and is
    interleaved; a python_then_lean run without its record, or with another, does not go on."""
    have = recorded(run_dir)
    if have is None:
        if is_phased(cfg):
            raise WorkflowError("this python_then_lean run has no record of its schedule (workflow/workflow.json); "
                                "it cannot be resumed as one: start a new run")
        return
    if have["schedule"] != schedule(cfg):
        raise WorkflowError("the run's workflow (mode, phases or the discovery allowance) differs from the one it started "
                            "with; a run keeps its schedule: start a new run for another")


def limits(run_dir: Path) -> dict:
    have = recorded(run_dir)
    if have is None or have["schedule"]["mode"] != PYTHON_THEN_LEAN:
        raise WorkflowError("the run has no python_then_lean schedule")
    return have["schedule"]


# the discovery phase's Lean allowance ------------------------------------------------------------
def _probes_path(run_dir: Path) -> Path:
    return research.state_dir(run_dir) / PROBES_FILE


def probe_entries(run_dir: Path) -> list[dict]:
    p = _probes_path(run_dir)
    return json.loads(p.read_text()) if p.is_file() else []


def probe_usage(run_dir: Path) -> dict:
    """What the discovery phase has spent of its Lean allowance: an unsettled share counts whole."""
    entries = probe_entries(run_dir)
    return {"compile_calls": sum(1 for e in entries if e["kind"] == "compile"),
            "auxiliary_submissions": sum(1 for e in entries if e["kind"] == "auxiliary"),
            "seconds": round(sum(e["seconds"] if e.get("settled") else e["reserved_s"] for e in entries), 1)}


def probe_left(run_dir: Path) -> dict:
    lim = limits(run_dir)["probe"]
    used = probe_usage(run_dir)
    return {"compile_calls": max(0, lim["compile_calls"] - used["compile_calls"]),
            "auxiliary_submissions": max(0, lim["auxiliary_submissions"] - used["auxiliary_submissions"]),
            "seconds": max(0.0, round(lim["seconds"] - used["seconds"], 1))}


def probe_reserve(run_dir: Path, kind: str, seconds_cap: float | None, info: dict) -> dict:
    """Take a share of the allowance before a discovery Lean call starts: one call of its kind and the seconds
    it may run (what is left of the allowance, and no more than seconds_cap). ProbeRefused when there is none."""
    key = {"compile": "compile_calls", "auxiliary": "auxiliary_submissions"}[kind]
    with research.locked(run_dir):
        lim = limits(run_dir)["probe"]
        used = probe_usage(run_dir)
        what = "compiles" if kind == "compile" else "auxiliary submissions"
        if used[key] >= lim[key]:
            raise ProbeRefused(f"the discovery phase's Lean allowance of {lim[key]} {what} is used up")
        seconds = lim["seconds"] - used["seconds"]
        if seconds < 1:
            raise ProbeRefused(f"the discovery phase's Lean allowance of {lim['seconds']:g} s is used up")
        share = seconds if seconds_cap is None else min(seconds, max(0.0, float(seconds_cap)))
        entries = probe_entries(run_dir)
        ticket = {"id": len(entries) + 1, "kind": kind, "reserved_s": round(share, 1), "settled": False,
                  "started": time.strftime("%Y-%m-%dT%H:%M:%S%z"), **info}
        entries.append(ticket)
        research._write_json(_probes_path(run_dir), entries)
    return ticket


def probe_settle(run_dir: Path, ticket: dict, seconds: float, outcome: str, details: dict | None = None) -> dict:
    """The call has ended: its share becomes the seconds it took (never more than it took) and its outcome."""
    with research.locked(run_dir):
        entries = probe_entries(run_dir)
        for e in entries:
            if e["id"] == ticket["id"] and not e.get("settled"):
                e.update(settled=True, seconds=round(min(float(seconds), e["reserved_s"]), 1),
                         outcome=outcome, ended=time.strftime("%Y-%m-%dT%H:%M:%S%z"), **(details or {}))
                research._write_json(_probes_path(run_dir), entries)
                return e
    return ticket


# the transition into formalization -----------------------------------------------------------------
def transition(run_dir: Path) -> dict | None:
    p = research.state_dir(run_dir) / TRANSITION_FILE
    return json.loads(p.read_text()) if p.is_file() else None


def record_transition(run_dir: Path, k: int) -> dict:
    """Before the first formalization round: the discovery phase's research, kept as it was, once. The
    shortlist is the one in the folder (the latest any session wrote); without one the candidates are listed
    unranked, for the formalization session to choose among."""
    run_dir = Path(run_dir)
    with research.locked(run_dir, "transition.lock"):
        have = transition(run_dir)
        if have is not None:
            return have
        dest = research.state_dir(run_dir) / SNAPSHOT_DIR
        if dest.exists():  # a copy interrupted before its record: made again
            research.remove_tree(dest)
        files = research.snapshot(run_dir, dest)
        cands = research.candidates(run_dir, dest)
        short = research.shortlist(run_dir, dest)
        ids = {c["id"] for c in cands}
        data = {"round": k, "at": time.strftime("%Y-%m-%dT%H:%M:%S%z"), "snapshot": f"{research.STATE_DIR}/{SNAPSHOT_DIR}",
                "files": files, "shortlist": short, "ranked": short is not None,
                "missing": [x["id"] for x in short or [] if x["id"] not in ids],
                "candidates": [{"id": c["id"], "title": c.get("title"), "problems": c["problems"]} for c in cands],
                "probes": probe_usage(run_dir)}
        research._write_json(research.state_dir(run_dir) / TRANSITION_FILE, data)
    return data


# what the run reports --------------------------------------------------------------------------------
def _num(x) -> str:
    if x is None:
        return "none"
    return f"{x:,}" if isinstance(x, int) else (f"{x:,.4g}" if isinstance(x, float) else str(x))


def phase_usage(run) -> dict:
    """Per phase: rounds done, seconds of the agent's sessions and the tool calls they made."""
    out = {DISCOVERY: {"rounds": [], "seconds": 0.0, "tools": {}}, FORMALIZATION: {"rounds": [], "seconds": 0.0, "tools": {}}}
    cfg = run.config()
    for k in run.done_rounds():
        p = phase(cfg, k)
        if p is None or ((run.read(k, "meta.json") or {}).get("prompt") or {}).get("phase") not in (None, p):
            continue  # a session after the proof rounds has a round of its own and no phase
        out[p]["rounds"].append(k)
        j = 0
        while (run.round_path(k) / f"attempt_{j}").is_dir():
            meta = run.read(k, f"attempt_{j}/response_meta.json") or {}
            out[p]["seconds"] += float(meta.get("seconds") or 0)
            for tool, n in (meta.get("tools_used") or {}).items():
                out[p]["tools"][tool] = out[p]["tools"].get(tool, 0) + int(n)
            j += 1
    return out


def lines(run, records: list[dict] | None = None, markdown: bool = False) -> list[str]:
    """The workflow's part of `status` and of the report: the mode, the phases, the research candidates and their
    provisional estimates, the discovery phase's Lean checks, and the accepted proofs beside the estimates."""
    cfg = run.config()
    if not is_phased(cfg):
        return []
    sched = recorded(run.path)
    sched = sched["schedule"] if sched else schedule(cfg)
    usage = phase_usage(run)
    h = (lambda t: ["", f"## {t}", ""]) if markdown else (lambda t: [f"{t}:"])
    ind = "" if markdown else "  "
    out = h("Workflow (python_then_lean)")
    for p, rng in ((DISCOVERY, sched["discovery_rounds"]), (FORMALIZATION, sched["formalization_rounds"])):
        u = usage[p]
        if rng[1] < rng[0]:  # a continuation that goes straight on with formalization
            out.append(f"{ind}- {p}: no rounds in this run")
            continue
        tools = ", ".join(f"{t} {n}" for t, n in sorted(u["tools"].items())) or "no tool calls"
        out.append(f"{ind}- {p}: rounds {rng[0]} to {rng[1]} configured, {len(u['rounds'])} done "
                   f"({', '.join(map(str, u['rounds'])) or 'none'}); {u['seconds']:,.0f} s of sessions; {tools}")
    lim, used = sched["probe"], probe_usage(run.path)
    if sched["discovery_rounds"][1] >= sched["discovery_rounds"][0]:
        out.append(f"{ind}- discovery's Lean allowance: {used['compile_calls']} of {lim['compile_calls']} compiles, "
                   f"{used['auxiliary_submissions']} of {lim['auxiliary_submissions']} auxiliary submissions, "
                   f"{used['seconds']:,.0f} of {lim['seconds']:,.0f} s")
    for e in probe_entries(run.path):
        what = e.get("outcome") or "unsettled (counted whole)"
        out.append(f"{ind}  - round {e.get('round')}: {e['kind']} for {e.get('candidate_id')}: {what}; "
                   f"{e.get('seconds', e['reserved_s'])} s; question: {str(e.get('question') or '')[:160]}")
    tr = transition(run.path)
    if tr:
        order = ", ".join(x["id"] for x in tr["shortlist"]) if tr["ranked"] else "no shortlist: candidates unranked"
        out.append(f"{ind}- transition before round {tr['round']}: shortlist {order}"
                   + (f"; listed without a record: {', '.join(tr['missing'])}" if tr["missing"] else ""))
    cands = research.candidates(run.path)
    out += h("Research candidates (agent-written; estimates are provisional, never scored)") if markdown else \
        [f"{ind}research candidates (agent-written; estimates are provisional, never scored):"]
    if not cands:
        out.append(f"{ind}- none saved")
    records = records if records is not None else run.read_archive()
    accepted = [r for r in records if r.get("lane") == "open" and not r.get("stage") and r.get("status") in ("ok", "verified")]
    for c in cands:
        est = f"estimated coverage {_num(c.get('estimated_coverage'))}, estimated cost {_num(c.get('estimated_cost'))}"
        mine = [r for r in accepted if r.get("research_candidate") == c["id"]]
        verified = ("; accepted: " + ", ".join(f"{r['certified']:,} certified" + (f" at length {r['length']:,}" if r.get("length") else "")
                                               for r in mine)) if mine else "; no accepted proof names it"
        bad = f" (record: {'; '.join(c['problems'])})" if c["problems"] else ""
        out.append(f"{ind}- {c['id']}: {str(c.get('title') or '')[:80]}; {est}; agent's assessment "
                   f"{str(c.get('agent_assessment') or 'none')[:40]}{verified}{bad}")
    return out
