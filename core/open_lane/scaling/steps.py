"""The scaling proofs' sessions: planning them once for a run, adding further ones, running them, and what each found.

- Which run: an open-lane run on one network whose proof rounds are over. A run with stages after its proof
  rounds says so itself (core.open_lane.stages, stages.json) and has locked its best scored proof. A run that
  plans no stage says nothing: for it the command needs `--end-proof-rounds`, which ends them for good and
  locks the best scored proof that can be locked, as the stages would have.
- Which proofs: the run's scored proofs of its network that no shorter proof matched in inputs certified. The
  locked proof is in each session's workspace, locked. The other proofs' modules are there to read and import
  where they do not clash with the locked proof's (a module at the same path with other text); a proof whose
  modules clash is listed with why, and not offered.
- Which sessions: core.open_lane.scaling.plan, against the network's sizes (core.open_lane.scaling.sizes). They
  are rounds of the run after its last round. Running the command again goes on with the sessions not done; an
  interrupted one is resumed like any round.
- What is recorded (stages.json, `scaling_proofs`): the network, its sizes, the proofs, and each session's
  round, texts and result. For each accepted lemma: its statement in full; which of the proofs' checkers Lean
  finds in the modules the service compiled for it (core.open_lane.lock.same_checker; the session asks for the
  locked proof, the others are asked after it); and which of the proofs' checkers its statement names. For each
  link the answer names: the theorem, and whether it is the named theorem of an accepted submission
  (core.open_lane.scaling.links). A statement is the agent's own: a person reads it before relying on it.
"""

from __future__ import annotations

import dataclasses
import json
from pathlib import Path

from ...agent.build_prompt import Prompt
from ...archive import RunDir
from .. import answer, stages
from ..lock import LockError, LockUnread, read_lock, same_checker
from . import links, plan, prompt, show
from . import sizes as network_sizes
from .plan import ScalingError

ENDED_BY_COMMAND = "the scaling proofs were started (scale --end-proof-rounds)"


# which proofs ------------------------------------------------------------------------------
def frontier_proofs(records: list[dict], entry: dict) -> list[dict]:
    """The run's scored proofs of the network that no shorter (or equally long, earlier listed) proof matched
    in inputs certified, shortest first."""
    out, best = [], -1
    for r in sorted(stages.scored_proofs(records, entry), key=lambda r: (r["length"], -r["certified"])):
        if r["certified"] > best:
            out.append(r)
            best = r["certified"]
    return out


def proof_entries(run: RunDir, cfg: dict, records: list[dict], entry: dict, locked: dict) -> list[dict]:
    """Each proof the sessions are about, with whether its modules can sit beside the locked proof's."""
    project = stages.lean_project_of(cfg)
    lock_dir = Path(locked["submission_dir"])
    locked_texts = {rel: (lock_dir / rel).read_text() for rel in locked["modules"]}
    out = []
    for r in frontier_proofs(records, entry):
        sub = stages.submission_dir(run, r)
        manifest = json.loads((sub / "manifest.json").read_text())
        receipt = json.loads((sub / "receipt.json").read_text())
        block = manifest.get("scored") if isinstance(manifest.get("scored"), dict) else {}
        scoring = receipt.get("scoring") if isinstance(receipt.get("scoring"), dict) else {}
        item = {"record_id": r["record_id"], "round": r["round"], "certified": r["certified"], "length": r["length"],
                "bill": scoring.get("bill"), "checker": block.get("checker"), "sound": block.get("sound"),
                "certificate_length": len(block.get("certificate") or []), "plan_length": len(block.get("plan") or []),
                "submission_dir": str(sub), "locked": r["record_id"] == locked["record_id"], "offered": True, "why": None,
                "modules": sorted(locked["modules"]) if r["record_id"] == locked["record_id"] else []}
        if not item["locked"]:
            try:
                lock = read_lock(sub, project)
            except LockUnread as exc:
                raise ScalingError(f"{r['record_id']} could not be read ({exc}); nothing was started, and the command can be run again")
            except LockError as exc:
                item.update(offered=False, why=f"its checker cannot be pinned down: {exc}")
                out.append(item)
                continue
            clash = [rel for rel, text in lock["modules"].items() if rel in locked_texts and locked_texts[rel] != text]
            if clash:
                item.update(offered=False, why=f"its {', '.join(clash)} differ from the locked proof's at the same path")
            item["modules"] = sorted(lock["modules"])
        out.append(item)
    return out


# the state ---------------------------------------------------------------------------------
def finished(run: RunDir, cfg: dict, entry: dict, end_proof_rounds: bool) -> dict:
    """The run's state after its proof rounds (stages.json), with its locked proof. A run that plans no stage
    after its proof rounds has none until the person says they are over."""
    state = stages.read_state(run)
    if state is None:
        if stages.planned(cfg):
            raise ScalingError("the run's proof rounds are not over: the scaling proofs follow a finished run "
                               "(python3 -m core.loop resume --run <run folder> finishes it)")
        if not end_proof_rounds:
            raise ScalingError("nothing in this run says its proof rounds are over (it plans no stage after them). "
                               "--end-proof-rounds says so: the run then makes no more proof rounds, and its best scored proof "
                               "that can be locked is locked for the scaling proofs")
        try:
            state = stages.begin(run, cfg, [entry], None, ENDED_BY_COMMAND)
        except stages.StageError as exc:
            raise ScalingError(str(exc))
    if state.get("locked") is None:
        reasons = "; ".join(f"{p['record_id']}: {p['reason']}" for p in state.get("passed_over") or [])
        raise ScalingError("the run locked no proof, so there is no scored proof for the scaling proofs to be about"
                           + (f" ({reasons})" if reasons else ""))
    if state["locked"].get("network") not in (None, entry["id"]):
        raise ScalingError(f"the run's locked proof is of {state['locked']['network']}, not of {entry['id']}")
    open_stages = [name for name, st in (state.get("stages") or {}).items() if st.get("result") is None]
    if open_stages:
        raise ScalingError(f"the run is not finished: {', '.join(open_stages)} still to do "
                           "(python3 -m core.loop resume --run <run folder> does them)")
    return state


def begin(run: RunDir, cfg: dict, folder, entry: dict, end_proof_rounds: bool = False) -> dict:
    """Fix the sessions (their rounds after the run's last), the network's sizes and the proofs they are about,
    once."""
    state = stages.read_state(run)
    if state is not None and state.get("scaling_proofs"):
        return state
    state = finished(run, cfg, entry, end_proof_rounds)
    try:
        sizes = network_sizes.of_network(cfg, folder, entry)
    except network_sizes.SizesError as exc:
        raise ScalingError(str(exc))
    steps = plan.planned(cfg, sizes)
    records = run.read_archive()
    proofs = proof_entries(run, cfg, records, entry, state["locked"])
    k = max(run.done_rounds() or [0])
    sessions = []
    for s in steps:
        k += 1
        sessions.append({**s, "round": k, "result": None})
    state["scaling_proofs"] = {"network": entry["id"], "sizes": sizes, "proofs": proofs, "steps": sessions}
    stages.write_state(run, state)
    return state


def add_sessions(run: RunDir, cfg: dict, state: dict, names: list[str], minutes: float | None = None,
                 usd: float | None = None) -> list[dict]:
    """`--again`: one further session for each name (plan.wanted), in the sessions' order, as rounds after the
    run's last, at the configured minutes and dollars unless others are given. Only once every session so far
    is done: one that waits is gone on with first, by the command without --again."""
    sp = state["scaling_proofs"]
    waiting = [s for s in sp["steps"] if s["result"] is None]
    if waiting:
        raise ScalingError(f"{plan.name(waiting[0])} (round {waiting[0]['round']}) is not done yet: go on with it first "
                           "(the command without --again), then add further sessions")
    for key, value in (("--minutes", minutes), ("--usd", usd)):
        if value is not None and not value > 0:
            raise ScalingError(f"{key} must be a positive number")
    sizes = network_sizes.stored(sp, cfg)
    wanted = plan.wanted(list(names), cfg, sizes)
    settings = plan.settings(cfg, sizes)
    k = max([s["round"] for s in sp["steps"]] + (run.done_rounds() or [0]))
    added = []
    for p in wanted:
        k += 1
        added.append({"parameter": p, "minutes": float(minutes) if minutes is not None else settings[p]["minutes"],
                      "usd": float(usd) if usd is not None else settings[p]["usd"], "round": k, "result": None, "again": True})
    sp["steps"] += added
    stages.write_state(run, state)
    return added


# what a session found ------------------------------------------------------------------------
def step_result(run: RunDir, cfg: dict, records: list[dict], k: int, sp: dict, symbols: list[str]) -> dict:
    """A session's lemmas (each with its statement, its modules, which proofs' checkers Lean finds in what the
    service compiled for it and which its statement names), its answer's sections, and the links its THEOREMS
    section names, each with whether its theorem is an accepted submission's."""
    base = stages.scaling_result(records, k)
    by_id = {r["record_id"]: r for r in records}
    project = stages.lean_project_of(cfg)
    others = [p for p in sp["proofs"] if p["offered"] and not p["locked"]]
    locks = {}
    for p in others:
        try:
            locks[p["record_id"]] = read_lock(Path(p["submission_dir"]), project)
        except (LockError, LockUnread) as exc:
            locks[p["record_id"]] = exc
    locked_proof = next(p for p in sp["proofs"] if p["locked"])
    lemmas = []
    for l in base["lemmas"]:
        sub = stages.submission_dir(run, by_id[l["record_id"]])
        try:
            modules = json.loads((sub / "manifest.json").read_text()).get("modules") or []
        except (OSError, ValueError):
            modules = []
        checkers = {locked_proof["record_id"]: {"verified": l["locked_checker"], "why": l.get("why")}}
        for p in others:
            lock = locks[p["record_id"]]
            if isinstance(lock, Exception):
                checkers[p["record_id"]] = {"verified": None, "why": f"its lock could not be read: {lock}"}
                continue
            try:
                check = same_checker(lock, sub, project, scored=False)
            except Exception as exc:  # recorded as unknown: the session's result stands without it
                check = {"verified": None, "why": f"the question failed: {exc!r}"}
            checkers[p["record_id"]] = {"verified": check["verified"], "why": check.get("why")}
        lemmas.append({**l, "submission_dir": str(sub), "modules": modules, "checkers": checkers,
                       "names": links.names_in(l.get("statement"), sp["proofs"])})
    said = answer.sections(run.read(k, "attempt_0/response.md") or "", prompt.ANSWER_SECTIONS)
    meta = run.read(k, "attempt_0/response_meta.json") or {}
    return {"lemmas": lemmas, "submissions": base["submissions"], "answer": said,
            "links": links.of_answer(said.get("THEOREMS", ""), symbols, records, k),
            "cost_usd": meta.get("cost_usd"), "seconds": meta.get("seconds")}


# running them ------------------------------------------------------------------------------
def run_steps(ctx, backend, run_round, only: list[str] | None = None, again: list[str] | None = None,
              minutes: float | None = None, usd: float | None = None, end_proof_rounds: bool = False) -> None:
    """Run the sessions not done yet, in order (with `only`, just those, which must be the next ones). With
    `again` (a list, which may be empty), first add further sessions (add_sessions). `run_round` is
    core.rounds.run_round; `ctx` the run's context."""
    cfg, run = ctx.cfg, ctx.run
    if len(ctx.entries) != 1:
        raise ScalingError(f"the scaling proofs are for a run on one network; this run has {len(ctx.entries)}")
    entry = ctx.entries[0]
    if again is None and (minutes is not None or usd is not None):
        raise ScalingError("--minutes and --usd are for the sessions --again adds; the first ones take open_lane.scaling_steps'")
    state = begin(run, cfg, ctx.folder, entry, end_proof_rounds)
    sp = state["scaling_proofs"]
    if sp["network"] != entry["id"]:
        raise ScalingError(f"this run's scaling proofs are about {sp['network']}, and its network is now {entry['id']}")
    try:
        sizes = network_sizes.stored(sp, cfg)
    except network_sizes.SizesError as exc:
        raise ScalingError(str(exc))
    symbols = [s["symbol"] for s in sizes]
    if again is not None:
        added = add_sessions(run, cfg, state, list(again), minutes, usd)
        ctx.log("added: " + "; ".join(f"{plan.name(s)} (round {s['round']}, {s['minutes']:g} minutes, ${float(s['usd']):.2f})" for s in added))
    todo = sorted((s for s in sp["steps"] if s["result"] is None), key=lambda s: s["round"])
    if only:
        names = [s["parameter"] for s in todo]
        if names[:len(only)] != list(only):
            raise ScalingError(f"the steps go in order; the next ones are {', '.join(names) or 'none'}, not {', '.join(only)}")
        todo = todo[:len(only)]
    if not todo:
        ctx.log("the scaling proofs are done; nothing to run (a further session: --again)")
        return
    locked = state["locked"]
    ctx.log(f"scaling proofs on {sp['network']} ({', '.join(network_sizes.text(s) for s in sizes)}): " + "; ".join(
        f"{p['record_id']} ({p['certified']:,} at length {p['length']:,})" + ("" if p["offered"] else f", not offered: {p['why']}")
        for p in sp["proofs"]) + f"; locked {locked['record_id']}")
    per_round = cfg["recipes_per_round"]
    for step in todo:
        k = step["round"]
        step_cfg = plan.step_config(cfg, step)
        if hasattr(backend, "bind"):
            backend.bind(step_cfg, step_cfg["model"], [entry], run.path)
        spent = backend.exhausted(run.path) if hasattr(backend, "exhausted") and not run.round_done(k) else None
        if spent:
            ctx.log(f"{spent}; {plan.name(step)} (round {k}) is left for a run of this command with --budget-usd")
            return
        saved = run.read(k, "prompt.json")
        if saved is None and not run.round_done(k) and not backend.available((k - 1) * per_round):
            ctx.log(f"the {backend.name} backend has no more responses; {plan.name(step)} (round {k}) is left for later")
            return
        if saved is None:
            # on record before the prompt is: a session with a saved prompt and no text named got the first sessions'
            step["template"] = prompt.template_of(step)
            stages.write_state(run, state)
            ctx.log(f"round {k}: {plan.name(step)}: compiling the workspace before the session")

            def compiled(built: list[dict], step=step) -> None:
                step["compiled_beforehand"] = built
                stages.write_state(run, state)

            sent = prompt.build(step_cfg, ctx.folder, run, k, step, state, entry, sizes, on_compiled=compiled)
        else:
            sent = Prompt.from_json(saved)
        # the pipeline the session runs with: it may be later than the run's (core.open_lane.scaling.later_pipeline)
        versions = ctx.versions or {}
        step["pipeline"] = {"commit": (versions.get("git") or {}).get("commit"),
                            "changed_since_run": list((versions.get("after_run") or {}).get("changed") or [])}
        stages.write_state(run, state)
        built = step.get("compiled_beforehand") or []
        ctx.log(f"round {k}: {plan.name(step)} ({step['minutes']:g} minutes, ${float(step['usd']):.2f})"
                + (f"; prompt of about {sent.stats['tokens_estimate']:,} tokens" if saved is None else "")
                + (f"; {sum(1 for b in built if b['compiled'])} of {len(built)} modules compiled beforehand "
                   f"({sum(b['seconds'] for b in built):.0f} s)" if built else ""))
        step_ctx = dataclasses.replace(ctx, cfg=step_cfg, entries=[entry])
        run_round(step_ctx, k, backend, (k - 1) * per_round, 1, "agent", prompt=sent)
        step["result"] = step_result(run, step_cfg, run.read_archive(), k, sp, symbols)
        stages.write_state(run, state)
        ctx.log("  " + show.step_line(step, sp["proofs"]))
