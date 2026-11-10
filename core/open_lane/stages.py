"""After the proof rounds of an open-lane run: the seed check and the scaling question.

A run proves one network. When its proof rounds are over (the round limit, patience), up to two more
sessions follow, each one round of the run, each resumable like any round:

- seed_check (`open_lane.seed_check: {network: <id>}`): the checker of the run's best scored proof is locked
  (core.open_lane.lock) and run, unchanged, on a second network of the same model and sizes, trained from
  another seed. The agent writes the instance for that network and nothing else. What comes out is what a
  checker written for one network certifies on another: a copy of the first network's weights, or a plan
  made for its inputs, certifies nothing there.
- scaling (`open_lane.scaling: true`): the agent states how the locked checker's cost grows with the sizes
  of the network, compares it with brute force's, and proves what it can of that as lemmas. Never scored.

`stages.json` in the run folder records that the proof rounds are over, which proof was locked (or why none
could be), the round of each stage and what it found. Once it exists the run makes no more proof rounds.
A stage's records carry `stage` and never enter the run's frontier or score.
"""

from __future__ import annotations

import dataclasses
import json
from pathlib import Path

from ..agent.build_prompt import CHARS_PER_TOKEN, Prompt, PromptError, TEMPLATES, fill, forbidden, load_template
from ..archive import RunDir
from ..scoring import fallback_cost_per_input
from .lock import LockError, read_lock
from .prompt import static_values
from .records import proof_records
from .session import Session

STAGES = ("seed_check", "scaling")
STATE_FILE = "stages.json"


class StageError(ValueError):
    pass


# configuration -------------------------------------------------------------------------------
def planned(cfg: dict) -> list[str]:
    ol = cfg.get("open_lane") or {}
    if not ol.get("enabled"):
        return []
    return [s for s in STAGES if ol.get(s)]


def check_network(cfg: dict, folder, entries: list[dict], dev: list[dict]) -> dict | None:
    """The seed check's network, checked: a development network of the model (held-out networks stay for the
    final evaluation), of the same size setting as the run's one network and not that network, with E and B
    measured. None when the run has no seed check. `dev` are the model's development networks."""
    if planned(cfg) and len(entries) != 1:
        raise StageError(f"the seed check and the scaling question are for a run on one network; this run has "
                         f"{len(entries)} (set networks to one id)")
    spec = (cfg.get("open_lane") or {}).get("seed_check")
    if not spec:
        return None
    mine = entries[0]
    entry = next((e for e in dev if e["id"] == spec["network"]), None)
    if entry is None:
        raise StageError(f"open_lane.seed_check.network {spec['network']!r} is not a development network of {folder.name}")
    if entry["id"] == mine["id"]:
        raise StageError("open_lane.seed_check.network is the run's own network; name another seed")
    if entry["setting"] != mine["setting"]:
        raise StageError(f"open_lane.seed_check.network is of size setting {entry['setting']}, the run's network of "
                         f"{mine['setting']}: the seed check keeps the sizes and changes the seed")
    if entry.get("E") is None or entry.get("B") is None:
        raise StageError(f"E and B are missing for {entry['id']}; run python -m core.check.costs on the model folder")
    return entry


# the state -----------------------------------------------------------------------------------
def read_state(run: RunDir) -> dict | None:
    p = run.path / STATE_FILE
    return json.loads(p.read_text()) if p.is_file() else None


def write_state(run: RunDir, state: dict) -> None:
    tmp = run.path / (STATE_FILE + ".tmp")
    tmp.write_text(json.dumps(state, indent=1))
    tmp.replace(run.path / STATE_FILE)


def started(run: RunDir) -> bool:
    """True once the proof rounds are over for good: the run then makes no more of them."""
    return (run.path / STATE_FILE).is_file()


# which proof is locked ---------------------------------------------------------------------------
def submission_dir(run: RunDir, record: dict) -> Path:
    return (run.round_path(record["round"]) / f"attempt_{record['attempt']}" / "open_lane" / "submissions"
            / f"{int(record.get('submission') or 0):03d}")


def finishing_total(record: dict, entry: dict, records: list[dict]) -> float:
    """What finishing the network from this proof costs: its length plus brute force on every correct input
    it leaves out."""
    unit, _ = fallback_cost_per_input(entry, records)
    return record["length"] + max(0, (entry.get("real_correct") or 0) - record["certified"]) * unit


def scored_proofs(records: list[dict], entry: dict) -> list[dict]:
    """The run's scored open-lane proofs of its network, the one that finishes cheapest first (the proof the
    score rests on); among equals the later one."""
    mine = [r for r in proof_records(records) if r.get("lane") == "open" and r.get("status") == "ok" and r.get("network") == entry["id"]]
    return sorted(mine, key=lambda r: (finishing_total(r, entry, records), -r["round"], -r["attempt"], -(r.get("submission") or 0)))


def choose_lock(run: RunDir, records: list[dict], entry: dict) -> tuple[dict | None, dict | None, list[dict]]:
    """The proof to lock: the best scored proof that can be locked. Returns its lock, its record, and the
    better proofs passed over with the reason each could not be locked."""
    passed = []
    for r in scored_proofs(records, entry):
        d = submission_dir(run, r)
        try:
            return read_lock(d), r, passed
        except LockError as exc:
            passed.append({"record_id": r["record_id"], "certified": r["certified"], "length": r["length"], "reason": str(exc)})
    return None, None, passed


def begin(run: RunDir, cfg: dict, entries: list[dict], check_entry: dict | None, why: str) -> dict:
    """The proof rounds are over: fix what is locked and which rounds the stages get. Written once."""
    records = run.read_archive()
    state = {"proof_rounds_ended": {"after_round": max([k for k in run.done_rounds()] or [0]), "why": why},
             "locked": None, "passed_over": [], "stages": {}}
    if len(entries) == 1:
        lock, record, passed = choose_lock(run, records, entries[0])
        state["passed_over"] = passed
        if lock is not None:
            entry = entries[0]
            total = finishing_total(record, entry, records)
            state["locked"] = {
                "record_id": record["record_id"], "round": record["round"], "attempt": record["attempt"],
                "submission": int(record.get("submission") or 0), "submission_dir": str(submission_dir(run, record)),
                "network": entry["id"], "certified": record["certified"], "real_correct": entry.get("real_correct"),
                "length": record["length"], "B": entry["B"], "finishing_total": total, "ratio": entry["B"] / total,
                "description_size": record.get("description_size"),
                "digest": lock["digest"], "modules": sorted(lock["modules"]), "free": lock["free"],
                "checker": lock["checker"], "sound": lock["sound"], "protected": lock["protected"],
            }
    k = state["proof_rounds_ended"]["after_round"]
    for name in planned(cfg):
        if name == "seed_check" and check_entry is None:
            continue
        k += 1
        state["stages"][name] = {"round": k, "result": None}
        if name == "seed_check":
            state["stages"][name]["network"] = check_entry["id"]
    write_state(run, state)
    return state


# the prompts ---------------------------------------------------------------------------------
def _num(x: float) -> str:
    return f"{x:,.0f}" if float(x).is_integer() else f"{x:,.1f}"


def from_result(locked: dict) -> str:
    full = locked["certified"] >= (locked.get("real_correct") or 0)
    covered = (f"all {locked['certified']:,} inputs it answers correctly" if full else
               f"{locked['certified']:,} of the {locked['real_correct']:,} inputs it answers correctly")
    return (f"{covered}, at length {locked['length']:,} (brute force: {locked['B']:,}; finishing from it costs "
            f"{_num(locked['finishing_total'])}, a ratio of {locked['ratio']:.3f}).")


def locked_text(lock: dict) -> str:
    lines = [f"- {rel} ({len(text.splitlines())} lines)" for rel, text in lock["modules"].items()]
    lines.append(f"The checker is {lock['checker']}, its soundness theorem {lock['sound']}.")
    return "\n".join(lines)


def rename_text(lock: dict) -> str:
    if not lock["protected"]:
        return ""
    return (f" One change is made for you: where they name the protected module of the network they were written "
            f"for ({lock['protected']}), they get the name of the protected module of the network, claimed count and "
            "certificate of that call.")


def free_text(lock: dict) -> str:
    if not lock["free"]:
        return ""
    return (" The first network's instance (" + ", ".join(lock["free"]) + ") is in your workspace to read and adapt; "
            "saving over it is allowed.")


def seed_check_line(state: dict) -> str:
    """One or two sentences on what the seed check found, for the scaling session, the log and the status;
    empty without one. A session that ended without an accepted result is said to be that, never a
    measurement of zero."""
    st = (state.get("stages") or {}).get("seed_check")
    if not st:
        return ""
    res = st.get("result")
    if res is None:
        return f"The seed check on {st['network']} has not been run."
    if res.get("outcome") != "certified":
        return (f"The seed check gave no accepted result on {st['network']} ({res.get('note') or 'no accepted submission'}). "
                "That is not a measurement: it does not say what the locked checker certifies there.")
    warn = ""
    if res.get("same_description_size") is False:
        warn = " Warning: the service measured another description size for the checker than in the locked proof."
    if not res["certified"]:
        return (f"The seed check: on {st['network']} the locked checker certifies none of the {res['real_correct']:,} inputs "
                f"that network answers correctly (a checked claim of 0, at length {res['length']:,})." + warn)
    return (f"The seed check: on {st['network']} the locked checker certified {res['certified']:,} of the "
            f"{res['real_correct']:,} inputs that network answers correctly, at length {res['length']:,} (a ratio of "
            f"{res['ratio']:.3f} there, against {state['locked']['ratio']:.3f} on the network it was written for)." + warn)


def build_stage_prompt(cfg: dict, folder, run: RunDir, k: int, name: str, state: dict, entry: dict) -> Prompt:
    """The prompt of a stage's session: the run's part 1 (for the network of this session) and the stage's
    own second part. Opens the stage's session, which starts from the locked proof."""
    part1_t, _ = load_template(cfg["prompt_template"])
    part1 = fill(part1_t, static_values(cfg, folder, [entry]))
    leaked = [t for t in forbidden(folder) if t in part1]
    if leaked:
        raise PromptError(f"the model folder puts forbidden strings into the prompt: {leaked}")
    locked = state["locked"]
    lock = read_lock(Path(locked["submission_dir"]))
    if lock["digest"] != locked["digest"]:
        raise StageError(f"the locked proof's modules in {locked['submission_dir']} changed since they were locked; the run halts")
    stage = {"name": name, "of": locked["record_id"], "submission": locked["submission_dir"], "lock": lock,
             "description_size": locked.get("description_size")}
    Session.create(run.round_path(k) / "attempt_0" / "open_lane", cfg, cfg["model"], [entry], run.path, stage=stage)
    path = TEMPLATES / f"open_lane_{name}.md"
    if not path.is_file():
        raise PromptError(f"no prompt text {path.name} in {TEMPLATES}")
    n = entry["n_inputs"]
    values = {
        "FROM_NETWORK": locked["network"], "FROM_RESULT": from_result(locked),
        "NETWORK": entry["id"], "LOCKED": locked_text(lock), "RENAME": rename_text(lock), "FREE": free_text(lock),
        "CHECKER": lock["checker"], "SOUND": lock["sound"],
        "SEED_CHECK_RESULT": seed_check_line(state),
        "N": f"{n:,}", "B": f"{entry['B']:,}", "PER_INPUT": _num((entry["B"] - entry["E"]) / n),
    }
    part2 = fill(path.read_text(), values)
    stats = {"chars": len(part1) + len(part2), "tokens_estimate": (len(part1) + len(part2)) // CHARS_PER_TOKEN, "trimmed": [],
             "template": cfg["prompt_template"], "lane": "open", "stage": name}
    return Prompt(part1, part2, stats)


# what a stage found ----------------------------------------------------------------------------
def seed_check_result(records: list[dict], k: int, entry: dict, session_note: str = "") -> dict:
    """The seed check's outcome from its round's records. Two outcomes, never to be confused:

    - `certified`: a scored proof was accepted under an intact lock. Its count is a checked result, zero
      included (a claim of 0 with its instance is a measurement that the checker certifies nothing there).
      With several, the one that finishes the second network cheapest.
    - `no_result`: the session ended without an accepted scored proof (it ran out of time, nothing
      compiled, the submissions were rejected). That says nothing about what the checker certifies."""
    mine = [r for r in records if r.get("round") == k and r.get("stage") == "seed_check"]
    per_input = (entry["B"] - entry["E"]) / entry["n_inputs"]  # cost-v4: B is E plus one forward pass per input
    real = entry.get("real_correct") or 0
    best = None
    for r in mine:
        lock = r.get("lock") or {}
        if r.get("status") != "ok" or r.get("network") != entry["id"] or not lock.get("intact"):
            continue
        total = r["length"] + max(0, real - r["certified"]) * per_input
        if best is None or total < best["finishing_total"]:
            best = {"outcome": "certified", "record_id": r["record_id"], "certified": r["certified"], "real_correct": real,
                    "length": r["length"], "B": entry["B"], "finishing_total": total, "ratio": entry["B"] / total,
                    "lock_intact": True, "lock_in_receipt": bool(lock.get("in_receipt")),
                    "same_description_size": lock.get("same_description_size")}
    if best is not None:
        return best
    counts: dict[str, int] = {}
    for r in mine:
        counts[str(r.get("status"))] = counts.get(str(r.get("status")), 0) + 1
    what = ", ".join(f"{n} {s}" for s, n in sorted(counts.items())) or "no record"
    reasons = [str(r.get("error"))[:200] for r in mine if r.get("error") and r.get("status") != "no_submission"]
    return {"outcome": "no_result", "real_correct": real, "B": entry["B"],
            "note": f"the session's records: {what}" + (f"; {session_note}" if session_note else ""), "reasons": reasons[:3]}


def scaling_result(records: list[dict], k: int) -> dict:
    mine = [r for r in records if r.get("round") == k and r.get("stage") == "scaling"]
    lemmas = [{"record_id": r["record_id"], "theorem": r.get("theorem"), "statement": r.get("statement")}
              for r in mine if r.get("status") == "lemma"]
    return {"lemmas": lemmas, "submissions": len([r for r in mine if r.get("status") != "no_submission"])}


def status_lines(run: RunDir) -> list[str]:
    """For the run's status: what followed the proof rounds, in a few lines; empty for a run without stages."""
    state = read_state(run)
    if state is None:
        return []
    locked = state.get("locked")
    if locked is None:
        return ["after the proof rounds: no proof could be locked; nothing followed"]
    lines = [f"after the proof rounds: locked {locked['record_id']} (cost of finishing {locked['ratio']:.3f} on {locked['network']})"]
    if "seed_check" in state["stages"]:
        lines.append("  " + seed_check_line(state))
    scaling = state["stages"].get("scaling")
    if scaling:
        res = scaling.get("result")
        lines.append(f"  the scaling question (round {scaling['round']}): " +
                     ("not asked yet" if res is None else f"{len(res['lemmas'])} lemma(s) accepted; the answer is the round's response"))
    return lines


def report_lines(run: RunDir) -> list[str]:
    """The report's section on what followed the proof rounds; empty for a run without stages."""
    state = read_state(run)
    if state is None:
        return []
    ended = state["proof_rounds_ended"]
    lines = ["## After the proof rounds", "", f"The proof rounds ended after round {ended['after_round']}: {ended['why']}.", ""]
    locked = state.get("locked")
    if locked is None:
        why = "; ".join(f"`{p['record_id']}`: {p['reason']}" for p in state["passed_over"]) or "the run has no scored proof"
        return lines + [f"No proof could be locked ({why}), so nothing followed.", ""]
    lines += [f"Locked: `{locked['record_id']}` on {locked['network']}, {locked['certified']:,} of {locked['real_correct']:,} correct inputs "
              f"certified at length {locked['length']:,} (B {locked['B']:,}; cost of finishing {locked['ratio']:.3f}). "
              f"Checker modules: {', '.join(locked['modules'])}.", ""]
    for p in state["passed_over"]:
        lines.append(f"- Passed over, though it finishes cheaper: `{p['record_id']}` (length {p['length']:,}): {p['reason']}")
    if state["passed_over"]:
        lines.append("")
    check = state["stages"].get("seed_check")
    if check:
        res = check.get("result")
        lines += ["### The seed check", ""]
        if res is None:
            lines += [f"Not run yet (round {check['round']}, on {check['network']}).", ""]
        elif res.get("outcome") == "certified":
            lines += ["| Network | Certified of correct | Length | B | Cost of finishing |", "| --- | --- | --- | --- | --- |",
                      f"| {locked['network']} (written for) | {locked['certified']:,} of {locked['real_correct']:,} | {locked['length']:,} | {locked['B']:,} | {locked['ratio']:.3f} |",
                      f"| {check['network']} (second seed, checker locked) | {res['certified']:,} of {res['real_correct']:,} | {res['length']:,} | {res['B']:,} | {res['ratio']:.3f} |",
                      "",
                      "The locked modules reached the service unchanged" + (", and the receipt's hashes say the same."
                                                                           if res.get("lock_in_receipt") else " by the pipeline's own comparison; the receipt carried no hashes of them.")
                      + {True: " The service measured the same description size for the checker on both networks.",
                         False: " Warning: the service measured another description size for the checker than in the locked proof; "
                                "read the two submissions before relying on this row.",
                         None: ""}[res.get("same_description_size")],
                      ""]
        else:
            lines += [f"No accepted result on {check['network']}: {res.get('note')}. This is not a measurement of zero: "
                      "the session did not complete the check, so it does not say what the locked checker certifies there.", ""]
            lines += [f"- {reason}" for reason in res.get("reasons") or []]
            if res.get("reasons"):
                lines.append("")
    scaling = state["stages"].get("scaling")
    if scaling:
        res = scaling.get("result")
        lines += ["### The scaling question", ""]
        if res is None:
            lines += [f"Not asked yet (round {scaling['round']}).", ""]
        else:
            lines += [f"The agent's answer is round {scaling['round']}'s response (`round_{scaling['round']:03d}/attempt_0/response.md`). "
                      f"Lemmas accepted: {len(res['lemmas'])}. A lemma's statement is the agent's own: read it before relying on it.", ""]
            lines += [f"- `{l['theorem']}`: {l['statement']}" for l in res["lemmas"]]
            if res["lemmas"]:
                lines.append("")
    return lines


# running them ----------------------------------------------------------------------------------
def run_stages(ctx, backend, check_entry: dict | None, why: str, run_round) -> None:
    """Run the stages still to do, in order. `run_round` is core.rounds.run_round; `ctx` the run's context."""
    cfg, run = ctx.cfg, ctx.run
    if not planned(cfg):
        return
    state = read_state(run) or begin(run, cfg, ctx.entries, check_entry, why)
    if state["locked"] is None:
        if not any(st.get("result") for st in state["stages"].values()):
            reasons = "; ".join(f"{p['record_id']}: {p['reason']}" for p in state["passed_over"]) or "the run has no scored proof"
            ctx.log(f"after the proof rounds: no proof to lock ({reasons}); the seed check and the scaling question are skipped")
        return
    locked = state["locked"]
    ctx.log(f"after the proof rounds: locked {locked['record_id']} ({locked['certified']:,} certified at length "
            f"{locked['length']:,}, a ratio of {locked['ratio']:.3f}); checker modules {', '.join(locked['modules'])}")
    for p in state["passed_over"]:
        ctx.log(f"  passed over {p['record_id']} (length {p['length']:,}): {p['reason']}")
    per_round = cfg["recipes_per_round"]
    for name in STAGES:
        st = state["stages"].get(name)
        if st is None or st.get("result") is not None:
            continue
        k = st["round"]
        entry = check_entry if name == "seed_check" else ctx.entries[0]
        saved = run.read(k, "prompt.json")
        fresh = saved is None and not run.round_done(k)
        if fresh and not backend.available((k - 1) * per_round):
            ctx.log(f"the {backend.name} backend has no more responses; {name} (round {k}) is left for a resume")
            return
        prompt = Prompt.from_json(saved) if saved is not None else build_stage_prompt(cfg, ctx.folder, run, k, name, state, entry)
        if saved is None:
            ctx.log(f"  {name}: prompt of about {prompt.stats['tokens_estimate']:,} tokens")
        stage_ctx = dataclasses.replace(ctx, entries=[entry])
        run_round(stage_ctx, k, backend, (k - 1) * per_round, 1, "agent", prompt=prompt)
        records = run.read_archive()
        if name == "seed_check":
            # how the session ended, where the backend says so (its last text, or a stop reason that is not an end)
            meta = run.read(k, "attempt_0/response_meta.json") or {}
            last = (run.read(k, "attempt_0/response.md") or "").strip()
            note = ("the session ran out of time" if last == "(the session ran out of time)" else
                    "the session reached its turn limit" if last == "(the session reached its turn limit)" else
                    f"the session stopped: {meta['stop_reason']}" if meta.get("stop_reason") not in (None, "end_turn") else "")
            st["result"] = seed_check_result(records, k, entry, note)
            ctx.log("  " + seed_check_line(state))
            if st["result"].get("outcome") == "certified" and not st["result"].get("lock_in_receipt"):
                ctx.log("  note: the receipt did not carry the locked modules' hashes; the lock rests on the pipeline's own comparison")
        else:
            st["result"] = scaling_result(records, k)
            ctx.log(f"  scaling: {len(st['result']['lemmas'])} lemma(s) accepted")
        write_state(run, state)
