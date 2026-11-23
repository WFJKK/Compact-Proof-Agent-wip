"""After a run: the scaling proofs, one session per size (`python3 -m core.loop scale --run <run folder>`).

A person starts this once a run's proofs have been looked at; the run itself never does. One session per size
of the network, in the order of open_lane.scaling_steps (by default: the number of token values V, then the
number of positions n, then the width d). Each asks how the cost of the run's scored proofs grows with that size
while the other two stay at this network's values, against brute force's, and for Lean proofs of as much of it
as the session can: the bill at this size for every weight, the bill as an exact formula in the size, its
leading order against brute force's. In words, it also asks what each proof certifies at other values of the
size. Nothing in these sessions is scored.

- Which sizes: the model folder's open_lane.scaling_sizes names, for V, n and d, the entries of its size
  settings that are that size (an attention model's width and head width vary together). A model folder without
  it has no scaling proofs.
- Time and money: each step's minutes and dollars (open_lane.scaling_steps; a run made before they existed takes
  config/defaults.yaml's). A run billed to an API key pays them from its own budget; `--budget-usd` raises it,
  as for resume.
- Which proofs: the run's scored proofs of its network that no shorter proof matched in inputs certified. The
  locked proof (core.open_lane.stages) is in each session's workspace, locked, as in the scaling question. The
  other proofs' modules are there to read and import where they do not clash with the locked proof's (a module
  at the same path with other text); a proof whose modules clash is listed with why, and not offered. Every
  proof's certificate and plan, with its receipt's count and bill, are in the Python workspace
  (py/handed_in_proofs.json).
- What carries over from one step to the next: the modules of the lemmas the earlier steps had accepted, and
  their answers' CLAIM and SCALING sections.
- What is recorded (stages.json, `scaling_proofs`): each step's round and result. For each accepted lemma, its
  statement in full, and which of the proofs' checkers Lean finds in the modules the service compiled for it
  (core.open_lane.lock.same_checker): the session asks for the locked proof, as in the scaling question, and the
  others are asked after the session. A statement is the agent's own: a person reads it before relying on it.

The steps are rounds of the run after its last round, fixed when the command first runs. Running the command
again goes on with the steps not done; an interrupted step is resumed like any round.
"""

from __future__ import annotations

import copy
import dataclasses
import json
import re
from pathlib import Path

import yaml

from ..agent.build_prompt import CHARS_PER_TOKEN, Prompt, PromptError, TEMPLATES, fill, forbidden, load_template
from ..archive import RunDir
from ..run_config import DEFAULTS_PATH, SCALING_PARAMETERS, scaling_steps_errors
from . import stages, workflow
from .lock import LockError, LockUnread, read_lock, same_checker
from .prompt import static_values
from .session import Session

TEMPLATE = "open_lane_scaling_step_v1"
PROOFS_FILE = "handed_in_proofs.json"
WORDS = {"V": "the number of token values", "n": "the number of positions", "d": "the width"}
SECTIONS = ("CLAIM", "SCALING", "WHY IT HELPS", "NOTES")


class ScalingError(ValueError):
    pass


# configuration -------------------------------------------------------------------------------
def configured_steps(cfg: dict) -> list[dict]:
    """The steps, in order: the run's open_lane.scaling_steps, or config/defaults.yaml's for a run made before
    there were any."""
    steps = (cfg.get("open_lane") or {}).get("scaling_steps")
    if steps is None:
        steps = yaml.safe_load(DEFAULTS_PATH.read_text())["open_lane"]["scaling_steps"]
    errors = scaling_steps_errors(steps)
    if errors:
        raise ScalingError("; ".join(errors))
    return [dict(s) for s in steps]


def sizes_of(folder, entry: dict) -> dict:
    """For V, n and d: the size names the model folder gives (open_lane.scaling_sizes) and their value on this
    network."""
    spec = ((folder.config.get("open_lane") or {}).get("scaling_sizes"))
    if not spec:
        raise ScalingError(f"the model folder {folder.path.name} has no open_lane.scaling_sizes, so it says of none of its sizes "
                           "which of V, n and d it is: no scaling proofs without it")
    sizes = folder.sizes(entry["setting"])
    out = {}
    for p in SCALING_PARAMETERS:
        values = {sizes[name] for name in spec[p]}
        if len(values) != 1:
            raise ScalingError(f"{', '.join(spec[p])} differ on {entry['id']}, so {p} has no one value there")
        out[p] = {"names": list(spec[p]), "value": values.pop()}
    return out


def step_config(cfg: dict, step: dict) -> dict:
    """The run's config for one step: its session time and its own dollar cap."""
    out = copy.deepcopy(cfg)
    out["open_lane"]["worker_seconds"] = int(round(float(step["minutes"]) * 60))
    if isinstance(out.get("api_budget"), dict):
        out["api_budget"]["round_usd"] = float(step["usd"])
    return out


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


def _submitted(sub: Path) -> tuple[dict, dict]:
    manifest = json.loads((sub / "manifest.json").read_text())
    receipt = json.loads((sub / "receipt.json").read_text())
    return manifest, receipt


def proof_entries(run: RunDir, cfg: dict, records: list[dict], entry: dict, locked: dict) -> list[dict]:
    """Each proof the steps are about, with whether its modules can sit beside the locked proof's."""
    project = stages.lean_project_of(cfg)
    lock_dir = Path(locked["submission_dir"])
    locked_texts = {rel: (lock_dir / rel).read_text() for rel in locked["modules"]}
    out = []
    for r in frontier_proofs(records, entry):
        sub = stages.submission_dir(run, r)
        manifest, receipt = _submitted(sub)
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
def begin(run: RunDir, cfg: dict, folder, entry: dict) -> dict:
    """Fix the steps (their rounds after the run's last) and the proofs they are about, once."""
    state = stages.read_state(run)
    if state is None:
        raise ScalingError("the run's proof rounds are not over: the scaling proofs follow a finished run "
                           "(python3 -m core.loop resume --run <run folder> finishes it)")
    if state.get("scaling_proofs"):
        return state
    if state.get("locked") is None:
        raise ScalingError("the run locked no proof, so there is no scored proof for the scaling proofs to be about")
    open_stages = [name for name, st in (state.get("stages") or {}).items() if st.get("result") is None]
    if open_stages:
        raise ScalingError(f"the run is not finished: {', '.join(open_stages)} still to do "
                           "(python3 -m core.loop resume --run <run folder> does them)")
    steps = configured_steps(cfg)
    sizes = sizes_of(folder, entry)
    records = run.read_archive()
    proofs = proof_entries(run, cfg, records, entry, state["locked"])
    k = max(run.done_rounds() or [0])
    planned = []
    for s in steps:
        k += 1
        planned.append({**s, "round": k, "result": None})
    state["scaling_proofs"] = {"network": entry["id"], "sizes": sizes, "proofs": proofs, "steps": planned}
    stages.write_state(run, state)
    return state


# the prompt --------------------------------------------------------------------------------
def _size_text(sizes: dict, p: str) -> str:
    s = sizes[p]
    names = " and ".join(s["names"])
    return f"{p} = {s['value']} ({names}" + (", varied together)" if len(s["names"]) > 1 else ")")


def proofs_text(proofs: list[dict]) -> str:
    lines = []
    for p in proofs:
        what = [f"{p['certified']:,} inputs certified at length {p['length']:,}" + (f" (bill {p['bill']:,})" if p.get("bill") is not None else "")]
        if p["certificate_length"]:
            what.append(f"a certificate of {p['certificate_length']:,} numbers")
        if p["plan_length"]:
            what.append(f"a plan of {p['plan_length']:,} numbers")
        where = ("locked, below" if p["locked"] else
                 "its modules are in your workspace to read and import" if p["offered"] else
                 f"not in your workspace: {p['why']}")
        lines.append(f"- {p['record_id']}: checker {p['checker']}, soundness theorem {p['sound']}; {', '.join(what)}; {where}.")
    return "\n".join(lines)


def answer_sections(text: str) -> dict:
    """The answer's CLAIM, SCALING, WHY IT HELPS and NOTES sections, as written; a missing one is absent."""
    out, current = {}, None
    for line in (text or "").splitlines():
        head = next((name for name in SECTIONS if line.startswith(name + ":")), None)
        if head:
            current = head
            out[head] = line[len(head) + 1:].strip()
        elif current:
            out[current] += "\n" + line
    return {k: v.strip() for k, v in out.items()}


def earlier_text(run: RunDir, sp: dict, step: dict) -> str:
    done = [s for s in sp["steps"] if s["round"] < step["round"] and s.get("result")]
    if not done:
        return "WHAT CAME BEFORE\nThis is the first of these sessions."
    lines = ["WHAT THE EARLIER SESSIONS FOUND"]
    for s in done:
        res = s["result"]
        lines.append(f"The session on {s['parameter']} (round {s['round']}):")
        for name in ("CLAIM", "SCALING"):
            if res["answer"].get(name):
                lines.append(f"{name}: {res['answer'][name]}")
        if res["lemmas"]:
            lines.append("Its accepted lemmas: " + ", ".join(l["theorem"] or "?" for l in res["lemmas"]) +
                         ". Their modules are in your workspace to read and import.")
        else:
            lines.append("It had no lemma accepted.")
    return "\n".join(lines)


def carried_modules(run: RunDir, sp: dict, step: dict, locked: dict) -> dict:
    """The modules a step's workspace starts with beyond the locked proof's: the other offered proofs', and
    those of the lemmas earlier steps had accepted (the later step's version of a path, the proofs' own
    version where a proof has one)."""
    out = {}
    for s in sorted((s for s in sp["steps"] if s["round"] < step["round"] and s.get("result")), key=lambda s: s["round"]):
        for l in s["result"]["lemmas"]:
            sub = Path(l["submission_dir"])
            for rel in l.get("modules") or []:
                if (sub / rel).is_file():
                    out[rel] = (sub / rel).read_text()
    for p in sp["proofs"]:
        if p["offered"] and not p["locked"]:
            sub = Path(p["submission_dir"])
            for rel in p["modules"]:
                if (sub / rel).is_file():
                    out[rel] = (sub / rel).read_text()
    return {rel: text for rel, text in out.items() if rel not in locked["modules"]}


def proofs_file(sp: dict) -> str:
    items = []
    for p in sp["proofs"]:
        manifest, receipt = _submitted(Path(p["submission_dir"]))
        block = manifest.get("scored") if isinstance(manifest.get("scored"), dict) else {}
        scoring = receipt.get("scoring") if isinstance(receipt.get("scoring"), dict) else {}
        items.append({"record_id": p["record_id"], "locked": p["locked"], "in_workspace": p["offered"], "checker": p["checker"],
                      "sound": p["sound"], "certificate": block.get("certificate") or [], "plan": block.get("plan"),
                      "certified_count": receipt.get("certified_count"), "bill": scoring.get("bill"), "length": scoring.get("length"),
                      "description_size": scoring.get("description_size"), "plan_bits": scoring.get("plan_bits"),
                      "modules": p["modules"]})
    return json.dumps({"what": "The run's scored proofs these sessions are about: each one's certificate and plan as submitted, "
                               "and what the service's receipt says of it.", "proofs": items}, indent=1)


def build_step_prompt(step_cfg: dict, folder, run: RunDir, k: int, step: dict, state: dict, entry: dict) -> Prompt:
    """A step's prompt: the run's part 1 (with the step's session time) and the step's own text. Opens the
    step's session, which starts from the locked proof and what the step carries."""
    part1_t, _ = load_template(workflow.general_template(step_cfg))
    part1 = fill(part1_t, static_values(step_cfg, folder, [entry]))
    leaked = [t for t in forbidden(folder) if t in part1]
    if leaked:
        raise PromptError(f"the model folder puts forbidden strings into the prompt: {leaked}")
    locked, sp = state["locked"], state["scaling_proofs"]
    try:
        lock = read_lock(Path(locked["submission_dir"]), stages.lean_project_of(step_cfg))
    except LockError as exc:
        raise ScalingError(f"the locked proof in {locked['submission_dir']} can no longer be read as it was locked ({exc})")
    if lock["digest"] != locked["digest"] or lock["fingerprints"] != locked["fingerprints"]:
        raise ScalingError(f"the locked proof's modules in {locked['submission_dir']} changed since they were locked")
    extra = carried_modules(run, sp, step, lock)
    stage = {"name": "scaling", "of": locked["record_id"], "submission": locked["submission_dir"], "lock": lock,
             "step": step["parameter"], "extra_modules": extra,
             "python_given": [{"path": PROOFS_FILE, "text": proofs_file(sp)}]}
    Session.create(run.round_path(k) / "attempt_0" / "open_lane", step_cfg, step_cfg["model"], [entry], run.path, stage=stage)
    path = TEMPLATES / f"{TEMPLATE}.md"
    if not path.is_file():
        raise PromptError(f"no prompt text {path.name} in {TEMPLATES}")
    order = [s["parameter"] for s in sp["steps"]]
    i = order.index(step["parameter"])
    held = [p for p in SCALING_PARAMETERS if p != step["parameter"]]
    others = [p for p in sp["proofs"] if not p["locked"] and p["offered"]]
    n = entry["n_inputs"]
    values = {
        "SYMBOL": step["parameter"], "NETWORK": entry["id"],
        "PARAMETER": f"{WORDS[step['parameter']]} {_size_text(sp['sizes'], step['parameter'])}",
        "HELD": " and ".join(f"{WORDS[p]} {_size_text(sp['sizes'], p)}" for p in held),
        "STEP_LINE": (f"There is one session per size, in this order: " + ", then ".join(f"{WORDS[p]} {p}" for p in order) +
                      f". This is session {i + 1} of {len(order)}."),
        "PROOFS": proofs_text(sp["proofs"]), "LOCKED": stages.locked_text(lock), "RENAME": stages.rename_text(lock),
        "OTHERS": ("" if not others else
                   " The modules of the other proofs above are in your workspace too, to read and import: "
                   + ", ".join(sorted({rel for p in others for rel in p["modules"] if rel not in lock["modules"]})) + "."),
        "EARLIER": earlier_text(run, sp, step),
        "SIZES": ", ".join(_size_text(sp["sizes"], p) for p in SCALING_PARAMETERS),
        "N": f"{n:,}", "B": f"{entry['B']:,}", "PER_INPUT": stages._num((entry["B"] - entry["E"]) / n),
    }
    part2 = fill(path.read_text(), values)
    stats = {"chars": len(part1) + len(part2), "tokens_estimate": (len(part1) + len(part2)) // CHARS_PER_TOKEN, "trimmed": [],
             "template": workflow.general_template(step_cfg), "lane": "open", "stage": f"scaling_{step['parameter']}"}
    return Prompt(part1, part2, stats)


# what a step found ---------------------------------------------------------------------------
def step_result(run: RunDir, cfg: dict, records: list[dict], k: int, sp: dict) -> dict:
    """A step's lemmas (each with its statement, its modules, and which proofs' checkers Lean finds in what the
    service compiled for it) and its answer's sections."""
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
    lemmas = []
    for l in base["lemmas"]:
        rec = by_id[l["record_id"]]
        sub = stages.submission_dir(run, rec)
        try:
            modules = json.loads((sub / "manifest.json").read_text()).get("modules") or []
        except (OSError, ValueError):
            modules = []
        checkers = {}
        locked_proof = next(p for p in sp["proofs"] if p["locked"])
        checkers[locked_proof["record_id"]] = {"verified": l["locked_checker"], "why": l.get("why")}
        for p in others:
            lock = locks[p["record_id"]]
            if isinstance(lock, Exception):
                checkers[p["record_id"]] = {"verified": None, "why": f"its lock could not be read: {lock}"}
                continue
            try:
                check = same_checker(lock, sub, project, scored=False)
            except Exception as exc:  # recorded as unknown: the step's result stands without it
                check = {"verified": None, "why": f"the question failed: {exc!r}"}
            checkers[p["record_id"]] = {"verified": check["verified"], "why": check.get("why")}
        lemmas.append({**l, "submission_dir": str(sub), "modules": modules, "checkers": checkers})
    answer = answer_sections(run.read(k, "attempt_0/response.md") or "")
    meta = run.read(k, "attempt_0/response_meta.json") or {}
    return {"lemmas": lemmas, "submissions": base["submissions"], "answer": answer,
            "cost_usd": meta.get("cost_usd"), "seconds": meta.get("seconds")}


# running them ------------------------------------------------------------------------------
def run_steps(ctx, backend, run_round, only: list[str] | None = None) -> None:
    """Run the steps not done yet, in order (with `only`, just those, which must be the next ones)."""
    cfg, run = ctx.cfg, ctx.run
    entry = ctx.entries[0]
    if len(ctx.entries) != 1:
        raise ScalingError("the scaling proofs are for a run on one network")
    state = begin(run, cfg, ctx.folder, entry)
    sp = state["scaling_proofs"]
    todo = [s for s in sp["steps"] if s["result"] is None]
    if only:
        names = [s["parameter"] for s in todo]
        if names[:len(only)] != list(only):
            raise ScalingError(f"the steps go in order; the next ones are {', '.join(names) or 'none'}, not {', '.join(only)}")
        todo = todo[:len(only)]
    if not todo:
        ctx.log("the scaling proofs are done; nothing to run")
        return
    locked = state["locked"]
    ctx.log(f"scaling proofs on {sp['network']}: " + "; ".join(
        f"{p['record_id']} ({p['certified']:,} at length {p['length']:,})" + ("" if p["offered"] else f", not offered: {p['why']}")
        for p in sp["proofs"]) + f"; locked {locked['record_id']}")
    per_round = cfg["recipes_per_round"]
    for step in todo:
        k = step["round"]
        step_cfg = step_config(cfg, step)
        if hasattr(backend, "bind"):
            backend.bind(step_cfg, step_cfg["model"], [entry], run.path)
        spent = backend.exhausted(run.path) if hasattr(backend, "exhausted") and not run.round_done(k) else None
        if spent:
            ctx.log(f"{spent}; the step on {step['parameter']} (round {k}) is left for a run of this command with --budget-usd")
            return
        saved = run.read(k, "prompt.json")
        if saved is None and not run.round_done(k) and not backend.available((k - 1) * per_round):
            ctx.log(f"the {backend.name} backend has no more responses; the step on {step['parameter']} (round {k}) is left for later")
            return
        prompt = Prompt.from_json(saved) if saved is not None else build_step_prompt(step_cfg, ctx.folder, run, k, step, state, entry)
        ctx.log(f"round {k}: scaling in {step['parameter']} ({step['minutes']:g} minutes, ${float(step['usd']):.2f})"
                + (f"; prompt of about {prompt.stats['tokens_estimate']:,} tokens" if saved is None else ""))
        step_ctx = dataclasses.replace(ctx, cfg=step_cfg, entries=[entry])
        run_round(step_ctx, k, backend, (k - 1) * per_round, 1, "agent", prompt=prompt)
        step["result"] = step_result(run, step_cfg, run.read_archive(), k, sp)
        stages.write_state(run, state)
        ctx.log("  " + step_line(step))


# what is shown -----------------------------------------------------------------------------
def step_line(step: dict) -> str:
    res = step.get("result")
    head = f"scaling in {step['parameter']} (round {step['round']})"
    if res is None:
        return head + ": not done yet"
    n = len(res["lemmas"])
    about = sum(1 for l in res["lemmas"] if any(c["verified"] for c in l["checkers"].values()))
    return (f"{head}: {n} lemma(s) accepted, {about} shown by Lean to hold a submitted proof's checker"
            + (f"; ${res['cost_usd']:.2f}" if isinstance(res.get("cost_usd"), (int, float)) and res["cost_usd"] else ""))


def status_lines(run: RunDir) -> list[str]:
    state = stages.read_state(run) or {}
    sp = state.get("scaling_proofs")
    if not sp:
        return []
    return ["scaling proofs (after the run, never scored):"] + ["  " + step_line(s) for s in sp["steps"]]


def report_lines(run: RunDir) -> list[str]:
    state = stages.read_state(run) or {}
    sp = state.get("scaling_proofs")
    if not sp:
        return []
    lines = ["## The scaling proofs", "",
             "Started after the run by a person, one session per size, each with the other sizes held at this network's: "
             + ", ".join(_size_text(sp["sizes"], p) for p in SCALING_PARAMETERS) + ". Never scored. A lemma's statement is "
             "the agent's own: read it before relying on it. Under each lemma: the proofs whose checker Lean finds, term "
             "for term, in the modules the service compiled for it; only for those is the checker's name in the statement "
             "the checker that was submitted.", "",
             "The proofs:", ""]
    lines += [f"- `{p['record_id']}`: checker `{p['checker']}`, {p['certified']:,} certified at length {p['length']:,}"
              + (" (locked)" if p["locked"] else "" if p["offered"] else f"; not offered: {p['why']}") for p in sp["proofs"]]
    lines.append("")
    for s in sp["steps"]:
        res = s.get("result")
        lines += [f"### {s['parameter']}: {WORDS[s['parameter']]} (round {s['round']}, {s['minutes']:g} minutes, at most ${float(s['usd']):.2f})", ""]
        if res is None:
            lines += ["Not done yet.", ""]
            continue
        for name in ("CLAIM", "SCALING"):
            if res["answer"].get(name):
                lines += [f"**{name.title()}** (the agent's):", "", res["answer"][name], ""]
        lines += [f"The whole answer is `round_{s['round']:03d}/attempt_0/response.md`. Lemmas accepted: {len(res['lemmas'])}.", ""]
        for l in res["lemmas"]:
            found = [rid for rid, c in l["checkers"].items() if c["verified"]]
            unknown = [rid for rid, c in l["checkers"].items() if c["verified"] is None]
            lines.append(f"- `{l['theorem']}`: " + (f"holds the checker of {', '.join(f'`{r}`' for r in found)}" if found else
                                                    "holds no submitted proof's checker, by Lean's account")
                         + (f"; not known for {', '.join(f'`{r}`' for r in unknown)}" if unknown else "")
                         + ("; it uses what the run does not offer of the Lean project's library" if l.get("beyond_offered") else ""))
            lines += ["", "  ```", "  " + (l.get("statement") or "(no statement in the receipt)"), "  ```", ""]
    return lines
