"""After a run: the scaling proofs (`python3 -m core.loop scale --run <run folder>`).

A person starts this once a run's proofs have been looked at; the run itself never does. The sessions ask, as
theorems of Lean, how the cost of the run's scored proofs grows with each size of the network (the number of
token values V, the number of positions n, the width d) against brute force's. Nothing in them is scored.

- The result for a size is four links, each a theorem the service accepted or missing (LINKS): `general`, a
  checker with the size as a parameter that is the submitted checker at this network's value (a submitted
  checker has the network's sizes written in, or tests them against the network's own graph, and then refuses
  every other value); `cost`, its exact bill at every value; `formula`, that bill in closed form or between
  bounds; `brute`, brute force's cost and the comparison. A formula worked out by hand, a Python model or a Lean
  function evaluated at a few sizes is not a link.
- The sessions, in the order of open_lane.scaling_steps: `general` (the first two links, for all three sizes at
  once: the work they share), then V, n and d (the other two links, and the first two where they are missing).
  Each has its own minutes and dollars (a run made before the setting existed takes config/defaults.yaml's). A
  run billed to an API key pays them from its own budget; `--budget-usd` raises it, as for resume.
- Further sessions: `--again [steps]` adds a session for each named step (none named: for each configured step)
  to a run whose steps are done, with `--minutes` and `--usd` in place of the configured ones when given. The
  first scaling proofs (23 and 24 November 2026) asked for formulas with whatever could be proved, and most of
  their formulas stayed unproved; a further session starts from all that was accepted and from what the earlier
  sessions left.
- Which sizes: the model folder's open_lane.scaling_sizes names, for V, n and d, the entries of its size
  settings that are that size (an attention model's width and head width vary together). A model folder without
  it has no scaling proofs.
- Which proofs: the run's scored proofs of its network that no shorter proof matched in inputs certified. The
  locked proof (core.open_lane.stages) is in each session's workspace, locked, as in the scaling question. The
  other proofs' modules are there to read and import where they do not clash with the locked proof's (a module
  at the same path with other text); a proof whose modules clash is listed with why, and not offered. Every
  proof's certificate and plan, with its receipt's count and bill, are in the Python workspace
  (py/handed_in_proofs.json).
- What a session starts with: the modules of the lemmas the earlier sessions had accepted; the modules they
  left without submitting them (drafts); their Python files; and their answers. Every module of the workspace
  is compiled before the session begins, in import order and at no charge (Session._prebuild): the first
  sessions spent a third of their compiles on building the locked proof's modules one by one.
- What is recorded (stages.json, `scaling_proofs`): each step's round, prompt text and result. For each accepted
  lemma: its statement in full; which of the proofs' checkers Lean finds in the modules the service compiled for
  it (core.open_lane.lock.same_checker; the session asks for the locked proof, the others are asked after it);
  and which of the proofs' checkers its statement names. Only a lemma whose statement names a checker that Lean
  found says anything about a submitted proof: the first sessions' lemmas that compared two formulas of the
  agent's own were counted as "holding the checker" because their modules did. For each link the answer names
  (its THEOREMS section): the theorem, and whether it is the named theorem of an accepted submission. A statement
  is the agent's own: a person reads it before relying on it.

The steps are rounds of the run after its last round. Running the command again goes on with the steps not
done; an interrupted step is resumed like any round.
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
from ..run_config import DEFAULTS_PATH, SCALING_GENERAL, SCALING_PARAMETERS, SCALING_STEPS, scaling_steps_errors
from . import answer, stages, workflow
from .lock import LockError, LockUnread, read_lock, same_checker
from .prompt import static_values
from .session import MODULE_PATH, PY_DIR, Session, last_compiles, workspace_files

TEMPLATE_FIRST = "open_lane_scaling_step_v1"  # the sessions of 23 and 24 November 2026: formulas, proved where it could be
TEMPLATE_GENERAL = "open_lane_scaling_general_v1"
TEMPLATE_SIZE = "open_lane_scaling_step_v2"
PROOFS_FILE = "handed_in_proofs.json"
WORDS = {"V": "the number of token values", "n": "the number of positions", "d": "the width"}
SECTIONS = ("CLAIM", "THEOREMS", "SCALING", "WHY IT HELPS", "NOTES")
LINKS = ("general", "cost", "formula", "brute")
AS_SUBMITTED = "as submitted"  # a THEOREMS line's word for a submitted checker that is general in the size as it is


class ScalingError(ValueError):
    pass


# configuration -------------------------------------------------------------------------------
def default_steps() -> list[dict]:
    return [dict(s) for s in yaml.safe_load(DEFAULTS_PATH.read_text())["open_lane"]["scaling_steps"]]


def configured_steps(cfg: dict) -> list[dict]:
    """The steps, in order: the run's open_lane.scaling_steps, or config/defaults.yaml's for a run made before
    there were any."""
    steps = (cfg.get("open_lane") or {}).get("scaling_steps")
    if steps is None:
        steps = default_steps()
    errors = scaling_steps_errors(steps)
    if errors:
        raise ScalingError("; ".join(errors))
    return [dict(s) for s in steps]


def is_general(step: dict) -> bool:
    return step["parameter"] == SCALING_GENERAL


def step_name(step: dict) -> str:
    """A step as the log, the status and the report call it."""
    return ("scaling, the general checker" if is_general(step) else f"scaling in {step['parameter']}") + (
        ", a further session" if step.get("again") else "")


def step_words(step: dict) -> str:
    """A step as a prompt calls it."""
    return ("the checker with its sizes as parameters" if is_general(step) else f"{WORDS[step['parameter']]} {step['parameter']}") + (
        " again" if step.get("again") else "")


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


def add_sessions(run: RunDir, cfg: dict, state: dict, names: list[str], minutes: float | None = None,
                 usd: float | None = None) -> list[dict]:
    """`--again`: one further session for each named step (none named: each configured step), in the steps'
    order, as rounds after the run's last, at the configured minutes and dollars unless others are given. Only
    once every step so far is done: a step that waits is gone on with first, by the command without --again."""
    sp = state["scaling_proofs"]
    waiting = [s for s in sp["steps"] if s["result"] is None]
    if waiting:
        raise ScalingError(f"{step_name(waiting[0])} (round {waiting[0]['round']}) is not done yet: go on with it first "
                           "(the command without --again), then add further sessions")
    for key, value in (("--minutes", minutes), ("--usd", usd)):
        if value is not None and not value > 0:
            raise ScalingError(f"{key} must be a positive number")
    unknown = [n for n in names if n not in SCALING_STEPS]
    if unknown:
        raise ScalingError(f"--again takes some of {', '.join(SCALING_STEPS)}, not {', '.join(map(str, unknown))}")
    settings = {s["parameter"]: s for s in default_steps()}
    settings.update({s["parameter"]: s for s in configured_steps(cfg)})
    wanted = [p for p in SCALING_STEPS if p in (names or [s["parameter"] for s in configured_steps(cfg)])]
    k = max([s["round"] for s in sp["steps"]] + (run.done_rounds() or [0]))
    added = []
    for p in wanted:
        k += 1
        added.append({"parameter": p, "minutes": float(minutes) if minutes is not None else settings[p]["minutes"],
                      "usd": float(usd) if usd is not None else settings[p]["usd"], "round": k, "result": None, "again": True})
    sp["steps"] += added
    stages.write_state(run, state)
    return added


# the links -----------------------------------------------------------------------------------
_LINK_LINE = re.compile(r"^[\s\-*`]*(V|n|d)[\s`*]+(general|cost|formula|brute)[\s`*]*:[\s`*]*(.*)$")
_THEOREM_NAME = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+")


def parse_links(text: str) -> list[dict]:
    """The THEOREMS section's lines `<size> <link>: <theorem>`: for each, the theorem's full name, or none; a
    checker said to be general `as submitted` is kept as that. Lines of another form are not links."""
    out = []
    for line in (text or "").splitlines():
        m = _LINK_LINE.match(line)
        if not m:
            continue
        value = m.group(3).strip()
        name = _THEOREM_NAME.match(value.lstrip("`*( "))
        out.append({"size": m.group(1), "link": m.group(2), "theorem": name.group(0) if name else None,
                    "as_submitted": name is None and value.lstrip("`*( ").lower().startswith(AS_SUBMITTED)})
    return out


def accepted_theorems(records: list[dict], upto: int) -> dict:
    """Theorem name -> the round the service accepted it in as the named theorem of a lemma submission, in the
    run's proof rounds or in a scaling session up to round `upto` (the service checks the axioms of the named
    theorem alone, so another theorem of an accepted module is not vouched for by it)."""
    out: dict = {}
    for r in sorted(records, key=lambda r: r.get("round") or 0):
        if r.get("status") == "lemma" and r.get("theorem") and (r.get("round") or 0) <= upto:
            out.setdefault(r["theorem"], r["round"])
    return out


def links_table(sp: dict) -> dict:
    """Per size and link, what the sessions' answers say holds it, the latest that names an accepted theorem (or
    says `as submitted`) first, else the latest line: {theorem, accepted, as_submitted, round}. Empty for a run
    whose sessions were not asked for the links."""
    table: dict = {}
    for s in sorted((s for s in sp["steps"] if s.get("result")), key=lambda s: s["round"]):
        for l in s["result"].get("links") or []:
            row = table.setdefault(l["size"], {})
            good = l.get("accepted") or l.get("as_submitted")
            had = row.get(l["link"])
            if good or had is None or not (had.get("accepted") or had.get("as_submitted")):
                row[l["link"]] = {**{k: l.get(k) for k in ("theorem", "accepted", "as_submitted")}, "round": s["round"]}
    return table


def _link_cell(cell: dict | None, code: bool = False) -> str:
    if cell is None:
        return "not said"
    if cell.get("as_submitted"):
        return "the submitted checker, as it is"
    if not cell.get("theorem"):
        return "none"
    name = f"`{cell['theorem']}`" if code else cell["theorem"]
    return name if cell.get("accepted") else f"{name} (named, not an accepted submission's theorem)"


def links_status(sp: dict) -> list[str]:
    """For the status: per size, which links an accepted theorem holds, by the sessions' own account."""
    table = links_table(sp)
    if not table:
        return []
    lines = ["theorems per size (general, cost, formula, brute), by the sessions' own account of what each says:"]
    for p in SCALING_PARAMETERS:
        row = table.get(p) or {}
        have = [k for k in LINKS if (row.get(k) or {}).get("accepted") or (row.get(k) or {}).get("as_submitted")]
        lines.append(f"  {p}: " + (", ".join(have) if have else "none") +
                     ("" if len(have) == len(LINKS) else "; missing: " + ", ".join(k for k in LINKS if k not in have)))
    return lines


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
    """The answer's CLAIM, THEOREMS, SCALING, WHY IT HELPS and NOTES sections, as written; a missing one is
    absent. Headings are read as `answer.sections` reads them: in bold too, and after text the session wrote
    before a tool call."""
    return answer.sections(text, SECTIONS)


def _earlier(sp: dict, step: dict) -> list[dict]:
    return sorted((s for s in sp["steps"] if s["round"] < step["round"] and s.get("result")), key=lambda s: s["round"])


def earlier_text(run: RunDir, sp: dict, step: dict) -> str:
    done = _earlier(sp, step)
    if not done:
        return "WHAT CAME BEFORE\nThis is the first of these sessions."
    lines = ["WHAT THE EARLIER SESSIONS FOUND"]
    for s in done:
        res = s["result"]
        lines.append(f"The session on {step_words(s)} (round {s['round']}):")
        for name in ("CLAIM", "THEOREMS", "SCALING"):
            if res["answer"].get(name):
                lines.append(f"{name}:" + ("\n" if "\n" in res["answer"][name] else " ") + res["answer"][name])
        if res["lemmas"]:
            lines.append("Its accepted lemmas: " + ", ".join(l["theorem"] or "?" for l in res["lemmas"]) +
                         ". Their modules are in your workspace to read and import.")
        else:
            lines.append("It had no lemma accepted.")
    table = links_table(sp)
    if table:
        lines.append("THE LINKS SO FAR, by those sessions' own account (a theorem is named here only as they named it):")
        for p in SCALING_PARAMETERS:
            lines.append(f"- {p}: " + "; ".join(f"{k}: {_link_cell((table.get(p) or {}).get(k))}" for k in LINKS))
    first = [str(s["round"]) for s in done if s.get("template", TEMPLATE_FIRST) == TEMPLATE_FIRST]
    if first:
        lines.append(f"The session{'s' if len(first) > 1 else ''} of round{'s' if len(first) > 1 else ''} {', '.join(first)} "
                     f"{'were' if len(first) > 1 else 'was'} asked for formulas, with as much of them proved as could be, and not "
                     "for the links: the SCALING above says which lemma proves what, and what was worked out by hand or only "
                     "evaluated. Check a lemma's statement before you build on it: what it fixes and what it leaves free.")
    return "\n".join(lines)


def carried_modules(run: RunDir, sp: dict, step: dict, locked: dict) -> dict:
    """The modules a step's workspace starts with beyond the locked proof's: the other offered proofs', and
    those of the lemmas earlier steps had accepted (the later step's version of a path, the proofs' own
    version where a proof has one)."""
    out = {}
    for s in _earlier(sp, step):
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


def session_dir(run: RunDir, step: dict) -> Path:
    return run.round_path(step["round"]) / "attempt_0" / "open_lane"


def draft_modules(run: RunDir, sp: dict, step: dict, locked: dict, held: dict) -> dict:
    """What the earlier steps' sessions left in their workspaces without having it accepted: path -> {text,
    compiled}, the latest session's version, with whether the last compile of that text succeeded (None when
    none is on record). A path the locked proof or a carried module holds stays that module's."""
    out: dict = {}
    for s in _earlier(sp, step):
        root = session_dir(run, s) / "workspace"
        if not (root / "Candidate").is_dir():
            continue
        last = last_compiles(session_dir(run, s))
        for f in sorted((root / "Candidate").rglob("*.lean")):
            rel = f.relative_to(root).as_posix()
            if not (f.is_file() and not f.is_symlink() and MODULE_PATH.match(rel)):
                continue
            text = f.read_text()
            if rel in last:
                compiled = bool(last[rel].get("ok"))
            else:  # not compiled in that session: as the session before left it, if it is the same text
                compiled = out[rel]["compiled"] if rel in out and out[rel]["text"] == text else None
            out[rel] = {"text": text, "compiled": compiled}
    taken = set(locked["modules"]) | set(locked.get("free") or []) | set(held)
    return {rel: d for rel, d in out.items() if rel not in taken}


def earlier_python(run: RunDir, sp: dict, step: dict) -> list[dict]:
    """The files the earlier steps' sessions left in their Python workspaces (the latest session's version of a
    path), but for the two the pipeline writes afresh."""
    out = {}
    for s in _earlier(sp, step):
        files, _ = workspace_files(session_dir(run, s) / PY_DIR)
        for rel, path in files.items():
            if rel not in (PROOFS_FILE, Session.LOCKED_PROOF):
                out[rel] = str(path)
    return [{"path": rel, "source": src} for rel, src in sorted(out.items())]


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


def workspace_text(session: Session, drafts: dict, python: list[dict]) -> str:
    """What a session's workspace holds beyond the proofs' modules, and what of it is compiled."""
    lines = []
    built = session.state.get("prebuilt")
    if isinstance(built, list) and built:
        bad = [b for b in built if not b["compiled"]]
        lines.append("Every module in your workspace was compiled before this session began, in import order, at no "
                     "charge to your budgets: import them as they are (a lean_check of one with `edits: []` compiles it again)."
                     if not bad else
                     f"The modules in your workspace were compiled before this session began, in import order, at no charge to "
                     f"your budgets: {len(built) - len(bad)} of {len(built)} compiled. Not compiled: "
                     + "; ".join(f"{b['path']} ({(b['errors'] or ['no message'])[0][:160]})" for b in bad) + ".")
    if drafts:
        lines.append("Left by the earlier sessions without being accepted (drafts: nothing in one is proved until the "
                     "service accepts it, and one may not compile): " + ", ".join(sorted(drafts)) + ".")
    if python:
        lines.append("Your Python workspace also holds the earlier sessions' files: " + ", ".join("py/" + f["path"] for f in python) + ".")
    return "\n".join(lines)


def clock_text(step_cfg: dict) -> str:
    """The session's time, said so that it cannot be subtracted twice (two of the first sessions took
    `remaining.seconds` to include the time kept for the answer, and stopped with half their tool time left)."""
    total = int(step_cfg["open_lane"]["worker_seconds"])
    reserve = int(step_cfg["open_lane"].get("notes_reserve_seconds") or 0)
    tools = max(0, total - reserve)
    return (f"This session has {total // 60} minutes: {tools // 60} of tool time, then {reserve // 60} for writing the answer. "
            f"`remaining.seconds` in a tool's answer is the tool time left (about {tools:,} at the start); the answer's "
            "time comes after it and is not in that number.")


def build_step_prompt(step_cfg: dict, folder, run: RunDir, k: int, step: dict, state: dict, entry: dict) -> Prompt:
    """A step's prompt: the run's part 1 (with the step's session time) and the step's own text. Opens the
    step's session, which starts from the locked proof and what the step carries, compiled."""
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
    drafts = draft_modules(run, sp, step, lock, extra)
    python = earlier_python(run, sp, step)
    stage = {"name": "scaling", "of": locked["record_id"], "submission": locked["submission_dir"], "lock": lock,
             "step": step["parameter"], "extra_modules": {**extra, **{rel: d["text"] for rel, d in drafts.items()}},
             "prebuild": True, "drafts": {rel: d["compiled"] for rel, d in drafts.items()},
             "python_given": [{"path": PROOFS_FILE, "text": proofs_file(sp)}] + python}
    session = Session.create(run.round_path(k) / "attempt_0" / "open_lane", step_cfg, step_cfg["model"], [entry], run.path, stage=stage)
    template = TEMPLATE_GENERAL if is_general(step) else TEMPLATE_SIZE
    path = TEMPLATES / f"{template}.md"
    if not path.is_file():
        raise PromptError(f"no prompt text {path.name} in {TEMPLATES}")
    order = sorted(sp["steps"], key=lambda s: s["round"])
    i = [s["round"] for s in order].index(step["round"])
    others = [p for p in sp["proofs"] if not p["locked"] and p["offered"]]
    n = entry["n_inputs"]
    values = {
        "NETWORK": entry["id"],
        "STEP_LINE": ("The sessions, in order: " + ", then ".join(step_words(s) for s in order) +
                      f". This is session {i + 1} of {len(order)}."),
        "PROOFS": proofs_text(sp["proofs"]), "LOCKED": stages.locked_text(lock), "RENAME": stages.rename_text(lock),
        "OTHERS": ("" if not others else
                   " The modules of the other proofs above are in your workspace too, to read and import: "
                   + ", ".join(sorted({rel for p in others for rel in p["modules"] if rel not in lock["modules"]})) + "."),
        "WORKSPACE": workspace_text(session, drafts, python),
        "EARLIER": earlier_text(run, sp, step),
        "SIZES": ", ".join(_size_text(sp["sizes"], p) for p in SCALING_PARAMETERS),
        "N": f"{n:,}", "B": f"{entry['B']:,}", "PER_INPUT": stages._num((entry["B"] - entry["E"]) / n),
        "CHECKERS": ", ".join(str(p["checker"]) for p in sp["proofs"] if p["offered"]),
        "CLOCK": clock_text(step_cfg),
    }
    if not is_general(step):
        held = [p for p in SCALING_PARAMETERS if p != step["parameter"]]
        values.update({
            "SYMBOL": step["parameter"], "VALUE": str(sp["sizes"][step["parameter"]]["value"]),
            "PARAMETER": f"{WORDS[step['parameter']]} {_size_text(sp['sizes'], step['parameter'])}",
            "HELD": " and ".join(f"{WORDS[p]} {_size_text(sp['sizes'], p)}" for p in held),
        })
    part2 = fill(path.read_text(), values)
    stats = {"chars": len(part1) + len(part2), "tokens_estimate": (len(part1) + len(part2)) // CHARS_PER_TOKEN, "trimmed": [],
             "template": workflow.general_template(step_cfg), "lane": "open", "stage": f"scaling_{step['parameter']}"}
    return Prompt(part1, part2, stats)


# what a step found ---------------------------------------------------------------------------
def names_in(statement: str | None, proofs: list[dict]) -> list[str]:
    """The proofs whose checker's name a statement holds as a whole name (their record ids)."""
    return [p["record_id"] for p in proofs
            if p.get("checker") and re.search(r"(?<![\w.'])" + re.escape(p["checker"]) + r"(?![\w'.])", statement or "")]


def about(lemma: dict, proofs: list[dict]) -> list[str]:
    """The proofs a lemma says something about: its statement names their checker, and Lean found that checker,
    term for term, in the modules the service compiled for it. (A result from before the names were recorded
    is read from its statement.)"""
    names = lemma["names"] if "names" in lemma else names_in(lemma.get("statement"), proofs)
    return [rid for rid in names if (lemma["checkers"].get(rid) or {}).get("verified")]


def step_result(run: RunDir, cfg: dict, records: list[dict], k: int, sp: dict) -> dict:
    """A step's lemmas (each with its statement, its modules, which proofs' checkers Lean finds in what the
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
        lemmas.append({**l, "submission_dir": str(sub), "modules": modules, "checkers": checkers,
                       "names": names_in(l.get("statement"), sp["proofs"])})
    answer = answer_sections(run.read(k, "attempt_0/response.md") or "")
    accepted = accepted_theorems(records, k)
    links = [{**l, "accepted": (l["theorem"] in accepted) if l["theorem"] else None} for l in parse_links(answer.get("THEOREMS", ""))]
    meta = run.read(k, "attempt_0/response_meta.json") or {}
    return {"lemmas": lemmas, "submissions": base["submissions"], "answer": answer, "links": links,
            "cost_usd": meta.get("cost_usd"), "seconds": meta.get("seconds")}


# running them ------------------------------------------------------------------------------
def run_steps(ctx, backend, run_round, only: list[str] | None = None, again: list[str] | None = None,
              minutes: float | None = None, usd: float | None = None) -> None:
    """Run the steps not done yet, in order (with `only`, just those, which must be the next ones). With `again`
    (a list, which may be empty), first add a further session for each named step (add_sessions)."""
    cfg, run = ctx.cfg, ctx.run
    entry = ctx.entries[0]
    if len(ctx.entries) != 1:
        raise ScalingError("the scaling proofs are for a run on one network")
    if again is None and (minutes is not None or usd is not None):
        raise ScalingError("--minutes and --usd are for the sessions --again adds; the first ones take open_lane.scaling_steps'")
    state = begin(run, cfg, ctx.folder, entry)
    sp = state["scaling_proofs"]
    if again is not None:
        added = add_sessions(run, cfg, state, list(again), minutes, usd)
        ctx.log("added: " + "; ".join(f"{step_name(s)} (round {s['round']}, {s['minutes']:g} minutes, ${float(s['usd']):.2f})" for s in added))
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
            ctx.log(f"{spent}; {step_name(step)} (round {k}) is left for a run of this command with --budget-usd")
            return
        saved = run.read(k, "prompt.json")
        if saved is None and not run.round_done(k) and not backend.available((k - 1) * per_round):
            ctx.log(f"the {backend.name} backend has no more responses; {step_name(step)} (round {k}) is left for later")
            return
        if saved is None:
            # on record before the prompt is: a step with a saved prompt and no text named got the first sessions'
            step["template"] = TEMPLATE_GENERAL if is_general(step) else TEMPLATE_SIZE
            stages.write_state(run, state)
            ctx.log(f"round {k}: {step_name(step)}: compiling the workspace before the session")
        prompt = Prompt.from_json(saved) if saved is not None else build_step_prompt(step_cfg, ctx.folder, run, k, step, state, entry)
        # the pipeline the step runs with: it may be later than the run's (core.loop.after_run_refusal)
        versions = ctx.versions or {}
        step["pipeline"] = {"commit": (versions.get("git") or {}).get("commit"),
                            "changed_since_run": list((versions.get("after_run") or {}).get("changed") or [])}
        stages.write_state(run, state)
        built = _prebuilt(run, step)
        ctx.log(f"round {k}: {step_name(step)} ({step['minutes']:g} minutes, ${float(step['usd']):.2f})"
                + (f"; prompt of about {prompt.stats['tokens_estimate']:,} tokens" if saved is None else "")
                + (f"; {sum(1 for b in built if b['compiled'])} of {len(built)} modules compiled beforehand "
                   f"({sum(b['seconds'] for b in built):.0f} s)" if built else ""))
        step_ctx = dataclasses.replace(ctx, cfg=step_cfg, entries=[entry])
        run_round(step_ctx, k, backend, (k - 1) * per_round, 1, "agent", prompt=prompt)
        step["result"] = step_result(run, step_cfg, run.read_archive(), k, sp)
        stages.write_state(run, state)
        ctx.log("  " + step_line(step, sp["proofs"]))


def _prebuilt(run: RunDir, step: dict) -> list[dict]:
    try:
        built = json.loads((session_dir(run, step) / "session.json").read_text()).get("prebuilt")
    except (OSError, ValueError):
        return []
    return built if isinstance(built, list) else []


# what is shown -----------------------------------------------------------------------------
def step_line(step: dict, proofs: list[dict]) -> str:
    res = step.get("result")
    head = f"{step_name(step)} (round {step['round']})"
    if res is None:
        return head + ": not done yet"
    n = len(res["lemmas"])
    said = sum(1 for l in res["lemmas"] if about(l, proofs))
    return (f"{head}: {n} lemma(s) accepted, {said} with a submitted proof's checker in its statement"
            + (f"; ${res['cost_usd']:.2f}" if isinstance(res.get("cost_usd"), (int, float)) and res["cost_usd"] else ""))


def status_lines(run: RunDir) -> list[str]:
    state = stages.read_state(run) or {}
    sp = state.get("scaling_proofs")
    if not sp:
        return []
    return (["scaling proofs (after the run, never scored):"] + ["  " + step_line(s, sp["proofs"]) for s in sp["steps"]]
            + ["  " + line for line in links_status(sp)])


def report_lines(run: RunDir) -> list[str]:
    state = stages.read_state(run) or {}
    sp = state.get("scaling_proofs")
    if not sp:
        return []
    lines = ["## The scaling proofs", "",
             "Started after the run by a person. They ask, as theorems of Lean, how the proofs' cost grows with each size "
             "of the network against brute force's; on this network " + ", ".join(_size_text(sp["sizes"], p) for p in SCALING_PARAMETERS)
             + ". Never scored. A lemma's statement is the agent's own: read it before relying on it. Under each lemma: the "
             "proofs whose checker Lean finds, term for term, in the modules the service compiled for it, and whether its "
             "statement names one of them. A lemma whose statement names no submitted checker says nothing about the proofs "
             "by itself (it may compare two formulas of the agent's own).", "",
             "The proofs:", ""]
    lines += [f"- `{p['record_id']}`: checker `{p['checker']}`, {p['certified']:,} certified at length {p['length']:,}"
              + (" (locked)" if p["locked"] else "" if p["offered"] else f"; not offered: {p['why']}") for p in sp["proofs"]]
    lines.append("")
    table = links_table(sp)
    if table:
        lines += ["### What is a theorem, per size", "",
                  "The result for a size is four links: `general`, a checker with the size as a parameter that is the submitted "
                  "checker at this network's value; `cost`, its exact bill at every value; `formula`, that bill in closed form or "
                  "between bounds; `brute`, brute force's cost and the comparison. Below, the theorem each session's answer names "
                  "for a link, where it is the named theorem of a submission the service accepted. That it says what the link "
                  "asks is the agent's account: the statements are under the sessions.", "",
                  "| size | general | cost | formula | brute |", "| --- | --- | --- | --- | --- |"]
        lines += [f"| {p} | " + " | ".join(_link_cell((table.get(p) or {}).get(k), code=True) for k in LINKS) + " |" for p in SCALING_PARAMETERS]
        lines.append("")
    for s in sp["steps"]:
        res = s.get("result")
        what = "the checker with its sizes as parameters" if is_general(s) else WORDS[s["parameter"]]
        lines += [f"### {s['parameter']}: {what}" + (", a further session" if s.get("again") else "")
                  + f" (round {s['round']}, {s['minutes']:g} minutes, at most ${float(s['usd']):.2f})", ""]
        if res is None:
            lines += ["Not done yet.", ""]
            continue
        if s.get("template", TEMPLATE_FIRST) == TEMPLATE_FIRST:
            lines += ["Asked for formulas, with as much proved as the session could; not for the links.", ""]
        for name in ("CLAIM", "THEOREMS", "SCALING"):
            if res["answer"].get(name):
                lines += [f"**{name.title()}** (the agent's):", "", res["answer"][name], ""]
        lines += [f"The whole answer is `round_{s['round']:03d}/attempt_0/response.md`. Lemmas accepted: {len(res['lemmas'])}.", ""]
        ran = s.get("pipeline") or {}
        if ran.get("commit"):
            changed = ran.get("changed_since_run") or []
            lines += [f"Ran with pipeline {ran['commit'][:7]}" + (
                f"; changed since the run started: {', '.join(changed)} (its networks, task and architecture are the run's)"
                if changed else "") + ".", ""]
        for l in res["lemmas"]:
            found = [rid for rid, c in l["checkers"].items() if c["verified"]]
            unknown = [rid for rid, c in l["checkers"].items() if c["verified"] is None]
            said = about(l, sp["proofs"])
            lines.append(f"- `{l['theorem']}`: " + (f"its modules hold the checker of {', '.join(f'`{r}`' for r in found)}" if found else
                                                    "its modules hold no submitted proof's checker, by Lean's account")
                         + (f"; not known for {', '.join(f'`{r}`' for r in unknown)}" if unknown else "")
                         + ("; its statement names the checker of " + ", ".join(f"`{r}`" for r in said) if said else
                            "; its statement names no submitted checker")
                         + ("; it uses what the run does not offer of the Lean project's library" if l.get("beyond_offered") else ""))
            lines += ["", "  ```", "  " + (l.get("statement") or "(no statement in the receipt)"), "  ```", ""]
    return lines
