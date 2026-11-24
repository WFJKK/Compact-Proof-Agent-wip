"""A scaling session's prompt: the run's first part, a frame every session shares, and a part per kind of session.

The frame (FRAME) holds what every session is told: the proofs, the locked modules, the workspace, what the
earlier sessions found, the sizes, what counts as a result, how to hand in and how to answer. A part (PARTS, by
plan.kind: the general checker, one size) fills the frame's {TITLE}, {AIM}, {VARIED}, {LINKS}, {TASK},
{HAND_IN} and {ANSWER}: a part file has one `== NAME ==` section for each. Nothing in the texts names a size:
the sizes, their symbols and their words come from the run (core.open_lane.scaling.sizes). A new kind of
session is a part file, an entry in PARTS and a parameter that plan.kind maps to it.

The first sessions (23 and 24 November 2026) got one text, FIRST, which asked for formulas with whatever could
be proved; it is kept as the record of what they were asked. A session's record names its text (`template`); one
that names none got FIRST.
"""

from __future__ import annotations

import re
from pathlib import Path

from ...agent.build_prompt import CHARS_PER_TOKEN, Prompt, PromptError, TEMPLATES, fill, forbidden, load_template
from ...archive import RunDir
from .. import stages, workflow
from ..lock import LockError, read_lock
from ..prompt import static_values
from ..session import Session
from . import links, plan, workspace
from . import sizes as network_sizes

FRAME = "open_lane_scaling_frame_v1"
PARTS = {"general": "open_lane_scaling_part_general_v1", "size": "open_lane_scaling_part_size_v1"}
PART_SECTIONS = ("TITLE", "AIM", "VARIED", "LINKS", "TASK", "HAND_IN", "ANSWER")
FIRST = "open_lane_scaling_step_v1"
ANSWER_SECTIONS = ("CLAIM", "THEOREMS", "SCALING", "WHY IT HELPS", "NOTES")
_SECTION_LINE = re.compile(r"^== ([A-Z_]+) ==$")


def _num(x: float) -> str:
    return f"{x:,.0f}" if float(x).is_integer() else f"{x:,.1f}"


def template_of(step: dict) -> str:
    """The texts a session gets, as its record names them."""
    return f"{FRAME}+{PARTS[plan.kind(step)]}"


def asked_for_links(step: dict) -> bool:
    """Whether a session was asked for the four links (every one but the first sessions, which got FIRST)."""
    return step.get("template", FIRST) != FIRST


def read_part(name: str) -> dict:
    """A part file's sections, by name."""
    path = TEMPLATES / f"{name}.md"
    if not path.is_file():
        raise PromptError(f"no prompt text {path.name} in {TEMPLATES}")
    out: dict = {}
    key = None
    for line in path.read_text().splitlines():
        m = _SECTION_LINE.match(line.strip())
        if m:
            key = m.group(1)
            out[key] = []
        elif key is not None:
            out[key].append(line)
    if set(out) != set(PART_SECTIONS):
        raise PromptError(f"{path.name} must have the sections {', '.join(PART_SECTIONS)}, each under a line `== NAME ==`; it has "
                          f"{', '.join(out) or 'none'}")
    return {k: "\n".join(v).strip("\n") for k, v in out.items()}


def clock_text(step_cfg: dict) -> str:
    """The session's time, said so that it cannot be subtracted twice (two of the first sessions took
    `remaining.seconds` to include the time kept for the answer, and stopped with half their tool time left)."""
    total = int(step_cfg["open_lane"]["worker_seconds"])
    reserve = int(step_cfg["open_lane"].get("notes_reserve_seconds") or 0)
    tools = max(0, total - reserve)
    return (f"This session has {total // 60} minutes: {tools // 60} of tool time, then {reserve // 60} for writing the answer. "
            f"`remaining.seconds` in a tool's answer is the tool time left (about {tools:,} at the start); the answer's "
            "time comes after it and is not in that number.")


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


def earlier_text(sp: dict, step: dict, sizes: list[dict]) -> str:
    done = workspace.earlier(sp, step)
    if not done:
        return "WHAT CAME BEFORE\nThis is the first of these sessions."
    lines = ["WHAT THE EARLIER SESSIONS FOUND"]
    for s in done:
        res = s["result"]
        lines.append(f"The session on {plan.words(s, sizes)} (round {s['round']}):")
        for name in ("CLAIM", "THEOREMS", "SCALING"):
            if res["answer"].get(name):
                lines.append(f"{name}:" + ("\n" if "\n" in res["answer"][name] else " ") + res["answer"][name])
        if res["lemmas"]:
            lines.append("Its accepted lemmas: " + ", ".join(l["theorem"] or "?" for l in res["lemmas"]) +
                         ". Their modules are in your workspace to read and import.")
        else:
            lines.append("It had no lemma accepted.")
    table = links.table(sp["steps"])
    if table:
        lines.append("THE LINKS SO FAR, by those sessions' own account (a theorem is named here only as they named it):")
        for size in sizes:
            row = table.get(size["symbol"]) or {}
            lines.append(f"- {size['symbol']}: " + "; ".join(f"{k}: {links.cell_text(row.get(k))}" for k in links.LINKS))
    first = [str(s["round"]) for s in done if not asked_for_links(s)]
    if first:
        lines.append(f"The session{'s' if len(first) > 1 else ''} of round{'s' if len(first) > 1 else ''} {', '.join(first)} "
                     f"{'were' if len(first) > 1 else 'was'} asked for formulas, with as much of them proved as could be, and not "
                     "for the links: the SCALING above says which lemma proves what, and what was worked out by hand or only "
                     "evaluated. Check a lemma's statement before you build on it: what it fixes and what it leaves free.")
    return "\n".join(lines)


def part_values(step: dict, sizes: list[dict], sp: dict, entry: dict) -> dict:
    """What a part's sections may name: the sizes' symbols, and for the session of one size, that size."""
    symbols = [s["symbol"] for s in sizes]
    values = {"SYMBOLS": network_sizes.listed(symbols), "ORDER": ", ".join(symbols), "FIRST": symbols[0], "B": f"{entry['B']:,}",
              "CHECKERS": ", ".join(str(p["checker"]) for p in sp["proofs"] if p["offered"])}
    if not plan.is_general(step):
        size = plan.size_of(step, sizes)
        others = [s for s in sizes if s["symbol"] != size["symbol"]]
        held = network_sizes.listed([f"{s['words']} {network_sizes.text(s)}" for s in others]) if others else ""
        values.update({
            "SYMBOL": size["symbol"], "VALUE": str(size["value"]),
            "PARAMETER": f"{size['words']} {network_sizes.text(size)}",
            "HELD": f", while {held} stay{'s' if len(others) == 1 else ''} as {'it is' if len(others) == 1 else 'they are'} on this network"
                    if others else "",
            "HOLDS": (f" and holds the other{'' if len(others) == 1 else 's'} at {'its value' if len(others) == 1 else 'these values'} "
                      f"(a theorem that leaves {'it' if len(others) == 1 else 'them'} free as well is stronger and as welcome)") if others else "",
        })
    return values


def build(step_cfg: dict, folder, run: RunDir, k: int, step: dict, state: dict, entry: dict, sizes: list[dict],
          on_compiled=None) -> Prompt:
    """A session's prompt: the run's part 1 (with the session's time), then the frame filled with the session's
    part. Opens the session, which starts from the locked proof and what the session carries
    (core.open_lane.scaling.workspace), and compiles its workspace; `on_compiled`, when given, gets what was
    compiled before the prompt says it."""
    part1_t, _ = load_template(workflow.general_template(step_cfg))
    part1 = fill(part1_t, static_values(step_cfg, folder, [entry]))
    leaked = [t for t in forbidden(folder) if t in part1]
    if leaked:
        raise PromptError(f"the model folder puts forbidden strings into the prompt: {leaked}")
    locked, sp = state["locked"], state["scaling_proofs"]
    try:
        lock = read_lock(Path(locked["submission_dir"]), stages.lean_project_of(step_cfg))
    except LockError as exc:
        raise plan.ScalingError(f"the locked proof in {locked['submission_dir']} can no longer be read as it was locked ({exc})")
    if lock["digest"] != locked["digest"] or lock["fingerprints"] != locked["fingerprints"]:
        raise plan.ScalingError(f"the locked proof's modules in {locked['submission_dir']} changed since they were locked")
    extra = workspace.carried_modules(run, sp, step, lock)
    drafts = workspace.draft_modules(run, sp, step, lock, extra)
    python = workspace.earlier_python(run, sp, step)
    stage = {"name": "scaling", "of": locked["record_id"], "submission": locked["submission_dir"], "lock": lock,
             "step": step["parameter"], "extra_modules": {**extra, **{rel: d["text"] for rel, d in drafts.items()}},
             "python_given": [{"path": workspace.PROOFS_FILE, "text": workspace.proofs_file(sp)}] + python}
    session = Session.create(run.round_path(k) / "attempt_0" / "open_lane", step_cfg, step_cfg["model"], [entry], run.path, stage=stage)
    built = workspace.compile_beforehand(session, {rel: d["compiled"] for rel, d in drafts.items()})
    if on_compiled is not None:
        on_compiled(built)
    frame = TEMPLATES / f"{FRAME}.md"
    if not frame.is_file():
        raise PromptError(f"no prompt text {frame.name} in {TEMPLATES}")
    order = sorted(sp["steps"], key=lambda s: s["round"])
    i = [s["round"] for s in order].index(step["round"])
    others = [p for p in sp["proofs"] if not p["locked"] and p["offered"]]
    n = entry["n_inputs"]
    own = part_values(step, sizes, sp, entry)
    values = {
        "NETWORK": entry["id"],
        "STEP_LINE": ("The sessions, in order: " + ", then ".join(plan.words(s, sizes) for s in order) +
                      f". This is session {i + 1} of {len(order)}."),
        "PROOFS": proofs_text(sp["proofs"]), "LOCKED": stages.locked_text(lock), "RENAME": stages.rename_text(lock),
        "OTHERS": ("" if not others else
                   " The modules of the other proofs above are in your workspace too, to read and import: "
                   + ", ".join(sorted({rel for p in others for rel in p["modules"] if rel not in lock["modules"]})) + "."),
        "WORKSPACE": workspace.text(built, drafts, python),
        "EARLIER": earlier_text(sp, step, sizes),
        "SIZES": ", ".join(network_sizes.text(s) for s in sizes),
        "N": f"{n:,}", "B": own["B"], "PER_INPUT": _num((entry["B"] - entry["E"]) / n),
        "CLOCK": clock_text(step_cfg),
        **{name: fill(text, own) for name, text in read_part(PARTS[plan.kind(step)]).items()},
    }
    part2 = fill(frame.read_text(), values)
    stats = {"chars": len(part1) + len(part2), "tokens_estimate": (len(part1) + len(part2)) // CHARS_PER_TOKEN, "trimmed": [],
             "template": workflow.general_template(step_cfg), "lane": "open", "stage": f"scaling_{step['parameter']}"}
    return Prompt(part1, part2, stats)
