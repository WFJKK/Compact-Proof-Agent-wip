"""The open-lane prompt: the specification, the cost language with its prices, the tools, the scoreboard,
the receipts so far, the agent's accepted lemmas from earlier rounds and its latest notes. No rule
descriptions: the agent is told what a proof is and what it costs, not which argument shapes to use.

Templates: core/agent/prompts/open_lane_v1.md (the pilot's), open_lane_v2.md (adds the further sources
and the split instance), open_lane_v3.md (the modules carried into the workspace listed instead of the
accepted sources pasted in; the instance as one `decide +kernel` with Lean's recursion limit raised, which
is what the kernel needs to compute a bill of thousands of charges) and open_lane_v4.md (for runs over
several networks scored on cost of finishing: the goal is the mechanism shared by seeds and sizes, the
score comes before the rules, the rules of scoring are lists, and there is advice on how to work). Under
the metric cost_of_finishing the scoreboard shows that one score and, per network, the cheapest way to
finish; under the other metrics it is unchanged. Part 1 is the same every round; part 2
is rebuilt from the archive. Building it opens the round's first session, which carries
the earlier rounds' accepted modules into its workspace (core.open_lane.session). The Lean
sources shown (Spec.lean, Counted.lean, CountedOps.lean, the scored example of `open_lane.example`, the
files of `open_lane.extra_sources`) are read from the Lean project the run config names, so the prompt
always matches the service that will check the proof.
"""

from __future__ import annotations

import re
from pathlib import Path

from ..agent.build_prompt import CHARS_PER_TOKEN, Prompt, PromptError, fill, forbidden, grid_text, load_template, metric_scores, metric_text
from ..archive import RunDir
from ..model_folder import ModelFolder
from ..scoring import (brute_force_line, finishing_detail, finishing_ratio, frontier, line_certified, run_cost_of_finishing,
                       summarize)
from ..util import REPO_ROOT
from .session import Session

MAX_LEMMA_CHARS = 12000
MAX_NOTES_CHARS = 6000
MAX_REASON = 300
STALL_TEXT = (
    "No submission of the last {n} rounds was accepted. Change the approach rather than refining the last one: "
    "a different account of the computation, a smaller claim that you can prove completely, or a different "
    "shape of checker. Say in WHY IT HELPS what you are changing and why."
)
AIM_TEXT = (
    "Raise the score. It stands at: {scores}. Before writing, weigh several approaches (a better account of "
    "how the network computes, a cheaper checker for the same inputs, covering inputs still uncertified) and "
    "pursue the one you expect to raise it most."
)
# The aim of a run scored on cost of finishing (the geometric mean over its networks).
AIM_FINISHING_TEXT = (
    "Raise the score. It stands at: {scores}. Before writing, weigh several approaches (a better account of "
    "how the network computes, one checker that serves every network and size, a cheaper checker for the same "
    "inputs, covering inputs still uncertified) and pursue the one you expect to raise it most."
)
AIM_UNCOVERED_TEXT = (
    "{n} of the {total} networks still stand at 1.000 (no proof beats brute force there). Under a geometric mean "
    "a given factor counts the same on every network, and a network at 1.000 usually has the largest factor left."
)


# In a run with a seed check, when the proof the score rests on cannot be taken there.
NOT_READY_TEXT = (
    "The proof your score rests on (length {length:,}) cannot be taken to the seed check as it is: {why} Before "
    "the rounds end, submit it again with the checker and its soundness proof in modules apart from the instance."
)


def not_ready_line(records: list[dict], entries: list[dict], ready: dict | None) -> str:
    """For a run on one network with a seed check: a line for the aim when the best scored proof (the one
    that finishes the network cheapest) cannot be locked; empty otherwise."""
    if ready is None or len(entries) != 1:
        return ""
    entry, best = entries[0], None
    for r in records:
        if r.get("record_id") in ready and r.get("network") == entry["id"]:
            d = finishing_detail([{"length": r["length"], "certified": r["certified"], "n_inputs": entry["n_inputs"]}], entry, records)
            if d is not None and (best is None or d["total"] <= best[0]):
                best = (d["total"], r)
    if best is None or ready[best[1]["record_id"]] is None:
        return ""
    return NOT_READY_TEXT.format(length=best[1]["length"], why=ready[best[1]["record_id"]][:MAX_REASON].rstrip(".") + ".")


def lean_project(cfg: dict) -> Path:
    return Path(cfg["open_lane"]["lean_project"]).expanduser().resolve()


def _read(project: Path, rel: str) -> str:
    p = project / rel
    if not p.is_file():
        raise PromptError(f"the Lean project has no {rel}")
    return p.read_text().rstrip()


def lean_block(text: str) -> str:
    return "```lean\n" + text.rstrip() + "\n```"


def elide_repeats(text: str, keep_first: int = 2, keep_last: int = 1, least: int = 5) -> str:
    """Shorten a run of blank-line-separated paragraphs that differ only in their numbers (an instance split
    into one decided fact per input): the first and last few stay, with a comment saying how many are left
    out. The example's file itself is unchanged; this is only what the prompt shows."""
    paras = text.split("\n\n")
    shape = [re.sub(r"\d+", "#", q.strip()) for q in paras]
    out, i = [], 0
    while i < len(paras):
        j = i
        while j + 1 < len(paras) and shape[j + 1] == shape[i] and shape[i]:
            j += 1
        n = j - i + 1
        if n >= least:
            out += paras[i : i + keep_first]
            out.append(f"-- ... {n - keep_first - keep_last} more of the same form, one per input ...")
            out += paras[j - keep_last + 1 : j + 1]
        else:
            out += paras[i : j + 1]
        i = j + 1
    return "\n\n".join(out)


KNOWLEDGE_TEXT = {
    "minimal": (
        "This run is the minimal-knowledge condition: a checker may use every field of Interp except ginterval "
        "and gtokenIntervals, which belong to another experimental condition (a checker that reaches one, by "
        "name or otherwise, is refused scoring)."
    ),
    "maximum": (
        "This run is the maximum-knowledge condition: a checker may use every field of Interp, including two of "
        "the fixed rules lane's rules for networks beyond linear maps, supplied as operations.\n"
        "I.ginterval graph task box bounds the network over a box of inputs (per position, the tokens lo..hi) "
        "with interval arithmetic and answers true when the label, constant on the box, has a lower bound above "
        "every other output's upper bound; a box whose label is not constant answers false and costs nothing. "
        "It charges what cost-v3 charges an interval leaf: the lookup from the box, per position d for one token "
        "and 2 d (hi - lo + 1) otherwise (d the matrix's columns); every other operation twice the single rule's "
        "price; the final comparison. CostM.ginterval_correct: a true answer means every input of the box is "
        "answered correctly; CostM.ginterval_run_of splits an instance as gsingle_run_of does.\n"
        "I.gtokenIntervals graph task boxes runs the token_interval rule on a list of boxes and returns one "
        "verdict per box (false, at no cost, for a box whose label is not constant). Per box it keeps each "
        "position's rows apart per token for as long as the graph allows (exactly per input where at most one "
        "position varies) and answers true when the label's margin bound is positive. It charges what cost-v3 "
        "charges a proof's token_interval leaves: each leaf's own work to token_interval, and the rows that "
        "depend on their token alone (the lookups and their products with the weights) to tables, once for the "
        "whole list, so one call with all of a proof's boxes pays the least (each further call pays for its rows "
        "again). CostM.gtokenIntervals_correct: one verdict per box, and every input of a box answered true is "
        "answered correctly; certifiedCount_le_numCorrect bounds the count of the inputs of the boxes answered "
        "true when no two boxes share an input (pairwiseApart) and each lies in the space (fits). An instance "
        "splits into one decided fact per box (TokenLeafFacts, CostM.gtokenIntervals_run_of_facts); a box's "
        "fact is what `#eval (dweights weights).bind fun dw => gtokenLeaf graph dw task box` prints in a "
        "lean_check module. The worked example below calls it on three boxes of another network of the same "
        "architecture (TokensCost.lean has the operation and its price); state the checker's run for any "
        "environment, as the example's D_run does, or the kernel may evaluate every box at once."
    ),
}


SECOND_EXAMPLE_TEXT = (
    "A second worked example, a scored proof that is not brute force, is in the Lean project at {path} (its "
    "source is not pasted here: read it with read_file). It is a proof of another network, which need not be of "
    "this run's architecture. Take from it how a compact scored proof is put together (what the checker computes "
    "once, the cheap test per input, the lemmas its soundness proof is made of), not its argument."
)


# What template open_lane_v5 says about the sessions after the proof rounds (core.open_lane.stages), each only
# when the run has it.
AFTER_HEAD = {0: "This run is about one network.",
              1: "This run is about one network. One thing comes after its rounds, and\nit says what a good proof is:",
              2: "This run is about one network. Two things come after its rounds, and\nthey say what a good proof is:"}
AFTER_SEED_CHECK = """- The seed check. The checker of your best scored proof that can be
  locked, and its soundness proof, are locked and run unchanged on a
  second network: the same architecture and sizes, trained from another
  seed. You then write only the instance for that network, with a new
  certificate if the checker reads one. This measures how a fixed
  checker carries over to another set of weights. One that rests on this
  network's own numbers will certify little there. One that rests on how
  the network computes can still certify less: another seed may compute
  differently, or with smaller margins. Numbers that belong to one
  network reach a checker through the charged certificate, never
  through its code."""
AFTER_SCALING = """- The scaling question. {when} you are asked how your checker's cost
  grows with the sizes of the network, whether it grows more slowly than
  brute force, and to prove as much of the answer as you can. Nothing
  here asks for a proof at another size. But a checker that reads its
  sizes from the weights, not from numbers written into it, is one this
  question can be asked of."""
MODULES_RULE = """- Keep the checker and the instance in separate modules, from your
  first scored submission on. One or more modules hold `D`, `D_sound`
  and everything they use. A module of its own, which imports them,
  holds `D_instance`, the facts it is built from and the theorem proving
  `Target`. Name each constant after its module (`Candidate.Check.D` in
  `Candidate/Check.lean`). The checker's modules may import the protected
  module for `graph` and `task`.
"""
MODULES_WHY = {
    "seed_check": """  The seed check locks the first kind and you rewrite the second for the
  other network, where the protected module's name is replaced for you.
  A proof kept in one module cannot be taken there; the receipts below
  say of each scored proof whether it can.
""",
    "scaling": """  The scaling question is asked of the first kind, locked. A proof kept
  in one module cannot be asked it.
""",
}


def after_rounds_text(ol: dict) -> str:
    """Part 1's account of what follows the proof rounds: the seed check and the scaling question, as the
    run has them."""
    parts = []
    if ol.get("seed_check"):
        parts.append(AFTER_SEED_CHECK)
    if ol.get("scaling"):
        parts.append(AFTER_SCALING.format(when="Last," if parts else "Then"))
    return "\n".join([AFTER_HEAD[len(parts)]] + parts)


def modules_rule_text(ol: dict) -> str:
    """The advice to keep the checker's modules apart from the instance's: only a run with a session after
    its proof rounds needs it."""
    why = MODULES_WHY["seed_check"] if ol.get("seed_check") else MODULES_WHY["scaling"] if ol.get("scaling") else None
    return MODULES_RULE + why if why else ""


SPLIT_EXAMPLE_TEXT = (
    "  The Lean project's docs/COUNTED.md describes this under \"Split instances\", with a trap to avoid, and\n"
    "  {path} is a complete example of it (brute force on a small\n"
    "  network, one decided fact per input and a lemma that glues them); read_file reads both."
)
SPLIT_EXAMPLE_SAME = (
    "  The Lean project's docs/COUNTED.md describes this under \"Split instances\", with a trap to avoid, and the\n"
    "  worked example below is put together this way."
)


def split_example_text(ol: dict) -> str:
    """Where the agent can see an instance put together from small decided facts (open_lane.split_example):
    a file of the Lean project it may read, or the run's own worked example when that is the one."""
    rel = ol.get("split_example")
    if not rel:
        return ""
    return SPLIT_EXAMPLE_SAME if rel == ol.get("example") else SPLIT_EXAMPLE_TEXT.format(path=rel)


def second_example_text(rel: str | None) -> str:
    """Part 1's pointer to open_lane.second_example (prompt template open_lane_v4); empty without one."""
    return SECOND_EXAMPLE_TEXT.format(path=rel) if rel else ""


def extra_sources_text(project: Path, rels: list[str]) -> str:
    if not rels:
        return ""
    return "\n".join(f"From {rel}:\n{lean_block(_read(project, rel))}" for rel in rels)


def protected_interface() -> str:
    return lean_block(
        "namespace Protected.N_<network>_c<claimed>   -- for example Protected.N_max2_v64_s0_c4095\n"
        "def graph : Graph := ...            -- the network's graph, operation by operation\n"
        "def weights : Weights ℚ := ...      -- every weight, an exact dyadic rational\n"
        "def task : Task := ...              -- the task: input space and label function\n"
        "def cert : Cert := #[...]           -- the certificate of a scored submission (empty otherwise)\n"
        "def claimedCount : Nat := <claimed>\n"
        "def Target : Prop := claimedCount ≤ numCorrect graph weights task\n"
        "end Protected.N_<network>_c<claimed>"
    )


def tools_text() -> str:
    return "\n".join(f"- {name}: {spec['description']}" for name, spec in Session.TOOLS.items())


def networks_text(entries: list[dict]) -> str:
    lines = []
    for e in entries:
        real = e.get("real_correct")
        acc = f"{real:,} of {e['n_inputs']:,} ({100 * real / e['n_inputs']:.3f}%)" if real is not None else "unknown"
        lines.append(f"- {e['id']} ({e['setting']}): correct {acc}; E {e['E']:,}; B {e['B']:,}")
    return "\n".join(lines)


def static_values(cfg: dict, folder: ModelFolder, entries: list[dict]) -> dict:
    project = lean_project(cfg)
    settings = list(dict.fromkeys(e["setting"] for e in entries))
    size_settings = "; ".join(
        f"{s}: " + ", ".join(f"{k}={v}" for k, v in folder.sizes(s).items()) + f" ({folder.n_inputs(s):,} inputs)" for s in settings
    )
    ol = cfg["open_lane"]
    budgets = (f"{ol['compile_calls']} lean_check calls, {ol['python_calls']} run_python calls, "
               f"{ol['submissions']} submissions, {ol['worker_seconds']:,} s of wall clock")
    return {
        "MODEL_SOURCE": "\n```python\n" + folder.source().rstrip() + "\n```",
        "TASK_DESCRIPTION": folder.task.DESCRIPTION,
        "SIZE_SETTINGS": size_settings,
        "NETWORKS": networks_text(entries),
        "PROTECTED_INTERFACE": protected_interface(),
        "SPEC": lean_block(_read(project, "CompactCheck/Spec.lean")),
        "COUNTED": lean_block(_read(project, "CompactCheck/Counted.lean")),
        "COUNTED_OPS": lean_block(_read(project, "CompactCheck/CountedOps.lean")),
        "EXAMPLE": lean_block(elide_repeats(_read(project, ol["example"]))),
        "EXTRA_SOURCES": extra_sources_text(project, ol["extra_sources"]),
        "SECOND_EXAMPLE": second_example_text(ol.get("second_example")),
        "SPLIT_EXAMPLE": split_example_text(ol),
        "MODEL_NOTES": (ol.get("notes") or "").strip(),
        "AFTER_ROUNDS": after_rounds_text(ol),
        "MODULES_RULE": modules_rule_text(ol),
        "KNOWLEDGE": KNOWLEDGE_TEXT[ol.get("knowledge", "minimal")],
        "TOOLS": tools_text(),
        "BUDGETS": budgets,
        "METRIC": metric_text(cfg, folder, entries) + (
            f"\nThe budget grid, per size setting: {grid_text(entries, cfg['budget_ratio'])}." if cfg["metric"] == "Q_grid" else ""),
    }


# part 2 ------------------------------------------------------------------------------------
def _num(x: float) -> str:
    return f"{x:,.0f}" if float(x).is_integer() else f"{x:,.1f}"


def finishing_scoreboard(records: list[dict], entries: list[dict], budget_ratio) -> str:
    """The scoreboard of a run scored on cost of finishing: the one score, then per network the cheapest way
    to finish from the checked proofs (the proof used, and what is left to brute force). No other metric is
    shown: the agent is asked to raise this number and nothing else."""
    summary = summarize(records, entries, budget_ratio)
    if not summary:
        return "nothing checked yet"
    fr = frontier(records)
    by_id = {e["id"]: e for e in entries}
    n = sum(len(v["networks"]) for v in summary.values())
    if n == 1:
        lines = [f"Score: {run_cost_of_finishing(summary):.3f} (cost of finishing; brute force is 1.000)"]
    else:
        lines = [f"Score: {run_cost_of_finishing(summary):.3f} (cost of finishing, the geometric mean over the {n} "
                 f"networks of the run; brute force everywhere is 1.000)"]
    for setting, v in summary.items():
        if n != 1:
            lines.append(f"{setting}: geometric mean {v['cost_of_finishing_geomean']:.3f}")
        for nid in v["networks"]:
            e = by_id[nid]
            d = finishing_detail(fr.get(nid, []), e, records)
            if d is None:
                lines.append(f"  {nid}: 1.000. No proof yet: finishing is brute force, B = {e['B']:,}.")
            elif d["total"] >= e["B"]:
                lines.append(f"  {nid}: 1.000. No proof beats brute force yet (B = {e['B']:,}; one input by brute force "
                             f"costs {_num(d['per_input'])}).")
            elif d["uncovered"] == 0:
                lines.append(f"  {nid}: {d['ratio']:.3f}. Cheapest complete proof: length {d['length']:,}, certifying all "
                             f"{e['real_correct']:,} correct inputs (B = {e['B']:,}).")
            else:
                lines.append(f"  {nid}: {d['ratio']:.3f}. Cheapest way to finish: {_num(d['total'])} = a proof of length "
                             f"{d['length']:,} certifying {d['certified']:,} of the {e['real_correct']:,} correct inputs, plus "
                             f"{d['uncovered']:,} inputs by brute force at {_num(d['per_input'])} each (B = {e['B']:,}).")
    return "\n".join(lines)


def scoreboard(records: list[dict], entries: list[dict], budget_ratio, metric: str | None = None) -> str:
    if metric == "cost_of_finishing":
        return finishing_scoreboard(records, entries, budget_ratio)
    lines = []
    for setting, s in summarize(records, entries, budget_ratio).items():
        lines.append(f"{setting}: Q_above mean {s['Q_above_mean']:.4f}, worst {s['Q_above_worst']:.4f}; "
                     f"Q_exact mean {s['Q_exact_mean']:.4f}; Q median {s['Q_median']:.4f}; "
                     f"cost of finishing median {s['cost_of_finishing_median']:.2f}")
        for nid, m in s["networks"].items():
            full = f"{m['shortest_full']:,} (B/{m['B'] / m['shortest_full']:.1f})" if m["shortest_full"] else "none"
            line = m["brute_force_line"]
            lines.append(f"  {nid}: Q_above {m['Q_above']:.4f}, Q_exact {m['Q_exact']:.4f}, Q {m['Q']:.4f}; best certified accuracy "
                         f"{100 * m['best_accuracy']:.3f}% of {100 * (m['real_accuracy'] or 0):.3f}%; shortest full-accuracy proof "
                         f"{full}; {m['points']} frontier proofs, {m['points_above_line']} above the brute-force line "
                         f"(k inputs for {line['c']:g} k + {line['E']:g}, up to {line['coverage']})")
    return "\n".join(lines) if lines else "nothing checked yet"


def lock_readiness(run: RunDir, records: list[dict]) -> dict:
    """For a run with a seed check: per scored open-lane proof, None if its checker can be locked and taken
    to the second network, else the reason it cannot (core.open_lane.lock)."""
    from .lock import lockable

    out = {}
    for r in records:
        if r.get("lane") == "open" and r.get("status") == "ok" and not r.get("stage"):
            d = run.round_path(r["round"]) / f"attempt_{r['attempt']}" / "open_lane" / "submissions" / f"{int(r.get('submission') or 0):03d}"
            out[r["record_id"]] = lockable(d)
    return out


def receipts_text(records: list[dict], entries: list[dict] | None = None, metric: str | None = None,
                  ready: dict | None = None) -> str:
    """The agent's submissions so far, one line each. A scored proof's line says what it is worth under the
    run's metric: under cost of finishing, what finishing from it costs against brute force; otherwise,
    whether it lies above the brute-force line. In a run with a seed check (`ready`, lock_readiness) it
    also says whether the proof can be taken there."""
    lines = []
    finishing = metric == "cost_of_finishing"
    by_id = {e["id"]: e for e in entries or []}
    lines_by_net = {} if finishing else {e["id"]: brute_force_line(e, records) for e in entries or []}
    for r in records:
        if r.get("lane") != "open" or r.get("status") == "no_submission":
            continue
        head = f"- round {r['round']} submission {r.get('submission')}: {r.get('network')}, claimed {r.get('claimed_count')}: {r['status']}"
        if r["status"] == "ok":
            line = lines_by_net.get(r.get("network"))
            above = ""
            e = by_id.get(r.get("network"))
            if finishing and e is not None:
                d = finishing_detail([{"length": r["length"], "certified": r["certified"], "n_inputs": e["n_inputs"]}], e, records)
                if d is not None:
                    above = (f"; finishing from it costs {_num(d['total'])}, against {e['B']:,} for brute force (a ratio of {d['ratio']:.3f})"
                             if d["total"] < e["B"] else
                             f"; finishing from it costs {_num(d['total'])}, no less than brute force ({e['B']:,}): it adds nothing to the score")
            elif line is not None:
                k = line_certified(line, r["length"])
                above = (f"; above the brute-force line (which certifies {k} at this length)" if r["certified"] > k
                         else f"; not above the brute-force line (which certifies {k} at this length): scores nothing")
            if ready is not None and r.get("record_id") in ready:
                why = ready[r["record_id"]]
                above += "; ready for the seed check" if why is None else f"; not ready for the seed check: {why[:MAX_REASON]}"
            lines.append(f"{head}, certified {r['certified']}, length {r['length']:,} (bill {r['length_by_rule']['bill']:,}){above}")
        elif r["status"] == "lemma":
            lines.append(f"{head} (auxiliary lemma accepted): {(r.get('statement') or '')[:MAX_REASON]}")
        elif r["status"] == "verified":
            lines.append(f"{head}, certified {r['certified']}; {(r.get('error') or '')[:MAX_REASON]}")
        else:
            lines.append(f"{head}: {(r.get('error') or '')[:MAX_REASON]}")
    return "\n".join(lines) if lines else "none yet"


def accepted_sources(run: RunDir, records: list[dict], n: int, max_chars: int) -> str:
    accepted = [r for r in records if r.get("lane") == "open" and r["status"] in ("ok", "verified", "lemma")]
    accepted.sort(key=lambda r: (r["round"], r["attempt"], r.get("submission") or 0), reverse=True)
    parts, used = [], 0
    for r in accepted[:n]:
        d = run.round_path(r["round"]) / f"attempt_{r['attempt']}" / "open_lane" / "submissions" / f"{r.get('submission', 0):03d}"
        for p in sorted(d.glob("Candidate/**/*.lean")):
            text = p.read_text()
            if used + len(text) > max_chars:
                text = text[: max(0, max_chars - used)] + "\n-- (cut)"
            used += len(text)
            parts.append(f"round {r['round']}, {r.get('network')}, {r['status']}, {p.relative_to(d)}:\n{lean_block(text)}")
            if used >= max_chars:
                break
        if used >= max_chars:
            break
    return "\n\n".join(parts) if parts else "none yet"


WORKSPACE_HEAD = (
    "These modules, from the submissions the service accepted in earlier rounds (the latest accepted version of "
    "each), are in your workspace and were compiled there before this session began. Import them (`import "
    "Candidate.<Name>`) rather than pasting their code again; read one with read_file (path Candidate/<Name>.lean); "
    "submit_candidate adds the workspace modules your submitted modules import, and the service checks them "
    "afresh with every submission. Saving a module of the same path with lean_check replaces it."
)


def workspace_text(carried) -> str:
    """Part 2's account of the modules carried into this round's workspace (core.open_lane.session)."""
    if not carried or not isinstance(carried, list):
        return "none yet"
    lines = [WORKSPACE_HEAD]
    for m in carried:
        if m.get("kind") == "auxiliary":
            what = f"accepted lemma {m.get('theorem')}"
        elif m.get("scored"):
            what = f"scored proof ({m.get('certified')} inputs, length {m.get('length'):,})" if m.get("length") else "scored proof"
        else:
            what = f"verified proof ({m.get('certified')} inputs)"
        state = "compiled" if m.get("compiled") else "did not compile here: " + " | ".join(m.get("errors") or [])[:MAX_REASON]
        lines.append(f"- {m['path']} ({m.get('lines')} lines; round {m['round']}, submission {m['submission']}, {what}): {state}")
    return "\n".join(lines)


def latest_notes(run: RunDir, k: int, max_chars: int) -> str:
    for kk in range(k - 1, 0, -1):
        j = 0
        texts = []
        while (run.round_path(kk) / f"attempt_{j}").is_dir():
            t = run.read(kk, f"attempt_{j}/response.md")
            if t:
                m = re.search(r"NOTES:(.*)\Z", t, re.S)
                texts.append((m.group(1) if m else t).strip())
            j += 1
        if texts:
            out = "\n".join(texts)
            return out[:max_chars] + ("\n(cut)" if len(out) > max_chars else "")
    return "none yet"


def stalled(records: list[dict], k: int, n: int) -> bool:
    """No accepted open-lane submission in agent rounds k-n to k-1 (and there were that many rounds)."""
    if k - 1 < n:
        return False
    recent = [r for r in records if r.get("lane") == "open" and k - n <= r["round"] <= k - 1]
    return not any(r["status"] in ("ok", "verified", "lemma") for r in recent)


def aim(records: list[dict], entries: list[dict], cfg: dict, k: int) -> str:
    summary = summarize(records, entries, cfg.get("budget_ratio"))
    if cfg["metric"] == "cost_of_finishing":
        ratios = [finishing_ratio(m["cost_of_finishing"]) for v in summary.values() for m in v["networks"].values()]
        if len(ratios) == 1:  # one network: no talk of a mean, or of a checker for several networks
            text = AIM_TEXT.format(scores=f"cost_of_finishing: {run_cost_of_finishing(summary):.3f}")
        else:
            text = AIM_FINISHING_TEXT.format(scores=f"cost_of_finishing: {run_cost_of_finishing(summary):.3f}, the geometric mean "
                                                    f"over the run's {len(ratios)} networks")
        at_one = sum(1 for x in ratios if x <= 1.0)
        if at_one and len(ratios) > 1:
            text += "\n" + AIM_UNCOVERED_TEXT.format(n=at_one, total=len(ratios))
    else:
        text = AIM_TEXT.format(scores=f"{cfg['metric']}: " + metric_scores(summary, cfg["metric"]))
    if stalled(records, k, cfg["open_lane"]["stall_rounds"]):
        text += "\n" + STALL_TEXT.format(n=cfg["open_lane"]["stall_rounds"])
    return text


def build_open_lane_prompt(cfg: dict, folder: ModelFolder, entries: list[dict], run: RunDir, k: int) -> Prompt:
    part1_t, part2_t = load_template(cfg["prompt_template"])
    terms = forbidden(folder)
    part1 = fill(part1_t, static_values(cfg, folder, entries))
    leaked = [t for t in terms if t in part1]
    if leaked:
        raise PromptError(f"the model folder puts forbidden strings into the prompt: {leaked}")
    records = [r for r in run.read_archive() if r["round"] < k]
    budget = cfg["prompt_budget_tokens"] * CHARS_PER_TOKEN
    lemma_chars, notes_chars = MAX_LEMMA_CHARS, MAX_NOTES_CHARS
    trimmed = []
    # the round's first session, made now so that the prompt can say what was carried into its workspace and
    # whether it compiled; the backend opens the same session (Session.create returns an existing one)
    session = Session.create(run.round_path(k) / "attempt_0" / "open_lane", cfg, cfg["model"], entries, run.path)
    ready = lock_readiness(run, records) if cfg["open_lane"].get("seed_check") else None
    nudge = not_ready_line(records, entries, ready)
    values = {
        "SCOREBOARD": scoreboard(records, entries, cfg.get("budget_ratio"), cfg["metric"]),
        "RECEIPTS": receipts_text(records, entries, cfg["metric"], ready),
        "AIM": aim(records, entries, cfg, k) + ("\n" + nudge if nudge else ""),
        "WORKSPACE": workspace_text(session.state.get("carried")),
    }
    while True:
        values["LEMMAS"] = accepted_sources(run, records, cfg["shown_top_recipes"], lemma_chars)
        values["NOTES"] = latest_notes(run, k, notes_chars)
        part2 = fill(part2_t, values)
        if len(part1) + len(part2) <= budget or (lemma_chars == 0 and notes_chars == 0):
            break
        if lemma_chars > 0:
            lemma_chars = 0
            trimmed.append("lemmas")
        else:
            notes_chars = 0
            trimmed.append("notes")
    stats = {"chars": len(part1) + len(part2), "tokens_estimate": (len(part1) + len(part2)) // CHARS_PER_TOKEN,
             "trimmed": trimmed, "template": cfg["prompt_template"], "lane": "open", "stalled": stalled(records, k, cfg["open_lane"]["stall_rounds"])}
    return Prompt(part1, part2, stats)
