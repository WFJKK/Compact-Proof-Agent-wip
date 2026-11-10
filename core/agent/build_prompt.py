"""Build the agent's prompt for a round from the template, the model folder and the archive.

Part 1, the same every round, comes from the model folder and the run config
alone: the module's source verbatim, the task's description and grouping, the
size settings, the recipe template with the helpers, the rules, the cost model
and the metric. Part 2 is rebuilt each round from the archive: the frontier per
size setting, the best recipes with their code, the agent's last attempts with
compact diagnostics, and its latest notes.

Information hygiene: the prompt never contains a string from the model's
hygiene list or the id of a held-out network. Part 1 holding one is an error in
the model folder; in Part 2 any that appears is replaced by "[removed]" and
counted. A test enforces both.
"""

from __future__ import annotations

import inspect
import json
from collections import Counter
import re
import statistics
from dataclasses import dataclass, field
from pathlib import Path

from ..archive import RunDir
from ..check import cost
from ..check.rules import describe
from ..diagnostics import at_label, knob_lines, render_attempt, rule_order, share
from ..model_folder import ModelFolder
from ..scoring import brute_force_line, budget_grid, default_budget_ratio, q_above, q_exact, q_grid, q_score, summarize
from ..zoo import read_manifest

TEMPLATES = Path(__file__).with_name("prompts")
RECIPE_TEMPLATE = Path(__file__).with_name("recipe_template.py")
HELPERS = Path(__file__).resolve().parent.parent / "helpers.py"
PART1_MARKER = "PART 1: SENT EVERY ROUND"
PART2_MARKER = "PART 2: REBUILT EACH ROUND"
CHARS_PER_TOKEN = 4  # a rough estimate for the size budget and the logs
REMOVED = "[removed]"
DIAGNOSTIC_LINES_WHEN_TRIMMED = 12
NOTES_CHARS_WHEN_TRIMMED = 4000


class PromptError(ValueError):
    pass


@dataclass
class Prompt:
    part1: str
    part2: str
    stats: dict = field(default_factory=dict)

    @property
    def text(self) -> str:
        return self.part1.rstrip() + "\n\n" + self.part2.strip() + "\n"

    def as_json(self) -> dict:
        return {"part1": self.part1, "part2": self.part2, "stats": self.stats}

    @classmethod
    def from_json(cls, d: dict) -> "Prompt":
        return cls(d["part1"], d["part2"], d.get("stats", {}))


# the template --------------------------------------------------------------------------
def load_template(name: str) -> tuple[str, str]:
    path = TEMPLATES / f"{name}.md"
    if not path.is_file():
        raise PromptError(f"no prompt template {name!r} in {TEMPLATES}")
    text = path.read_text()
    if PART2_MARKER not in text:
        raise PromptError(f"template {name} has no {PART2_MARKER!r} line")
    part1, part2 = text.split(PART2_MARKER, 1)
    return part1.replace(PART1_MARKER, "", 1).strip() + "\n", part2.strip() + "\n"


def placeholders(text: str) -> set[str]:
    return set(re.findall(r"\{([A-Za-z_]+)\}", text))


def fill(text: str, values: dict) -> str:
    """Replace each {NAME} once; braces inside the values are left alone."""
    missing = placeholders(text) - set(values)
    if missing:
        raise PromptError(f"no value for {sorted(missing)}")
    return re.sub(r"\{([A-Za-z_]+)\}", lambda m: str(values[m.group(1)]), text)


def code_block(source: str) -> str:
    return "```python\n" + source.rstrip() + "\n```"


# part 1 ------------------------------------------------------------------------------------
KNOB_TEXT = (
    "knob is a number between 0 and 1 that we vary. Use it to trade proof\n"
    "length against certified accuracy (for example split depth or precision),\n"
    "so that one recipe traces out a curve."
)
BUDGET_TEXT = (
    "We run your recipe once per budget from a fixed grid: per size setting\n"
    "B/{ratio:g}, B/{ratio2:g}, and so on down to E ({grid}). info[\"budget\"] is the\n"
    "budget in checker operations, with info[\"E\"] and info[\"B\"] next to it;\n"
    "knob is the budget's position on the log scale from E (0) to B (1). Return\n"
    "the proof that certifies the most inputs within the budget. A proof over\n"
    "budget counts only at the larger budgets it fits, so predict its length\n"
    "(the length by rule in the diagnostics shows what each rule costs). Where\n"
    "a proof sits between grid budgets earns nothing: only the accuracy reached\n"
    "at each budget counts."
)


def grid_text(entries: list[dict], ratio: float) -> str:
    parts = []
    for s in dict.fromkeys(e["setting"] for e in entries):
        e = _first(entries, s)
        grid = budget_grid(e["E"], e["B"], ratio)
        parts.append(f"{s}: {len(grid)} budgets, {grid[0]:,} down to {grid[-1]:,}" if grid else f"{s}: no budget between E and B")
    return "; ".join(parts)


def knob_text(cfg: dict, entries: list[dict]) -> str:
    if cfg["metric"] == "Q_grid":
        ratio = cfg["budget_ratio"]
        return BUDGET_TEXT.format(ratio=ratio, ratio2=ratio * ratio, grid=grid_text(entries, ratio))
    return KNOB_TEXT


def metric_text(cfg: dict, folder: ModelFolder, entries: list[dict]) -> str:
    settings = list(dict.fromkeys(e["setting"] for e in entries))
    eb = "; ".join(f"{s}: E {_first(entries, s)['E']:,}, B {_first(entries, s)['B']:,}" for s in settings)
    if cfg["metric"] == "Q_grid":
        head = (
            "Your score is Q_grid, per size setting the median over its networks (the worst network is reported too). "
            "For one network, take each budget of the fixed grid in turn and the best certified accuracy among the "
            "checked proofs (yours and earlier ones) of length at most that budget; Q_grid is the mean of these "
            "accuracies over the grid, between 0 and 1. Brute force alone scores 0; a proof certifying everything "
            "within the smallest budget would score 1. More accuracy within a budget raises it; a proof that is "
            "shorter than its budget but no more accurate does not."
        )
    elif cfg["metric"] == "Q_exact":
        head = (
            "Your score is Q_exact, per size setting the mean over its networks (the worst network is reported too). "
            "For one network, a(b) is the best certified accuracy among the checked proofs (yours and earlier ones) of "
            "length at most b; Q_exact is the average of a(b) over budgets b drawn log-uniformly between "
            "max(E, B/1000) and B, computed exactly from the proofs' lengths, between 0 and 1. Brute force alone "
            "scores 0. Shorter proofs of the same accuracy raise it, and so does more accuracy at the same length: "
            "any shorter proof counts, not only one that crosses a budget. Cost of finishing breaks ties and is "
            "reported separately."
        )
    elif cfg["metric"] == "Q_above":
        head = (
            "Your score is Q_above, per size setting the mean over its networks (the worst network is reported too). "
            "For one network, a(L) is the best certified accuracy among the checked proofs (yours and earlier ones) of "
            "length at most L, and b(L) is what brute force certifies at length L: checking k inputs one by one costs "
            "c per input plus E (c is the single rule's charge, read from round 0's brute-force proof), so "
            "b(L) = min(coverage, floor((L - E) / c)) / n, with coverage the inputs brute force certifies. Q_above is "
            "the area of max(a(L) - b(L), 0) over log L between max(E, B/1000) and B, divided by the area of the room "
            "above the line there, between 0 and 1. A proof earns credit only where it certifies more inputs than "
            "brute force of the same length: brute force on any subset of the inputs scores exactly 0, a proof at or "
            "below the line scores 0 and costs nothing, and a proof certifying every correct input at the smallest "
            "length would score 1. Shorter proofs of the same accuracy raise it, and so does more accuracy at the same "
            "length, in both cases only above the line. Cost of finishing breaks ties and is reported separately."
        )
    elif cfg["metric"] == "cost_of_finishing":
        head = (
            "Your score is the cost of finishing, per size setting the median over its networks (the worst network "
            "is reported too). For one network, take a proof's length plus, for every input it classifies correctly "
            "but leaves uncertified, what certifying that input alone costs (the single rule's charge, read from "
            "round 0's brute-force proof; B divided by the number of inputs when there is none); the score is B "
            "divided by the smallest such total over your proofs. Higher is better; brute force scores 1."
        )
    else:
        head = (
            "Your score is Q, per size setting the median over its networks (the worst network is reported too). "
            "For one network, a(b) is the best certified accuracy among your checked proofs of length at most b; Q is "
            "the average of a(b) over lengths b from E to B on a log scale, between 0 and 1. A proof as short as "
            "reading the weights that certified every input would score 1; brute force alone scores 0. Shorter proofs "
            "of the same accuracy raise Q, and so does more accuracy at the same length; every knob value's proof counts."
        )
    return f"{head}\nE (reading the weights) and B (brute force) per size setting: {eb}."


def _first(entries, setting):
    return next(e for e in entries if e["setting"] == setting)


def static_values(cfg: dict, folder: ModelFolder, entries: list[dict]) -> dict:
    settings = list(dict.fromkeys(e["setting"] for e in entries))
    size_settings = "; ".join(
        f"{s}: " + ", ".join(f"{k}={v}" for k, v in folder.sizes(s).items()) + f" ({folder.n_inputs(s):,} inputs)"
        for s in settings
    )
    example = {"sizes": folder.sizes(settings[0]), "input_space": folder.input_space(settings[0])}
    shapes = ", ".join(f"{k} {tuple(v.shape)}" for k, v in folder.build(settings[0]).state_dict().items())
    rules = describe(tuple(cfg["rule_set"]))
    own = getattr(folder.rules, "RULES", None) if folder.rules is not None else None
    if isinstance(own, dict):
        rules += "\n" + "\n".join(f"- {k}: {v}" for k, v in own.items())
    template = code_block(RECIPE_TEMPLATE.read_text())
    template += "\n\nThe helpers module (helpers.py), importable in a recipe:\n" + code_block(HELPERS.read_text())
    return {
        "MODEL_SOURCE": "\n" + code_block(folder.source()),
        "TASK_DESCRIPTION": folder.task.DESCRIPTION,
        "SIZE_SETTINGS": size_settings,
        "INFO": f"for example, at {settings[0]}, {json.dumps(example)}; there the weights are {shapes}",
        "TEMPLATE": "\n" + template,
        "RULES_SPEC": "\n" + rules,
        "COST_MODEL": "\n" + inspect.getdoc(cost).strip(),
        "METRIC": metric_text(cfg, folder, entries),
        "KNOB": knob_text(cfg, entries),
        "TIME_LIMIT": f"{cfg['time_limit_s']:g} seconds and {cfg['memory_limit_mb']:g} MB of memory",
        "GROUPING": folder.task.GROUPING,
    }


# part 2 ------------------------------------------------------------------------------------
def attempts(records: list[dict]) -> dict[tuple[int, int], list[dict]]:
    out: dict = {}
    for r in records:
        out.setdefault((r["round"], r["attempt"]), []).append(r)
    return dict(sorted(out.items()))


def label(run: RunDir, key: tuple[int, int], per_round: int) -> str:
    k, j = key
    if k == 0:
        source = (run.read(0, f"attempt_{j}/response_meta.json") or {}).get("source", f"{j}")
        return f"baseline {Path(source).stem}"
    return f"round {k}" + (f" attempt {j}" if per_round > 1 else "")


def attempt_score(rs: list[dict], entries: list[dict], metric: str = "Q", budget_ratio: float | None = None) -> float:
    """The attempt's own score (Q, or Q_grid when that is the metric): per network from its proofs alone,
    median per size setting, mean over settings."""
    by_setting: dict = {}
    for e in entries:
        pts = sorted(
            (r for r in rs if r["network"] == e["id"] and r["status"] == "ok"),
            key=lambda r: (r["length"], -r["certified"]),
        )
        frontier, best = [], -1
        for r in pts:
            if r["certified"] > best:
                frontier.append({"length": r["length"], "certified": r["certified"], "n_inputs": r["n_inputs"]})
                best = r["certified"]
        score = (q_grid(frontier, e["E"], e["B"], budget_ratio) if metric == "Q_grid"
                 else q_exact(frontier, e["E"], e["B"]) if metric == "Q_exact"
                 else q_above(frontier, e, brute_force_line(e, rs)) if metric == "Q_above"
                 else q_score(frontier, e["E"], e["B"]))
        by_setting.setdefault(e["setting"], []).append(score)
    return statistics.mean(statistics.median(v) for v in by_setting.values()) if by_setting else 0.0


def render_frontier(records: list[dict], entries: list[dict], run: RunDir, per_round: int, metric: str, budget_ratio: float | None = None) -> str:
    summary = summarize(records, entries, budget_ratio)
    lines = []
    for setting in dict.fromkeys(e["setting"] for e in entries):
        nets = [e for e in entries if e["setting"] == setting]
        ids = {e["id"] for e in nets}
        s = summary[setting]
        real = statistics.median(e["real_accuracy"] for e in nets)
        if metric == "cost_of_finishing":
            score = f"cost of finishing median {s['cost_of_finishing_median']:.2f}, worst {s['cost_of_finishing_worst']:.2f}"
        elif metric == "Q_grid":
            score = f"Q_grid median {s['Q_grid_median']:.4f}, worst {s['Q_grid_worst']:.4f}"
        elif metric == "Q_exact":
            score = f"Q_exact mean {s['Q_exact_mean']:.4f}, worst {s['Q_exact_worst']:.4f}; cost of finishing median {s['cost_of_finishing_median']:.2f}"
        elif metric == "Q_above":
            score = f"Q_above mean {s['Q_above_mean']:.4f}, worst {s['Q_above_worst']:.4f}; cost of finishing median {s['cost_of_finishing_median']:.2f}"
        else:
            score = f"Q median {s['Q_median']:.4f}, worst {s['Q_worst']:.4f}"
        lines.append(f"{setting} ({len(nets)} networks; real accuracy median {100 * real:.3f}%): {score}")
        if metric == "Q_grid":
            lines += grid_lines(records, nets, run, per_round, budget_ratio)
            continue
        points = []
        groups: dict = {}
        for r in records:
            if r["status"] == "ok" and r["network"] in ids:
                groups.setdefault((r["round"], r["attempt"], r["knob"]), []).append(r)
        for (k, j, knob), rs in groups.items():
            if {r["network"] for r in rs} != ids:
                continue  # only recipes checked on every network of the setting
            points.append(
                (
                    statistics.median(r["length"] for r in rs),
                    statistics.median(r["certified"] / r["n_inputs"] for r in rs),
                    (k, j),
                    knob,
                )
            )
        points.sort(key=lambda p: (p[0], -p[1]))
        best = -1.0
        B = nets[0]["B"]
        for length, acc, key, knob in points:
            if acc > best:
                lines.append(
                    f"  length {int(length):,} (B/{B / length:.1f}): certified {100 * acc:.3f}% (median), "
                    f"{label(run, key, per_round)}, knob {knob:g}"
                )
                best = acc
        if best < 0:
            lines.append("  no recipe has been checked on every network yet")
    return "\n".join(lines)


METRIC_NAMES = {"Q": "Q", "Q_grid": "Q_grid", "Q_exact": "Q_exact", "Q_above": "Q_above", "cost_of_finishing": "cost of finishing"}
AIM_TEXT = (
    "Raise your score, {name}. It stands at: {scores}.\n"
    "Before writing the recipe, consider several approaches that could raise it: a\n"
    "better account of how the network computes, a different way of splitting the\n"
    "inputs, cheaper checks of the same pieces, or covering inputs that are still\n"
    "uncertified. Estimate what each would add to {name}, using the scoreboard, the\n"
    "diagnostics and your notes, and write the one you expect to raise it most. Say\n"
    "in WHY IT HELPS which approaches you weighed and why you chose this one."
)


def metric_scores(summary: dict, metric: str) -> str:
    """Per size setting, the metric as the run scores it (the median over networks, or for Q_exact the mean:
    run_config.METRIC_KEYS) and its worst network."""
    from ..run_config import METRIC_KEYS

    centre = METRIC_KEYS[metric]
    label = "mean" if centre.endswith("_mean") else "median"
    fmt = "{:.2f}" if metric == "cost_of_finishing" else "{:.4f}"
    return "; ".join(f"{setting} {label} {fmt.format(s[centre])}, worst {fmt.format(s[metric + '_worst'])}"
                     for setting, s in summary.items())


def aim_text(records: list[dict], entries: list[dict], metric: str, budget_ratio: float | None = None) -> str:
    """The explicit aim (template v3): the score as it stands, per size setting, and the ask to raise it."""
    summary = summarize(records, entries, budget_ratio)
    return AIM_TEXT.format(name=METRIC_NAMES[metric], scores=metric_scores(summary, metric))


def grid_lines(records: list[dict], nets: list[dict], run: RunDir, per_round: int, budget_ratio: float | None) -> list[str]:
    """Per fixed budget, smallest first: the median over networks of the best certified accuracy within the budget
    (which is what Q_grid averages), and the recipe that holds it on most networks."""
    ratio = budget_ratio if budget_ratio is not None else default_budget_ratio()
    B = nets[0]["B"]
    grid = budget_grid(nets[0]["E"], B, ratio)
    ok = [r for r in records if r["status"] == "ok" and r["certified"] > 0]
    lines = []
    for i, b in reversed(list(enumerate(grid))):
        accs, holders = [], Counter()
        for e in nets:
            mine = [r for r in ok if r["network"] == e["id"] and r["length"] <= b]
            if mine:
                best = max(mine, key=lambda r: (r["certified"], -r["length"]))
                accs.append(best["certified"] / best["n_inputs"])
                holders[(best["round"], best["attempt"])] += 1
            else:
                accs.append(0.0)
        head = f"  budget B/{ratio ** (i + 1):g} ({b:,}):"
        if holders:
            key, n = holders.most_common(1)[0]
            lines.append(f"{head} certified {100 * statistics.median(accs):.3f}% (median), {label(run, key, per_round)} on {n} of {len(nets)} networks")
        else:
            lines.append(f"{head} nothing certified yet")
    return lines


def _parsed(run: RunDir, key: tuple[int, int]) -> dict:
    return run.read(key[0], f"attempt_{key[1]}/parsed.json") or {}


def result_lines(rs: list[dict]) -> str:
    """The knob curve per size setting, a line or two each."""
    if len(rs) == 1 and rs[0]["status"] == "parse":
        return f"  status parse: {rs[0]['error']}"
    out = []
    for setting in dict.fromkeys(r["setting"] for r in rs):
        ok = [r for r in rs if r["setting"] == setting and r["status"] == "ok"]
        if ok:
            lines, best = knob_lines(ok)
            out.append(f"  {setting}:")
            out += ["  " + ln for ln in lines]
            kr = sorted((r for r in ok if r["knob"] == best), key=lambda r: r["length"])
            mid = kr[len(kr) // 2]
            parts = [(c, mid["length_by_rule"].get(c, 0)) for c in rule_order() if mid["length_by_rule"].get(c)]
            out.append(
                f"    length by rule at {at_label(mid)} ({mid['network']}): "
                + ", ".join(f"{c} {share(v, mid['length'])}" for c, v in parts)
            )
        else:
            statuses = sorted({r["status"] for r in rs if r["setting"] == setting})
            out.append(f"  {setting}: {', '.join(statuses)}")
    return "\n".join(out)


def render_top(records, entries, run: RunDir, n: int, per_round: int, with_code: int, metric: str = "Q", budget_ratio: float | None = None) -> str:
    scored = [
        (attempt_score(rs, entries, metric, budget_ratio), key, rs)
        for key, rs in attempts(records).items()
        if any(r["status"] == "ok" for r in rs)
    ]
    scored.sort(key=lambda t: (-t[0], t[1]))
    if not scored:
        return "None yet."
    blocks = []
    for i, (score, key, rs) in enumerate(scored[:n]):
        p = _parsed(run, key)
        block = [
            f"{i + 1}. {label(run, key, per_round)} (its own {'Q_grid' if metric == 'Q_grid' else 'Q'}, mean over size settings: {score:.4f})",
            f"CLAIM: {p.get('claim', '')}",
            f"PREDICTION: {p.get('prediction', '')}",
            f"KNOB: {p.get('knob', '')}",
            "RESULT:",
            result_lines(rs),
        ]
        if i < with_code:
            block += ["CODE:", code_block(run.read(key[0], f"attempt_{key[1]}/recipe.py") or "")]
        else:
            block.append("(code left out to keep the prompt short)")
        blocks.append("\n".join(block))
    return "\n\n".join(blocks)


def render_last(records, entries, run: RunDir, m: int, per_round: int, group_label: str, max_lines: int | None) -> str:
    mine = [(key, rs) for key, rs in attempts(records).items() if key[0] > 0]
    if not mine:
        return "None yet: this is your first round."
    blocks = []
    for key, rs in mine[-m:]:
        p = _parsed(run, key)
        if "error" in p:
            blocks.append(f"{label(run, key, per_round)}: your response could not be used: {p['error']}")
            continue
        diag = render_attempt(rs, group_label)
        if len({r["network"] for r in rs}) < len(entries):
            diag += (
                "\n(screened: it certified nothing on the first network of each size setting, "
                "so it was not run on the others)"
            )
        if max_lines is not None and len(diag.splitlines()) > max_lines:
            diag = "\n".join(diag.splitlines()[:max_lines]) + "\n(diagnostics cut to keep the prompt short)"
        blocks.append(
            "\n".join(
                [
                    f"{label(run, key, per_round)}:",
                    f"CLAIM: {p.get('claim', '')}",
                    f"PREDICTION: {p.get('prediction', '')}",
                    f"KNOB: {p.get('knob', '')}",
                    "RESULT AND DIAGNOSTICS:",
                    diag,
                ]
            )
        )
    return "\n\n".join(blocks)


def latest_notes(records, run: RunDir, max_chars: int | None) -> str:
    for key in reversed(list(attempts(records))):
        if key[0] == 0:
            continue
        notes = _parsed(run, key).get("notes")
        if notes:
            return notes if max_chars is None or len(notes) <= max_chars else notes[:max_chars] + " [cut]"
    return "None yet."


# the whole prompt ----------------------------------------------------------------------------
def forbidden(folder: ModelFolder) -> list[str]:
    terms = [t for t in folder.hygiene_terms() if t]
    terms += [e["id"] for e in read_manifest(folder)["networks"] if e["split"] == "held_out"]
    return sorted(set(terms), key=len, reverse=True)


def scrub(text: str, terms: list[str]) -> tuple[str, int]:
    count = 0
    for t in terms:
        n = text.count(t)
        if n:
            count += n
            text = text.replace(t, REMOVED)
    return text, count


def build_prompt(cfg: dict, folder: ModelFolder, entries: list[dict], run: RunDir, k: int) -> Prompt:
    """The prompt for agent round k (k >= 1), from the archive as it stands."""
    part1_t, part2_t = load_template(cfg["prompt_template"])
    terms = forbidden(folder)
    part1 = fill(part1_t, static_values(cfg, folder, entries))
    leaked = [t for t in terms if t in part1]
    if leaked:
        raise PromptError(f"the model folder puts forbidden strings into the prompt: {leaked}")

    records = [r for r in run.read_archive() if r["round"] < k]
    per_round = cfg["recipes_per_round"]
    budget = cfg["prompt_budget_tokens"] * CHARS_PER_TOKEN
    n_top = cfg["shown_top_recipes"]
    trimmed = []
    with_code, max_lines, notes_chars = n_top, None, None
    while True:
        values = {
            "k": k,
            "K": cfg["rounds_max"],
            "m": cfg["shown_last_attempts"],
            "GROUPING": folder.task.GROUPING,
            "FRONTIER": render_frontier(records, entries, run, per_round, cfg["metric"], cfg.get("budget_ratio")),
            "TOP_RECIPES": render_top(records, entries, run, n_top, per_round, with_code, cfg["metric"], cfg.get("budget_ratio")),
            "DIAGNOSTICS": render_last(
                records, entries, run, cfg["shown_last_attempts"], per_round, folder.group_label(), max_lines
            ),
            "NOTES": latest_notes(records, run, notes_chars),
            "AIM": aim_text(records, entries, cfg["metric"], cfg.get("budget_ratio")),
        }
        part2, removed = scrub(fill(part2_t, values), terms)
        size = len(part1) + len(part2)
        if size <= budget:
            break
        if with_code > 0:
            with_code -= 1
            trimmed.append(f"code of best recipe {with_code + 1}")
        elif max_lines is None:
            max_lines = DIAGNOSTIC_LINES_WHEN_TRIMMED
            trimmed.append("diagnostics")
        elif notes_chars is None:
            notes_chars = NOTES_CHARS_WHEN_TRIMMED
            trimmed.append("notes")
        else:
            trimmed.append("still over budget")
            break
    stats = {
        "template": cfg["prompt_template"],
        "chars": size,
        "tokens_estimate": size // CHARS_PER_TOKEN,
        "part1_chars": len(part1),
        "part2_chars": len(part2),
        "budget_tokens": cfg["prompt_budget_tokens"],
        "removed": removed,
        "trimmed": trimmed,
    }
    return Prompt(part1, part2, stats)
