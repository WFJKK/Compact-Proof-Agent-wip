"""Frontiers and metrics, computed from archive records alone (section 5 of the spec).

Per network, a(b) is the best certified accuracy among checked proofs of
length at most b. The metrics:

- Q: the area under a(b) on a log length scale from E to B, divided by ln(B/E).
- Q_grid: the mean of a(b) over the fixed budgets B/r, B/r^2, ... down to E, with r
  the run's budget_ratio. It is Q read only at the grid, so where a recipe places
  its proofs between grid points earns nothing (docs/SPEC.md, section 5).
- shortest_full: the shortest proof that certifies the network's real accuracy.
- within: the best certified accuracy within B/10, B/100 and B/1000.
- cost_of_finishing: B divided by (length + uncertified correct inputs x B/n),
  for the best proof.
- Q_above: the improvement over the brute-force line, normalised by the room
  above it (below). Brute force on any subset of the inputs scores 0.

Per size setting, the median and the worst network. All numbers are
Python-checked until rules have Lean proofs.
"""

from __future__ import annotations

import math
import statistics

BUDGET_DIVISORS = (10, 100, 1000)


def default_budget_ratio() -> float:
    from .run_config import defaults

    return float(defaults()["budget_ratio"])


def budget_grid(E: float, B: float, ratio: float) -> list[int]:
    """The fixed budgets B/ratio, B/ratio^2, ..., all at least E, as integers; empty if E or B is missing."""
    if not E or not B or ratio <= 1 or B / ratio < E:
        return []
    out, b = [], B / ratio
    while b >= E:
        out.append(int(math.floor(b)))
        b /= ratio
    return out


def budget_position(budget: float, E: float, B: float) -> float:
    """Where a budget sits on the log axis from E (0) to B (1); what the recipe sees as its knob."""
    return 0.0 if B <= E else max(0.0, min(1.0, math.log(budget / E) / math.log(B / E)))


def q_grid(points: list[dict], E: float, B: float, ratio: float | None = None) -> float:
    grid = budget_grid(E, B, ratio if ratio is not None else default_budget_ratio())
    if not grid:
        return 0.0
    return sum(accuracy_within(points, b) for b in grid) / len(grid)


def scored(records: list[dict]) -> list[dict]:
    """Records that count: checked proofs the checker accepted."""
    return [
        r
        for r in records
        if r.get("status") == "ok" and r.get("network") and r.get("length") is not None and r.get("certified") is not None
    ]


def frontier(records: list[dict]) -> dict[str, list[dict]]:
    """Per network, the proofs no other proof beats on both length and certified inputs, by increasing length.

    A proof that certifies nothing is never on it.
    """
    by_net: dict[str, list[dict]] = {}
    for r in scored(records):
        if r["certified"] > 0:
            by_net.setdefault(r["network"], []).append(r)
    out = {}
    for net, rs in by_net.items():
        rs.sort(key=lambda r: (r["length"], -r["certified"], r["record_id"]))
        points, best = [], -1
        for r in rs:
            if r["certified"] > best:
                points.append(
                    {
                        "length": r["length"],
                        "certified": r["certified"],
                        "n_inputs": r["n_inputs"],
                        "record_id": r["record_id"],
                        "round": r["round"],
                        "attempt": r["attempt"],
                        "knob": r["knob"],
                    }
                )
                best = r["certified"]
        out[net] = points
    return out


def accuracy_within(points: list[dict], budget: float) -> float:
    best = 0.0
    for p in points:
        if p["length"] <= budget:
            best = max(best, p["certified"] / p["n_inputs"])
    return best


def q_score(points: list[dict], E: float, B: float) -> float:
    if not E or not B or B <= E:
        return 0.0
    total = 0.0
    for i, p in enumerate(points):
        lo = max(p["length"], E)
        hi = min(points[i + 1]["length"], B) if i + 1 < len(points) else B
        if hi > lo:
            total += p["certified"] / p["n_inputs"] * (math.log(hi) - math.log(lo))
    return total / math.log(B / E)


def q_exact(points: list[dict], E: float, B: float) -> float:
    """The log-area of the verified frontier over [max(E, B/1000), B] (B included), normalised by the
    width of that range: the expected certified accuracy at a budget drawn log-uniformly from the range,
    computed from the proofs' actual lengths. Decided 22 October 2026 as the primary objective (the
    budget grid of Q_grid cannot see an improvement between two of its budgets, such as a full proof going
    from 1,031 to 719); it is clean when the evaluator chooses where proofs are requested (the frozen
    method on a fixed schedule) and it inherits Q's placement effect when the agent chooses its own points."""
    if not E or not B:
        return 0.0
    lo_limit = max(E, B / 1000)
    if B <= lo_limit:
        return 0.0
    total = 0.0
    for i, p in enumerate(points):
        lo = max(p["length"], lo_limit)
        hi = min(points[i + 1]["length"], B) if i + 1 < len(points) else B
        if hi > lo:
            total += p["certified"] / p["n_inputs"] * (math.log(hi) - math.log(lo))
    return total / math.log(B / lo_limit)


# Q_above: improvement over the brute-force line ----------------------------------------
#
# Brute force on any k inputs is a proof the agent can always write: k forward passes at the single rule's
# charge c each, plus extract E, certifying k inputs (at most the `coverage` inputs the baseline brute force
# certifies, which is every input the network gets right). So at length L brute force certifies
#
#     b(L) = min(coverage, floor((L - E) / c)) / n,
#
# the brute-force line. Q_exact counts the area under b as score (about 0.21 on the tiny attention network,
# most of the hand proof's 0.25), so an agent that beats brute force nowhere still scores by submitting
# subsets. Q_above counts only the area above the line, normalised by the room above it:
#
#     Q_above = integral of (a(L) - b(L))+ over log L / integral of (a_max - b(L)) over log L,
#
# both over [max(E, B/1000), B], with a_max the share of inputs the network gets right (what any sound proof
# can certify at most). Equivalently (Q_exact(max(a, b)) - Q_exact(b)) / (a_max - Q_exact(b)): the gain of
# the frontier merged with the line over the line alone, over the headroom. A point at or below the line adds
# nothing and costs nothing; 1 means every correct input certified at every length from the range's start.
# A score of 0.05 means 5% of the headroom's log-area, not 5% of the operations saved.
#
# The line's facts come from the run's own round-0 brute-force record (coverage and c) and the open lane's
# accounting (E, the extract the service charges, which equals the zoo's E: the weight count); c is the
# single rule's charge per input, which the open lane's single and gsingle charge too. When no brute-force
# record exists the line is estimated (coverage = the real correct count, c = B / n) and the metrics say so.
# The integral is exact: a and b are step functions, so it is summed over their merged breakpoints.


def brute_force_line(entry: dict, records: list[dict] | None) -> dict:
    """The brute-force line of a network: per-input cost c, extract E, coverage, n, and how they were found."""
    n = int(entry.get("n_inputs") or 0)
    E = float(entry.get("E") or 0.0)
    for r in records or []:
        if r.get("network") != entry.get("id") or r.get("round") != 0 or r.get("status") != "ok":
            continue
        by_rule = r.get("length_by_rule") or {}
        leaves = r.get("leaves") or {}
        others = [k for k, v in by_rule.items() if v and k not in ("single", "extract", "read", "tree")]
        if by_rule.get("single") and n and not others and leaves.get("total") == n and not leaves.get("skipped"):
            return {"c": by_rule["single"] / n, "E": E, "coverage": int(r["certified"]), "n": n,
                    "how": "exact: the single rule's charge per input and the coverage of round 0's brute force"}
    B = float(entry.get("B") or 0.0)
    return {"c": (B / n if n else 0.0), "E": E, "coverage": int(entry.get("real_correct") or 0), "n": n,
            "how": "estimate: B over the number of inputs, coverage the real correct count (no brute-force record)"}


def line_certified(line: dict, length: float) -> int:
    """How many inputs brute force certifies at this length."""
    if not line["c"] or length < line["E"]:
        return 0
    return min(line["coverage"], int(math.floor((length - line["E"]) / line["c"])))


def above_line(line: dict, length: float, certified: int) -> bool:
    """Whether a proof certifies more than brute force of the same length."""
    return certified > line_certified(line, length)


def _log_area(step, lo_limit: float, B: float, breaks: list[float]) -> float:
    """The integral of a step function over log L on [lo_limit, B], where `step(L)` is constant between
    consecutive breakpoints (its value on a piece is its value at the piece's left end)."""
    xs = sorted({lo_limit, B, *(x for x in breaks if lo_limit < x < B)})
    total = 0.0
    for lo, hi in zip(xs, xs[1:]):
        total += step(lo) * (math.log(hi) - math.log(lo))
    return total


def q_above(points: list[dict], entry: dict, line: dict) -> float:
    """The improvement of the frontier over the brute-force line, normalised by the room above the line."""
    E, B, n = entry.get("E"), entry.get("B"), line["n"]
    if not E or not B or not n:
        return 0.0
    lo_limit = max(E, B / 1000)
    if B <= lo_limit:
        return 0.0
    a_max = (entry.get("real_correct") if entry.get("real_correct") is not None else line["coverage"]) / n

    def a(L: float) -> float:
        return accuracy_within(points, L)

    def b(L: float) -> float:
        return line_certified(line, L) / n

    breaks = [p["length"] for p in points]
    if line["c"]:
        breaks += [line["E"] + line["c"] * k for k in range(1, line["coverage"] + 1)]
    gain = _log_area(lambda L: max(a(L) - b(L), 0.0), lo_limit, B, breaks)
    room = _log_area(lambda L: max(a_max - b(L), 0.0), lo_limit, B, breaks)
    return gain / room if room > 0 else 0.0


def fallback_cost_per_input(entry: dict, records: list[dict] | None) -> tuple[float, str]:
    """What one uncovered input costs to certify by the fallback rule, exactly: the single rule's charge
    per input, read from the run's brute-force baseline record for this network (its `single` charge over
    its inputs). When no such record exists, B over the number of inputs, and the result says so."""
    n = entry.get("n_inputs") or 0
    for r in records or []:
        if r.get("network") == entry.get("id") and r.get("round") == 0 and r.get("status") == "ok":
            by_rule = r.get("length_by_rule") or {}
            if by_rule.get("single") and n and r.get("certified") == n:
                return by_rule["single"] / n, "exact: the single rule's charge per input"
    B = entry.get("B") or 0.0
    return (B / n if n else 0.0), "estimate: B over the number of inputs (no brute-force baseline record)"


def cost_of_finishing(points: list[dict], real_correct: int, B: float, per_input: float | None = None) -> float:
    """B over the cheapest total of proof length plus the fallback cost of every correct input it leaves
    uncertified. The fallback cost per input is the single rule's exact charge when known
    (fallback_cost_per_input); B over the number of inputs otherwise."""
    if not points or not real_correct:
        return 0.0
    n = points[0]["n_inputs"]
    unit = per_input if per_input is not None else B / n
    best = None
    for p in points:
        total = p["length"] + max(0, real_correct - p["certified"]) * unit
        best = total if best is None else min(best, total)
    return B / best


def network_metrics(points: list[dict], entry: dict, budget_ratio: float | None = None, records: list[dict] | None = None) -> dict:
    E, B, real = entry.get("E"), entry.get("B"), entry.get("real_correct")
    ratio = budget_ratio if budget_ratio is not None else default_budget_ratio()
    full = [p["length"] for p in points if real is not None and p["certified"] >= real]
    unit, unit_how = fallback_cost_per_input(entry, records)
    line = brute_force_line(entry, records)
    return {
        "Q": q_score(points, E, B),
        "Q_exact": q_exact(points, E, B),
        "Q_above": q_above(points, entry, line),
        "brute_force_line": line,
        "points_above_line": sum(1 for p in points if above_line(line, p["length"], p["certified"])),
        "Q_grid": q_grid(points, E, B, ratio),
        "grid": {str(b): accuracy_within(points, b) for b in budget_grid(E, B, ratio)},
        "best_accuracy": max((p["certified"] / p["n_inputs"] for p in points), default=0.0),
        "real_accuracy": entry.get("real_accuracy"),
        "shortest_full": min(full) if full else None,
        "within": {f"B/{d}": accuracy_within(points, B / d) for d in BUDGET_DIVISORS} if B else {},
        "cost_of_finishing": cost_of_finishing(points, real, B, unit) if B else 0.0,
        "fallback_cost_per_input": unit_how,
        "E": E,
        "B": B,
        "points": len(points),
    }


def summarize(records: list[dict], entries: list[dict], budget_ratio: float | None = None) -> dict:
    """Per size setting: metrics per network, then the median and the worst network.

    budget_ratio sets the grid of Q_grid; a run passes its config's value, and None
    means the default in config/defaults.yaml.
    """
    fr = frontier(records)
    by_setting: dict[str, dict] = {}
    for e in entries:
        by_setting.setdefault(e["setting"], {})[e["id"]] = network_metrics(fr.get(e["id"], []), e, budget_ratio, records)
    out = {}
    for setting, nets in by_setting.items():
        q = [m["Q"] for m in nets.values()]
        qg = [m["Q_grid"] for m in nets.values()]
        qe = [m["Q_exact"] for m in nets.values()]
        qa = [m["Q_above"] for m in nets.values()]
        cof = [m["cost_of_finishing"] for m in nets.values()]
        full = [m["shortest_full"] / m["B"] if m["shortest_full"] and m["B"] else None for m in nets.values()]
        out[setting] = {
            "networks": nets,
            "Q_median": statistics.median(q),
            "Q_worst": min(q),
            "Q_grid_median": statistics.median(qg),
            "Q_grid_worst": min(qg),
            "Q_exact_mean": statistics.mean(qe),  # equal weight per network (seed); across sizes, equal weight per size
            "Q_exact_worst": min(qe),
            "Q_above_mean": statistics.mean(qa),
            "Q_above_worst": min(qa),
            "cost_of_finishing_median": statistics.median(cof),
            "cost_of_finishing_worst": min(cof),
            "shortest_full_over_B_median": statistics.median(full) if all(f is not None for f in full) else None,
        }
    return out
