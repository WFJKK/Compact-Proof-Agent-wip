"""Scoring at fixed budgets (metric Q_grid): the grid, the score, the recipe's budget, the prompt and the baseline."""

import json
import math
import re
from pathlib import Path

import pytest
import yaml

from core import loop
from core.agent.build_prompt import build_prompt, load_template, placeholders
from core.check.checker import check_proof
from core.model_folder import load_model_folder
from core.run_config import RunConfigError, merge
from core.scoring import budget_grid, budget_position, q_grid, summarize
from core.zoo import load_weights

TESTS = Path(__file__).resolve().parent
REPO = TESTS.parent
BUDGET_RECIPE = '''```python
import helpers


def make_proof(weights, info, knob):
    # Brute force within the budget: one single leaf per input while the budget lasts, skip the rest.
    space = info["input_space"]
    per_input = info["B"] / (space[0] * space[1])
    n_ok = int(max(0, info["budget"] - info["E"]) // per_input)
    tree = helpers.full_tree(space)
    count = [0]

    def trim(node):
        if "leaf" in node:
            count[0] += 1
            return node if count[0] <= n_ok else {"leaf": "skip"}
        return {**node, "children": [trim(c) for c in node["children"]]}

    return helpers.proof(trim(tree), notes="budget %d knob %.3f" % (info["budget"], knob))
```'''


def _quiet(*a, **k):
    pass


def response(recipe: str) -> str:
    return (
        "CLAIM: It spends its budget on brute force.\n\nWHY IT HELPS: no.\n\nPREDICTION: accuracy grows with the budget.\n\n"
        f"KNOB: the budget.\n\nRECIPE:\n{recipe}\n\nNOTES: none.\n"
    )


def grid_config(tmp_path, model, responses, **over) -> Path:
    cfg = {
        "run_id": "grid-run",
        "model": str(model),
        "runs_dir": str(tmp_path / "runs"),
        "metric": "Q_grid",
        "budget_ratio": 2,
        "sandbox": "process",
        "fake_responses": [str(p) for p in responses],
        "rounds_max": 2,
        **over,
    }
    path = tmp_path / "grid.yaml"
    path.write_text(yaml.safe_dump(cfg))
    return path


def test_the_grid_halves_from_b_down_to_e():
    grid = budget_grid(1_088, 2_696_387, 2)
    assert len(grid) == 11 and grid[0] == 2_696_387 // 2 and all(b >= 1_088 for b in grid)
    assert all(grid[i] // 2 == grid[i + 1] or grid[i] // 2 == grid[i + 1] + 1 for i in range(10))
    assert len(budget_grid(4_352, 40_407_555, 2)) == 13
    assert budget_grid(100, 150, 2) == [] and budget_grid(None, 1000, 2) == [] and budget_grid(10, 1000, 1) == []
    assert budget_position(1_088, 1_088, 2_696_387) == 0.0 and budget_position(2_696_387, 1_088, 2_696_387) == 1.0
    assert 0.5 < budget_position(2_696_387 // 16, 1_088, 2_696_387) < 0.7


def test_q_grid_reads_accuracy_only_at_the_grid():
    E, B = 1_000, 1_024_000  # 10 budgets: 512k, 256k, ..., 1k
    full = {"length": 300_000, "certified": 10, "n_inputs": 10}
    assert q_grid([full], E, B, 2) == pytest.approx(1 / 10)  # fits under 512k only
    assert q_grid([{**full, "length": 256_000}], E, B, 2) == pytest.approx(2 / 10)  # a budget itself counts
    assert q_grid([{**full, "length": 260_000}], E, B, 2) == pytest.approx(1 / 10)  # 2% shorter earns nothing yet
    half = {"length": 3_000, "certified": 5, "n_inputs": 10}
    assert q_grid([half, full], E, B, 2) == pytest.approx((1.0 * 1 + 0.5 * 7) / 10)  # 512k: the full proof; 256k to 4k: half
    assert q_grid([], E, B, 2) == 0.0


def test_config_validates_the_metric_the_ratio_and_the_template(trained_stub):
    base = {"run_id": "x", "model": str(trained_stub)}
    assert merge({**base, "metric": "Q_grid"})["prompt_template"] == "v4"
    with pytest.raises(RunConfigError, match="budget_ratio"):
        merge({**base, "budget_ratio": 1})
    with pytest.raises(RunConfigError, match="KNOB"):
        merge({**base, "metric": "Q_grid", "prompt_template": "v1"})
    merge({**base, "metric": "Q", "prompt_template": "v1"})  # the old template still serves the old metrics


def test_template_v2_is_v1_with_the_knob_paragraph_as_a_placeholder():
    p1, q1 = load_template("v1")
    p2, q2 = load_template("v2")
    assert placeholders(p2) == placeholders(p1) | {"KNOB"} and placeholders(q1) == placeholders(q2)
    assert "knob is a number between 0 and 1 that we vary" in p1 and "{KNOB}" in p2


def test_a_grid_run_gives_the_recipe_its_budget_and_scores_at_the_grid(trained_stub, tmp_path):
    folder = tmp_path / "responses"
    folder.mkdir()
    (folder / "00.md").write_text(response(BUDGET_RECIPE))
    ctx = loop.start(grid_config(tmp_path, trained_stub, [folder]), log=_quiet)
    loop.drive(ctx)
    records = [r for r in ctx.run.read_archive() if r["round"] == 1 and r["status"] == "ok"]
    assert records, "the budget recipe ran"
    for e in ctx.entries:
        mine = sorted((r for r in records if r["network"] == e["id"]), key=lambda r: r["budget"])
        grid = budget_grid(e["E"], e["B"], 2)
        assert [r["budget"] for r in mine] == sorted(grid)  # one execution per fixed budget
        for r in mine:
            assert r["knob"] == pytest.approx(budget_position(r["budget"], e["E"], e["B"]))
            assert r["record_id"].endswith(f"/b{r['budget']}")
            assert (ctx.run.round_path(1) / "attempt_0" / "proofs" / f"{e['id']}__b{r['budget']}.json.gz").exists()
        # the recipe saw the budget: brute force within it certifies more at larger budgets, never beyond the budget's share
        certified = [r["certified"] for r in mine]
        assert certified == sorted(certified) and certified[-1] > certified[0]
    s = summarize(ctx.run.read_archive(), ctx.entries, 2)
    for v in s.values():
        assert 0 < v["Q_grid_median"] <= 1 and v["Q_grid_worst"] <= v["Q_grid_median"]
        for m in v["networks"].values():
            assert set(m["grid"]) == {str(b) for b in budget_grid(m["E"], m["B"], 2)}
    # the next prompt scores and ranks by Q_grid and shows the grid scoreboard with budgets, not knob values
    p = build_prompt(ctx.cfg, ctx.folder, ctx.entries, ctx.run, 2)
    assert "Your score is Q_grid" in p.part1 and 'info["budget"]' in p.part1 and "knob is a number between 0 and 1 that we vary" not in p.part1
    assert "budget B/2 (" in p.part2 and "budget B/4 (" in p.part2 and "its own Q_grid" in p.part2
    assert re.search(r"budget B/\d+ \([\d,]+\): certified [\d.]+% \(median\), round 1 on \d of 2 networks", p.part2)
    assert "length by rule at budget B/" in p.part2
    assert "knob 0:" not in p.part2


def test_the_knob_baseline_stays_within_a_fixed_budget():
    folder = load_model_folder(str(REPO / "models" / "max2"))
    src = (REPO / "models" / "max2" / "baselines" / "04_contract_interval_budget.md").read_text()
    ns = {}
    import sys

    sys.path.insert(0, str(REPO / "core"))
    exec(re.search(r"```python\n(.*?)```", src, re.S).group(1), ns)
    manifest = json.loads((REPO / "models" / "max2" / "zoo" / "manifest.json").read_text())
    e = next(x for x in manifest["networks"] if x["id"] == "max2-v64-s0")
    w = load_weights(folder, e["id"])
    V = w["embedding.weight"].shape[1]
    certified = []
    for b in budget_grid(e["E"], e["B"], 2):  # B/2 down to B/2048
        proof = ns["make_proof"](w, {"input_space": [V, V], "budget": b, "E": e["E"], "B": e["B"]}, budget_position(b, e["E"], e["B"]))
        proof["network"] = e["id"]
        r = check_proof(proof, folder, e["id"])
        assert r["status"] == "ok" and r["length"] <= b, (b, r["length"])
        certified.append(r["certified"])
    assert certified[0] == e["real_correct"] and certified == sorted(certified, reverse=True)
    assert certified[5] > 0 and certified[-1] == 0  # B/64 still buys part of the largest group; near E nothing fits


def test_q_exact_is_the_clipped_log_area_of_the_verified_frontier():
    """Q_exact is the log-area of the verified frontier over [max(E, B/1000), B]: on a v64 network B/1000 is
    above E, so its range is narrower than Q's, which starts at E."""
    from core.scoring import cost_of_finishing, fallback_cost_per_input, q_exact, q_score

    pts = [{"length": 300_000, "certified": 4000, "n_inputs": 4096}, {"length": 600_000, "certified": 4096, "n_inputs": 4096}]
    q = q_exact(pts, 1088, 2_696_387)
    import math
    L0 = 2_696_387 / 1000
    expected = (4000 / 4096 * math.log(600_000 / 300_000) + math.log(2_696_387 / 600_000)) / math.log(2_696_387 / L0)
    assert abs(q - expected) < 1e-12
    assert q_exact(pts, 1088, 2_696_387) > q_score(pts, 1088, 2_696_387)  # Q's range starts at E, below B/1000, so it counts more empty decades
    # without the brute-force baseline record, cost of finishing estimates an input at B / n
    E, B, n = 80, 4112, 64
    entry = {"id": "max2_tiny-v8-s0", "n_inputs": n, "B": B, "E": E, "real_correct": 64}
    partial = [{"length": 536, "certified": 38, "n_inputs": 64}]
    assert cost_of_finishing(partial, 64, B) == B / (536 + 26 * B / 64)
    assert fallback_cost_per_input(entry, [])[1].startswith("estimate")


def test_q_above_counts_only_what_beats_the_brute_force_line():
    """Q_above (26 October 2026): the frontier's log-area above the brute-force line b(L) = min(coverage,
    floor((L - E) / c)) / n over the room above it. Checked: brute force on any subset scores 0 (the max2
    attention pilot's four subset points, which Q_exact scores 0.148); the identity with Q_exact of the frontier
    merged with the line; the hand proof's number from its actual frontier, which ties the line at its first
    point (the raw difference of Q_exacts would give 0.055, the positive part 0.078); the line's facts from a
    round-0 record, and the estimate without one; coverage below n; the breakpoints are exact."""
    from core.scoring import above_line, brute_force_line, line_certified, q_above, q_exact

    entry = {"id": "attn", "n_inputs": 64, "E": 136, "B": 12571, "real_correct": 64}
    round0 = {"network": "attn", "round": 0, "status": "ok", "certified": 64, "n_inputs": 64,
              "length_by_rule": {"extract": 136, "read": 138, "single": 12224, "tree": 73},
              "leaves": {"accepted": 64, "rejected": 0, "skipped": 0, "total": 64}}
    line = brute_force_line(entry, [round0])
    assert (line["c"], line["E"], line["coverage"], line["n"]) == (191.0, 136, 64, 64) and line["how"].startswith("exact")
    assert line_certified(line, 100) == 0 and line_certified(line, 136 + 191 * 3) == 3 and line_certified(line, 12571) == 64
    subsets = [{"length": 191 * k + 136, "certified": k, "n_inputs": 64} for k in (10, 20, 32, 48)]
    assert round(q_exact(subsets, 136, 12571), 3) == 0.148
    assert q_above(subsets, entry, line) == 0.0 and not any(above_line(line, p["length"], p["certified"]) for p in subsets)
    # the line alone, as Q_exact of its own points: the reviewer's 0.206
    line_pts = [{"length": 136 + 191 * k, "certified": k, "n_inputs": 64} for k in range(1, 65)]
    assert round(q_exact(line_pts, 136, 12571), 3) == 0.206
    # the identity: (Q_exact(merged) - Q_exact(line)) / (1 - Q_exact(line)) for a frontier above the line everywhere
    pts = [{"length": 1000, "certified": 16, "n_inputs": 64}, {"length": 4000, "certified": 64, "n_inputs": 64}]
    merged = sorted(pts + line_pts, key=lambda p: (p["length"], -p["certified"]))
    fr, best = [], -1
    for q in merged:
        if q["certified"] > best:
            fr.append(q)
            best = q["certified"]
    ql = q_exact(line_pts, 136, 12571)
    assert abs(q_above(pts, entry, line) - (q_exact(fr, 136, 12571) - ql) / (1 - ql)) < 1e-12
    # the hand proof on attn_max2_tiny-v8d4-s1 (cost-v3 lengths, certified): ties the line at 1,664 (8 inputs), above it after
    hand_points = [(1664, 8), (1664, 8), (2165, 15), (3083, 26), (3923, 33), (5768, 48), (7384, 64)]
    hand = sorted(({"length": L, "certified": c} for L, c in hand_points), key=lambda p: (p["length"], -p["certified"]))
    fr, best = [], -1
    for q in hand:
        if q["certified"] > best:
            fr.append({"length": q["length"], "certified": q["certified"], "n_inputs": 64})
            best = q["certified"]
    assert not above_line(line, 1664, 8) and above_line(line, 2165, 15)
    assert round(q_above(fr, entry, line), 4) == 0.0776
    assert round(q_exact(fr, 136, 12571), 4) == 0.2496 and round((0.2496 - 0.2062) / (1 - 0.2062), 3) == 0.055
    # the breakpoints are exact: one input above the line on [1000, 1091) only (brute force reaches 5 at 1091)
    one = [{"length": 1000, "certified": 5, "n_inputs": 64}]
    gain = (5 - 4) / 64 * (math.log(136 + 191 * 5) - math.log(1000))  # brute force has 4 at 1000, 5 from 1091
    xs = [136] + [136 + 191 * k for k in range(1, 65)] + [12571]  # the line's steps and the range's ends
    room = sum((1 - k / 64) * (math.log(min(hi, 12571)) - math.log(max(lo, 136)))
               for k, (lo, hi) in enumerate(zip(xs, xs[1:])) if hi > max(lo, 136))
    assert abs(q_above(one, entry, line) - gain / room) < 1e-12
    # coverage below n: the line stops at the inputs brute force certifies, and the room's ceiling is the real count
    entry2 = {"id": "attn", "n_inputs": 64, "E": 136, "B": 12571, "real_correct": 60}
    round0b = {**round0, "certified": 60}
    line2 = brute_force_line(entry2, [round0b])
    assert line2["coverage"] == 60 and line_certified(line2, 12571) == 60
    assert q_above([{"length": 136 + 191 * 60, "certified": 60, "n_inputs": 64}], entry2, line2) == 0.0
    at_start = [{"length": 136, "certified": 60, "n_inputs": 64}]  # every correct input from the range's start: 1
    assert abs(q_above(at_start, entry2, line2) - 1.0) < 1e-12
    # without a brute-force record: an estimate, said so
    est = brute_force_line(entry, [])
    assert est["how"].startswith("estimate") and est["c"] == 12571 / 64 and est["coverage"] == 64
    # a baseline that is not brute force (another rule charged, or skipped leaves) does not define the line
    other = {**round0, "length_by_rule": {"extract": 136, "single": 191, "token_convex": 500}}
    assert brute_force_line(entry, [other])["how"].startswith("estimate")


def test_a_run_on_cost_of_finishing_is_scored_by_the_geometric_mean_over_its_networks():
    """10 November 2026: cost of finishing drives a run as the geometric mean over its networks (ratios average
    on the log scale). A network counts at least 1, since brute force alone always finishes at B: no proof, or
    only proofs that finish above B, is 1 and never 0. Per network nothing changes: any proof counts for what
    it saves, a brute-force subset finishes at exactly B, and there is no budget whose crossing matters."""
    from core.run_config import METRIC_KEYS
    from core.scoring import finishing_detail, finishing_ratio, geometric_mean, run_cost_of_finishing, summarize

    assert METRIC_KEYS["cost_of_finishing"] == "cost_of_finishing_geomean"
    assert geometric_mean([4.0, 1.0]) == 2.0 and geometric_mean([]) == 0.0 and abs(geometric_mean([2.0, 4.0, 8.0]) - 4.0) < 1e-12
    assert finishing_ratio(0.0) == 1.0 and finishing_ratio(0.4) == 1.0 and finishing_ratio(4.5) == 4.5
    entries = [{"id": f"n{i}", "setting": s, "n_inputs": 64, "E": 136, "B": 12360, "real_correct": 64}
               for i, s in enumerate(("small", "small", "large"))]

    def rec(net, k, certified, length, by_rule):
        return {"record_id": f"{net}/{k}/{length}", "network": net, "round": k, "attempt": 0, "status": "ok", "certified": certified,
                "n_inputs": 64, "length": length, "length_by_rule": by_rule, "knob": 1.0}

    brute = [rec(e["id"], 0, 64, 12360, {"extract": 136, "single": 12224}) for e in entries[:2]]  # n2 has no proof at all
    s0 = summarize(brute, entries)
    assert s0["small"]["cost_of_finishing_geomean"] == 1.0 and s0["large"]["cost_of_finishing_geomean"] == 1.0
    assert s0["large"]["cost_of_finishing_median"] == 0.0 and run_cost_of_finishing(s0) == 1.0
    records = brute + [rec("n0", 1, 64, 3090, {"bill": 2954, "extract": 136, "read": 0}),        # complete: B / 3090 = 4
                       rec("n1", 1, 10, 2046, {"bill": 1910, "extract": 136, "read": 0}),        # a brute-force subset: B
                       rec("n1", 2, 20, 9000, {"bill": 8864, "extract": 136, "read": 0})]        # finishes above B
    s1 = summarize(records, entries)
    assert s1["small"]["networks"]["n0"]["cost_of_finishing"] == 4.0 and s1["small"]["networks"]["n1"]["cost_of_finishing"] == 1.0
    assert abs(s1["small"]["cost_of_finishing_geomean"] - 2.0) < 1e-12 and s1["small"]["cost_of_finishing_median"] == 2.5
    assert abs(run_cost_of_finishing(s1) - 4.0 ** (1 / 3)) < 1e-12
    d = finishing_detail([{"length": 2000, "certified": 20, "n_inputs": 64}], entries[0], records)
    assert (d["total"], d["uncovered"], d["per_input"]) == (2000 + 44 * 191, 44, 191.0) and finishing_detail([], entries[0], records) is None
    # a shorter complete proof always counts, however little: nothing waits for a budget to be crossed
    s2 = summarize(records + [rec("n0", 3, 64, 3089, {"bill": 2953, "extract": 136, "read": 0})], entries)
    assert s2["small"]["cost_of_finishing_geomean"] > s1["small"]["cost_of_finishing_geomean"]
