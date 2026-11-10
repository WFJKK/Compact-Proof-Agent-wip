"""Tests of token_convex (rule.py; the argument is in SOUNDNESS.md).

    python -m pytest rules/token_convex/test_rule.py

The two searches against brute force in exact arithmetic; leaf bounds against the float64 network on random
leaves of all four attention folders (never above the true smallest margin, never certifying less than
token_interval, deciding exactly when one position varies); reuse charged once; linear networks refused; and a
whole proof built from the rule certifying every correct input of a network far below brute force.

Version 2 (leaves where the query varies): the relative-weight box against brute force on random score tables;
the per-token largest-other-output shortcut against brute force; query-varying leaves on trained, sharp random
and perturbed networks against the float64 network; such leaves certifying whenever all their fixed-query parts
do; their reuse charged once; and a whole proof of leaves "the positions in S hold M, the others below M".
"""

from __future__ import annotations

import itertools
import random
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest
import torch

from core.check.checker import check_proof
from core.check.cost import Counter
from core.check.evaluate import CheckError
from core.check.plugins import drop_candidates, use_candidate
from core.check.proof import SCHEMA
from core.check.trace import build_any, make_program
from core.model_folder import load_model_folder
from core.zoo import load_module, load_weights, networks

HERE = Path(__file__).resolve().parent
REPO = HERE.parents[1]
FOLDERS = ["attn-max4", "attn-min4", "attn-max2", "attn-min2"]


@pytest.fixture(scope="module")
def rule():
    r = use_candidate(HERE)
    yield r
    drop_candidates()


def setup(name, setting=None):
    folder = load_model_folder(REPO / "models" / name)
    e = next(x for x in networks(folder) if setting is None or x["setting"] == setting)
    space = folder.input_space(e["setting"])
    prog = make_program(build_any(folder.build(e["setting"])), load_weights(folder, e["id"]), Counter(), space)
    return folder, e, prog, load_module(folder, e["id"]).double()


def true_margin(folder, e, module, ranges, label):
    toks = np.array(list(itertools.product(*[range(lo, hi + 1) for lo, hi in ranges])))
    with torch.no_grad():
        z = module(folder.encode(toks, e["setting"]).double()).numpy()
    return float((z[:, label] - np.delete(z, label, axis=1).max(axis=1)).min())


def random_leaves(folder, e, rng, n, fixed_query, max_width=6):
    sizes = folder.sizes(e["setting"])
    V, P = sizes["d_vocab"], sizes["n_ctx"]
    out = []
    while len(out) < n:
        ranges = []
        for p in range(P):
            lo = int(rng.integers(0, V))
            w = 0 if (fixed_query and p == P - 1) else int(rng.integers(0, max_width))
            ranges.append((lo, min(V - 1, lo + w)))
        label = folder.task.constant_label(ranges, sizes)
        if label is not None:
            out.append((ranges, int(label)))
    return out


# the two searches -----------------------------------------------------------------------------------------
def test_box_search_is_the_minimum_over_the_box(rule):
    ev = rule.module.ConvexEvaluator
    rnd = random.Random(1)
    for _ in range(300):
        n = rnd.randint(1, 5)
        cs = [rnd.randint(-50, 50) for _ in range(n)]
        lo = [rnd.choice([0, rnd.randint(1, 40)]) for _ in range(n)]
        hi = [l + rnd.randint(0 if l else 1, 60) for l in lo]
        N, D = ev.threshold(lo, [h - l for h, l in zip(hi, lo)], cs)
        brute = min(
            Fraction(sum(u * c for u, c in zip(us, cs)), sum(us))
            for us in itertools.product(*zip(lo, hi))
            if sum(us) > 0
        )
        assert Fraction(N, D) == brute


def test_token_search_is_the_minimum_over_token_choices(rule):
    mod = rule.module
    rnd = random.Random(2)
    ev = mod.ConvexEvaluator.__new__(mod.ConvexEvaluator)  # only charge() is used
    ev.counter = Counter()
    for _ in range(150):
        n = rnd.randint(1, 3)
        k = [rnd.randint(1, 3) for _ in range(n)]
        cs = [[rnd.randint(-40, 40) for _ in range(k[p])] for p in range(n)]
        wl = [[rnd.choice([0, rnd.randint(1, 30)]) for _ in range(k[p])] for p in range(n)]
        wh = [[w + rnd.randint(0 if w else 1, 40) for w in wl[p]] for p in range(n)]
        ctx = {"wl": wl, "wh": wh, "n_tok": sum(k)}
        got = ev.exact_search(ctx, cs, 0, -64)
        options = [[(i, w) for i in range(k[p]) for w in (wl[p][i], wh[p][i])] for p in range(n)]
        brute = min(
            Fraction(sum(w * cs[p][i] for p, (i, w) in enumerate(ch)), sum(w for _, w in ch))
            for ch in itertools.product(*options)
            if sum(w for _, w in ch) > 0
        )
        assert got is not None
        assert Fraction(got, 2**64) <= brute < Fraction(got + 1, 2**64)  # the minimum, rounded down


# leaves -----------------------------------------------------------------------------------------------------
@pytest.mark.parametrize("name", FOLDERS)
def test_sound_and_never_weaker_than_token_interval(rule, name):
    folder, e, prog, module = setup(name)
    _, _, prog2, _ = setup(name)
    rng = np.random.default_rng(11)
    leaves = random_leaves(folder, e, rng, 15, fixed_query=True) + random_leaves(folder, e, rng, 10, fixed_query=False)
    for ranges, label in leaves:
        ok, bound, _ = rule.check_leaf(prog, ranges, label, Counter())
        ok_ti, bound_ti, _ = prog2.run_token_interval(ranges, label, Counter())
        true = true_margin(folder, e, module, ranges, label)
        assert float(bound) <= true + 1e-9, (ranges, label)
        assert ok == (bound > 0)
        assert ok or not ok_ti, (ranges, label)


@pytest.mark.parametrize("name", ["attn-max4", "attn-min2"])
def test_exact_decision_when_one_position_varies(rule, name):
    """With one varying position the rule certifies exactly the leaves whose inputs are all classified correctly,
    and a leaf it does not certify gets its exact smallest margin (version 2 stops at the first positive bound,
    so a certified leaf's bound may be lower than its margin)."""
    folder, e, prog, module = setup(name)
    rng = np.random.default_rng(12)
    sizes = folder.sizes(e["setting"])
    V, P = sizes["d_vocab"], sizes["n_ctx"]
    done = failed = 0
    while done < 40:
        free = int(rng.integers(0, P))
        ranges = [(int(t), int(t)) for t in rng.integers(0, V, size=P)]
        lo = int(rng.integers(0, V))
        ranges[free] = (lo, min(V - 1, lo + int(rng.integers(1, 8))))
        label = folder.task.constant_label(ranges, sizes)
        if label is None:
            continue
        ok, bound, _ = rule.check_leaf(prog, ranges, int(label), Counter())
        true = true_margin(folder, e, module, ranges, int(label))
        assert float(bound) <= true + 1e-9
        if abs(true) > 1e-6:
            assert ok == (true > 0), (ranges, label, true, float(bound))
        if not ok:
            assert true - 1e-6 <= float(bound)
            failed += 1
        done += 1


def test_boxes_with_two_varying_positions_are_tight_with_a_fixed_query(rule):
    """Peeling boxes (the query fixed, one position holding the largest token, two below it): certified, and
    never above the true smallest margin."""
    folder, e, prog, module = setup("attn-max4", "v16")
    V = folder.sizes(e["setting"])["d_vocab"]
    certified = 0
    for M, q in [(15, 3), (12, 5), (9, 9), (14, 0), (7, 2)]:
        ranges = [(M, M), (0, M), (0, M), (q, q)]
        ok, bound, _ = rule.check_leaf(prog, ranges, M, Counter())
        true = true_margin(folder, e, module, ranges, M)
        assert float(bound) <= true + 1e-9
        certified += ok and true > 0
    assert certified >= 4
    assert V == 16


def test_reuse_is_charged_once(rule):
    folder, e, prog, _ = setup("attn-max4", "v16")
    ranges = [(0, 11), (12, 12), (0, 12), (5, 5)]
    first, second = Counter(), Counter()
    rule.check_leaf(prog, ranges, 12, first)
    rule.check_leaf(prog, ranges, 12, second)
    assert first.as_dict().get("tables", 0) > 0
    assert second.as_dict().get("tables", 0) == 0
    assert first.as_dict()["token_convex"] == second.as_dict()["token_convex"]


def test_linear_networks_refuse_it(rule, tmp_path):
    import shutil

    from tests.conftest import STUB
    from tests.netutil import install, min_task_weights

    shutil.copytree(STUB, tmp_path / "stub", ignore=shutil.ignore_patterns("zoo", "__pycache__"))
    stub = load_model_folder(tmp_path / "stub")
    setting = stub.setting_names()[0]
    nid = install(stub, "lin-0", min_task_weights(stub.sizes(setting)["d_vocab"]), setting)
    space = stub.input_space(setting)
    prog = make_program(build_any(stub.build(setting)), load_weights(stub, nid), Counter(), space)
    with pytest.raises(CheckError):
        rule.check_leaf(prog, [(0, 0)] * len(space), 0, Counter())
    proof = {"schema": SCHEMA, "network": nid, "tree": {"leaf": "token_convex"}}
    res = check_proof(proof, stub, nid, rule_set=("single", "token_convex"))
    assert res["status"] == "rejected"


def peeling_tree(folder, setting, prog, rule, max_leaves=64):
    """Max of n: fix the last position (q), then with the other positions allowed 0..M, either position 0 holds M
    (a box), or it is below M and position 1 holds M, and so on, then the same with M - 1. Each box is refined by
    peeling the top token off its widest varying position until token_convex certifies it (or it is skipped)."""
    sizes = folder.sizes(setting)
    V, n = sizes["d_vocab"], sizes["n_ctx"]

    def refine(rt, budget):
        if budget[0] <= 0:
            return {"leaf": "skip"}
        label = folder.task.constant_label(rt, sizes)
        budget[0] -= 1
        if rule.check_leaf(prog, rt, int(label), Counter())[0]:
            return {"leaf": "token_convex"}
        varying = [p for p, (lo, hi) in enumerate(rt) if hi > lo]
        if not varying:
            return {"leaf": "skip"}
        p = max(varying, key=lambda x: rt[x][1] - rt[x][0])
        lo, hi = rt[p]
        low, top = list(rt), list(rt)
        low[p], top[p] = (lo, hi - 1), (hi, hi)
        return {"split": {"position": p, "cuts": [hi]}, "children": [refine(low, budget), refine(top, budget)]}

    def peel(q, M):
        k = n - 1
        if M <= q:
            return refine([(0, M)] * k + [(q, q)], [max_leaves])

        def level(i):
            if i == k:
                return peel(q, M - 1)
            at_m = [(0, M - 1)] * i + [(M, M)] + [(0, M)] * (k - 1 - i) + [(q, q)]
            return {"split": {"position": i, "cuts": [M]}, "children": [level(i + 1), refine(at_m, [max_leaves])]}

        return level(0)

    return {"split": {"position": n - 1, "cuts": list(range(1, V))}, "children": [peel(q, V - 1) for q in range(V)]}


def test_a_whole_proof_certifies_every_correct_input_far_below_brute_force(rule):
    folder, e, prog, _ = setup("attn-max4", "v16")
    proof = {"schema": SCHEMA, "network": e["id"], "tree": peeling_tree(folder, e["setting"], prog, rule)}
    res = check_proof(proof, folder, e["id"], rule_set=("single", "token_convex", "skip"))
    assert res["status"] == "ok"
    assert res["certified"] == e["real_correct"]
    assert res["length"] * 150 < e["B"]


def test_check_proof_needs_the_rule_in_the_run(rule):
    folder, e, _, _ = setup("attn-max4", "v16")
    proof = {"schema": SCHEMA, "network": e["id"], "tree": {"leaf": "token_convex"}}
    res = check_proof(proof, folder, e["id"], rule_set=("single", "token_interval"))
    assert res["status"] == "rejected" and "not allowed" in res["reason"]


@pytest.mark.parametrize("stub", ["stub_general", "stub_twopaths"])
def test_sound_on_the_synthetic_architectures(rule, stub):
    """Biased linear layers (stub_general) and two terms with one origin reaching one product (stub_twopaths),
    with random weights, many leaves on one program so the memo is shared across them."""
    folder = load_model_folder(REPO / "tests" / stub)
    setting = folder.setting_names()[0]
    module = folder.build(setting)
    rng = np.random.default_rng(5)
    for scale in (1.0, 5.0):
        weights = {k: (rng.uniform(-1, 1, size=v.shape) * scale).astype(np.float32) for k, v in module.state_dict().items()}
        module.load_state_dict({k: torch.tensor(v) for k, v in weights.items()})
        prog = make_program(build_any(folder.build(setting)), weights, Counter(), folder.input_space(setting))
        e = {"setting": setting}
        for ranges, label in random_leaves(folder, e, rng, 20, fixed_query=False, max_width=4):
            _, bound, _ = rule.check_leaf(prog, ranges, label, Counter())
            prog.run_token_interval(ranges, label, Counter())  # interleaved, sharing the memo
            assert float(bound) <= true_margin(folder, e, module.double(), ranges, label) + 1e-9
        module = folder.build(setting)


def test_range_tables_against_brute_force_with_changing_exponents(rule):
    """_Table on random prefix and suffix requests whose rows arrive at different exponents."""
    Table = rule.module._Table
    rnd = random.Random(4)
    V, width = 9, 3
    exact = [[Fraction(rnd.randint(-99, 99), 2 ** rnd.randint(0, 6)) for _ in range(width)] for _ in range(V)]
    for suffix in (False, True):
        tab = Table(suffix, True)
        for _ in range(40):
            k = rnd.randint(1, V)
            tokens = list(range(V - k, V)) if suffix else list(range(k))
            e = -rnd.randint(6, 9)  # every row is a multiple of 2**-6, so any exponent at or below -6 is exact
            rows = [[int(x * 2 ** -e) for x in exact[t]] for t in tokens]
            lo, hi, te = tab.query(len(tokens), e, lambda i: rows[i], lambda n: None)
            want_lo = [min(exact[t][c] for t in tokens) for c in range(width)]
            want_hi = [max(exact[t][c] for t in tokens) for c in range(width)]
            assert [Fraction(int(x)) * Fraction(2) ** te for x in lo] == want_lo
            assert [Fraction(int(x)) * Fraction(2) ** te for x in hi] == want_hi


# version 2: leaves where the query varies -------------------------------------------------------------------
def bare_evaluator(mod, V):
    """An evaluator with only what the searches and tables use (no network)."""
    from types import SimpleNamespace

    ev = mod.ConvexEvaluator.__new__(mod.ConvexEvaluator)
    ev.counter = Counter()
    ev.memo = {}
    ev._ends = {}
    ev._leaf = {}
    ev.prog = SimpleNamespace(_n_values=V)
    return ev


def test_relative_weight_box_contains_every_input(rule):
    """pair_ends: for every input of a random score table (every token per position and every query token), each
    position's weight relative to the reference lies in its enclosure, scaled alike."""
    import math

    mod = rule.module
    rnd = random.Random(6)
    for _ in range(60):
        V = rnd.randint(3, 6)
        n = rnd.randint(2, 4)
        qpos = rnd.randrange(n)
        tokens = []
        for p in range(n):
            lo = rnd.randrange(V)
            hi = rnd.randint(lo, V - 1) if rnd.random() < 0.7 else lo
            tokens.append(list(range(lo, hi + 1)))
        if len(tokens[qpos]) < 2:
            tokens[qpos] = list(range(0, V))
        nq = len(tokens[qpos])
        e = -rnd.randint(2, 5)
        ent = []
        for p in range(n):
            if p == qpos:
                ent.append(np.array([rnd.randint(-60, 60) for _ in range(nq)], dtype=object))
            else:
                ent.append(np.array([[rnd.randint(-60, 60) for _ in range(nq)] for _ in tokens[p]], dtype=object))
        ps = mod.PScores(qpos, tokens, ent, e, [None] * n)
        soft = mod.Soft(None, None, 1, 1, None, ps)
        ev = bare_evaluator(mod, V)
        El, dE = ev.pair_ends(soft)
        Eh = [a + b for a, b in zip(El, dE)]
        cand = [p for p in range(n) if p != qpos]
        r = min(cand, key=lambda p: (len(tokens[p]), p))
        scale = 2.0 ** -120
        choice_sets = [range(len(tokens[p])) if p != qpos else [None] for p in range(n)]
        for i in range(nq):
            for ch in itertools.product(*choice_sets):
                s = [float(ent[p][i]) if p == qpos else float(ent[p][ch[p], i]) for p in range(n)]
                s = [x * 2.0 ** e for x in s]
                for p in range(n):
                    rel = math.exp(s[p] - s[r])
                    # u_p / u_r for some K: u_p in [El_p, Eh_p] * 2**-120 and u_r in [El_r, Eh_r] * 2**-120
                    lo_ratio = (El[p] * scale) / (Eh[r] * scale) if Eh[r] else 0.0
                    hi_ratio = (Eh[p] * scale) / (El[r] * scale) if El[r] else math.inf
                    assert lo_ratio * (1 - 1e-12) <= rel <= hi_ratio * (1 + 1e-12) + 1e-300


def test_largest_other_output_shortcut(rule):
    """row_min_all (R[i, label] minus the largest other entry, from top_two) is the smallest difference, ties
    included, and top_two is kept once per token."""
    mod = rule.module
    rnd = random.Random(7)
    for _ in range(200):
        n_out = rnd.randint(2, 6)
        k = rnd.randint(1, 4)
        rows = [[rnd.randint(-5, 5) for _ in range(n_out)] for _ in range(k)]
        t = mod.GTerm(None, 0, list(range(k)), mod.IT.exact(np.array(rows, dtype=object), 0), True, "o", ("key", rnd.random()))
        ev = bare_evaluator(mod, k)
        for label in range(n_out):
            for i in range(k):
                want = min(rows[i][label] - rows[i][j] for j in range(n_out) if j != label)
                assert ev.row_min_all(t, i, label) == want
        assert ev.counter.as_dict().get("tables", 0) == 2 * n_out * k


def query_leaves(folder, e, rng, n, max_inputs=2500):
    """Leaves whose query position varies, of two kinds: random ranges, and label sets (the positions in S hold a
    token M, the others below or above it)."""
    sizes = folder.sizes(e["setting"])
    V, P = sizes["d_vocab"], sizes["n_ctx"]
    out = []
    while len(out) < n:
        if len(out) % 2 == 0:
            ranges = []
            for p in range(P):
                lo = int(rng.integers(0, V))
                ranges.append((lo, min(V - 1, lo + int(rng.integers(0, 6)))))
        else:
            M = int(rng.integers(1, V))
            S = [p for p in range(P - 1) if rng.random() < 0.4] or [int(rng.integers(0, P - 1))]
            below = rng.random() < 0.5
            ranges = [(M, M) if p in S else ((0, M - 1) if below else (M + 1, V - 1)) for p in range(P)]
            if any(lo > hi for lo, hi in ranges):
                continue
        if ranges[P - 1][1] == ranges[P - 1][0]:
            continue
        size = int(np.prod([hi - lo + 1 for lo, hi in ranges]))
        label = folder.task.constant_label(ranges, sizes)
        if label is None or size > max_inputs:
            continue
        out.append((ranges, int(label)))
    return out


@pytest.mark.parametrize("name", FOLDERS)
def test_query_varying_leaves_are_sound(rule, name):
    """On a trained network, a sharp random one (scale 16) and a perturbed one: never above the float64 network's
    smallest margin, with token_interval leaves interleaved on the same program (the memo is shared)."""
    folder, e, prog, module = setup(name)
    rng = np.random.default_rng(13)
    trained = load_weights(folder, e["id"])
    nets = [("trained", trained)]
    nets.append(("random", {k: (rng.uniform(-1, 1, size=v.shape) * 16 * np.abs(v).max()).astype(np.float32) for k, v in trained.items()}))
    nets.append(("perturbed", {k: (v + rng.normal(size=v.shape) * 0.3 * v.std()).astype(np.float32) for k, v in trained.items()}))
    space = folder.input_space(e["setting"])
    for kind, w in nets:
        p = make_program(build_any(folder.build(e["setting"])), w, Counter(), space)
        m = folder.build(e["setting"]).double()
        m.load_state_dict({k: torch.tensor(v, dtype=torch.float64) for k, v in w.items()})
        for ranges, label in query_leaves(folder, e, rng, 14):
            if rng.random() < 0.5:
                p.run_token_interval(ranges, label, Counter())
            ok, bound, _ = rule.check_leaf(p, ranges, label, Counter())
            true = true_margin(folder, e, m, ranges, label)
            assert float(bound) <= true + 1e-9, (kind, ranges, label)
            assert ok == (bound > 0)


def test_query_varying_leaf_certifies_when_its_fixed_query_parts_do(rule):
    folder, e, prog, module = setup("attn-max4", "v16")
    rng = np.random.default_rng(14)
    checked = 0
    for ranges, label in query_leaves(folder, e, rng, 30):
        lo, hi = ranges[-1]
        parts = [rule.check_leaf(prog, ranges[:-1] + [(q, q)], label, Counter())[0] for q in range(lo, hi + 1)]
        if all(parts):
            assert rule.check_leaf(prog, ranges, label, Counter())[0], ranges
            checked += 1
    assert checked >= 5


def test_query_varying_reuse_is_charged_once(rule):
    folder, e, prog, _ = setup("attn-max4", "v16")
    ranges = [(12, 12), (0, 11), (0, 11), (0, 11)]
    first, second = Counter(), Counter()
    ok1, b1, _ = rule.check_leaf(prog, ranges, 12, first)
    ok2, b2, _ = rule.check_leaf(prog, ranges, 12, second)
    assert first.as_dict().get("tables", 0) > 0
    assert second.as_dict().get("tables", 0) == 0
    assert first.as_dict()["token_convex"] == second.as_dict()["token_convex"]
    assert (ok1, b1) == (ok2, b2)


def label_set_tree(folder, setting, prog, rule, max_leaves=64):
    """Max of n: for each largest token M and each nonempty set S of positions holding it, the box with the
    positions in S at M and the others below M, reached by splitting each position in turn at M; when every
    position is below M, the same with M - 1. A box the rule does not certify is refined by peeling the top token
    off its widest varying position (or skipped)."""
    sizes = folder.sizes(setting)
    V, n = sizes["d_vocab"], sizes["n_ctx"]

    def refine(rt, budget):
        if budget[0] <= 0:
            return {"leaf": "skip"}
        label = folder.task.constant_label(rt, sizes)
        budget[0] -= 1
        if rule.check_leaf(prog, rt, int(label), Counter())[0]:
            return {"leaf": "token_convex"}
        varying = [p for p, (lo, hi) in enumerate(rt) if hi > lo]
        if not varying:
            return {"leaf": "skip"}
        p = max(varying, key=lambda x: (rt[x][1] - rt[x][0], -x))
        lo, hi = rt[p]
        low, top = list(rt), list(rt)
        low[p], top[p] = (lo, hi - 1), (hi, hi)
        return {"split": {"position": p, "cuts": [hi]}, "children": [refine(low, budget), refine(top, budget)]}

    def node(M, i, decided, has_m):
        if M == 0:
            return refine([(0, 0)] * n, [max_leaves])
        if i == n:
            return refine(decided, [max_leaves]) if has_m else node(M - 1, 0, [], False)
        return {"split": {"position": i, "cuts": [M]},
                "children": [node(M, i + 1, decided + [(0, M - 1)], has_m), node(M, i + 1, decided + [(M, M)], True)]}

    return node(V - 1, 0, [], False)


def test_a_whole_proof_with_varying_queries(rule):
    """Leaves where the query varies: every correct input certified, far below brute force and below the proof
    that fixes the query."""
    folder, e, prog, _ = setup("attn-max4", "v16")
    proof = {"schema": SCHEMA, "network": e["id"], "tree": label_set_tree(folder, e["setting"], prog, rule)}
    res = check_proof(proof, folder, e["id"], rule_set=("single", "token_convex", "skip"))
    assert res["status"] == "ok"
    assert res["certified"] == e["real_correct"]
    assert res["length"] * 300 < e["B"]
    fixed = {"schema": SCHEMA, "network": e["id"], "tree": peeling_tree(folder, e["setting"], prog, rule)}
    res_fixed = check_proof(fixed, folder, e["id"], rule_set=("single", "token_convex", "skip"))
    assert res["length"] < res_fixed["length"]
