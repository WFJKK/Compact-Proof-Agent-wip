"""Tests of token_convex (rule.py; the argument is in SOUNDNESS.md).

    python -m pytest rules/token_convex/test_rule.py

The two searches against brute force in exact arithmetic; leaf bounds against the float64 network on random
leaves of all four attention folders (never above the true smallest margin, never certifying less than
token_interval, exact when one position varies); reuse charged once; linear networks refused; and a whole
proof built from the rule certifying every correct input of a network far below brute force.
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
def test_exact_when_one_position_varies(rule, name):
    folder, e, prog, module = setup(name)
    rng = np.random.default_rng(12)
    sizes = folder.sizes(e["setting"])
    V, P = sizes["d_vocab"], sizes["n_ctx"]
    done = 0
    while done < 15:
        free = int(rng.integers(0, P))
        ranges = [(int(t), int(t)) for t in rng.integers(0, V, size=P)]
        lo = int(rng.integers(0, V))
        ranges[free] = (lo, min(V - 1, lo + int(rng.integers(1, 8))))
        label = folder.task.constant_label(ranges, sizes)
        if label is None:
            continue
        _, bound, _ = rule.check_leaf(prog, ranges, int(label), Counter())
        true = true_margin(folder, e, module, ranges, int(label))
        assert true - 1e-6 <= float(bound) <= true + 1e-9
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
