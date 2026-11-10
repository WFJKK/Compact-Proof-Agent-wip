"""Diagnostics: every uncertified input is attributed to the leaf that decided it."""

import numpy as np
import pytest

from core import inputs
from core.check.checker import check_proof
from core.check.proof import SCHEMA
from core.diagnostics import diagnose, float_margins, render_attempt
from core.zoo import network_entry

from tests.netutil import install, min_task_weights

V = 5


def leaf(rule):
    return {"leaf": rule}


def split(position, cuts, children):
    return {"split": {"position": position, "cuts": cuts}, "children": children}


def values(position, lo, hi, child):
    if lo == hi:
        return child(lo)
    return split(position, list(range(lo + 1, hi + 1)), [child(v) for v in range(lo, hi + 1)])


def rotated(V):
    """The perfect network with its hidden layer rotated: the same function, but naive intervals get loose."""
    w = min_task_weights(V)
    Q, _ = np.linalg.qr(np.random.default_rng(0).normal(size=(V, V)))
    return {"inp.weight": Q, "inp.bias": np.zeros(V), "out.weight": w["out.weight"] @ Q.T, "out.bias": np.zeros(V)}


@pytest.fixture
def nets(stub):
    """A perfect network, its rotated twin, and one whose output bias makes some inputs wrong."""
    bias = np.zeros(V)
    bias[3] = 1.5  # output 3 wins wherever the right answer's lead is small
    weights = {"good": min_task_weights(V), "rot": rotated(V), "bad": min_task_weights(V, out_bias=bias)}
    out = {}
    for nid, w in weights.items():
        install(stub, nid, w, "tiny")
        m = float_margins(stub, nid)
        install(stub, nid, w, "tiny", correct=m > 0)
        out[nid] = (m, m > 0)
    assert out["rot"][1].all() and out["good"][1].all()
    return out


def run(stub, nid, proof, nets):
    proof = {"schema": SCHEMA, "network": nid, **proof}
    res = check_proof(proof, stub, nid, detail=True)
    assert res["status"] == "ok", res["reason"]
    margins, correct = nets[nid]
    return res, diagnose(stub, network_entry(stub, nid), res, margins, correct)


def consistent(diag, res):
    s = diag["uncertified_summary"]
    assert s["groups_shown"] == s["groups"]  # small enough to show everything
    lost = sum(d["uncertified_correct"] for d in diag["uncertified_by_group"].values())
    assert lost == s["uncertified_correct"]
    for d in diag["uncertified_by_group"].values():
        assert d["certified"] + d["uncertified_correct"] + d["wrong"] == d["inputs"]
        if d["uncertified_correct"]:
            assert sum(d["why"].values()) == d["uncertified_correct"]
    assert res["certified"] + s["uncertified_correct"] + s["wrong"] == res["n_inputs"]


def test_brute_force_on_a_perfect_network_leaves_nothing(stub, nets):
    res, diag = run(stub, "good", {"tree": values(0, 0, V - 1, lambda a: values(1, 0, V - 1, lambda b: leaf("single")))}, nets)
    assert res["certified"] == V * V
    assert diag["uncertified_by_group"] == {}
    assert diag["rejected_summary"]["count"] == 0


def test_wrong_inputs_are_listed_by_group(stub, nets):
    margins, correct = nets["bad"]
    assert 0 < (~correct).sum() < V * V
    res, diag = run(stub, "bad", {"tree": values(0, 0, V - 1, lambda a: values(1, 0, V - 1, lambda b: leaf("single")))}, nets)
    consistent(diag, res)
    toks = inputs.all_inputs([V, V])
    for g, d in diag["uncertified_by_group"].items():
        in_g = toks.min(axis=1) == int(g)
        assert d["wrong"] == int((~correct & in_g).sum())
        assert d["uncertified_correct"] == 0
        for ex in d["wrong_examples"]:
            assert min(ex) == int(g) and not correct[inputs.input_index(np.array([ex]), [V, V])[0]]
    assert diag["rejected_summary"]["by_reason"] == {"margin not positive": int((~correct).sum())}


def test_reasons_skip_label_and_bound(stub, nets):
    # First token 0: skipped. First token 1: one interval leaf over every second token (label not constant).
    # First token 2 to 4 with second token 0: one interval leaf (label 0), bounded through two linear maps,
    # which is too loose on the rotated network although every input is correct. The rest: singles.
    tree = split(
        0,
        [1, 2],
        [
            leaf("skip"),
            leaf("interval"),
            split(1, [1], [leaf("interval"), values(0, 2, V - 1, lambda a: values(1, 1, V - 1, lambda b: leaf("single")))]),
        ],
    )
    res, diag = run(stub, "rot", {"tree": tree}, nets)
    consistent(diag, res)
    why = {}
    for d in diag["uncertified_by_group"].values():
        for k, v in d.get("why", {}).items():
            why[k] = why.get(k, 0) + v
    assert why == {"skipped": V, "label not constant": V, "margin bound not positive": V - 2}
    g0 = diag["uncertified_by_group"]["0"]
    assert g0["worst_shortfall"] > 0 and g0["float_min_margin"] > 0.9
    assert diag["rejected_summary"]["by_reason"] == {"label not constant": 1, "margin bound not positive": 1}
    assert diag["rejected_summary"]["skipped_leaves"] == 1
    assert diag["rejected_summary"]["shortfall"]["max"] == pytest.approx(g0["worst_shortfall"])
    # The same proof on the unrotated network: the interval bound holds there.
    res, diag = run(stub, "good", {"tree": tree}, nets)
    assert "margin bound not positive" not in str(diag)


def test_symmetry_decides_by_the_sorted_input(stub, nets):
    def row(a):
        singles = values(1, a, V - 1, lambda b: leaf("single"))
        return singles if a == 0 else split(1, [a], [leaf("skip"), singles])

    res, diag = run(stub, "good", {"symmetry": True, "tree": values(0, 0, V - 1, row)}, nets)
    assert res["certified"] == V * V  # the skipped unsorted inputs are certified through their sorted versions
    assert diag["uncertified_by_group"] == {}
    # Now skip one sorted input: it and its swap are lost, both blamed on its leaf.
    def row2(a):
        if a == 1:
            return split(1, [1, 2], [leaf("skip"), leaf("skip"), values(1, 2, V - 1, lambda b: leaf("single"))])
        return row(a)

    res, diag = run(stub, "good", {"symmetry": True, "tree": values(0, 0, V - 1, row2)}, nets)
    consistent(diag, res)
    assert res["certified"] == V * V - 1  # (1, 1) has no swap
    res, diag = run(
        stub, "good", {"symmetry": True, "tree": values(0, 0, V - 1, lambda a: row(a) if a != 1 else split(1, [1, 3], [leaf("skip"), values(1, 1, 2, lambda b: leaf("skip") if b == 2 else leaf("single")), values(1, 3, V - 1, lambda b: leaf("single"))]))}, nets
    )
    consistent(diag, res)
    assert res["certified"] == V * V - 2  # (1, 2) and (2, 1)
    assert diag["uncertified_by_group"]["1"]["why"] == {"skipped": 2}


def test_render_attempt_reads_well(stub, nets):
    res, diag = run(stub, "bad", {"tree": values(0, 0, V - 1, lambda a: values(1, 0, V - 1, lambda b: leaf("single")))}, nets)
    base = {
        "setting": "tiny",
        "network": "bad",
        "status": "ok",
        "certified": res["certified"],
        "n_inputs": res["n_inputs"],
        "real_accuracy": float(nets["bad"][1].mean()),
        "length": res["length"],
        "length_by_rule": res["length_by_rule"],
        "B": res["length"],
        **diag,
    }
    recs = [{**base, "knob": 0.0}, {**base, "knob": 1.0}]
    recs.append({**base, "knob": 0.5, "status": "crash", "error": "Traceback\nValueError: boom", "certified": None})
    text = render_attempt(recs, "smallest token")
    assert "knobs 0 to 1: certified" in text and "(B/1.0)" in text
    assert "crash x1: ValueError: boom" in text
    assert "wrong inputs, never certifiable" in text and "smallest token" in text
    assert render_attempt([{"status": "parse", "error": "the response has no RECIPE section"}]) == (
        "status parse: the response has no RECIPE section"
    )
