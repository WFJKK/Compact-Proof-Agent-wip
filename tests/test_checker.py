"""Tests of the trusted checker on the stub model and on hand-made networks."""

import itertools
import shutil
from fractions import Fraction

import numpy as np
import pytest

from core import inputs
from core.check.arith import Exact, parse_number, ProofNumberError
from core.check.checker import brute_force_proof, check_proof, extraction_and_brute_force_costs
from core.check.cost import Counter, count_scalars
from core.check.proof import SCHEMA, full_tree, sorted_orbit_count
from core.check.trace import build_graph
from core.model_folder import load_model_folder
from core.train import train_zoo
from core.zoo import networks
from tests.netutil import install, min_task_weights

V = 5  # the stub's vocabulary, from its config


@pytest.fixture(scope="module")
def zoo(tmp_path_factory):
    dst = tmp_path_factory.mktemp("stubzoo") / "stub"
    from tests.conftest import STUB

    shutil.copytree(STUB, dst, ignore=shutil.ignore_patterns("zoo", "__pycache__"))
    folder = load_model_folder(dst)
    train_zoo(folder, log=lambda *a: None)
    install(folder, "perfect", min_task_weights(V), "tiny")
    install(folder, "wrong", min_task_weights(V, out_bias=[0, 0, 0, 0, 2.5]), "tiny")
    install(folder, "tie", min_task_weights(V, out_bias=[0, 0, 0, 0, 1.0]), "tiny")
    return load_model_folder(dst)


def P(nid, tree, **kw):
    return {"schema": SCHEMA, "network": nid, "tree": tree, **kw}


def exact_correct(folder, nid):
    """Ground truth: exact brute-force certification of every input, as a mask."""
    r = check_proof(brute_force_proof(folder, nid), folder, nid, want_mask=True)
    return r["mask"]


def sorted_tree(Vn, leaf=None):
    """Singles on t1 <= t2, skip elsewhere (for symmetric proofs)."""
    leaf = leaf or {"leaf": "single"}

    def row(t1):
        if t1 == Vn - 1:
            sub = dict(leaf)
        else:
            sub = {"split": {"position": 1, "cuts": list(range(t1 + 1, Vn))}, "children": [dict(leaf) for _ in range(t1, Vn)]}
        if t1 == 0:
            return sub
        return {"split": {"position": 1, "cuts": [t1]}, "children": [{"leaf": "skip"}, sub]}

    return {"split": {"position": 0, "cuts": list(range(1, Vn))}, "children": [row(t) for t in range(Vn)]}


# brute force and costs ---------------------------------------------------------
def test_brute_force_certifies_exactly_the_correct_inputs(zoo):
    for nid in ("perfect", "wrong", "tie"):
        r = check_proof(brute_force_proof(zoo, nid), zoo, nid, want_mask=True)
        assert r["status"] == "ok"
        tokens = inputs.all_inputs([V, V])
        if nid == "perfect":
            assert r["certified"] == 25
        if nid == "wrong":  # (s, 4) and (4, s) for s < 4 go to output 4
            bad = {(s, 4) for s in range(4)} | {(4, s) for s in range(4)}
            expect = np.array([tuple(t) not in bad for t in tokens])
            assert np.array_equal(r["mask"], expect)
        if nid == "tie":  # (s, 4): output s and output 4 tie exactly; ties are never certified
            assert r["certified"] == 25 - 8


def trained(zoo):
    return [n for n in networks(zoo, "dev") if n["real_correct"] is not None]


def test_brute_force_length_is_B(zoo):
    for n in trained(zoo):
        E, B = extraction_and_brute_force_costs(zoo, n["id"])
        r = check_proof(brute_force_proof(zoo, n["id"]), zoo, n["id"])
        assert r["length"] == B
        assert E == sum(np.asarray(v).size for v in __import__("core.zoo", fromlist=["x"]).load_weights(zoo, n["id"]).values())
        assert r["certified"] == n["real_correct"]  # float correctness agrees with exact here


# symmetry -----------------------------------------------------------------------
def test_symmetry_halves_the_inputs_checked(zoo):
    for nid in ("perfect", "wrong"):
        full = check_proof(brute_force_proof(zoo, nid), zoo, nid, want_mask=True)
        sym = check_proof(P(nid, sorted_tree(V), symmetry=True), zoo, nid, want_mask=True)
        assert sym["status"] == "ok"
        assert np.array_equal(full["mask"], sym["mask"])
        assert sym["length_by_rule"]["single"] * 25 == full["length_by_rule"]["single"] * 15


def test_symmetry_counts_only_sorted_inputs(zoo):
    # One interval-free leaf covering everything with symmetry: each sorted input
    # counts with its orbit; a single leaf over the full box is malformed, so use singles.
    sym = check_proof(P("perfect", full_tree([V, V]), symmetry=True), zoo, "perfect", want_mask=True)
    assert sym["certified"] == 25  # unsorted leaves count nothing but their sorted twins do


def test_orbit_counts_match_enumeration():
    rng = np.random.default_rng(0)
    for P_ in (1, 2, 3):
        for _ in range(40):
            ranges = []
            for _ in range(P_):
                a = int(rng.integers(0, 6))
                ranges.append((a, a + int(rng.integers(0, 4))))
            total = 0
            for t in itertools.product(*[range(a, b + 1) for a, b in ranges]):
                if list(t) == sorted(t):
                    total += len(set(itertools.permutations(t)))
            assert sorted_orbit_count(ranges) == total


# contraction and interval soundness -------------------------------------------
def test_contraction_changes_nothing_but_cost(zoo):
    con = [{"name": "M", "chain": ["inp", "out"]}]
    for nid in ("perfect", "wrong", "tie"):
        a = check_proof(brute_force_proof(zoo, nid), zoo, nid, want_mask=True)
        b = check_proof(P(nid, full_tree([V, V]), contract=con), zoo, nid, want_mask=True)
        assert b["status"] == "ok" and np.array_equal(a["mask"], b["mask"])
        assert b["length_by_rule"]["contract"] > 0


def _random_leaf_tree(rng, label_fn, approx=None):
    """A tree splitting both positions into random ranges, interval leaves where the label is constant."""
    cuts0 = sorted(rng.choice(range(1, V), size=int(rng.integers(0, V - 1)), replace=False).tolist())
    cuts1 = sorted(rng.choice(range(1, V), size=int(rng.integers(0, V - 1)), replace=False).tolist())
    b0 = [0] + cuts0 + [V]
    b1 = [0] + cuts1 + [V]
    leaves = {}

    def leaf(r0, r1):
        lab = label_fn([r0, r1])
        node = {"leaf": "interval"} if lab is not None else {"leaf": "skip"}
        if lab is not None and approx:
            node["approx"] = approx
        leaves[(r0, r1)] = node
        return node

    def kids1(r0):
        ch = [leaf(r0, (b1[i], b1[i + 1] - 1)) for i in range(len(b1) - 1)]
        return ch[0] if not cuts1 else {"split": {"position": 1, "cuts": cuts1}, "children": ch}

    ch0 = [kids1((b0[i], b0[i + 1] - 1)) for i in range(len(b0) - 1)]
    tree = ch0[0] if not cuts0 else {"split": {"position": 0, "cuts": cuts0}, "children": ch0}
    return tree


@pytest.mark.parametrize("contract", [False, True])
def test_interval_is_sound(zoo, contract):
    rng = np.random.default_rng(1)
    con = [{"name": "M", "chain": ["inp", "out"]}] if contract else []
    nids = ["perfect", "wrong", "tie"] + [n["id"] for n in trained(zoo)]
    for nid in nids:
        truth = exact_correct(zoo, nid)
        for _ in range(15):
            tree = _random_leaf_tree(rng, lambda rs: zoo.task.constant_label(rs, zoo.sizes("tiny")))
            r = check_proof(P(nid, tree, contract=con), zoo, nid, want_mask=True)
            assert r["status"] == "ok", r["reason"]
            assert not (r["mask"] & ~truth).any(), "interval certified an input that is not correct"


def test_contracted_interval_is_exact_when_one_position_is_fixed(zoo):
    # With the whole network contracted and t1 fixed, the bound is the exact minimum over t2.
    con = [{"name": "M", "chain": ["inp", "out"]}]
    for nid in ("perfect", "wrong"):
        truth = exact_correct(zoo, nid).reshape(V, V)

        def row(s):  # t1 = s, t2 in [s, V-1]: label s (the smaller token)
            node = {"leaf": "interval"}
            return node if s == 0 else {"split": {"position": 1, "cuts": [s]}, "children": [{"leaf": "skip"}, node]}

        tree = {"split": {"position": 0, "cuts": list(range(1, V))}, "children": [row(s) for s in range(V)]}
        r = check_proof(P(nid, tree, contract=con, symmetry=True), zoo, nid)
        expect = 0
        for s in range(V):
            if truth[s, s:].all():
                expect += 1 + 2 * (V - 1 - s)
        assert r["certified"] == expect


@pytest.mark.parametrize("form", ["dense", "low_rank", "row_segments"])
def test_approximations_are_sound(zoo, form):
    rng = np.random.default_rng(2)
    con = [{"name": "M", "chain": ["inp", "out"]}]
    for nid in ["perfect", "wrong"] + [n["id"] for n in trained(zoo)]:
        truth = exact_correct(zoo, nid)
        from core.zoo import load_weights

        w = load_weights(zoo, nid)
        M = w["out.weight"].astype(np.float64) @ w["inp.weight"].astype(np.float64)
        for trial in range(6):
            noise = rng.normal(scale=[0.0, 0.05, 0.5][trial % 3], size=M.shape)
            if form == "dense":
                spec = {"form": "dense", "values": [[float(x) for x in row] for row in (M + noise)]}
            elif form == "low_rank":
                U_, S_, Vt = np.linalg.svd(M + noise)
                r = 1 + trial % V
                spec = {"form": "low_rank", "left": (U_[:, :r] * S_[:r]).tolist(), "right": Vt[:r].tolist()}
            else:
                rows = []
                for i in range(V):
                    cuts = sorted(set(rng.choice(range(1, V), size=int(rng.integers(0, 3))).tolist()))
                    b = [0] + cuts + [V]
                    rows.append([[b[k], b[k + 1] - 1, float(M[i, b[k] : b[k + 1]].mean() + noise[i, 0])] for k in range(len(b) - 1)])
                spec = {"form": "row_segments", "rows": rows}
            tree = _random_leaf_tree(rng, lambda rs: zoo.task.constant_label(rs, zoo.sizes("tiny")), approx="A")
            proof = P(nid, tree, contract=con, approximate=[{"name": "A", "of": "M", **spec}])
            r = check_proof(proof, zoo, nid, want_mask=True)
            assert r["status"] == "ok", r["reason"]
            assert not (r["mask"] & ~truth).any()


def test_approximation_eps_is_exact(zoo):
    from core.check.approx import Approximation

    W = Exact.from_float(np.array([[0.5, 0.25], [1.0, -2.0]], dtype=np.float32))
    spec = {"form": "row_segments", "rows": [[[0, 1, "3/8"]], [[0, 0, 1], [1, 1, "-2"]]]}
    a = Approximation("A", "M", spec, W, Counter())
    assert a.eps == Fraction(1, 8)
    spec = {"form": "dense", "values": [["1/2", "1/4"], [1, "-1.5"]]}
    assert Approximation("A", "M", spec, W, Counter()).eps == Fraction(1, 2)


# malformed proofs and false claims -------------------------------------------
@pytest.mark.parametrize(
    "mutate, reason",
    [
        (lambda p: p.update(network="other"), "names network"),
        (lambda p: p.update(schema="v0"), "schema"),
        (lambda p: p.update(extra=1), "unknown top-level"),
        (lambda p: p.pop("tree"), "no tree"),
        (lambda p: p.update(tree={"leaf": "single"}), "exactly one input"),
        (lambda p: p.update(tree={"leaf": "magic"}), "not allowed"),
        (lambda p: p.update(tree={"leaf": "interval", "approx": "nope"}), "unknown approximation"),
        (lambda p: p.update(tree={"split": {"position": 0, "cuts": [0]}, "children": [{"leaf": "skip"}] * 2}), "cuts must increase"),
        (lambda p: p.update(tree={"split": {"position": 0, "cuts": [2, 2]}, "children": [{"leaf": "skip"}] * 3}), "cuts must increase"),
        (lambda p: p.update(tree={"split": {"position": 0, "cuts": [5]}, "children": [{"leaf": "skip"}] * 2}), "cuts must increase"),
        (lambda p: p.update(tree={"split": {"position": 2, "cuts": [1]}, "children": [{"leaf": "skip"}] * 2}), "position"),
        (lambda p: p.update(tree={"split": {"position": 0, "cuts": [1]}, "children": [{"leaf": "skip"}]}), "children"),
        (lambda p: p.update(tree={"split": {"position": True, "cuts": [1]}, "children": [{"leaf": "skip"}] * 2}), "position"),
        (lambda p: p.update(tree={"leaf": "skip", "extra": 1}), "unknown leaf keys"),
        (lambda p: p.update(symmetry="yes"), "true or false"),
        (lambda p: p.update(contract=[{"name": "M", "chain": ["out", "inp"]}]), "feeds more"),
        (lambda p: p.update(contract=[{"name": "inp", "chain": ["inp", "out"]}]), "already used"),
        (lambda p: p.update(contract=[{"name": "M", "chain": ["inp"]}]), "at least two"),
        (lambda p: p.update(approximate=[{"name": "A", "of": "nope", "form": "dense", "values": [[0]]}]), "unknown linear"),
        (lambda p: p.update(approximate=[{"name": "A", "of": "out", "form": "dense", "values": [["x"] * 5] * 5}]), "not a number"),
        (lambda p: p.update(approximate=[{"name": "A", "of": "out", "form": "row_segments", "rows": [[[0, 3, 1]]] * 5}]), "reach the last"),
        (lambda p: p.update(approximate=[{"name": "A", "of": "out", "form": "dense", "values": [[float("nan")] * 5] * 5}]), "finite"),
    ],
)
def test_malformed_proofs_are_rejected(zoo, mutate, reason):
    proof = P("perfect", full_tree([V, V]))
    mutate(proof)
    r = check_proof(proof, zoo, "perfect")
    assert r["status"] == "rejected" and reason in r["reason"], r["reason"]
    assert r["certified"] == 0


def test_rules_outside_the_rule_set_are_rejected(zoo):
    proof = P("perfect", full_tree([V, V]), contract=[{"name": "M", "chain": ["inp", "out"]}])
    r = check_proof(proof, zoo, "perfect", rule_set=("single", "interval", "skip"))
    assert r["status"] == "rejected" and "not allowed" in r["reason"]
    r = check_proof(P("perfect", {"leaf": "interval"}), zoo, "perfect", rule_set=("single", "skip"))
    assert r["status"] == "rejected"


def test_false_claims_certify_nothing(zoo):
    # An interval leaf over every input with t2 = 4 claims (s, 4) is fine; "wrong" misclassifies those.
    tree = {"split": {"position": 1, "cuts": [4]}, "children": [{"leaf": "skip"}, {"leaf": "interval"}]}
    r = check_proof(P("wrong", tree), zoo, "wrong")
    assert r["status"] == "ok" and r["certified"] == 0
    # A leaf whose label is not constant certifies nothing (it is not a malformed proof).
    r = check_proof(P("perfect", {"leaf": "interval"}), zoo, "perfect")
    assert r["status"] == "ok" and r["certified"] == 0 and r["rejected_pieces"][0]["reason"] == "label not constant"


def test_huge_trees_are_refused(zoo):
    deep = {"leaf": "skip"}
    for _ in range(20000):
        deep = {"split": {"position": 0, "cuts": [1]}, "children": [deep, {"leaf": "skip"}]}
    r = check_proof(P("perfect", deep), zoo, "perfect")
    assert r["status"] == "rejected"


def test_symmetry_is_refused_when_positions_are_not_summed_first(tmp_path):
    from tests.conftest import STUB

    dst = tmp_path / "persum"
    shutil.copytree(STUB, dst, ignore=shutil.ignore_patterns("zoo", "__pycache__"))
    src = (dst / "model.py").read_text().replace("self.out(self.inp(x.sum(dim=1)))", "self.out(self.inp(x).sum(dim=1))")
    (dst / "model.py").write_text(src)
    folder = load_model_folder(dst)
    install(folder, "perfect", min_task_weights(V), "tiny")
    assert not build_graph(folder.build("tiny")).summed_over_positions_first()
    r = check_proof(P("perfect", sorted_tree(V), symmetry=True), folder, "perfect")
    assert r["status"] == "rejected" and "symmetry does not hold" in r["reason"]
    # Without symmetry the per-position path still checks, and interval is still sound.
    truth = exact_correct(folder, "perfect")
    assert truth.sum() == 25
    rng = np.random.default_rng(3)
    for _ in range(10):
        tree = _random_leaf_tree(rng, lambda rs: folder.task.constant_label(rs, folder.sizes("tiny")))
        r = check_proof(P("perfect", tree), folder, "perfect", want_mask=True)
        assert r["status"] == "ok" and not (r["mask"] & ~truth).any()


def test_unsupported_ops_stop_the_check(tmp_path):
    from tests.conftest import STUB

    dst = tmp_path / "relu"
    shutil.copytree(STUB, dst, ignore=shutil.ignore_patterns("zoo", "__pycache__"))
    src = (dst / "model.py").read_text().replace("self.out(self.inp(x.sum(dim=1)))", "self.out(torch.relu(self.inp(x.sum(dim=1))))")
    (dst / "model.py").write_text(src)
    folder = load_model_folder(dst)
    install(folder, "perfect", min_task_weights(V), "tiny")
    r = check_proof(brute_force_proof(folder, "perfect"), folder, "perfect")
    assert r["status"] == "rejected" and "relu" in r["reason"]


# arithmetic and counting --------------------------------------------------------
def test_exact_conversion_is_exact():
    rng = np.random.default_rng(4)
    a = rng.normal(size=(7, 3)).astype(np.float32)
    a[0, 0] = np.float32(1e-40)  # subnormal
    a[1, 1] = 0.0
    e = Exact.from_float(a)
    fr = e.to_fractions()
    for x, f in zip(a.reshape(-1), fr.reshape(-1)):
        assert Fraction(float(x)) == f


def test_parse_number():
    assert parse_number("-3/4") == Fraction(-3, 4)
    assert parse_number("1.25") == Fraction(5, 4)
    assert parse_number(7) == 7
    assert parse_number(0.5) == Fraction(1, 2)
    for bad in [True, None, "x", float("inf"), "1" * 300, [1]]:
        with pytest.raises(ProofNumberError):
            parse_number(bad)


def test_count_scalars_and_counter():
    assert count_scalars({"a": [1, 2, {"b": "x", "c": None}], "d": True}) == 4
    c = Counter()
    c.add("single", 3)
    c.add("contract", 2)
    assert c.total == 5 and c.as_dict() == {"single": 3, "contract": 2}
    with pytest.raises(ValueError):
        c.add("magic", 1)
    with pytest.raises(ValueError):
        c.add("single", -1)
    for plan in ("tree", "symmetry"):  # the plan is free under cost-v4: nothing may charge it
        with pytest.raises(ValueError):
            c.add(plan, 1)


def test_the_plan_is_free_and_read_counts_the_numbers_a_proof_supplies(zoo):
    """cost-v4: the tree, the leaf rules, the symmetry flag, names and notes cost nothing; read is 1 per
    number of an approximation's form. So a proof's length is E plus its rules' work on numbers, as in the
    open lane (a checker's code is capped, not charged), and brute force is E plus one forward pass per input."""
    nid = "perfect"
    E, B = extraction_and_brute_force_costs(zoo, nid)
    brute = check_proof(brute_force_proof(zoo, nid), zoo, nid)
    per_input = brute["length_by_rule"]["single"] // 25
    assert brute["length_by_rule"] == {"extract": E, "single": 25 * per_input} and brute["length"] == B == E + 25 * per_input
    # a large tree of skip leaves, with notes, costs E alone
    skips = check_proof(P(nid, full_tree([V, V], leaf={"leaf": "skip"}), notes="a plan costs nothing"), zoo, nid)
    assert skips["status"] == "ok" and skips["length"] == E and skips["length_by_rule"] == {"extract": E}
    # symmetry: the 15 sorted inputs' forward passes, and counting their orbits is free
    sym = check_proof(P(nid, sorted_tree(V), symmetry=True), zoo, nid)
    assert sym["certified"] == 25 and sym["length_by_rule"] == {"extract": E, "single": 15 * per_input}
    # an approximation's numbers are read: a dense form of the contracted 5 x 5 map has 25
    con = [{"name": "M", "chain": ["inp", "out"]}]
    W = load_contracted(zoo, nid)
    values = [[str(Fraction(round(float(x) * 16), 16)) for x in row] for row in W]  # dyadic, near W
    dense = check_proof(P(nid, {"leaf": "skip"}, contract=con, approximate=[{"name": "A", "of": "M", "form": "dense", "values": values}]), zoo, nid)
    assert dense["status"] == "ok" and dense["length_by_rule"]["read"] == 25
    segs = [[[0, 2, values[i][0]], [3, 4, values[i][3]]] for i in range(5)]
    rows = check_proof(P(nid, {"leaf": "skip"}, contract=con, approximate=[{"name": "A", "of": "M", "form": "row_segments", "rows": segs}]), zoo, nid)
    assert rows["status"] == "ok" and rows["length_by_rule"]["read"] == 3 * 10


def load_contracted(folder, nid):
    """The stub's contracted map out @ inp in float64 (outputs x inputs)."""
    from core.zoo import load_weights

    w = load_weights(folder, nid)
    keys = sorted(w)
    inp = next(np.asarray(w[k], dtype=np.float64) for k in keys if k.startswith("inp") and k.endswith("weight"))
    out = next(np.asarray(w[k], dtype=np.float64) for k in keys if k.startswith("out") and k.endswith("weight"))
    return out @ inp


def test_symmetry_needs_a_symmetric_label(tmp_path):
    from tests.conftest import STUB

    dst = tmp_path / "first"
    shutil.copytree(STUB, dst, ignore=shutil.ignore_patterns("zoo", "__pycache__"))
    # Same network shape, but the label is the first token: not symmetric.
    t = (dst / "task.py").read_text()
    t = t.replace("LABEL_SYMMETRIC = True", "LABEL_SYMMETRIC = False")
    t = t.replace("return np.asarray(tokens).min(axis=1)\n\n\ndef constant_label", "return np.asarray(tokens)[:, 0]\n\n\ndef constant_label")
    (dst / "task.py").write_text(t)
    folder = load_model_folder(dst)
    install(folder, "net", min_task_weights(V), "tiny")
    r = check_proof(P("net", sorted_tree(V), symmetry=True), folder, "net")
    assert r["status"] == "rejected" and "reordering keeps the label" in r["reason"]
    # Declaring it falsely is caught when the folder is loaded.
    (dst / "task.py").write_text(t.replace("LABEL_SYMMETRIC = False", "LABEL_SYMMETRIC = True"))
    from core.model_folder import ModelFolderError

    with pytest.raises(ModelFolderError, match="LABEL_SYMMETRIC"):
        load_model_folder(dst)


def test_an_exact_segment_approximation_is_never_cheaper_than_the_dense_check(zoo):
    """cost-v2: writing the contracted matrix itself as one-entry row segments (error 0) does the same
    work as the dense range check, so it must not be charged less (cost-v1 charged it half)."""
    from core.zoo import load_weights

    con = [{"name": "M", "chain": ["inp", "out"]}]
    checked = False
    ids = ["perfect"] + [n["id"] for n in trained(zoo)]
    for nid in ids:
        w = load_weights(zoo, nid)
        M = (Exact.from_float(w["out.weight"]).matmul(Exact.from_float(w["inp.weight"]))).to_fractions()
        rows = [[[t, t, f"{M[i, t].numerator}/{M[i, t].denominator}"] for t in range(V)] for i in range(V)]
        approx = [{"name": "A", "of": "M", "form": "row_segments", "rows": rows}]

        def tree(leaf):
            # the stub's label is the smaller token: group a holds the sorted inputs (a, t) with t >= a
            def group(a):
                if a == 0:
                    return dict(leaf)
                return {"split": {"position": 1, "cuts": [a]}, "children": [{"leaf": "skip"}, dict(leaf)]}

            return {"split": {"position": 0, "cuts": list(range(1, V))}, "children": [group(a) for a in range(V)]}

        dense = check_proof(P(nid, tree({"leaf": "interval"}), contract=con, symmetry=True), zoo, nid)
        seg = check_proof(P(nid, tree({"leaf": "interval", "approx": "A"}), contract=con, symmetry=True, approximate=approx), zoo, nid)
        assert dense["status"] == seg["status"] == "ok"
        assert seg["certified"] == dense["certified"] > 1
        assert seg["length_by_rule"]["interval"] >= dense["length_by_rule"]["interval"]
        assert seg["length"] > dense["length"]
        checked = True
    assert checked


def test_approximation_ranges_are_charged_for_what_they_do():
    """cost-v2: each form's range charge is what the checker does, so none is cheaper than its work; cost-v4:
    the numbers of the form are read, 1 each."""
    from core.check.approx import Approximation

    rng = np.random.default_rng(3)
    n_out, n_in = 4, 6
    W = Exact.from_float(rng.normal(size=(n_out, n_in)).astype(np.float32))
    Wf = W.to_fractions()

    def charged(spec, lo, hi):
        c = Counter()
        a = Approximation("A", "M", spec, W, c)
        setup = c.as_dict()
        c = Counter()
        out = a.row_min_diffs(0, lo, hi, c)
        return setup, c.total, out

    # dense: 2 per token per output, like the exact check
    dense = {"form": "dense", "values": [[str(x) for x in row] for row in Wf]}
    setup, cost, out = charged(dense, 1, 4)
    assert setup == {"approximate": 2 * n_out * n_in, "read": n_out * n_in} and cost == 2 * n_out * 4
    assert all(out[j] == min(Wf[0, t] - Wf[j, t] for t in range(1, 5)) for j in range(n_out))

    # low_rank: 2r per token plus 3r per output (difference, sign test, multiply-add per factor)
    r = 2
    left = [[str(x) for x in row] for row in Wf[:, :r]]
    right = [[1 if i == k else 0 for k in range(n_in)] for i in range(r)]
    setup, cost, _ = charged({"form": "low_rank", "left": left, "right": right}, 0, 5)
    assert setup == {"approximate": n_out * r * n_in + 2 * n_out * n_in, "read": n_out * r + r * n_in}
    assert cost == 2 * r * 6 + 3 * n_out * r

    # row_segments: setup 3 per entry plus 2 per segment; a range 2 per merge step plus 2 per row
    rows = [[[0, 2, "1"], [3, 5, "0"]], [[0, 5, "0"]], [[0, 0, "1"], [1, 5, "-1"]], [[0, 3, "1/2"], [4, 5, "1/2"]]]
    setup, cost, out = charged({"form": "row_segments", "rows": rows}, 0, 5)
    assert setup == {"approximate": 3 * n_out * n_in + 2 * 7, "read": 3 * 7}
    # merge steps of row 0 (ends 2, 5) against rows: 0 -> 2, 1 -> 2, 2 -> 3, 3 -> 3; two lookups per row plus the label row
    assert cost == 2 * (2 + 2 + 3 + 3) + 2 * (n_out + 1)
    assert list(out) == [Fraction(0), Fraction(0), Fraction(0), Fraction(-1, 2)]
    # a range inside one segment of every row costs the same whatever its width
    setup, narrow, _ = charged({"form": "row_segments", "rows": rows}, 4, 4)
    setup, wide, _ = charged({"form": "row_segments", "rows": rows}, 4, 5)
    assert narrow == wide == 2 * n_out + 2 * (n_out + 1)


def test_segments_are_located_by_index(zoo):
    """Random segmentations: the index finds the same segments as a scan, and the bound is the true minimum of P."""
    from core.check.approx import Approximation

    rng = np.random.default_rng(4)
    n_out, n_in = 3, 9
    W = Exact.from_float(rng.normal(size=(n_out, n_in)).astype(np.float32))
    for _ in range(30):
        rows, P = [], np.empty((n_out, n_in), dtype=object)
        for i in range(n_out):
            cuts = sorted(set(rng.choice(range(1, n_in), size=int(rng.integers(0, n_in - 1))).tolist()))
            b = [0] + cuts + [n_in]
            segs = [[b[k], b[k + 1] - 1, str(int(rng.integers(-3, 4)))] for k in range(len(b) - 1)]
            rows.append(segs)
            for a_, b_, v in segs:
                P[i, a_ : b_ + 1] = Fraction(v)
        a = Approximation("A", "M", {"form": "row_segments", "rows": rows}, W, Counter())
        for _ in range(10):
            lo = int(rng.integers(0, n_in))
            hi = int(rng.integers(lo, n_in))
            for i in range(n_out):
                scan = [k for k in range(len(rows[i])) if rows[i][k][0] <= hi and rows[i][k][1] >= lo]
                got = a._clip(i, lo, hi)
                assert [max(rows[i][k][0], lo) for k in scan] == [g[0] for g in got]
                assert [min(rows[i][k][1], hi) for k in scan] == [g[1] for g in got]
            l = int(rng.integers(0, n_out))
            out = a.row_min_diffs(l, lo, hi, Counter())
            assert all(out[j] == min(P[l, t] - P[j, t] for t in range(lo, hi + 1)) for j in range(n_out))

