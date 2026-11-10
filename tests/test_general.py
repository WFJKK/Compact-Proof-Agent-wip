"""Networks beyond linear maps: interval arithmetic, exp, softmax, and the xorformer model folder."""

import decimal
import itertools
import random
from fractions import Fraction
from pathlib import Path

import numpy as np
import pytest
import torch

from core.check.checker import brute_force_proof, check_proof
from core.check.cost import Counter
from core.check.interval import IT, PRECISION, concat, exp, exp_bounds, softmax
from core.check.trace import UnsupportedOp, build_any, make_program
from core.model_folder import load_model_folder
from core.zoo import load_module, load_weights, networks

REPO = Path(__file__).resolve().parent.parent
XOR = REPO / "models" / "xorformer-majority"


# exp -----------------------------------------------------------------------------------
def _exp_scaled(X: int, e: int) -> decimal.Decimal:
    """exp(X * 2**e) * 2**PRECISION, correctly rounded to 200 digits."""
    with decimal.localcontext() as ctx:
        ctx.prec = 200
        x = decimal.Decimal(X) * (decimal.Decimal(2) ** e)
        return x.exp() * (decimal.Decimal(2) ** PRECISION)


def test_exp_bounds_enclose_the_true_value():
    random.seed(0)
    cases = [(0, 0), (1, 0), (-1, 0), (5, -3), (-5, -3), (4095, 0), (-4095, 0), (3, -300), (-3, -300), (1, 11), (-1, 11)]
    cases += [(random.randint(-(2**60), 2**60), random.randint(-70, -49)) for _ in range(200)]
    cases += [(random.randint(-(2**200), 2**200), random.randint(-215, -190)) for _ in range(50)]
    for X, e in cases:
        L, H = exp_bounds(X, e)
        true = _exp_scaled(X, e)
        with decimal.localcontext() as ctx:
            ctx.prec = 200
            slack = true * decimal.Decimal("1e-150")
            assert decimal.Decimal(L) <= true + slack and true - slack <= decimal.Decimal(H), (X, e)
            assert decimal.Decimal(H - L) <= max(decimal.Decimal(4), true * decimal.Decimal(2) ** -100), (X, e)


def test_exp_refuses_huge_positive_arguments_and_encloses_huge_negative_ones():
    with pytest.raises(ArithmeticError):
        exp_bounds(1, 13)
    assert exp_bounds(-1, 13) == (0, 1)  # exp(-8192) * 2**PRECISION lies in (0, 1)
    assert exp_bounds(-(2**40), 0) == (0, 1)


def test_softmax_with_one_dominant_entry_far_below_the_rest():
    z = IT.exact(np.array([[0, -(2**20), 5]], dtype=object), 0)
    s = softmax(z, 1)
    assert int(s.lo[0, 1]) == 0 and int(s.hi[0, 1]) >= 0


# interval arithmetic ---------------------------------------------------------------------
def _rand_interval(rng, shape, exact=False):
    lo = rng.integers(-50, 50, size=shape).astype(object)
    if exact:
        return IT.exact(lo, int(rng.integers(-4, 3)))
    hi = lo + rng.integers(0, 20, size=shape).astype(object)
    return IT(lo, hi, int(rng.integers(-4, 3)))


def _sample(it: IT, rng):
    """A point inside the interval tensor, as Fractions."""
    t = rng.random(it.shape)
    lo = np.vectorize(lambda v: Fraction(int(v)) * Fraction(2) ** it.exp, otypes=[object])(it.lo)
    hi = np.vectorize(lambda v: Fraction(int(v)) * Fraction(2) ** it.exp, otypes=[object])(it.hi)
    return lo + (hi - lo) * np.vectorize(lambda v: Fraction(v).limit_denominator(64), otypes=[object])(t)


def _inside(value, it: IT) -> bool:
    lo = np.vectorize(lambda v: Fraction(int(v)) * Fraction(2) ** it.exp, otypes=[object])(it.lo)
    hi = np.vectorize(lambda v: Fraction(int(v)) * Fraction(2) ** it.exp, otypes=[object])(it.hi)
    value = np.asarray(value, dtype=object)
    return bool(np.all(lo <= value) and np.all(value <= hi))


@pytest.mark.parametrize("exact_a,exact_b", [(False, False), (True, False), (False, True), (True, True)])
def test_interval_operations_contain_every_sampled_result(exact_a, exact_b):
    rng = np.random.default_rng(1)
    for _ in range(20):
        a = _rand_interval(rng, (2, 3, 4), exact_a)
        b = _rand_interval(rng, (2, 3, 4), exact_b)
        m = _rand_interval(rng, (4, 5), exact_b)
        v = _rand_interval(rng, (4,), exact_b)
        for _ in range(5):
            xa, xb, xm, xv = _sample(a, rng), _sample(b, rng), _sample(m, rng), _sample(v, rng)
            assert _inside(xa + xb, a + b)
            assert _inside(xa - xb, a - b)
            assert _inside(xa * xb, a * b)
            assert _inside(np.matmul(xa, xm), a @ m)
            assert _inside(np.matmul(xa, xv), a @ v)
            assert _inside(np.sum(xa, axis=1), a.sum(1))
            assert _inside(np.concatenate([xa, xb], axis=2), concat([a, b], 2))


def test_exp_and_softmax_contain_every_sampled_result():
    rng = np.random.default_rng(2)
    with decimal.localcontext() as ctx:
        ctx.prec = 80
        for _ in range(20):
            z = _rand_interval(rng, (3, 5))
            ez, sz = exp(z), softmax(z, 1)
            for _ in range(5):
                x = _sample(z, rng)
                ex = np.vectorize(lambda f: decimal.Decimal(f.numerator) / decimal.Decimal(f.denominator), otypes=[object])(x)
                e = np.vectorize(lambda d: d.exp(), otypes=[object])(ex)
                for idx in np.ndindex(*z.shape):
                    lo = decimal.Decimal(int(ez.lo[idx])) / (decimal.Decimal(2) ** PRECISION)
                    hi = decimal.Decimal(int(ez.hi[idx])) / (decimal.Decimal(2) ** PRECISION)
                    assert lo <= e[idx] <= hi
                    w = e[idx] / sum(e[idx[0]])
                    lo = decimal.Decimal(int(sz.lo[idx])) / (decimal.Decimal(2) ** PRECISION)
                    hi = decimal.Decimal(int(sz.hi[idx])) / (decimal.Decimal(2) ** PRECISION)
                    assert lo <= w <= hi


# the model folder ----------------------------------------------------------------------
class _Reference(torch.nn.Module):
    """xorformer's TorchAttentionCore.forward (experiments/hstar/attention_model.py), copied verbatim
    apart from taking its parameters from a module, to show model.py computes the same function."""

    def __init__(self, src):
        super().__init__()
        self.n_bits, self.heads = src.n_bits, src.heads
        for k, v in src.named_parameters():
            setattr(self, k, v)

    def forward(self, inputs):
        batch_size = inputs.shape[0]
        e_zero = self.token_embeddings[0]
        e_one = self.token_embeddings[1]
        e_query = self.token_embeddings[2]
        input_vectors = (
            (1.0 - inputs).unsqueeze(-1) * e_zero.view(1, 1, -1)
            + inputs.unsqueeze(-1) * e_one.view(1, 1, -1)
            + self.positional_embeddings[: self.n_bits].unsqueeze(0)
        )
        query_vector = e_query + self.positional_embeddings[self.n_bits]
        query_batch = query_vector.view(1, -1).expand(batch_size, -1)
        all_positions = torch.cat([input_vectors, query_batch.unsqueeze(1)], dim=1)
        residual = query_batch
        for head in range(self.heads):
            query = self.WQ[head] @ query_vector
            keys = all_positions @ self.WK[head].T
            values = all_positions @ self.WV[head].T
            logits = keys @ query
            weights = torch.softmax(logits, dim=1)
            head_output = torch.sum(weights.unsqueeze(-1) * values, dim=1)
            projected = head_output @ self.WO[head].T
            residual = residual + projected
        return residual @ self.readout - self.threshold


@pytest.fixture(scope="module")
def xor_folder():
    return load_model_folder(XOR)


@pytest.mark.parametrize("heads", [1, 3])
def test_model_matches_xorformer_forward(xor_folder, heads):
    torch.manual_seed(0)
    m = xor_folder.module_class(n_bits=6, heads=heads, d_model=5, d_head=4).double()
    ref = _Reference(m)
    toks = np.array(list(itertools.product([0, 1], repeat=6)))
    with torch.no_grad():
        ours = m(torch.nn.functional.one_hot(torch.as_tensor(toks), 2).double())
        theirs = ref(torch.as_tensor(toks, dtype=torch.float64))
    assert torch.allclose(ours[:, 1], theirs, atol=1e-12) and torch.all(ours[:, 0] == 0)


def test_zoo_is_float64_and_fits(xor_folder):
    nets = networks(xor_folder, split=None)
    assert len(nets) == 10 and all(n["real_accuracy"] == 1.0 for n in nets)
    w = load_weights(xor_folder, nets[0]["id"], allow_held_out=True)
    assert all(v.dtype == np.float64 for v in w.values())


def test_brute_force_certifies_everything_at_length_B(xor_folder):
    e = networks(xor_folder)[0]
    r = check_proof(brute_force_proof(xor_folder, e["id"]), xor_folder, e["id"])
    assert r["status"] == "ok" and r["certified"] == e["n_inputs"] == 4096 and r["length"] == e["B"]


def test_interval_leaves_are_sound_against_the_float_network(xor_folder):
    e = networks(xor_folder)[0]
    prog = make_program(build_any(xor_folder.build(e["setting"])), load_weights(xor_folder, e["id"]), Counter(), [2] * 12)
    module = load_module(xor_folder, e["id"])
    toks = np.array(list(itertools.product([0, 1], repeat=12)))
    with torch.no_grad():
        S = module(torch.nn.functional.one_hot(torch.as_tensor(toks), 2).double())[:, 1].numpy()
    rng = np.random.default_rng(3)
    certified = 0
    for _ in range(60):
        free = rng.choice(12, int(rng.integers(1, 6)), replace=False)
        base = rng.integers(0, 2, 12)
        ranges = [(0, 1) if p in free else (int(base[p]), int(base[p])) for p in range(12)]
        inside = np.all([(toks[:, p] >= lo) & (toks[:, p] <= hi) for p, (lo, hi) in enumerate(ranges)], axis=0)
        for lab in (0, 1):
            good, worst, _ = prog.run_interval(ranges, lab, Counter())
            true = (S[inside] if lab == 1 else -S[inside]).min()
            assert float(worst) <= true + 1e-9
            certified += good
    assert certified > 0  # the bound is useful, not only sound


def test_linear_only_rules_are_refused(xor_folder):
    e = networks(xor_folder)[0]
    tree = brute_force_proof(xor_folder, e["id"])["tree"]
    for extra, why in (
        ({"symmetry": True}, "symmetry does not hold"),
        ({"contract": [{"name": "C", "chain": ["a", "b"]}]}, "linear maps"),
        ({"approximate": [{"name": "P", "of": "x", "form": "dense", "values": [[0]]}]}, "unknown linear map"),
    ):
        r = check_proof({"schema": "split-tree-v1", "network": e["id"], "tree": tree, **extra}, xor_folder, e["id"])
        assert r["status"] == "rejected" and why in r["reason"], r["reason"]


def test_unsupported_operations_are_named():
    class Tanh(torch.nn.Module):
        def __init__(self):
            super().__init__()
            self.w = torch.nn.Parameter(torch.ones(2, 3))

        def forward(self, x):
            return torch.tanh(x @ self.w).sum(dim=1)

    with pytest.raises(UnsupportedOp, match="tanh"):
        build_any(Tanh())


def test_max2_still_uses_the_exact_linear_evaluator():
    folder = load_model_folder(REPO / "models" / "max2")
    graph = build_any(folder.build("v64"))
    assert not getattr(graph, "general", False)


def test_general_evaluator_agrees_with_the_linear_one_on_max2():
    from core.check.evaluate import Program
    from core.check.general import GeneralProgram, build_general_graph
    from core.check.trace import build_graph
    from core.inputs import all_inputs

    folder = load_model_folder(REPO / "models" / "max2")
    e = networks(folder, setting="v64")[0]
    module = folder.build("v64")
    w = load_weights(folder, e["id"])
    space = folder.input_space("v64")
    toks = all_inputs(space)
    labels = np.asarray(folder.task.label(toks, folder.sizes("v64")), dtype=np.int64)
    ok_lin, m_lin = Program(build_graph(module), w, Counter()).run_singles(toks, labels, Counter())
    ok_gen, m_gen = GeneralProgram(build_general_graph(module), w, Counter(), space).run_singles(toks, labels, Counter())
    assert np.array_equal(ok_lin, ok_gen) and np.allclose(m_lin, m_gen, rtol=0, atol=1e-12)


def test_unknown_keyword_arguments_are_refused_not_ignored():
    """torch.stack(..., axis=1) must not be read as dim 0 (found by the soundness review)."""

    class Axis(torch.nn.Module):
        def __init__(self):
            super().__init__()
            self.a = torch.nn.Parameter(torch.tensor([1.0, 0.0]))
            self.b = torch.nn.Parameter(torch.tensor([2.0, 0.0]))

        def forward(self, x):
            return x.sum(dim=1) @ torch.stack([self.a, self.b], axis=1)

    with pytest.raises(UnsupportedOp, match="axis"):
        build_any(Axis())


def test_functional_softmax_and_keyword_forms_are_accepted():
    class F(torch.nn.Module):
        def __init__(self):
            super().__init__()
            self.w = torch.nn.Parameter(torch.randn(2, 3))

        def forward(self, x):
            h = torch.nn.functional.softmax(x @ self.w, dim=-1)
            return h.sum(dim=1).transpose(dim0=0, dim1=1).transpose(0, 1)[:, 0:2] * x.size(dim=1)

    m = F()
    g = build_any(m)
    assert getattr(g, "general", False)
    w = {k: v.detach().numpy() for k, v in m.state_dict().items()}
    prog = make_program(g, w, Counter(), [2, 2])
    toks = np.array([[0, 1], [1, 1]])
    with torch.no_grad():
        ref = m(torch.nn.functional.one_hot(torch.as_tensor(toks), 2).float()).numpy()
    labels = ref.argmax(axis=1)
    ok, margins = prog.run_singles(toks, labels, Counter())
    true = np.sort(ref, axis=1)[:, -1] - np.sort(ref, axis=1)[:, -2]
    assert np.allclose(margins, true, atol=1e-5)


def test_interval_products_of_big_scalars_do_not_overflow():
    """Regression (19 October 2026, found by the rule route's review): a product of 0-d interval tensors went
    through np.where and np.minimum with Python ints, which raised OverflowError beyond 2**63 (scaling a
    softmax-weighted head, say), and the checker rejected the whole proof. Products must match the four
    corners exactly at any size, for 0-d operands and arrays alike."""
    import random

    import numpy as np

    from core.check.interval import IT, _obj

    rnd = random.Random(0)
    for _ in range(300):
        shape = rnd.choice([(), (3,)])

        def make(exact):
            n = int(np.prod(shape)) if shape else 1
            lo = [rnd.randint(-(1 << 90), 1 << 90) for _ in range(n)]
            w = [0 if exact else rnd.randint(0, 1 << 90) for _ in range(n)]
            arr = lambda v: _obj(np.array(v[0], dtype=object)) if not shape else _obj(np.array(v, dtype=object))
            return IT.exact(arr(lo), 0) if exact else IT(arr(lo), arr([a + b for a, b in zip(lo, w)]), 0)

        x, y = make(rnd.random() < 0.3), make(rnd.random() < 0.3)
        z = x * y
        flat = lambda a: np.asarray(a, dtype=object).reshape(-1)
        for xl, xh, yl, yh, zl, zh in zip(flat(x.lo), flat(x.hi), flat(y.lo), flat(y.hi), flat(z.lo), flat(z.hi)):
            corners = [xl * yl, xl * yh, xh * yl, xh * yh]
            assert zl == min(corners) and zh == max(corners)
