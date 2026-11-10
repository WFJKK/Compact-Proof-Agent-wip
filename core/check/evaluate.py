"""Exact evaluation of a traced graph.

Two modes:

- singles: a batch of individual inputs, evaluated exactly; an input is
  certified if its label's output is strictly larger than every other output.
- interval: one set of inputs (an inclusive range of tokens per position),
  evaluated with exact bounds; the set is certified if a lower bound on the
  margin between the label's output and every other output is positive.

One-hot inputs stay symbolic until the first linear map, so a linear map
applied to a token set sees the exact columns of those tokens.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from fractions import Fraction

import numpy as np

from .approx import Approximation
from .arith import Exact
from .cost import Counter
from .trace import Graph, UnsupportedOp


class CheckError(ValueError):
    """A malformed part of a proof file; the whole proof is rejected."""


@dataclass
class Lin:
    name: str
    W: Exact  # (out, in), like a torch Linear weight
    b: Exact | None  # (out,)
    chain: list[str] = field(default_factory=list)


@dataclass
class Step:
    name: str
    op: str  # input | linear | sum | add
    args: list[str]
    lin: Lin | None = None
    dim: int | None = None


@dataclass
class OneHot:
    """Concrete tokens (batch, positions) or symbolic ranges [(lo, hi), ...]."""

    tokens: np.ndarray | None = None
    ranges: list | None = None
    summed: bool = False


@dataclass
class Box:
    center: Exact
    radius: Exact  # >= 0, same shape as center


def _matvec(W: Exact, v: Exact) -> Exact:
    return Exact(np.dot(W.ints, v.ints), W.exp + v.exp)


def _matmul(A: Exact, B: Exact) -> Exact:
    return Exact(np.dot(A.ints, B.ints), A.exp + B.exp)


def _abs(W: Exact) -> Exact:
    return Exact(np.abs(W.ints), W.exp)


def _to_frac(ints, exp: int):
    scale = Fraction(2) ** exp
    return np.array([Fraction(int(x)) * scale for x in np.asarray(ints).reshape(-1)], dtype=object).reshape(
        np.asarray(ints).shape
    )


def _float(x: int, exp: int) -> float:
    try:
        return math.ldexp(float(int(x)), exp)
    except OverflowError:
        return float("inf") if x > 0 else float("-inf")


class Program:
    """The graph with exact weights, after any contractions."""

    def __init__(self, graph: Graph, weights: dict[str, np.ndarray], counter: Counter):
        self.exact = {}
        n_params = 0
        for k, v in weights.items():
            self.exact[k] = Exact.from_float(v)
            n_params += int(np.asarray(v).size)
        counter.add("extract", n_params)
        self.n_params = n_params
        self.steps: list[Step] = []
        for n in graph.nodes:
            if n.op == "linear":
                if n.weight not in self.exact or (n.bias and n.bias not in self.exact):
                    raise CheckError(f"weights for {n.name} are missing")
                lin = Lin(n.name, self.exact[n.weight], self.exact[n.bias] if n.bias else None, [n.name])
                self.steps.append(Step(n.name, "linear", list(n.args), lin=lin))
            else:
                self.steps.append(Step(n.name, n.op, list(n.args), dim=n.dim))
        self.input = graph.input
        self.output = graph.output
        self.contracted: dict[str, Lin] = {}

    def step(self, name: str) -> Step:
        for s in self.steps:
            if s.name == name:
                return s
        raise KeyError(name)

    def users(self, name: str) -> list[str]:
        out = [s.name for s in self.steps if name in s.args]
        if name == self.output:
            out.append("<output>")
        return out

    def linear(self, name: str) -> Lin:
        s = self.step(name)
        if s.op != "linear":
            raise KeyError(name)
        return s.lin

    # contract rule -------------------------------------------------------------
    def contract(self, cname: str, chain: list, counter: Counter) -> Lin:
        names = {s.name for s in self.steps}
        if not isinstance(cname, str) or not cname or cname in names:
            raise CheckError(f"contraction name {cname!r} is empty or already used")
        if not isinstance(chain, list) or len(chain) < 2 or not all(isinstance(n, str) for n in chain):
            raise CheckError("a contraction chain lists at least two linear maps by name")
        if len(set(chain)) != len(chain):
            raise CheckError("a contraction chain repeats a map")
        for i, n in enumerate(chain):
            if n not in names or self.step(n).op != "linear":
                raise CheckError(f"{n!r} is not a linear map of the network")
            if i > 0:
                prev = chain[i - 1]
                if self.step(n).args != [prev] or self.users(prev) != [n]:
                    raise CheckError(f"{prev!r} feeds more than {n!r}; only consecutive single-use maps contract")
        lins = [self.step(n).lin for n in chain]
        # Weight product W_k ... W_1, multiplied in the cheapest order.
        mats = [l.W for l in reversed(lins)]
        dims = [mats[0].shape[0]] + [m.shape[1] for m in mats]
        k = len(mats)
        cost = [[0] * k for _ in range(k)]
        split = [[0] * k for _ in range(k)]
        for length in range(2, k + 1):
            for i in range(k - length + 1):
                j = i + length - 1
                cost[i][j] = None
                for s in range(i, j):
                    c = cost[i][s] + cost[s + 1][j] + dims[i] * dims[s + 1] * dims[j + 1]
                    if cost[i][j] is None or c < cost[i][j]:
                        cost[i][j], split[i][j] = c, s

        def product(i, j):
            if i == j:
                return mats[i]
            s = split[i][j]
            left, right = product(i, s), product(s + 1, j)
            counter.add("contract", dims[i] * dims[s + 1] * dims[j + 1])
            return _matmul(left, right)

        W = product(0, k - 1)._normalised()
        b = None
        for l in lins:  # bias pushed through, input side first
            if b is not None:
                b = _matvec(l.W, b)
                counter.add("contract", l.W.shape[0] * l.W.shape[1])
            if l.b is not None:
                b = l.b if b is None else b + l.b
                counter.add("contract", l.W.shape[0])
        lin = Lin(cname, W, b, list(chain))
        first, last = chain[0], chain[-1]
        new_step = Step(cname, "linear", list(self.step(first).args), lin=lin)
        pos = [i for i, s in enumerate(self.steps) if s.name == last][0]
        self.steps[pos] = new_step
        self.steps = [s for s in self.steps if s.name not in chain]
        for s in self.steps:
            s.args = [cname if a == last else a for a in s.args]
        if self.output == last:
            self.output = cname
        self.contracted[cname] = lin
        return lin

    # singles ---------------------------------------------------------------------
    def run_singles(self, tokens: np.ndarray, labels: np.ndarray, counter: Counter, chunk: int = 2048):
        """Exact evaluation of each input; returns (certified mask, minimum margins as floats)."""
        ok = np.zeros(len(tokens), dtype=bool)
        margins = np.zeros(len(tokens), dtype=float)
        for i in range(0, len(tokens), chunk):
            t, lab = tokens[i : i + chunk], labels[i : i + chunk]
            logits = self._run_concrete(t, counter)
            n_out = logits.shape[1]
            if lab.min() < 0 or lab.max() >= n_out:
                raise CheckError("labels outside the network's outputs")
            own = logits.ints[np.arange(len(t)), lab]
            diff = own[:, None] - logits.ints
            pos = np.asarray(diff > 0, dtype=bool)
            pos[np.arange(len(t)), lab] = True
            ok[i : i + chunk] = pos.all(axis=1)
            masked = diff.copy()
            masked[np.arange(len(t)), lab] = None
            for r in range(len(t)):
                vals = [x for x in masked[r] if x is not None]
                margins[i + r] = _float(min(vals), logits.exp) if vals else float("inf")
            counter.add("single", len(t) * (n_out - 1))
        return ok, margins

    def _run_concrete(self, tokens: np.ndarray, counter: Counter) -> Exact:
        B = len(tokens)
        vals = {}
        for st in self.steps:
            if st.op == "input":
                vals[st.name] = OneHot(tokens=tokens)
            elif st.op == "sum":
                x = vals[st.args[0]]
                if isinstance(x, OneHot):
                    if x.summed or st.dim not in (1, -2):
                        raise UnsupportedOp("a sum over one-hot inputs must be over the positions dimension")
                    vals[st.name] = OneHot(tokens=x.tokens, summed=True)
                else:
                    axis = st.dim
                    res = x.sum(axis)
                    counter.add("single", int(np.asarray(res.ints).size) * (x.shape[axis] - 1))
                    vals[st.name] = res
            elif st.op == "linear":
                vals[st.name] = self._linear_concrete(st.lin, vals[st.args[0]], counter)
            elif st.op == "add":
                a, b = vals[st.args[0]], vals[st.args[1]]
                if isinstance(a, OneHot) or isinstance(b, OneHot):
                    raise UnsupportedOp("adding one-hot inputs directly")
                res = a + b
                counter.add("single", int(np.asarray(res.ints).size))
                vals[st.name] = res
        out = vals[self.output]
        if not isinstance(out, Exact) or out.ints.ndim != 2 or out.shape[0] != B:
            raise UnsupportedOp("the network's output must be (batch, outputs) logits")
        return out

    def _linear_concrete(self, lin: Lin, x, counter: Counter) -> Exact:
        W = lin.W
        out, inn = W.shape
        if isinstance(x, OneHot):
            B, P = x.tokens.shape
            cols = W.ints[:, x.tokens]  # (out, B, P)
            ints = cols.sum(axis=2).T if x.summed else cols.transpose(1, 2, 0)
            res = Exact(np.ascontiguousarray(ints), W.exp)
            counter.add("single", B * P * out)
        else:
            if x.shape[-1] != inn:
                raise UnsupportedOp(f"shape mismatch at {lin.name}")
            res = x.matmul_t(W)
            counter.add("single", int(np.asarray(x.ints).size) * out)
        if lin.b is not None:
            res = res + lin.b
            counter.add("single", int(np.asarray(res.ints).size))
        return res

    # interval --------------------------------------------------------------------
    def run_token_interval(self, ranges: list, label: int, counter: Counter):
        raise CheckError("the token_interval rule is for networks beyond linear maps; here interval leaves already "
                         "use each token's exact row once the maps are contracted")

    def run_interval(self, ranges: list, label: int, counter: Counter, approx: Approximation | None = None):
        """Bounds over all inputs in the product of ranges, all with the same label.

        Returns (certified, lower bound on the worst margin, the output that attains it).
        """
        vals = {}
        for st in self.steps:
            if st.op == "input":
                vals[st.name] = OneHot(ranges=ranges)
            elif st.op == "sum":
                x = vals[st.args[0]]
                if isinstance(x, OneHot):
                    if x.summed or st.dim not in (1, -2):
                        raise UnsupportedOp("a sum over one-hot inputs must be over the positions dimension")
                    vals[st.name] = OneHot(ranges=x.ranges, summed=True)
                else:
                    axis = st.dim - 1 if st.dim > 0 else st.dim
                    if isinstance(x, Box):
                        res = Box(x.center.sum(axis), x.radius.sum(axis))
                        counter.add("interval", 2 * int(np.asarray(res.center.ints).size) * (x.center.shape[axis] - 1))
                    else:
                        res = x.sum(axis)
                        counter.add("interval", int(np.asarray(res.ints).size) * (x.shape[axis] - 1))
                    vals[st.name] = res
            elif st.op == "linear":
                x = vals[st.args[0]]
                if st.name == self.output:
                    return self._final_margins(st.lin, x, label, counter, approx)
                vals[st.name] = self._linear_interval(st.lin, x, counter)
            elif st.op == "add":
                a, b = vals[st.args[0]], vals[st.args[1]]
                if isinstance(a, OneHot) or isinstance(b, OneHot):
                    raise UnsupportedOp("adding one-hot inputs directly")
                if isinstance(a, Box) or isinstance(b, Box):
                    a = a if isinstance(a, Box) else Box(a, Exact.zeros(a.shape))
                    b = b if isinstance(b, Box) else Box(b, Exact.zeros(b.shape))
                    res = Box(a.center + b.center, a.radius + b.radius)
                    counter.add("interval", 2 * int(np.asarray(res.center.ints).size))
                else:
                    res = a + b
                    counter.add("interval", int(np.asarray(res.ints).size))
                vals[st.name] = res
        return self._margins_from_value(vals[self.output], label, counter)

    def _linear_interval(self, lin: Lin, x, counter: Counter):
        W = lin.W
        out, inn = W.shape
        if isinstance(x, OneHot):
            if x.summed:
                c, r = self._onehot_box(W, x.ranges, counter)
                res = Box(c, r)
            else:
                parts = [self._onehot_box(W, [rg], counter) for rg in x.ranges]
                res = Box(
                    Exact(np.stack([p[0].ints for p in parts]), parts[0][0].exp),
                    Exact(np.stack([p[1].ints for p in parts]), parts[0][1].exp),
                )
        elif isinstance(x, Box):
            if x.center.shape[-1] != inn:
                raise UnsupportedOp(f"shape mismatch at {lin.name}")
            rows = int(np.asarray(x.center.ints).size) // inn
            res = Box(x.center.matmul_t(W), x.radius.matmul_t(_abs(W)))
            counter.add("interval", 2 * rows * inn * out)
        else:
            if x.shape[-1] != inn:
                raise UnsupportedOp(f"shape mismatch at {lin.name}")
            res = x.matmul_t(W)
            counter.add("interval", int(np.asarray(x.ints).size) * out)
        if lin.b is not None:
            if isinstance(res, Box):
                res = Box(res.center + lin.b, res.radius)
                counter.add("interval", int(np.asarray(res.center.ints).size))
            else:
                res = res + lin.b
                counter.add("interval", int(np.asarray(res.ints).size))
        return res

    @staticmethod
    def _onehot_box(W: Exact, ranges, counter: Counter):
        """Centre and radius (both at exponent W.exp - 1) of the sum over positions of W's columns."""
        out = W.shape[0]
        center = np.zeros(out, dtype=object)
        radius = np.zeros(out, dtype=object)
        for lo, hi in ranges:
            if lo == hi:
                center = center + 2 * W.ints[:, lo]
                counter.add("interval", out)
            else:
                block = W.ints[:, lo : hi + 1]
                mn, mx = block.min(axis=1), block.max(axis=1)
                center = center + mn + mx
                radius = radius + mx - mn
                counter.add("interval", 2 * out * (hi - lo + 1))
        return Exact(center, W.exp - 1), Exact(radius, W.exp - 1)

    def _final_margins(self, lin: Lin, x, label: int, counter: Counter, approx: Approximation | None):
        W = lin.W
        n_out, inn = W.shape
        if not 0 <= label < n_out:
            raise CheckError("label outside the network's outputs")
        if isinstance(x, OneHot):
            if not x.summed:
                raise UnsupportedOp("an output computed per position")
            if approx is not None and approx.of != lin.name:
                raise CheckError(f"approximation {approx.name!r} is of {approx.of!r}, not of {lin.name!r}")
            if approx is not None:
                lower = np.array([Fraction(0)] * n_out, dtype=object)
                for lo, hi in x.ranges:
                    if lo == hi:
                        lower = lower + _to_frac(W.ints[label, lo] - W.ints[:, lo], W.exp)
                        counter.add("interval", n_out)
                    else:
                        lower = lower + (approx.row_min_diffs(label, lo, hi, counter) - 2 * approx.eps)
                        counter.add("interval", n_out)  # subtracting the error from every output
                if lin.b is not None:
                    lower = lower + _to_frac(lin.b.ints[label] - lin.b.ints, lin.b.exp)
                    counter.add("interval", n_out)
                return self._decide(lower, label, counter, as_fraction=True)
            ints = np.zeros(n_out, dtype=object)
            for lo, hi in x.ranges:
                d = W.ints[label, lo : hi + 1] - W.ints[:, lo : hi + 1]
                ints = ints + d.min(axis=1)
                counter.add("interval", 2 * n_out * (hi - lo + 1) if hi > lo else n_out)
            lower = Exact(ints, W.exp)
        elif isinstance(x, Box):
            if x.center.ints.ndim != 1 or x.center.shape[0] != inn:
                raise UnsupportedOp(f"shape mismatch at {lin.name}")
            diff = Exact(W.ints[label] - W.ints, W.exp)
            lower = _matvec(diff, x.center) - _matvec(_abs(diff), x.radius)
            counter.add("interval", 3 * n_out * inn)
        else:
            if x.ints.ndim != 1 or x.shape[0] != inn:
                raise UnsupportedOp(f"shape mismatch at {lin.name}")
            logits = _matvec(W, x)
            lower = Exact(logits.ints[label] - logits.ints, logits.exp)
            counter.add("interval", n_out * inn)
        if lin.b is not None:
            lower = lower + Exact(lin.b.ints[label] - lin.b.ints, lin.b.exp)
            counter.add("interval", n_out)
        return self._decide(lower, label, counter)

    def _margins_from_value(self, v, label: int, counter: Counter):
        if isinstance(v, Box):
            if v.center.ints.ndim != 1:
                raise UnsupportedOp("the network's output must be one logit vector")
            lo_l = Exact(v.center.ints[label : label + 1], v.center.exp) - Exact(v.radius.ints[label : label + 1], v.radius.exp)
            hi_all = v.center + v.radius
            lower = Exact(lo_l.ints - 0, lo_l.exp) - hi_all
            counter.add("interval", 2 * v.center.shape[0])
            return self._decide(Exact(lower.ints, lower.exp), label, counter)
        if isinstance(v, Exact):
            if v.ints.ndim != 1:
                raise UnsupportedOp("the network's output must be one logit vector")
            return self._decide(Exact(v.ints[label] - v.ints, v.exp), label, counter)
        raise UnsupportedOp("the network's output must be computed from its input")

    @staticmethod
    def _decide(lower, label: int, counter: Counter, as_fraction: bool = False):
        n = len(lower) if as_fraction else lower.shape[0]
        counter.add("interval", n - 1)
        if as_fraction:
            vals = [(lower[j], j) for j in range(n) if j != label]
            worst, j = min(vals, key=lambda p: p[0]) if vals else (Fraction(1), -1)
            return bool(worst > 0), worst, j
        ints = lower.ints
        best = None
        for j in range(n):
            if j == label:
                continue
            if best is None or ints[j] < ints[best]:
                best = j
        if best is None:
            return True, Fraction(1), -1
        worst = Fraction(int(ints[best])) * Fraction(2) ** lower.exp
        return bool(ints[best] > 0), worst, best
