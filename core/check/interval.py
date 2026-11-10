"""Sound interval arithmetic on dyadic rationals, for networks with exp and softmax.

A value is an interval tensor: two integer arrays lo and hi (numpy object
arrays of Python ints) and one shared exponent, standing for the intervals
[lo * 2**exp, hi * 2**exp], elementwise. Sums, differences and products of
interval tensors are computed exactly, with no rounding at all. An interval
tensor whose lo and hi are the same array is an exact number; the network's
float weights are exact numbers (core.check.arith converts them exactly).

Only two operations round, and both round outwards (lower bounds down, upper
bounds up) at 2**-PRECISION:

- exp, enclosed by a Taylor series with a remainder bound after halving the
  argument, then squaring back (see exp_bounds), and
- the division inside softmax.

So every true value always lies inside its interval. docs/RULES.md has the
argument in words.
"""

from __future__ import annotations

from functools import lru_cache

import numpy as np

PRECISION = 120  # exp and softmax results are multiples of 2**-PRECISION, rounded outwards
MAX_EXP_LOG2 = 12  # exp is refused for arguments of 2**12 or more; below -2**12 it is enclosed by [0, 2**-PRECISION]


class IntervalError(ArithmeticError):
    pass


def _obj(x) -> np.ndarray:
    return x if isinstance(x, np.ndarray) and x.dtype == object else np.asarray(x, dtype=object)


def _floor_div(a: int, b: int) -> int:
    return a // b


def _ceil_div(a: int, b: int) -> int:
    return -((-a) // b)


class IT:
    """An interval tensor: [lo * 2**exp, hi * 2**exp] elementwise; exact when lo is hi."""

    __slots__ = ("lo", "hi", "exp")

    def __init__(self, lo, hi, exp: int):
        exact = hi is lo
        self.lo = _obj(lo)
        self.hi = self.lo if exact else _obj(hi)
        self.exp = int(exp)

    # construction ---------------------------------------------------------------
    @classmethod
    def exact(cls, ints, exp: int) -> "IT":
        a = _obj(ints)
        return cls(a, a, exp)

    @classmethod
    def from_exact(cls, e) -> "IT":
        """From a core.check.arith.Exact (the network's weights)."""
        return cls.exact(e.ints, e.exp)

    @classmethod
    def zeros(cls, shape) -> "IT":
        return cls.exact(np.zeros(shape, dtype=object), 0)

    # properties -----------------------------------------------------------------
    @property
    def is_exact(self) -> bool:
        return self.lo is self.hi

    @property
    def shape(self) -> tuple:
        return tuple(self.lo.shape)

    @property
    def ndim(self) -> int:
        return self.lo.ndim

    def _new(self, lo, hi_or_none, exp) -> "IT":
        """lo with hi; hi None means exact."""
        lo = _obj(lo)
        return IT(lo, lo if hi_or_none is None else hi_or_none, exp)

    def at(self, exp: int) -> "IT":
        """The same intervals written with a smaller (or equal) exponent: exact."""
        k = self.exp - exp
        if k < 0:
            raise RuntimeError("internal error: an interval can only move to a smaller exponent")
        if k == 0:
            return self
        m = 1 << k
        return self._new(self.lo * m, None if self.is_exact else _obj(self.hi * m), exp)

    # elementwise ----------------------------------------------------------------
    def __add__(self, other: "IT") -> "IT":
        a, b, e = _align(self, other)
        if a.is_exact and b.is_exact:
            return self._new(a.lo + b.lo, None, e)
        return self._new(a.lo + b.lo, _obj(a.hi + b.hi), e)

    def __sub__(self, other: "IT") -> "IT":
        a, b, e = _align(self, other)
        if a.is_exact and b.is_exact:
            return self._new(a.lo - b.lo, None, e)
        return self._new(a.lo - b.hi, _obj(a.hi - b.lo), e)

    def __neg__(self) -> "IT":
        if self.is_exact:
            return self._new(-self.lo, None, self.exp)
        return self._new(-self.hi, _obj(-self.lo), self.exp)

    def __mul__(self, other: "IT") -> "IT":
        a, b = self, other
        e = a.exp + b.exp
        if a.is_exact and b.is_exact:
            return self._new(a.lo * b.lo, None, e)
        # Products of 0-d operands come back as Python ints; _obj keeps them object arrays, so np.where and
        # np.minimum never try to fit an integer beyond 2**63 into int64.
        if b.is_exact:
            pos = _obj(b.lo >= 0).astype(bool)
            lo_if, lo_else, hi_if, hi_else = _obj(a.lo * b.lo), _obj(a.hi * b.lo), _obj(a.hi * b.lo), _obj(a.lo * b.lo)
            return self._new(_obj(np.where(pos, lo_if, lo_else)), _obj(np.where(pos, hi_if, hi_else)), e)
        if a.is_exact:
            pos = _obj(a.lo >= 0).astype(bool)
            lo_if, lo_else, hi_if, hi_else = _obj(a.lo * b.lo), _obj(a.lo * b.hi), _obj(a.lo * b.hi), _obj(a.lo * b.lo)
            return self._new(_obj(np.where(pos, lo_if, lo_else)), _obj(np.where(pos, hi_if, hi_else)), e)
        p = [_obj(a.lo * b.lo), _obj(a.lo * b.hi), _obj(a.hi * b.lo), _obj(a.hi * b.hi)]
        lo = _obj(np.minimum(_obj(np.minimum(p[0], p[1])), _obj(np.minimum(p[2], p[3]))))
        hi = _obj(np.maximum(_obj(np.maximum(p[0], p[1])), _obj(np.maximum(p[2], p[3]))))
        return self._new(lo, hi, e)

    def __matmul__(self, other: "IT") -> "IT":
        a, b = self, other
        e = a.exp + b.exp
        if a.is_exact and b.is_exact:
            return self._new(np.matmul(a.lo, b.lo), None, e)
        if b.is_exact:
            bp = np.where(_obj(b.lo > 0).astype(bool), b.lo, 0).astype(object)
            bn = np.where(_obj(b.lo < 0).astype(bool), b.lo, 0).astype(object)
            return self._new(np.matmul(a.lo, bp) + np.matmul(a.hi, bn), _obj(np.matmul(a.hi, bp) + np.matmul(a.lo, bn)), e)
        if a.is_exact:
            ap = np.where(_obj(a.lo > 0).astype(bool), a.lo, 0).astype(object)
            an = np.where(_obj(a.lo < 0).astype(bool), a.lo, 0).astype(object)
            return self._new(np.matmul(ap, b.lo) + np.matmul(an, b.hi), _obj(np.matmul(ap, b.hi) + np.matmul(an, b.lo)), e)
        # Both are intervals: products elementwise, then sums.
        a2 = a if a.ndim > 1 else a.unsqueeze(0)
        b2 = b if b.ndim > 1 else b.unsqueeze(-1)
        prod = a2.unsqueeze(-1) * b2.unsqueeze(-3)  # (..., m, k, n)
        out = prod.sum(-2)
        if a.ndim == 1:
            out = out[..., 0, :]
        if b.ndim == 1:
            out = out[..., 0]
        return out

    # shape --------------------------------------------------------------------
    def __getitem__(self, idx) -> "IT":
        lo = self.lo[idx]
        return self._new(lo, None if self.is_exact else _obj(self.hi[idx]), self.exp)

    def unsqueeze(self, dim: int) -> "IT":
        d = dim if dim >= 0 else self.ndim + 1 + dim
        lo = np.expand_dims(self.lo, d)
        return self._new(lo, None if self.is_exact else _obj(np.expand_dims(self.hi, d)), self.exp)

    def expand(self, shape) -> "IT":
        shape = list(shape)
        lead = len(shape) - self.ndim
        if lead < 0 or any(s == -1 for s in shape[:lead]):
            raise IntervalError("expand to fewer dimensions, or -1 for a new dimension")
        full = [s if s != -1 else self.shape[i - lead] for i, s in enumerate(shape)]
        lo = np.broadcast_to(self.lo, full)
        return self._new(lo, None if self.is_exact else _obj(np.broadcast_to(self.hi, full)), self.exp)

    @property
    def T(self) -> "IT":
        return self._new(self.lo.T, None if self.is_exact else _obj(self.hi.T), self.exp)

    def sum(self, dim: int) -> "IT":
        lo = _obj(np.sum(self.lo, axis=dim))
        return self._new(lo, None if self.is_exact else _obj(np.sum(self.hi, axis=dim)), self.exp)

    # bounds as fractions -------------------------------------------------------
    def bounds_at(self, index) -> tuple:
        """(lower, upper) of one element as (int, int) at exponent self.exp."""
        return int(self.lo[index]), int(self.hi[index])


def _align(a: IT, b: IT) -> tuple[IT, IT, int]:
    e = min(a.exp, b.exp)
    return a.at(e), b.at(e), e


def concat(values: list[IT], axis: int, stack: bool = False) -> IT:
    e = min(v.exp for v in values)
    vs = [v.at(e) for v in values]
    join = np.stack if stack else np.concatenate
    lo = _obj(join([v.lo for v in vs], axis=axis))
    if all(v.is_exact for v in vs):
        return IT(lo, lo, e)
    return IT(lo, _obj(join([v.hi for v in vs], axis=axis)), e)


# exp ----------------------------------------------------------------------------------
@lru_cache(maxsize=1 << 16)
def exp_bounds(X: int, e: int) -> tuple[int, int]:
    """(L, H) with L <= exp(X * 2**e) * 2**PRECISION <= H.

    Write x = X * 2**e and y = |x| / 2**m with m chosen so that y <= 2**-8. The
    series exp(y) = sum of y**k / k! has positive terms, each at most y times the
    one before, so after the terms up to k the rest is at most twice the next
    term. All terms are computed in integers at 2**-W, rounded down for the lower
    bound and up for the upper bound. For x < 0, exp(x) = 1 / exp(|x|). Then m
    squarings, again rounded outwards, give exp(x) = exp(+-y) ** (2**m).
    """
    P = PRECISION
    if X == 0:
        return 1 << P, 1 << P
    neg = X < 0
    A = -X if neg else X
    bl = A.bit_length()  # |x| < 2**(bl + e)
    if bl + e > MAX_EXP_LOG2:
        if neg:  # x <= -2**12, so 0 < exp(x) * 2**P < 1
            return 0, 1
        raise IntervalError(f"exp of a number of 2**{MAX_EXP_LOG2} or more")
    m = max(0, bl + e + 8)
    W = P + m + 32  # 32 guard bits; not a size
    s = e - m + W  # y * 2**W = A * 2**s
    if s >= 0:
        ylo = yhi = A << s
    else:
        ylo = A >> (-s)
        yhi = -((-A) >> (-s))
    one = 1 << W
    lo_sum = hi_sum = 0
    tlo = thi = one
    k = 0
    while True:
        lo_sum += tlo
        hi_sum += thi
        k += 1
        tlo = _floor_div(tlo * ylo, k << W)
        thi = _ceil_div(thi * yhi, k << W)
        if thi <= 1:
            hi_sum += 2 * thi  # the rest of the series
            break
    if neg:
        L = _floor_div(1 << (2 * W), hi_sum)
        H = _ceil_div(1 << (2 * W), lo_sum)
    else:
        L, H = lo_sum, hi_sum
    for _ in range(m):
        L = (L * L) >> W
        H = -((-(H * H)) >> W)
    d = W - P
    return L >> d, -((-H) >> d)


def _exp_endpoint(X: int, e: int, upper: bool) -> int:
    lo, hi = exp_bounds(int(X), int(e))
    return hi if upper else lo


def exp(x: IT) -> IT:
    """Elementwise exp, at exponent -PRECISION."""
    flat_lo = x.lo.reshape(-1)
    flat_hi = x.hi.reshape(-1)
    lo = np.array([_exp_endpoint(v, x.exp, False) for v in flat_lo], dtype=object).reshape(x.shape)
    hi = np.array([_exp_endpoint(v, x.exp, True) for v in flat_hi], dtype=object).reshape(x.shape)
    return IT(lo, hi, -PRECISION)


def softmax(x: IT, dim: int) -> IT:
    """Softmax along dim, at exponent -PRECISION.

    softmax(z) = softmax(z - c) for any c, so each row is first shifted by the
    largest upper bound (an exact subtraction). The weight of entry j,
    e_j / (e_j + sum over k != j of e_k), grows with e_j and shrinks with every
    other e_k; so it is at least lower(e_j) / (lower(e_j) + sum of upper(e_k)),
    and at most upper(e_j) / (upper(e_j) + sum of lower(e_k)). Divisions round
    outwards, and weights stay within [0, 1].
    """
    P = PRECISION
    lo = np.moveaxis(x.lo, dim, -1)
    hi = np.moveaxis(x.hi, dim, -1)
    c = np.max(hi, axis=-1, keepdims=True)
    # lower bounds of exp at the shifted lower ends, upper bounds at the shifted upper ends
    E_lo = exp(IT.exact(_obj(lo - c), x.exp)).lo
    E_hi = exp(IT.exact(_obj(hi - c), x.exp)).hi
    S_lo = np.sum(E_lo, axis=-1, keepdims=True)
    S_hi = np.sum(E_hi, axis=-1, keepdims=True)
    one = 1 << P
    shape = E_lo.shape
    a_lo = np.empty(shape, dtype=object)
    a_hi = np.empty(shape, dtype=object)
    for idx in np.ndindex(*shape):
        row = idx[:-1] + (0,)
        el, eh = int(E_lo[idx]), int(E_hi[idx])
        den_lo = el + int(S_hi[row]) - eh
        den_hi = eh + int(S_lo[row]) - el
        a_lo[idx] = max(0, _floor_div(el << P, den_lo)) if den_lo > 0 else 0
        a_hi[idx] = min(one, _ceil_div(eh << P, den_hi)) if den_hi > 0 else one
    return IT(np.moveaxis(a_lo, -1, dim), np.moveaxis(a_hi, -1, dim), -P)
