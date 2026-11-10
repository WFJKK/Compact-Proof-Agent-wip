"""Exact arithmetic for the checker.

Weights are float32, hence dyadic rationals. An Exact tensor stores Python
integers (in a numpy object array) and one shared power-of-two exponent:
value = ints * 2**exp. Sums, differences and products of Exact tensors are
exact; nothing is ever rounded. Numbers supplied by a proof file are parsed
into Fractions, never floats.

Operation counting lives in core.check.cost; this module only computes.
"""

from __future__ import annotations

from fractions import Fraction

import numpy as np

MAX_NUMBER_CHARS = 200
# Proof numbers must be dyadic (value = p / 2**k), like the float weights they
# describe. These bound p and k so that sums and products of proof numbers stay
# small: an arbitrary rational with a large or coprime denominator could make
# the exact arithmetic blow up while every operation still counted as 1.
MAX_NUMBER_BITS = 160
MAX_DYADIC_EXP = 1100  # comfortably covers float32 (and float64) magnitudes

# Decimals and fractions only; exponent notation is refused before Fraction()
# sees it, so a short string like "1e-99999999" cannot build a huge number.
import re as _re  # noqa: E402

_NUMBER_STRING = _re.compile(r"[+-]?(?:[0-9]+|[0-9]+/[0-9]+|[0-9]*\.[0-9]+|[0-9]+\.[0-9]*)")


class ProofNumberError(ValueError):
    pass


def _check_dyadic(f: Fraction) -> Fraction:
    """A proof number is p / 2**k with |p| and k bounded; reject anything else."""
    d = f.denominator
    if d & (d - 1) != 0:  # not a power of two
        raise ProofNumberError("numbers must be dyadic (denominator a power of two), like the float weights")
    if (d.bit_length() - 1) > MAX_DYADIC_EXP or f.numerator.bit_length() > MAX_NUMBER_BITS:
        raise ProofNumberError("number too large")
    return f


class Exact:
    __slots__ = ("ints", "exp")

    def __init__(self, ints, exp: int):
        self.ints = ints if isinstance(ints, np.ndarray) and ints.dtype == object else np.asarray(ints, dtype=object)
        self.exp = int(exp)

    # construction -----------------------------------------------------------
    @staticmethod
    def from_float(arr) -> "Exact":
        """Exact conversion of a float32/float64 array (every float is a dyadic rational)."""
        a = np.asarray(arr, dtype=np.float64)
        if not np.all(np.isfinite(a)):
            raise ValueError("weights must be finite")
        mant, ex = np.frexp(a)  # a = mant * 2**ex, 0.5 <= |mant| < 1 or mant == 0
        m = (mant * 2.0**53).astype(np.int64)  # exact: |mant| * 2**53 < 2**53
        e = ex.astype(np.int64) - 53
        nz = m != 0
        if not nz.any():
            return Exact(np.zeros(a.shape, dtype=object), 0)
        e0 = int(e[nz].min())
        shifts = (e - e0).astype(np.int64)
        flat_m = m.reshape(-1).tolist()
        flat_s = shifts.reshape(-1).tolist()
        ints = np.array([mi << si if mi else 0 for mi, si in zip(flat_m, flat_s)], dtype=object).reshape(a.shape)
        return Exact(ints, e0)._normalised()

    @staticmethod
    def zeros(shape) -> "Exact":
        z = np.empty(shape, dtype=object)
        z.fill(0)
        return Exact(z, 0)

    def _normalised(self) -> "Exact":
        """Remove common factors of two, keeping integers small."""
        flat = [int(x) for x in self.ints.reshape(-1) if x]
        if not flat:
            return Exact(self.ints, 0)
        tz = min((x & -x).bit_length() - 1 for x in flat)
        if tz <= 0:
            return self
        return Exact(self.ints // (1 << tz), self.exp + tz)

    # alignment -------------------------------------------------------------
    @staticmethod
    def _shift(ints, k: int):
        if k == 0:
            return ints
        return ints * (1 << k)

    @staticmethod
    def align(a: "Exact", b: "Exact"):
        e = min(a.exp, b.exp)
        return Exact._shift(a.ints, a.exp - e), Exact._shift(b.ints, b.exp - e), e

    # arithmetic ------------------------------------------------------------
    def __add__(self, other: "Exact") -> "Exact":
        x, y, e = Exact.align(self, other)
        return Exact(x + y, e)

    def __sub__(self, other: "Exact") -> "Exact":
        x, y, e = Exact.align(self, other)
        return Exact(x - y, e)

    def __neg__(self) -> "Exact":
        return Exact(-self.ints, self.exp)

    def abs(self) -> "Exact":
        return Exact(np.abs(self.ints), self.exp)

    def half(self) -> "Exact":
        return Exact(self.ints, self.exp - 1)

    def matmul_t(self, w: "Exact") -> "Exact":
        """self @ w.T, with w of shape (out, in) like a Linear weight."""
        return Exact(np.dot(self.ints, w.ints.T), self.exp + w.exp)

    def matmul(self, other: "Exact") -> "Exact":
        return Exact(np.dot(self.ints, other.ints), self.exp + other.exp)

    def sum(self, axis) -> "Exact":
        return Exact(self.ints.sum(axis=axis), self.exp)

    def min(self, axis) -> "Exact":
        return Exact(self.ints.min(axis=axis), self.exp)

    def max(self, axis) -> "Exact":
        return Exact(self.ints.max(axis=axis), self.exp)

    def __getitem__(self, idx) -> "Exact":
        sub = self.ints[idx]
        if not isinstance(sub, np.ndarray):
            sub = np.array(sub, dtype=object)
        return Exact(sub, self.exp)

    @property
    def shape(self):
        return self.ints.shape

    def positive(self) -> np.ndarray:
        """Elementwise value > 0 (exact; 2**exp > 0)."""
        return np.asarray(self.ints > 0, dtype=bool)

    def to_fractions(self) -> np.ndarray:
        scale = Fraction(2) ** self.exp
        return np.vectorize(lambda x: Fraction(x) * scale, otypes=[object])(self.ints)

    def to_float(self) -> np.ndarray:
        return np.vectorize(lambda x: float(Fraction(x) * Fraction(2) ** self.exp), otypes=[float])(self.ints)


def parse_number(v) -> Fraction:
    """A number from a proof file: an integer, a string like "-3/4" or "1.25", or a finite float."""
    if isinstance(v, bool):
        raise ProofNumberError("booleans are not numbers")
    if isinstance(v, int):
        if v.bit_length() > MAX_NUMBER_BITS:
            raise ProofNumberError("number too large")
        return Fraction(v)
    if isinstance(v, float):
        if v != v or v in (float("inf"), float("-inf")):
            raise ProofNumberError("numbers must be finite")
        return _check_dyadic(Fraction(v))  # every finite float is dyadic
    if isinstance(v, str):
        s = v.strip()
        if len(s) > MAX_NUMBER_CHARS:
            raise ProofNumberError("number string too long")
        if not _NUMBER_STRING.fullmatch(s):
            raise ProofNumberError(f"not a number (integers, p/q or decimals only, no exponents): {v!r}")
        try:
            f = Fraction(s)
        except (ValueError, ZeroDivisionError) as exc:
            raise ProofNumberError(f"not a number: {v!r}") from exc
        return _check_dyadic(f)
    raise ProofNumberError(f"not a number: {v!r}")


def frac_of(x: Exact) -> np.ndarray:
    return x.to_fractions()
