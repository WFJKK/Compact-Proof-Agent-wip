"""Approximations of a contracted matrix, for the approximate rule.

A proof file may give a simpler matrix P for a contracted product W. The
checker computes eps = max |W - P| over all entries exactly; interval leaves
may then bound min over tokens t of (W[l,t] - W[j,t]) from below by
min over t of (P[l,t] - P[j,t]) - 2*eps, computed from P's form:

    dense         P written out in full
    low_rank      P = left @ right, left (outputs x r), right (r x inputs)
    row_segments  each row of P is constant on consecutive column ranges,
                  given as [start, end, value] triples covering every column

What a range of s tokens costs, per the cost model (everything the checker does):

    dense         2 per token per output (a difference and a comparison)
    low_rank      2r per token (the minimum and maximum of each factor row over
                  the range) plus 3r per output (a difference, a sign test and
                  a multiply-add per factor)
    row_segments  2 per merge step of the two rows' segments (a difference and
                  a comparison, like a dense range per token, so it pays only
                  where segments are long) plus 2 per row to locate its segments
                  (two lookups in a column index built when the approximation
                  is read)

Subtracting 2*eps from each output is charged by the caller.
"""

from __future__ import annotations

from fractions import Fraction

import numpy as np

from .arith import Exact, ProofNumberError, parse_number
from .cost import Counter


class ApproximationError(ValueError):
    pass


def _matrix(rows, n_rows: int | None, n_cols: int | None, what: str) -> np.ndarray:
    if not isinstance(rows, list) or not rows or not all(isinstance(r, list) for r in rows):
        raise ApproximationError(f"{what} must be a list of rows")
    if n_rows is not None and len(rows) != n_rows:
        raise ApproximationError(f"{what} needs {n_rows} rows")
    width = len(rows[0])
    if n_cols is not None and width != n_cols:
        raise ApproximationError(f"{what} needs {n_cols} columns")
    if any(len(r) != width for r in rows):
        raise ApproximationError(f"{what} rows differ in length")
    try:
        return np.array([[parse_number(v) for v in r] for r in rows], dtype=object)
    except ProofNumberError as exc:
        raise ApproximationError(f"{what}: {exc}") from exc


class Approximation:
    def __init__(self, name: str, of: str, spec: dict, W: Exact, counter: Counter):
        self.name, self.of = name, of
        self.form = spec.get("form")
        n_out, n_in = W.shape
        self.n_out, self.n_in = n_out, n_in
        Wf = W.to_fractions()
        # read (cost-v4): 1 per number of P's form, the numbers the proof supplies; its name, map and form
        # are plan, which is free
        if self.form == "dense":
            self.P = _matrix(spec.get("values"), n_out, n_in, "values")
            counter.add("read", n_out * n_in)
            self.eps = max(abs(x) for x in (Wf - self.P).reshape(-1))
            counter.add("approximate", 2 * n_out * n_in)
        elif self.form == "low_rank":
            self.F = _matrix(spec.get("left"), n_out, None, "left")
            r = self.F.shape[1]
            if not 0 < r <= min(n_out, n_in):  # a rank above min(rows, cols) is never needed
                raise ApproximationError(f"low_rank inner dimension must be between 1 and {min(n_out, n_in)}, not {r}")
            self.G = _matrix(spec.get("right"), r, n_in, "right")
            counter.add("read", n_out * r + r * n_in)
            P = np.dot(self.F, self.G)
            counter.add("approximate", n_out * r * n_in)
            self.eps = max(abs(x) for x in (Wf - P).reshape(-1))
            counter.add("approximate", 2 * n_out * n_in)
        elif self.form == "row_segments":
            rows = spec.get("rows")
            if not isinstance(rows, list) or len(rows) != n_out:
                raise ApproximationError(f"rows needs one list of segments per output ({n_out})")
            self.seg = []
            self.index = []  # per row, the segment holding each column, so a range's segments are two lookups
            eps = Fraction(0)
            n_segments = 0
            for i, segs in enumerate(rows):
                if not isinstance(segs, list) or not segs:
                    raise ApproximationError(f"row {i} has no segments")
                starts, ends, vals = [], [], []
                index = np.empty(n_in, dtype=np.int64)
                expect = 0
                for s in segs:
                    if not (isinstance(s, list) and len(s) == 3 and all(isinstance(v, int) and not isinstance(v, bool) for v in s[:2])):
                        raise ApproximationError(f"row {i}: segments are [start, end, value]")
                    a, b = s[0], s[1]
                    if a != expect or b < a or b >= n_in:
                        raise ApproximationError(f"row {i}: segments must cover the columns in order")
                    try:
                        v = parse_number(s[2])
                    except ProofNumberError as exc:
                        raise ApproximationError(f"row {i}: {exc}") from exc
                    seg_w = W.ints[i, a : b + 1]
                    hi = Fraction(int(seg_w.max())) * Fraction(2) ** W.exp
                    lo = Fraction(int(seg_w.min())) * Fraction(2) ** W.exp
                    eps = max(eps, abs(hi - v), abs(lo - v))
                    index[a : b + 1] = len(starts)
                    starts.append(a)
                    ends.append(b)
                    vals.append(v)
                    expect = b + 1
                if expect != n_in:
                    raise ApproximationError(f"row {i}: segments must reach the last column")
                self.seg.append((np.array(starts), np.array(ends), vals))
                self.index.append(index)
                n_segments += len(starts)
            self.eps = eps
            counter.add("read", 3 * n_segments)  # each segment's start, end and value
            # Per entry: the difference and comparison for eps (2) and the index entry (1); per segment:
            # its two error terms against the running eps (2).
            counter.add("approximate", 3 * n_out * n_in + 2 * n_segments)
        else:
            raise ApproximationError(f"unknown form {self.form!r}; use dense, low_rank or row_segments")

    def _clip(self, i: int, lo: int, hi: int):
        """The segments of row i that meet [lo, hi], clipped to it: two index lookups, charged by the caller."""
        starts, ends, vals = self.seg[i]
        k0, k1 = int(self.index[i][lo]), int(self.index[i][hi]) + 1
        return [(max(int(starts[k]), lo), min(int(ends[k]), hi), vals[k]) for k in range(k0, k1)]

    def row_min_diffs(self, l: int, lo: int, hi: int, counter: Counter) -> np.ndarray:
        """For every output j: a lower bound on min over t in [lo, hi] of P[l, t] - P[j, t].

        Charges what it does (see the module docstring); the caller charges the eps subtraction.
        """
        s = hi - lo + 1
        if self.form == "dense":
            d = self.P[l, lo : hi + 1] - self.P[:, lo : hi + 1]
            counter.add("interval", 2 * self.n_out * s)
            return d.min(axis=1)
        if self.form == "low_rank":
            r = self.G.shape[0]
            gmin = self.G[:, lo : hi + 1].min(axis=1)
            gmax = self.G[:, lo : hi + 1].max(axis=1)
            c = self.F[l] - self.F
            out = np.empty(self.n_out, dtype=object)
            for j in range(self.n_out):
                out[j] = sum((ck * (gmin[k] if ck >= 0 else gmax[k]) for k, ck in enumerate(c[j])), Fraction(0))
            counter.add("interval", 2 * r * s + 3 * self.n_out * r)
            return out
        # row_segments: merge the two rows' segments over [lo, hi]. Each merge step takes a difference
        # and a comparison, so it costs 2, as a dense range costs 2 per token (cost-v2; cost-v1 charged 1,
        # which made an exact one-entry-per-segment "approximation" look half as long as the dense check
        # it repeats). Locating a row's segments is two index lookups.
        mine = self._clip(l, lo, hi)
        out = np.empty(self.n_out, dtype=object)
        ops = 0
        for j in range(self.n_out):
            theirs = self._clip(j, lo, hi)
            a = b = 0
            best = None
            while a < len(mine) and b < len(theirs):
                d = mine[a][2] - theirs[b][2]
                best = d if best is None or d < best else best
                ops += 1
                if mine[a][1] < theirs[b][1]:
                    a += 1
                elif mine[a][1] > theirs[b][1]:
                    b += 1
                else:
                    a += 1
                    b += 1
            out[j] = best
        counter.add("interval", 2 * ops + 2 * (self.n_out + 1))
        return out
