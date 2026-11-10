"""token_convex: token_interval, plus the softmax's own structure for leaves where several positions vary.

The idea is Gross et al.'s convexity argument for attention, in a form that does not know the model: an
attention output is a softmax-weighted average of per-position rows, and the weights of one softmax sum to
one. token_interval bounds each weight by an interval and each term separately, so with several varying
positions it lets every non-maximal position take its largest weight at once, which can add up to far more
than one. Here a softmax over the positions keeps its scores (their box, and each token's own score when they
are exact per token), and the weighted sum's worst case is found exactly (SOUNDNESS.md has the argument):

    min of  sum_p u_p c_p / sum_p u_p,   u_p = exp(score_p)

over the scores' box (levels 0 and 2) or over every choice of one token per position, each with its own
score and difference (levels 1 and 3). Over a box the minimum puts every u_p at an end of its range, the
upper end exactly where c_p is below the minimum, so sorting the c_p and trying the n + 1 splits finds it.
Over token choices, Dinkelbach's method finds it: at a ratio lam each position independently minimises
u (c - lam), and the ratio of that choice is lower unless lam is the minimum. Levels 0 and 1 take each
token's smallest difference over every other output (one search per leaf, as Gross et al. pessimise over the
wrong logit first); levels 2 and 3 are per output, for outputs still unsettled. Everything is exact rational
arithmetic; only exp is enclosed, at 2**-120, outwards.

Reuse makes such leaves cheap enough to matter, and it only changes what is charged:

- Range tables. The smallest label-minus-output difference of a token-only row over a range of tokens that
  starts at the first token or ends at the last is read from running minima kept for the whole proof (per
  row, label and direction), and so are the smallest and largest entries of kept rows when a value is boxed;
  each token's smallest difference over the other outputs is kept per row and label.
- Rows that depend on their token and on a value that is the same for every input of the leaf (keys times a
  fixed query: the attention scores) are kept per such value, like token-only rows, and a leaf that meets
  the same value again pays only for matching it.

With at most one varying position everything is per input already, and the rule is token_interval with the
reuse above.

Version 2 adds leaves where the query position varies as well (Gross et al.'s sub-cubic idea: bound the
attention for every query at once). A value that depends only on that position's token (a Mix whose terms all
sit there: the query vector) is kept exactly per token; its product with a Sep summed over the last dimension
is kept per pair of tokens (position p's token and the query position's: the score table); and a softmax of
such scores keeps them. The softmax depends only on score differences, so against a reference position r
(fewest tokens, not the query position) each position's weight relative to r's lies in

    [exp(min (S_p[t, q] - S_r[t_r, q])), exp(max (S_p[t, q] - S_r[t_r, q]))]

over the leaf's tokens and query tokens, read per query token from running minima and maxima of the table's
columns, while r's relative weight is exactly 1. Level A (every output at once) and level B (each output) are
levels 0 and 2 on that box, with the query position's own terms at their smallest over its tokens. Outputs
still unsettled then go query token by query token: with the query position's token fixed the scores are
exact per token (a column of the table), and levels 0 to 3 apply as with a fixed query. Leaves without such
scores are unchanged.
"""

from __future__ import annotations

import math
from fractions import Fraction

import numpy as np

from core.check.evaluate import CheckError
from core.check.general import GeneralProgram
from core.check.interval import IT, _obj, exp_bounds, softmax
from core.check.tokens import Mix, Sep, Term, TokenEvaluator, Var, WSep, _min_max, _size
from core.check.trace import UnsupportedOp

NAME = "token_convex"
CATEGORY = "token_convex"
APPLIES_TO = "general"
TABLES = "tables"
GUARD_BITS = 64  # a group's bound is rounded down at 2**-64 of its rows' unit
DESCRIPTION = (
    'Leaf rule {"leaf": "token_convex"}. For networks with operations beyond linear maps (softmax attention, '
    "say). The correct output must be the same for every input in the leaf. It does everything token_interval "
    "does; it differs through the softmax. A softmax over the positions keeps the box of its scores (per "
    "position, the smallest and largest score over the leaf) and, when the scores are exact per token (the query "
    "fixed in the leaf, say) or per pair of tokens (the query varying, below), those scores. When its weights "
    "multiply exact per-token rows and are summed over the positions, the bound uses that the weights are a "
    "softmax, which sum to one, not an interval per weight. Write c_p for a position's label-minus-output "
    "difference. The bound on the weighted sum is the smallest softmax-weighted average of the c_p, found "
    "exactly, in four levels, each tried only if the ones before leave the margin not positive. Level 0: per "
    "position, c_p is its smallest difference over its tokens and over every other output, and the average's "
    "minimum over the box of scores is exact (it puts each score at an end of its range, high exactly where c_p "
    "is low, so sorting the c_p and trying the n + 1 splits finds it); the rest of the margin counts at its "
    "smallest over the outputs. Level 1, with scores per token: the minimum over every choice of one token per "
    "position, each with its own score and its own difference (smallest over the other outputs), found exactly "
    "by Dinkelbach's method: at a ratio lam, each position independently takes the token minimising "
    "weight * (c - lam); repeat with the ratio of that choice until nothing lowers it (a few steps). Level 2: "
    "level 0 for each other output on its own. Level 3, with scores per token: level 1 for each output still "
    "not positive, with that output's own differences. exp is enclosed at 2**-120, outwards. "
    "LEAVES WHERE THE QUERY VARIES (version 2). A value that depends only on one position's token (a Mix whose "
    "terms all sit at that position, the query vector say) is kept exactly per token there; its product with a "
    "Sep summed over the last dimension is kept per pair of tokens, position p's and that query position's (the "
    "query position's own entry reads its token twice), and a softmax of such scores keeps them. With one query "
    "token the scores are exact per token (a column of the table) and the levels above apply. With several, two "
    "levels come first. Level A: against a reference position r (a position other than the query position with "
    "the fewest tokens), each position's weight relative to r's lies between exp of the smallest and exp of the "
    "largest of its score minus r's over the leaf (for each query token, its column's lowest and highest entry "
    "over the position's tokens, against r's), r's relative weight is 1, and level 0's minimum over that box is "
    "used, with the query position's own terms outside the softmax at their smallest over its tokens and the "
    "outputs. Level B: the same for each other output on its own. Outputs still not positive then go query "
    "token by query token: with the query position's token fixed, levels 0 to 3 apply to the leaf restricted to "
    "it (the box per position from that column's extremes; the query position's terms exact), and an output's "
    "bound is the larger of level B's and the smallest over the query tokens; the first query token that leaves "
    "an output not positive ends the search, and the leaf is not certified. With at most one varying position, "
    "a softmax with scores exact per token or per pair is kept as well and these levels decide: they certify "
    "exactly the leaves whose inputs are all correct (up to exp's rounding), but a certified leaf's bound may be "
    "below its smallest margin; every other value is kept per input, as by token_interval. "
    "REUSE. The smallest difference of a row that depends on its token alone, over a range of tokens starting at "
    "the first token or ending at the last, comes from running minima kept for the whole proof per row, label "
    "and direction (to tables: 2 per token and output for level 2's; 3 per token for level 0's); the smallest "
    "difference over every other output is the label's entry minus the largest other entry, and the outputs of "
    "a row's two largest entries are kept per token (2 per output, to tables). The smallest and largest entries "
    "of kept rows when a value is boxed, and of a pair table's column over a range of tokens, come from running "
    "minima and maxima (2 per entry to build, to tables, 2 to read); the query position's terms' smallest and "
    "largest differences per output likewise (3 per token and output to build, 2 per output to read). Kept "
    "per-token values of the query position: 2 per term and entry, plus 1 per entry, to tables; kept pair scores: "
    "2d - 1 each (d the summed dimension), to tables; a leaf pays 1 per number to match a value it depends on "
    "that is the same for every input (the query's weights and constant, a fixed query), once. Minima per term "
    "are computed once per leaf. CHARGES per leaf, to token_convex: what token_interval charges for the "
    "operations, except: a softmax's interval weights (6 per entry, plus 2 per pair score for their box) only "
    "if something uses them; 5 per position for the exponentials of a box's ends; level 0: 1 per position (a "
    "table read; else 3 per token), n*ceil(log2 n) + 9n + 4 for the search, and outputs - 1 for the smallest "
    "rest; level 1: 3 per token (its score's exponentials), 2 per token for its difference, 1 per token + 3n to "
    "start the search and per step 5 per token + 4n + 1; level 2: per other output, 1 per position (else 2 per "
    "token) and n*ceil(log2 n) + 9n + 4; level 3: per output, 1 per token for its differences, 1 per token + 3n "
    "to start, per step 5 per token + 4n + 1, and 2 to use the result. Level A: per query token, 2 per position "
    "to read its column's extremes (1 for a position with one token or the query position) and 4 per position to "
    "compare, then 5 per position for the exponentials and level 0's search; the query position's terms 2 each; "
    "level B: level 2's charges, 2 per output per query position term, and outputs - 1 to find those still not "
    "positive; per query token: 2 per output per query position term, the box (as level A's reads), the levels "
    "as above (over the outputs still not positive), and 1 per such output to keep the smallest, then 1 per such "
    "output to compare with level B. A term with one row and an exact weight costs 2 per output, the final "
    "minimum outputs - 1."
)


# values -----------------------------------------------------------------------------------------------------
class Soft:
    """softmax(scores) along one axis, where the scores lie in box (shape (1, n)); weights is the interval
    softmax of that box (what any other use of the value sees), axis the softmax axis within weights. If the
    scores were exact per token (a Sep), rows[p] holds position p's score for each of its tokens; if they were
    exact per pair of tokens (a PScores), pair holds them."""

    def __init__(self, box: IT, weights: IT, axis: int, gid, rows=None, pair=None):
        self.box, self.weights, self.axis, self.gid, self.rows, self.pair = box, weights, axis, gid, rows, pair

    @property
    def shape(self) -> tuple:
        return tuple(self.weights.shape)


class QVal:
    """A value that depends only on the token at one position (the leaf's query position, where several tokens
    are allowed): vals[i] (shape `dims`) is its exact value when that position holds tokens[i]. key is the memo
    key its values are kept under (None if they are not kept)."""

    def __init__(self, pos: int, tokens: list, vals: IT, dims: tuple, key):
        self.pos, self.tokens, self.vals, self.dims, self.key = pos, tokens, vals, tuple(dims), key

    @property
    def shape(self) -> tuple:
        return self.dims


class PProd:
    """sep * qv elementwise, not computed yet: a Sep of shape (1, positions, d) times a QVal of shape (1, 1, d)."""

    def __init__(self, sep, qv: QVal):
        self.sep, self.qv = sep, qv

    @property
    def shape(self) -> tuple:
        return tuple(self.sep.shape)


class PScores:
    """A (1, positions) value whose entry at p depends on the tokens at p and at the query position qpos. For
    p != qpos, ent[p][a, i] is its exact value when p holds tokens[p][a] and qpos holds tokens[qpos][i]; for
    p == qpos, ent[p][i] is its value when qpos holds tokens[qpos][i] (both factors read that token). Entries
    are integers at 2**exp; keys[p] is the memo key position p's entries are kept under (None if not kept)."""

    def __init__(self, qpos: int, tokens: list, ent: list, exp: int, keys: list):
        self.qpos, self.tokens, self.ent, self.exp, self.keys = qpos, tokens, ent, exp, keys

    @property
    def shape(self) -> tuple:
        return (1, len(self.ent))

    @property
    def n_entries(self) -> int:
        return sum(int(np.asarray(e).size) for e in self.ent)


class CSep(Sep):
    """A Sep whose rows know how they were kept: per position, its context (() for rows that depend on their
    token alone, a tuple of exact values for rows that also depend on values fixed in the leaf, None for rows
    computed for this leaf only) and the memo key the rows are kept under (None if not kept)."""

    def __init__(self, rows, tokens, pure, origin, ctxs, keys):
        super().__init__(rows, tokens, pure, origin)
        self.ctxs, self.keys = ctxs, keys


class GTerm(Term):
    """A term that knows the memo key of its rows (for range tables) and, if its weight is one softmax weight
    left as it was, its (softmax id, position)."""

    def __init__(self, w, pos, tokens, rows, pure, origin, key=None, group=None, chain=()):
        super().__init__(w, pos, tokens, rows, pure, origin, chain)
        self.key, self.group = key, group


class GMix(Mix):
    """A Mix with the softmaxes its grouped terms came from, by id."""

    def __init__(self, const, terms, groups):
        super().__init__(const, terms)
        self.groups = groups


DOMAIN = TokenEvaluator.domain + (Soft, QVal, PProd, PScores)


def _ctx(sep, p):
    if isinstance(sep, CSep):
        return sep.ctxs[p]
    return () if sep.pure else None


def _key(t):
    return t.key if isinstance(t, GTerm) else None


def _group(t):
    return t.group if isinstance(t, GTerm) else None


def _groups(v) -> dict:
    return v.groups if isinstance(v, GMix) else {}


def _value_key(it: IT) -> tuple:
    """An exact value as a hashable key: its exponent and its integers."""
    return (it.exp, tuple(int(x) for x in np.asarray(it.lo).reshape(-1)))


def _floor_ratio(N: int, D: int, shift: int) -> int:
    """floor(N * 2**shift / D) for D > 0."""
    return (N << shift) // D if shift >= 0 else N // (D << -shift)


def _ctx_size(ctx) -> int:
    return sum(len(v[1]) for v in ctx)


def _shift(x: int, s: int) -> int:
    """x * 2**s, rounded down when s < 0."""
    return x << s if s >= 0 else x >> -s


class _Table:
    """Running minima (and maxima) of exact rows over tokens counted from one end of a position's range:
    entry i of a prefix table covers tokens 0..i, of a suffix table tokens V-1-i..V-1. Extended on demand."""

    def __init__(self, suffix: bool, with_max: bool):
        self.suffix, self.with_max = suffix, with_max
        self.exp = None
        self.mins, self.maxs = [], []

    def query(self, n_tokens: int, exp: int, row, charge, cost_per_row=None):
        """(min, max or None, exponent) over the n_tokens tokens at the table's end; row(i) is the exact row
        (integers at exp) of the i-th of the request's tokens in increasing order. Each new row costs
        cost_per_row (default 2 per entry: two comparisons, or a difference and a comparison)."""
        if self.exp is None:
            self.exp = exp
        if exp < self.exp:  # keep one exponent: rescale what is stored (exact)
            m = 1 << (self.exp - exp)
            self.mins = [x * m for x in self.mins]
            self.maxs = [x * m for x in self.maxs]
            self.exp = exp
        scale = 1 << (exp - self.exp)
        while len(self.mins) < n_tokens:
            i = len(self.mins)
            r = np.array(row(n_tokens - 1 - i if self.suffix else i), dtype=object).reshape(-1) * scale  # flat
            self.mins.append(r if not self.mins else np.minimum(self.mins[-1], r))
            if self.with_max:
                self.maxs.append(r if not self.maxs else np.maximum(self.maxs[-1], r))
            charge(2 * r.size if cost_per_row is None else cost_per_row)
        return self.mins[n_tokens - 1], (self.maxs[n_tokens - 1] if self.with_max else None), self.exp


# the evaluator ----------------------------------------------------------------------------------------------
class ConvexEvaluator(TokenEvaluator):
    domain = DOMAIN
    category = CATEGORY

    def __init__(self, prog, memo, counter, box):
        super().__init__(prog, memo, counter, box)
        self._next_gid = 0
        self._ends = {}
        self._matched = set()
        self._weights_paid = set()
        self._n_of = {}  # softmax id -> its number of entries
        self._box_cost = {}  # softmax id -> the work of its box, when that is charged with its weights
        self._leaf = {}  # per-term minima computed once in this leaf (the term is kept alive with its value)
        self.tokens = box.tokens
        self.qpos = None  # the position whose token a QVal depends on, once one is made

    def tables(self, n) -> None:
        self.counter.add(TABLES, int(n))

    # kept rows ----------------------------------------------------------------------------------------------
    def crows(self, key: tuple, ctx, tokens, prev, fn, cost_per_row):
        """Rows fn(prev) for tokens: kept under key (plus the context's values) when ctx is not None; a leaf
        that finds rows kept under a context pays 1 per number of the context to match it."""
        if ctx is None:
            return self.rows(key, tokens, prev, fn, cost_per_row, False), None
        full = key if ctx == () else key + (ctx,)
        for value in ctx:  # each value fixed in the leaf is matched once per leaf
            if value not in self._matched:
                self._matched.add(value)
                self.charge(len(value[1]))
        return self.rows(full, tokens, prev, fn, cost_per_row, True), full

    def lookup(self, n, box, w, w_free):
        sep = super().lookup(n, box, w, w_free)
        n_pos = len(sep.rows)
        return CSep(sep.rows, sep.tokens, True, sep.origin, [()] * n_pos, [(n.name, n.name, p) for p in range(n_pos)])

    def add_const(self, n, sep, c, c_free):
        if not c.is_exact:
            return None
        try:
            b = np.broadcast_to(c.lo, sep.shape)
        except ValueError:
            return None
        pure = sep.pure and c_free
        rows, ctxs, keys = [], [], []
        for p, r in enumerate(sep.rows):
            cp = IT.exact(_obj(np.array(b[0, p])), c.exp)
            base = _ctx(sep, p)
            ctx = () if pure else (base if c_free else (None if base is None else base + (_value_key(cp),)))
            # "+" keeps these rows apart from those of a linear node's own product (an nn.Linear with a bias)
            rr, k = self.crows((n.name, "+", sep.origin, p), ctx, sep.tokens[p], r, lambda R, cp=cp: R + cp, _size(sep.rest))
            rows.append(rr)
            ctxs.append(ctx)
            keys.append(k)
        return CSep(rows, sep.tokens, pure, sep.origin, ctxs, keys)

    def mul_sep(self, n, sep, c, c_free):
        shape = sep.shape
        try:
            lo = np.broadcast_to(c.lo, shape)
            hi = np.broadcast_to(c.hi, shape)
        except ValueError:
            return None
        rest = shape[2:]
        first = (slice(None), slice(None)) + (slice(0, 1),) * len(rest)
        if np.all(lo == lo[first]) and np.all(hi == hi[first]):
            return super().mul_sep(n, sep, c, c_free)  # one weight per position: a WSep, no rows computed
        if not c.is_exact:
            return None
        pure = sep.pure and c_free
        rows, ctxs, keys = [], [], []
        for p, r in enumerate(sep.rows):
            cp = IT.exact(_obj(np.array(lo[0, p])), c.exp)
            base = _ctx(sep, p)
            ctx = () if pure else (base if c_free else (None if base is None else base + (_value_key(cp),)))
            rr, k = self.crows((n.name, sep.origin, p), ctx, sep.tokens[p], r, lambda R, cp=cp: R * cp, _size(rest))
            rows.append(rr)
            ctxs.append(ctx)
            keys.append(k)
        return CSep(rows, sep.tokens, pure, sep.origin, ctxs, keys)

    def sum_rows(self, n, sep, dim):
        axis = dim - 1
        rows, ctxs, keys = [], [], []
        for p, r in enumerate(sep.rows):
            size = _size(r.shape[1:])
            per_row = size - size // r.shape[axis]
            ctx = _ctx(sep, p)
            rr, k = self.crows((n.name, sep.origin, p), ctx, sep.tokens[p], r, lambda R, a=axis: R.sum(a), per_row)
            rows.append(rr)
            ctxs.append(ctx)
            keys.append(k)
        return CSep(rows, sep.tokens, sep.pure, sep.origin, ctxs, keys)

    def matmul(self, n, v, b, b_free):
        cost = b.shape[0] * b.shape[1]
        if isinstance(v, Sep):
            pure = v.pure and b_free
            rows, ctxs, keys = [], [], []
            for p, r in enumerate(v.rows):
                ctx = _ctx(v, p) if b_free else None
                rr, k = self.crows((n.name, v.origin, p), ctx, v.tokens[p], r, lambda R: R @ b, cost)
                rows.append(rr)
                ctxs.append(ctx)
                keys.append(k)
            return CSep(rows, v.tokens, pure, v.origin, ctxs, keys)
        terms = []
        for t in v.terms:
            pure = t.pure and b_free
            key = (n.name, t.origin, t.pos, t.chain)  # the whole chain (core.check.tokens.Term): h @ A + h @ B
            rows = self.rows(key, t.tokens, t.rows, lambda R: R @ b, cost, pure)
            terms.append(GTerm(t.w, t.pos, t.tokens, rows, pure, t.origin, key if pure else None, _group(t), t.chain + (n.name,)))
        if v.const.is_exact and not np.any(v.const.lo):  # a zero constant stays zero (checked entry by entry)
            const = IT.zeros(v.const.shape[:-1] + (b.shape[1],))
            self.charge(_size(v.const.shape))
        else:
            const = v.const @ b
            self.charge(_size(const.shape) * b.shape[0] * (1 if v.const.is_exact else 2))
        return GMix(const, terms, dict(_groups(v)))

    # the query position: values that depend on its token alone, and scores per pair of tokens -------------
    def qval(self, m, args, kwargs):
        """m.unsqueeze(dim) as a QVal, when every term of the Mix m sits at one position, with an exact scalar
        weight, and m's constant is exact: then m's value is exact for each token there (the leaf's query
        position; one per leaf). Kept per token (2 per term and entry, plus 1 per entry for the constant, to
        tables) when every term's rows are kept; the weights and the constant are then part of the key, matched
        once per leaf (1 per number)."""
        if not m.terms or not m.const.is_exact:
            return None
        d = kwargs.get("dim", args[1] if len(args) > 1 else None)
        if not isinstance(d, int) or isinstance(d, bool):
            return None
        shape = tuple(m.shape)
        d = d if d >= 0 else len(shape) + 1 + d
        if not 0 <= d <= len(shape) or len(shape) < 1 or shape[0] != 1:
            return None
        positions = {t.pos for t in m.terms}
        if len(positions) != 1:
            return None
        p0 = positions.pop()
        toks = self.tokens[p0]
        if self.qpos is not None and self.qpos != p0:
            return None
        for t in m.terms:
            if not (t.w.is_exact and t.w.ndim == 0 and t.rows.is_exact and list(t.tokens) == list(toks)):
                return None
        rest = shape[1:]
        keys = [_key(t) for t in m.terms]
        values = [_value_key(t.w) for t in m.terms] + [_value_key(m.const)]
        key = None
        if all(k is not None for k in keys):
            key = ("token_convex:qval", tuple(zip(keys, values[:-1])), values[-1])
            for value in values:  # each weight and the constant are matched once per leaf
                if value not in self._matched:
                    self._matched.add(value)
                    self.charge(len(value[1]))
        e = min([m.const.exp] + [t.w.exp + t.rows.exp for t in m.terms])
        const = _obj(m.const.lo).reshape(rest) * (1 << (m.const.exp - e))
        terms = [(t.rows.lo, int(t.w.lo) << (t.w.exp + t.rows.exp - e)) for t in m.terms]

        def fn(sel):
            out = np.empty((len(sel.lo),) + rest, dtype=object)
            for r, i in enumerate(int(x) for x in sel.lo):
                acc = const.copy()
                for rows, w in terms:
                    acc = acc + _obj(rows[i]) * w
                out[r] = acc
            return IT.exact(out, e)

        ids = IT.exact(_obj(np.arange(len(toks))), 0)
        vals = self.rows(key, toks, ids, fn, (2 * len(m.terms) + 1) * _size(rest), key is not None)
        dims = shape[:d] + (1,) + shape[d:]
        self.qpos = p0
        return QVal(p0, toks, IT.exact(_obj(vals.lo.reshape((len(toks),) + dims)), vals.exp), dims, key)

    def pair_scores(self, pp: PProd):
        """sum over d of sep * qv: position p's score for every pair of its token and the query position's token
        (for the query position, the diagonal), each the dot product of an exact row and an exact value (2 d - 1),
        kept per pair for the whole proof (to tables) when both are kept, else charged to the leaf."""
        sep, qv = pp.sep, pp.qv
        qpos, qtoks = qv.pos, qv.tokens
        d = sep.shape[2]
        if list(sep.tokens[qpos]) != list(qtoks):
            raise RuntimeError("internal error: the query position's tokens differ between the Sep and the QVal")
        Q = qv.vals.lo.reshape(len(qtoks), d)
        raw, keys = [], []
        for p, r in enumerate(sep.rows):
            kp = sep.keys[p] if isinstance(sep, CSep) else None
            key = None if kp is None or qv.key is None else ("token_convex:pair", kp, qv.key)
            ep = r.exp + qv.vals.exp
            if p == qpos:
                pairs = [(i, i) for i in range(len(qtoks))]
            else:
                pairs = [(a, i) for a in range(len(sep.tokens[p])) for i in range(len(qtoks))]
            store = self.memo.setdefault(key, {}) if key is not None else None
            vals, new = [], 0
            for a, i in pairs:
                tk = (sep.tokens[p][a], qtoks[i])
                if store is not None and tk in store:
                    vals.append(store[tk])
                    continue
                x = (int(np.dot(_obj(r.lo[a]), _obj(Q[i]))), ep)
                if store is not None:
                    store[tk] = x
                vals.append(x)
                new += 1
            if new:
                (self.tables if store is not None else self.charge)((2 * d - 1) * new)
            raw.append(vals)
            keys.append(key)
        e = min(x[1] for vals in raw for x in vals)
        ent = []
        for p, vals in enumerate(raw):
            a = np.array([x << (xe - e) for x, xe in vals], dtype=object)
            ent.append(a if p == qpos else a.reshape(len(sep.tokens[p]), len(qtoks)))
        return PScores(qpos, sep.tokens, ent, e, keys)

    @staticmethod
    def pscores_box(ps: PScores) -> IT:
        """Per position, the smallest and largest entry (shape (1, positions)); the caller charges it."""
        lo = np.array([[int(np.min(x)) for x in ps.ent]], dtype=object)
        hi = np.array([[int(np.max(x)) for x in ps.ent]], dtype=object)
        return IT(lo, hi, ps.exp)

    def query_var(self, v):
        """In a leaf with at most one varying position: a QVal, PProd or PScores as one exact value per input (as
        token_interval keeps every value of such a leaf). Either the query position is the varying one, or it has
        one token and its values are the same for every input."""
        k = self.k
        if isinstance(v, QVal):
            vals = v.vals
            if vals.shape[0] != k:
                vals = IT.exact(_obj(np.broadcast_to(vals.lo, (k,) + tuple(vals.shape[1:]))).copy(), vals.exp)
            return Var(vals)
        if isinstance(v, PProd):
            out = self.to_var(v.sep).it * self.query_var(v.qv).it
            self.charge(_size(out.shape))
            return Var(out)
        cols = []
        for p, e in enumerate(v.ent):
            a = np.asarray(e)
            vec = a.reshape(-1) if p == v.qpos else (a[:, 0] if a.shape[1] == 1 else a[0, :])
            cols.append(np.broadcast_to(vec, (k,)) if len(vec) != k else vec)
        lo = np.stack(cols, axis=1).reshape(k, 1, len(cols))
        return Var(IT.exact(_obj(lo), v.exp))

    def collapse_query(self, v):
        """A QVal, PProd or PScores as an interval tensor: the box over its tokens (2 per entry), or for a
        PProd the interval product of its factors' boxes. Once per value per leaf."""
        key = ("collapsed", id(v))
        if key in self._leaf:
            return self._leaf[key][1]
        if isinstance(v, QVal):
            self.charge(2 * _size(v.vals.shape))
            out = _min_max(v.vals)[0]
        elif isinstance(v, PProd):
            out = self.collapse(v.sep) * self.collapse_query(v.qv)
            self.charge(_size(out.shape) * (1 if out.is_exact else 2))
        else:
            self.charge(2 * v.n_entries)
            out = self.pscores_box(v)
        self._leaf[key] = (v, out)
        return out

    def add_mix(self, v, c):
        const = v.const + c
        self.charge(_size(const.shape) * (1 if const.is_exact else 2))
        return GMix(const, list(v.terms), dict(_groups(v)))

    def add_mixes(self, x, y):
        const = x.const + y.const
        self.charge(_size(const.shape) * (1 if const.is_exact else 2))
        return GMix(const, list(x.terms) + list(y.terms), {**_groups(x), **_groups(y)})

    def scale_mix(self, v, s):
        # a scaled weight is no longer a softmax weight: the terms leave their group
        self.pay_weights(_groups(v))
        terms = [GTerm(t.w * s, t.pos, t.tokens, t.rows, t.pure, t.origin, _key(t), None, t.chain) for t in v.terms]
        const = v.const * s
        self.charge((sum(_size(t.w.shape) for t in v.terms) + _size(const.shape)) * (1 if s.is_exact else 2))
        return GMix(const, terms, {})

    # softmax over the positions ------------------------------------------------------------------------------
    def intercept(self, n, env):
        """A softmax over the positions of a (1, n) tensor keeps its scores: their box with several varying
        positions, and their exact values per token (a Sep) or per pair of tokens (a PScores) in any leaf. With at
        most one varying position other scores stay one value per input (token_interval's Var)."""
        if n.kind != "softmax":
            return None
        args = self.prog._value(n.args, env)
        kwargs = {k: self.prog._value(v, env) for k, v in n.kwargs.items()}
        x = args[0]
        dim = kwargs.get("dim", args[1] if len(args) > 1 else None)
        if dim is None or not isinstance(dim, int) or isinstance(dim, bool):
            return None
        shape = tuple(x.shape) if isinstance(x, self.domain) or isinstance(x, IT) else None
        if shape is None or len(shape) != 2 or shape[0] != 1 or dim not in (1, -1):
            return None
        per_token = isinstance(x, Sep) and all(r.ndim == 1 and r.is_exact for r in x.rows)
        if self.aligned and not (per_token or isinstance(x, PScores)):
            return None
        rows = pair = None
        if isinstance(x, PScores) and len(x.tokens[x.qpos]) == 1:
            # one query token: the scores are exact per token (a column of the table), as with a Sep's rows
            rows, ext = [], []
            for p in range(len(x.ent)):
                col = [x.ent[p][0]] if p == x.qpos else list(x.ent[p][:, 0])
                rows.append(IT.exact(np.array([int(c) for c in col], dtype=object), x.exp))
                ext.append(self.col_extremes(x, p, 0))
            box = IT(np.array([[a for a, _ in ext]], dtype=object), np.array([[b for _, b in ext]], dtype=object), x.exp)
        elif isinstance(x, PScores):
            pair = x  # scores per pair of tokens; their box is charged with the weights, if those are used
            box = self.pscores_box(x)
        else:
            if per_token:
                rows = list(x.rows)  # each position's exact score for each of its tokens
            box = self.collapse(x) if isinstance(x, self.domain) else self.prog._tensor(x)
        weights = softmax(box, 1)  # charged when something uses them (pay_weights): the grouped bound does not
        self._next_gid += 1
        self._n_of[self._next_gid] = _size(box.shape)
        if pair is not None:
            self._box_cost[self._next_gid] = 2 * pair.n_entries
        return Soft(box, weights, 1, self._next_gid, rows, pair)

    def pay_weights(self, gids) -> None:
        """Charge a softmax's interval weights (3 per entry, doubled for intervals) the first time they are used,
        and for scores per pair of tokens, their box (2 per pair)."""
        for gid in gids:
            if gid not in self._weights_paid:
                self._weights_paid.add(gid)
                self.charge(6 * self._n_of[gid] + self._box_cost.get(gid, 0))

    def _plain(self, v):
        """The value without its softmax structure (what an operation that cannot use it sees)."""
        if isinstance(v, (QVal, PProd, PScores)):
            return self.query_var(v) if self.aligned else self.collapse_query(v)
        if isinstance(v, Soft):
            self.pay_weights([v.gid])
            return v.weights
        if isinstance(v, WSep) and isinstance(v.w, Soft):
            self.pay_weights([v.w.gid])
            return WSep(v.w.weights, v.sep)
        if isinstance(v, GMix):
            self.pay_weights(v.groups)  # its terms' weights are about to be used as intervals
        return v

    def evaluate(self, n, args, kwargs, free):
        k = n.kind
        a0 = args[0] if args else None
        # the query position's values (version 2)
        if k == "unsqueeze" and isinstance(a0, Mix) and len(args) <= 2:
            qv = self.qval(a0, args, kwargs)
            if qv is not None:
                return qv
        if k == "mul" and len(args) == 2:
            x, y = args
            sep, qv = (x, y) if isinstance(y, QVal) else (y, x)
            if isinstance(qv, QVal) and isinstance(sep, Sep) and qv.pos == self.qpos and len(sep.shape) == 3:
                if qv.shape == (1, 1, sep.shape[2]) and all(r.is_exact for r in sep.rows):
                    return PProd(sep, qv)
        if k == "sum" and isinstance(a0, PProd):
            dim = kwargs.get("dim", args[1] if len(args) > 1 else None)
            if isinstance(dim, int) and not isinstance(dim, bool) and dim in (2, -1) and not kwargs.get("keepdim"):
                return self.pair_scores(a0)
        if isinstance(a0, Soft) and k == "unsqueeze" and len(args) <= 2:
            d = kwargs.get("dim", args[1] if len(args) > 1 else None)
            if isinstance(d, int) and not isinstance(d, bool):
                nd = a0.weights.ndim
                d = d if d >= 0 else nd + 1 + d
                if 0 <= d <= nd:
                    return Soft(a0.box, a0.weights.unsqueeze(d), a0.axis + (1 if d <= a0.axis else 0), a0.gid, a0.rows,
                                a0.pair)
        if k == "mul" and len(args) == 2:
            x, y = args
            soft, sep = (x, y) if isinstance(x, Soft) else (y, x)
            if isinstance(soft, Soft) and isinstance(sep, Sep) and not isinstance(sep, Soft):
                want = (1, len(sep.rows)) + (1,) * (len(sep.shape) - 2)
                if soft.axis == 1 and soft.shape == want and soft.box.shape == (1, len(sep.rows)):
                    return WSep(soft, sep)  # one softmax weight per position, waiting for the sum over positions
        if k == "sum" and isinstance(a0, WSep) and isinstance(a0.w, Soft):
            dim = kwargs.get("dim", args[1] if len(args) > 1 else None)
            if dim is not None and not kwargs.get("keepdim") and int(dim) in (1, 1 - len(a0.shape)):
                return self.grouped_sum(n, a0)
        # A Soft the rules above cannot use becomes its interval weights; a Mix keeps its groups (the token rules
        # for Mixes, linear maps and sums, act on rows and leave weights alone).
        args = tuple(a if isinstance(a, GMix) else self._plain(a) for a in args)
        kwargs = {key: (v if isinstance(v, GMix) else self._plain(v)) for key, v in kwargs.items()}
        return super().evaluate(n, args, kwargs, free)

    def grouped_sum(self, n, v: WSep) -> GMix:
        soft, sep = v.w, v.sep
        terms = []
        for p, r in enumerate(sep.rows):
            w = soft.weights[(0, p) + (0,) * (soft.weights.ndim - 2)]
            terms.append(GTerm(w, p, sep.tokens[p], r, sep.pure, n.name, None, (soft.gid, p)))
        return GMix(IT.zeros((1,) + sep.rest), terms, {soft.gid: soft})

    def leave(self, v):
        return super().leave(self._plain(v))

    def to_var(self, v):
        return super().to_var(self._plain(v))

    def collapse(self, v):
        v = self._plain(v)
        if not isinstance(v, CSep):
            return super().collapse(v)
        boxes = []
        for p, r in enumerate(v.rows):
            if r.shape[0] > 1:
                b = self.extremes(v.keys[p], v.tokens[p], r)
                if b is None:
                    self.charge(2 * _size(r.shape))
                    b = _min_max(r)
            else:
                b = r
            boxes.append(b)
        e = min(b.exp for b in boxes)
        boxes = [b.at(e) for b in boxes]
        lo = _obj(np.concatenate([b.lo for b in boxes]))[None]
        if all(b.is_exact for b in boxes):
            return IT.exact(lo, e)
        return IT(lo, _obj(np.concatenate([b.hi for b in boxes]))[None], e)

    # range tables -------------------------------------------------------------------------------------------
    def _end(self, tokens):
        """'prefix' if the tokens are 0..k, 'suffix' if they are k..V-1, else None (they are always a range)."""
        if tokens[0] == 0:
            return "prefix"
        if tokens[-1] == self.prog._n_values - 1:
            return "suffix"
        return None

    def extremes(self, key, tokens, r: IT):
        """The box (entrywise min and max over the tokens, shape (1, *rest)) of kept exact rows, from a table."""
        end = self._end(tokens)
        if key is None or end is None or not r.is_exact:
            return None
        tab = self.memo.setdefault(("token_convex:extremes", key, end), _Table(end == "suffix", True))
        lo, hi, e = tab.query(len(tokens), r.exp, lambda i: r.lo[i], self.tables)
        rest = (1,) + tuple(r.shape[1:])
        self.charge(2 * _size(r.shape[1:]))
        return IT(_obj(lo).reshape(rest), _obj(hi).reshape(rest), e)

    def min_difference(self, t, label: int):
        """(per output j, the smallest R[t, label] - R[t, j] over the term's tokens, its exponent)."""
        R = t.rows.lo
        n_out = R.shape[1]
        if R.shape[0] == 1:
            self.charge(n_out)
            return _obj(R[0, label]) - _obj(R[0]), t.rows.exp
        end = self._end(t.tokens)
        key = _key(t)
        if key is not None and end is not None:
            tab = self.memo.setdefault(("token_convex:mindiff", key, label, end), _Table(end == "suffix", False))
            lo, _, e = tab.query(len(t.tokens), t.rows.exp, lambda i: _obj(R[i, label]) - _obj(R[i]), self.tables)
            self.charge(n_out)
            return lo, e
        self.charge(2 * R.shape[0] * n_out)
        return (_obj(R[:, [label]]) - _obj(R)).min(axis=0), t.rows.exp

    def top_two(self, t, i: int):
        """(a, b): the output with the largest entry in row i of the term's rows, and the output with the largest
        entry among the others (version 2). Kept per token for the whole proof when the rows are kept (2 per
        output to find, to tables), else found for this leaf (2 per output)."""
        key = _key(t)
        tok = t.tokens[i]
        store = self.memo.setdefault(("token_convex:top2", key), {}) if key is not None else None
        if store is not None and tok in store:
            return store[tok]
        row = [int(x) for x in t.rows.lo[i]]
        a = max(range(len(row)), key=lambda j: row[j])
        b = max((j for j in range(len(row)) if j != a), key=lambda j: row[j])
        if store is not None:
            store[tok] = (a, b)
            self.tables(2 * len(row))
        else:
            self.charge(2 * len(row))
        return a, b

    def row_min_all(self, t, i: int, label: int) -> int:
        """min over every other output j of R[i, label] - R[i, j] (an integer at t.rows.exp): R[i, label] minus the
        largest other entry, which top_two names (a comparison and a subtraction, charged by the caller)."""
        a, b = self.top_two(t, i)
        R = t.rows.lo[i]
        return int(R[label]) - int(R[b if a == label else a])

    def min_difference_all(self, t, label: int):
        """(the smallest R[t, label] - R[t, j] over the term's tokens and every other output j, its exponent): per
        token from row_min_all (2), then the smallest; over tokens that start at the first token or end at the
        last, from running minima kept for the whole proof per row, label and end (3 per token to build, to tables;
        1 to read)."""
        R = t.rows.lo
        if R.shape[0] == 1:
            self.charge(2)
            return self.row_min_all(t, 0, label), t.rows.exp
        end = self._end(t.tokens)
        key = _key(t)
        if key is not None and end is not None:
            tab = self.memo.setdefault(("token_convex:mindiffall", key, label, end), _Table(end == "suffix", False))
            lo, _, e = tab.query(len(t.tokens), t.rows.exp, lambda i: [self.row_min_all(t, i, label)], self.tables, 3)
            self.charge(1)
            return lo[0], e
        self.charge(3 * R.shape[0])
        return min(self.row_min_all(t, i, label) for i in range(R.shape[0])), t.rows.exp

    # the decision -------------------------------------------------------------------------------------------
    def complete_groups(self, v) -> dict:
        """The softmax groups whose weights all reach the output untouched, one term per position."""
        groups = _groups(v)
        by_gid = {}
        for i, t in enumerate(v.terms):
            g = _group(t)
            if g is not None and g[0] in groups:
                by_gid.setdefault(g[0], []).append(i)
        out = {}
        for gid, idx in by_gid.items():
            n = groups[gid].box.shape[1]
            pos = sorted(v.terms[i].group[1] for i in idx)
            if pos == list(range(n)) and all(v.terms[i].pos == v.terms[i].group[1] for i in idx):
                out[gid] = sorted(idx, key=lambda i: v.terms[i].group[1])
        return out

    def lower_margin(self, v, label: int):
        if not isinstance(v, GMix):
            v = self._plain(v)
        # with at most one varying position, the softmax levels decide only where a complete group reaches the
        # output (version 2); otherwise values are per input and token_interval's decision is exact
        if not isinstance(v, Mix) or (self.aligned and not self.complete_groups(v)):
            if isinstance(v, GMix):
                self.pay_weights(v.groups)
            return super().lower_margin(v, label)
        n_out = v.shape[1]
        if not 0 <= label < n_out:
            raise UnsupportedOp("label outside the network's outputs")
        if n_out == 1:  # no other output to beat, as token_interval reports it
            return Fraction(1), -1
        groups = self.complete_groups(v)
        self.pay_weights([g for g in _groups(v) if g not in groups])  # incomplete groups use interval weights
        if any(_groups(v)[gid].pair is not None for gid in groups):
            return self.pair_margin(v, label, groups, n_out)  # scores per pair of tokens (version 2)
        in_group = {i for idx in groups.values() for i in idx}
        singles, others = [], []
        for i, t in enumerate(v.terms):
            if i in in_group:
                continue
            if t.rows.shape[0] == 1 and t.w.is_exact and t.w.ndim == 0:
                singles.append(t)
            else:
                others.append(t)
        c = v.const
        exps = [c.exp] + [t.w.exp + t.rows.exp for t in singles + others]
        exps += [min(v.terms[i].rows.exp for i in idx) - GUARD_BITS for idx in groups.values()]
        e0 = min(exps)
        acc = (_obj(c.lo[0, label]) - _obj(c.hi[0])) * (1 << (c.exp - e0))
        self.charge(n_out - 1)
        for t in singles:  # one row and an exact weight: a constant
            R = t.rows.lo[0]
            acc = acc + (_obj(R[label]) - _obj(R)) * _obj(t.w.lo) * (1 << (t.w.exp + t.rows.exp - e0))
            self.charge(2 * (n_out - 1))
        for t in others:  # as token_interval with several varying positions
            R = t.rows.lo
            D = _obj(R[:, [label]]) - _obj(R)
            dmin, dmax = np.min(D, axis=0), np.max(D, axis=0)
            w_lo, w_hi = _obj(t.w.lo).min(), _obj(t.w.hi).max()
            lo = np.minimum(np.minimum(w_lo * dmin, w_lo * dmax), np.minimum(w_hi * dmin, w_hi * dmax))
            acc = acc + lo * (1 << (t.w.exp + t.rows.exp - e0))
            self.charge((3 * R.shape[0] + 8) * (n_out - 1))
        gs = _groups(v)
        acc = acc.astype(object)
        if groups:
            # Level 0: every other output at once. Each softmax-weighted sum is bounded with, per position, the
            # smallest difference over its tokens and over every other output; the rest of the margin by its
            # smallest value over the outputs. Their sum is below every output's margin.
            g0 = sum(self.group_bound_all(gs[gid], [v.terms[i] for i in idx], label, e0) for gid, idx in groups.items())
            others_j = [j for j in range(n_out) if j != label]
            j0 = min(others_j, key=lambda j: acc[j]) if others_j else -1
            self.charge(n_out - 1)
            if j0 >= 0 and acc[j0] + g0 > 0:
                return Fraction(acc[j0] + g0) * Fraction(2) ** e0, j0
        # Level 1 (where every softmax has its scores per token): the exact search over each position's tokens,
        # once, with each token's smallest difference over the other outputs.
        exact = {gid: None for gid in groups if gs[gid].rows is not None}
        if groups and len(exact) == len(groups) and j0 >= 0:
            g1 = 0
            for gid in groups:
                terms = [v.terms[i] for i in groups[gid]]
                exact[gid] = self.exact_setup(gs[gid], terms, label)
                g = self.exact_bound_all(exact[gid], terms, label, e0)
                if g is None:
                    break
                g1 += g
            else:
                if acc[j0] + g1 > 0:
                    return Fraction(acc[j0] + g1) * Fraction(2) ** e0, j0
        # Level 2: each other output on its own, over the box of scores.
        cheap = {}
        for gid, idx in groups.items():
            cheap[gid] = self.group_bound(gs[gid], [v.terms[i] for i in idx], label, n_out, e0)
            acc = acc + cheap[gid]
        acc = acc.astype(object)
        # Level 3: outputs still unsettled get the exact search over each position's tokens, output by output.
        for j in range(n_out):
            if j == label or acc[j] > 0:
                continue
            for gid in exact:
                if exact[gid] is None:
                    exact[gid] = self.exact_setup(gs[gid], [v.terms[i] for i in groups[gid]], label)
                g = self.exact_bound(exact[gid], j, e0)
                self.charge(2)  # the comparison with the level-2 value and the update
                if g is not None and g > cheap[gid][j]:
                    acc[j] += g - cheap[gid][j]
        acc[label] = None
        best, arg = None, -1
        for j, b in enumerate(acc):
            if b is not None and (best is None or b < best):
                best, arg = b, j
        self.charge(n_out - 1)
        if best is None:
            return Fraction(1), -1
        return Fraction(best) * Fraction(2) ** e0, arg

    def box_ends(self, soft: Soft):
        """Per position, enclosures of exp at its scores' ends, shifted by the leaf's largest score: El (a lower
        bound at the lower end) and dE (the upper bound at the upper end minus El). Once per softmax per leaf,
        5 per position (two shifts, two exps, a difference)."""
        if soft.gid not in self._ends:
            n = soft.box.shape[1]
            es = soft.box.exp
            L = [int(soft.box.lo[0, p]) for p in range(n)]
            H = [int(soft.box.hi[0, p]) for p in range(n)]
            K = max(H)
            El = [exp_bounds(x - K, es)[0] for x in L]  # exp(L_p - K) >= El * 2**-120
            Eh = [exp_bounds(x - K, es)[1] for x in H]  # exp(H_p - K) <= Eh * 2**-120
            self._ends[soft.gid] = (El, [h - l for h, l in zip(Eh, El)])
            self.charge(5 * n)
        return self._ends[soft.gid]

    @staticmethod
    def threshold(El, dE, cs):
        """(N, D) with N/D the minimum over u_p in [El_p, El_p + dE_p] of sum u_p c_p / sum u_p: the minimum puts
        u_p at its upper end exactly where c_p is below it, so the n + 1 splits of the sorted c_p are tried."""
        N = sum(l * x for l, x in zip(El, cs))
        D = sum(El)
        best = (N, D) if D > 0 else None
        for p in sorted(range(len(cs)), key=lambda q: cs[q]):  # lowest difference gets the high end first
            N += dE[p] * cs[p]
            D += dE[p]
            if D > 0 and (best is None or N * best[1] < best[0] * D):
                best = (N, D)
        return best

    def search_cost(self, n: int) -> int:
        """Sorting n numbers, the first split (3n), n moves (3 each), n + 1 comparisons of ratios (3 each), a division."""
        return (n * max(1, math.ceil(math.log2(n))) if n > 1 else 0) + 9 * n + 4

    def cached(self, kind: str, t, label: int, fn):
        """fn() once per leaf for this term, kind and label (a leaf that needs the same minima again, for another
        query token, reads them back)."""
        key = (kind, id(t), label)
        if key not in self._leaf:
            self._leaf[key] = (t, fn())  # the term is kept with its value, so its id stays its own
        return self._leaf[key][1]

    def group_bound_all(self, soft: Soft, terms: list, label: int, e0: int, ends=None) -> int:
        """A lower bound (an integer at 2**e0) of the weighted sum for every other output at once, over the box of
        exponentials `ends` (default: the softmax's own box, box_ends)."""
        El, dE = self.box_ends(soft) if ends is None else ends
        vals, exps = [], []
        for t in terms:
            x, e = self.cached("min_all", t, label, lambda t=t: self.min_difference_all(t, label))
            vals.append(x)
            exps.append(e)
        er = min(exps)
        cs = [int(x) << (e - er) for x, e in zip(vals, exps)]
        N, D = self.threshold(El, dE, cs)
        self.charge(self.search_cost(len(terms)))
        return _floor_ratio(N, D, er - e0)

    def group_bound(self, soft: Soft, terms: list, label: int, n_out: int, e0: int, ends=None, outputs=None):
        """Per output j (every other output, or those in outputs), a lower bound (integers at 2**e0) of
        sum_p softmax(s)_p * (R_p[t_p, label] - R_p[t_p, j]) over every score vector s in the box (or the box of
        exponentials `ends`) and every token t_p the terms allow."""
        n = len(terms)
        El, dE = self.box_ends(soft) if ends is None else ends
        cols, exps = [], []
        for t in terms:
            col, e = self.cached("min", t, label, lambda t=t: self.min_difference(t, label))
            cols.append(col)
            exps.append(e)
        er = min(exps)
        cols = [col * (1 << (e - er)) for col, e in zip(cols, exps)]
        shift = er - e0
        out = np.zeros(n_out, dtype=object)
        js = [j for j in range(n_out) if j != label] if outputs is None else list(outputs)
        for j in js:
            N, D = self.threshold(El, dE, [int(col[j]) for col in cols])
            out[j] = _floor_ratio(N, D, shift)  # rounded down: still a lower bound
        self.charge(self.search_cost(n) * len(js))
        return out


    def exact_setup(self, soft: Soft, terms: list, label: int) -> dict:
        """Per position: its tokens' exponential enclosures (a common shift, the leaf's largest score) and the
        rows of label-minus-output differences; computed once per leaf, at 3 per token."""
        es = min(q.exp for q in soft.rows)
        scores = []
        for p, t in enumerate(terms):
            r = soft.rows[p]
            if len(r.lo) != len(t.tokens):
                raise RuntimeError("internal error: scores and rows disagree on a position's tokens")
            scores.append([int(x) << (r.exp - es) for x in r.lo])
        K = max(max(sc) for sc in scores)
        wl = [[exp_bounds(x - K, es)[0] for x in sc] for sc in scores]
        wh = [[exp_bounds(x - K, es)[1] for x in sc] for sc in scores]
        n_tok = sum(len(sc) for sc in scores)
        self.charge(3 * n_tok)
        er = min(t.rows.exp for t in terms)
        diffs = [(_obj(t.rows.lo[:, [label]]) - _obj(t.rows.lo)) * (1 << (t.rows.exp - er)) for t in terms]
        return {"wl": wl, "wh": wh, "diffs": diffs, "er": er, "n_tok": n_tok}

    def token_min_all(self, t, label: int) -> list:
        """Per token of the term, (the smallest R[t, label] - R[t, j] over every other output j, its exponent),
        from row_min_all (2 per token)."""
        self.charge(2 * len(t.tokens))
        return [(self.row_min_all(t, i, label), t.rows.exp) for i in range(len(t.tokens))]

    def exact_bound_all(self, ctx: dict, terms: list, label: int, e0: int):
        """exact_bound for every other output at once: each token's difference is its smallest over the outputs."""
        vals = [self.cached("tokmin", t, label, lambda t=t: self.token_min_all(t, label)) for t in terms]
        er = min(e for col in vals for _, e in col)
        cs = [[x << (e - er) for x, e in col] for col in vals]
        return self.exact_search(ctx, cs, er, e0)

    def exact_bound(self, ctx: dict, j: int, e0: int) -> int:
        """The exact minimum, over every token at every position and every weight within its exponential
        enclosure, of sum_p w_p c_p / sum_p w_p with c_p the label-minus-j difference of the chosen token;
        rounded down at 2**e0. Dinkelbach's method: at a ratio lam = N/D, each position independently takes
        the token and weight end minimising w (D c - N); if their sum is negative, the minimiser's own ratio
        is smaller, and it repeats; when the sum is zero, lam is the minimum. Every lam after the first is the
        ratio of an actual choice, so each step strictly lowers it and the search ends."""
        diffs = ctx["diffs"]
        cs = [[int(x) for x in d[:, j]] for d in diffs]
        self.charge(ctx["n_tok"])  # the column of differences
        return self.exact_search(ctx, cs, ctx["er"], e0)

    def exact_search(self, ctx: dict, cs: list, er: int, e0: int):
        """Dinkelbach's search on per-position lists cs[p][i] (integers at 2**er) of each token's difference."""
        wl, wh = ctx["wl"], ctx["wh"]
        n = len(cs)
        # start from each position's token with the smallest difference at its upper weight
        N = D = 0
        for p in range(n):
            i = min(range(len(cs[p])), key=lambda q: cs[p][q])
            N += wh[p][i] * cs[p][i]
            D += wh[p][i]
        self.charge(ctx["n_tok"] + 3 * n)  # the smallest difference per position, then its weighted sums
        steps = 0
        while True:
            steps += 1
            total = 0
            Nn = Dn = 0
            for p in range(n):
                best = None
                for i, c in enumerate(cs[p]):
                    a = D * c - N
                    w = wl[p][i] if a >= 0 else wh[p][i]
                    val = w * a
                    if best is None or val < best[0]:
                        best = (val, w, c)
                total += best[0]
                Nn += best[1] * best[2]
                Dn += best[1]
            if total >= 0 or steps > 64:
                break
            N, D = Nn, Dn
        self.charge(steps * (5 * ctx["n_tok"] + 4 * n + 1))
        if total < 0:  # not settled within the step limit (never seen): lam is not known to be the minimum
            return None
        return _floor_ratio(N, D, er - e0)

    # scores per pair of tokens: the query position varies (version 2) ----------------------------------------
    def pair_margin(self, v, label: int, groups: dict, n_out: int):
        """The decision when some complete softmax group has scores per pair of tokens. Terms outside the groups:
        a constant, terms with one row and an exact weight, the query position's terms with an exact weight
        (exact per query token), and the rest (bounded as token_interval does). Level A: every other output at
        once over every query token; level B: each other output; then, for outputs still not positive, each
        query token on its own with levels 0 to 3."""
        gs = _groups(v)
        qtoks = list(self.tokens[self.qpos])
        in_group = {i for idx in groups.values() for i in idx}
        singles, qterms, others = [], [], []
        for i, t in enumerate(v.terms):
            if i in in_group:
                continue
            exact_w = t.w.is_exact and t.w.ndim == 0
            if t.rows.shape[0] == 1 and exact_w:
                singles.append(t)
            elif t.pos == self.qpos and exact_w and list(t.tokens) == qtoks:
                qterms.append(t)
            else:
                others.append(t)
        c = v.const
        exps = [c.exp] + [t.w.exp + t.rows.exp for t in singles + qterms + others]
        exps += [min(v.terms[i].rows.exp for i in idx) - GUARD_BITS for idx in groups.values()]
        e0 = min(exps)
        acc = (_obj(c.lo[0, label]) - _obj(c.hi[0])) * (1 << (c.exp - e0))
        self.charge(n_out - 1)
        for t in singles:  # one row and an exact weight: a constant
            R = t.rows.lo[0]
            acc = acc + (_obj(R[label]) - _obj(R)) * _obj(t.w.lo) * (1 << (t.w.exp + t.rows.exp - e0))
            self.charge(2 * (n_out - 1))
        for t in others:  # as token_interval with several varying positions
            R = t.rows.lo
            D = _obj(R[:, [label]]) - _obj(R)
            dmin, dmax = np.min(D, axis=0), np.max(D, axis=0)
            w_lo, w_hi = _obj(t.w.lo).min(), _obj(t.w.hi).max()
            lo = np.minimum(np.minimum(w_lo * dmin, w_lo * dmax), np.minimum(w_hi * dmin, w_hi * dmax))
            acc = acc + lo * (1 << (t.w.exp + t.rows.exp - e0))
            self.charge((3 * R.shape[0] + 8) * (n_out - 1))
        acc = np.array(acc, dtype=object)
        terms_of = {gid: [v.terms[i] for i in idx] for gid, idx in groups.items()}
        ends = {gid: (self.pair_ends(gs[gid]) if gs[gid].pair is not None else None) for gid in groups}
        others_j = [j for j in range(n_out) if j != label]
        # Level A: every other output at once, over every query token. The query position's own terms count at
        # their smallest over its tokens and over the outputs (weights >= 0), else per output.
        if all(int(t.w.lo) >= 0 for t in qterms):
            j0 = min(others_j, key=lambda j: acc[j])
            self.charge(n_out - 1)
            rest = acc[j0]
            for t in qterms:
                x, e = self.cached("min_all", t, label, lambda t=t: self.min_difference_all(t, label))
                rest += _shift(int(t.w.lo) * int(x), t.w.exp + e - e0)
                self.charge(2)  # the product with the weight and the sum
        else:
            acc_a = acc.copy()
            for t in qterms:
                acc_a = acc_a + self.pessimised(t, label, e0)
            j0 = min(others_j, key=lambda j: acc_a[j])
            self.charge(n_out - 1)
            rest = acc_a[j0]
        g = sum(self.group_bound_all(gs[gid], ts, label, e0, ends[gid]) for gid, ts in terms_of.items())
        if rest + g > 0:
            return Fraction(rest + g) * Fraction(2) ** e0, j0
        # Level B: each other output on its own, over every query token.
        best = acc.copy()
        for t in qterms:
            best = best + self.pessimised(t, label, e0)
        for gid, ts in terms_of.items():
            best = best + self.group_bound(gs[gid], ts, label, n_out, e0, ends[gid])
        best = np.array(best, dtype=object)
        unsettled = [j for j in others_j if best[j] <= 0]
        self.charge(n_out - 1)
        if unsettled:
            low = self.by_query(label, gs, terms_of, acc, qterms, unsettled, n_out, e0)
            if low is not None:  # every query token settled every output: the smallest over them holds
                for j in unsettled:
                    if low[j] > best[j]:
                        best[j] = low[j]
                self.charge(len(unsettled))
        value, arg = None, -1
        for j in others_j:
            if value is None or best[j] < value:
                value, arg = best[j], j
        self.charge(n_out - 1)
        return Fraction(value) * Fraction(2) ** e0, arg

    def min_max_difference(self, t, label: int):
        """(per output j, the smallest and the largest R[t, label] - R[t, j] over the term's tokens, their exponent):
        from running minima and maxima kept for the whole proof when the rows are kept and the tokens start at
        the first token or end at the last (3 per token and output to build, to tables; 2 per output to read),
        else computed (3 per token and output)."""
        R = t.rows.lo
        n_out = R.shape[1]
        end = self._end(t.tokens)
        key = _key(t)
        if key is not None and end is not None:
            tab = self.memo.setdefault(("token_convex:minmaxdiff", key, label, end), _Table(end == "suffix", True))
            lo, hi, e = tab.query(len(t.tokens), t.rows.exp, lambda i: _obj(R[i, label]) - _obj(R[i]), self.tables, 3 * n_out)
            self.charge(2 * n_out)
            return lo, hi, e
        D = _obj(R[:, [label]]) - _obj(R)
        self.charge(3 * R.shape[0] * n_out)
        return D.min(axis=0), D.max(axis=0), t.rows.exp

    def pessimised(self, t, label: int, e0: int):
        """Per output j, a lower bound (integers at 2**e0, rounded down) of w (R[q, label] - R[q, j]) over the
        term's tokens q, for an exact scalar weight w: w times the smallest difference, or the largest if w < 0
        (a product and a sum per other output)."""
        lo, hi, e = self.min_max_difference(t, label)
        w = int(t.w.lo)
        m = lo if w >= 0 else hi
        s = t.w.exp + e - e0
        out = np.array([_shift(w * int(x), s) for x in np.asarray(m).reshape(-1)], dtype=object)
        self.charge(2 * (len(out) - 1))
        return out

    def col_extremes(self, ps: PScores, p: int, i: int):
        """(lowest, highest) score of position p over its tokens with the query position at its i-th token,
        integers at 2**ps.exp. The query position itself and a position with one token: one entry (1). Else from
        running minima and maxima of the column kept for the whole proof, when its entries are kept and the
        tokens start at the first token or end at the last (2 per entry to build, to tables; 2 to read), or
        computed (2 per entry)."""
        if p == ps.qpos:
            self.charge(1)
            x = int(ps.ent[p][i])
            return x, x
        col = ps.ent[p][:, i]
        toks = ps.tokens[p]
        if len(toks) == 1:
            self.charge(1)
            x = int(col[0])
            return x, x
        end = self._end(toks)
        key = ps.keys[p]
        if key is not None and end is not None:
            tab = self.memo.setdefault(("token_convex:pcol", key, ps.tokens[ps.qpos][i], end), _Table(end == "suffix", True))
            lo, hi, e = tab.query(len(toks), ps.exp, lambda a: [col[a]], self.tables)
            s = ps.exp - e  # the table may keep a finer exponent; its extremes are entries of col, so exact here
            lo, hi = int(lo[0]), int(hi[0])
            if lo % (1 << s) == 0 and hi % (1 << s) == 0:
                self.charge(2)
                return lo >> s, hi >> s
        self.charge(2 * len(toks))
        return int(np.min(col)), int(np.max(col))

    def pair_ends(self, soft: Soft):
        """For a softmax with scores per pair of tokens: enclosures (El, dE as in box_ends) of each position's weight
        relative to a reference position r, over every input of the leaf. r is a position other than the query
        position with the fewest tokens (the lowest such position; the query position if it is the only one).
        For each query token q: r's lowest and highest score (col_extremes), and for every other position its
        lowest and highest; the relative score s_p - s_r then lies between lowest_p - highest_r and highest_p -
        lowest_r (2 subtractions), kept as running extremes over q (2 comparisons). r's relative score is 0.
        With K the largest upper end (at least 0), the exponentials of the ends minus K are enclosed (5 per
        position). Once per softmax per leaf."""
        key = ("pair", soft.gid)
        if key in self._ends:
            return self._ends[key]
        ps = soft.pair
        n = len(ps.ent)
        nq = len(ps.tokens[ps.qpos])
        cand = [p for p in range(n) if p != ps.qpos]
        r = min(cand, key=lambda p: (len(ps.tokens[p]), p)) if cand else ps.qpos
        ref = [self.col_extremes(ps, r, i) for i in range(nq)]
        glo, ghi = [0] * n, [0] * n
        for p in range(n):
            if p == r:
                continue
            lo = hi = None
            for i in range(nq):
                a, b = self.col_extremes(ps, p, i)
                x, y = a - ref[i][1], b - ref[i][0]
                lo = x if lo is None else min(lo, x)
                hi = y if hi is None else max(hi, y)
            glo[p], ghi[p] = lo, hi
        self.charge(4 * (n - 1) * nq)
        K = max([0] + [ghi[p] for p in range(n) if p != r])
        El, Eh = [], []
        for p in range(n):
            if p == r:
                lo_e, hi_e = exp_bounds(-K, ps.exp)
            else:
                lo_e, hi_e = exp_bounds(glo[p] - K, ps.exp)[0], exp_bounds(ghi[p] - K, ps.exp)[1]
            El.append(lo_e)
            Eh.append(hi_e)
        self.charge(5 * n)
        self._ends[key] = (El, [h - l for h, l in zip(Eh, El)])
        return self._ends[key]

    def by_query(self, label: int, gs: dict, terms_of: dict, acc, qterms: list, outputs: list, n_out: int, e0: int):
        """For each token at the query position, levels 0 to 3 with that token fixed, for the outputs given: per
        output the smallest bound over the tokens, or None as soon as a token leaves an output not positive (the
        leaf then fails). The query position's terms with an exact weight are exact for each token (2 per other
        output, as a term with one row)."""
        low = {}
        for i in range(len(self.tokens[self.qpos])):
            acc_q = acc.copy()
            for t in qterms:
                R = t.rows.lo[i]
                acc_q = acc_q + (_obj(R[label]) - _obj(R)) * _obj(t.w.lo) * (1 << (t.w.exp + t.rows.exp - e0))
                self.charge(2 * (n_out - 1))
            acc_q = np.array(acc_q, dtype=object)
            views = [self.query_view(gs[gid], ts, i) for gid, ts in terms_of.items()]
            out = self.fixed_levels(views, acc_q, outputs, label, n_out, e0)
            for j in outputs:
                low[j] = out[j] if j not in low else min(low[j], out[j])
            self.charge(len(outputs))
            if any(out[j] <= 0 for j in outputs):
                return None
        return low

    def query_view(self, soft: Soft, terms: list, i: int):
        """The group with the query position holding its i-th token: (a Soft, the terms). A group with scores per
        pair of tokens becomes one with scores per token (the table's column for that token) and its box (from
        col_extremes); a group with scores per token keeps only that token's at the query position; a group with
        a box keeps it (it holds for every input). The query position's term keeps that token's row."""
        qp = self.qpos
        ts = []
        for t in terms:
            if t.pos == qp:
                # one row, the term's row for that token: what is kept under the term's key for it is the same
                ts.append(GTerm(t.w, t.pos, [t.tokens[i]], IT.exact(t.rows.lo[i:i + 1], t.rows.exp), t.pure, t.origin,
                                _key(t), _group(t), t.chain))
            else:
                ts.append(t)
        if soft.pair is not None:
            ps = soft.pair
            n = len(ps.ent)
            ext = [self.col_extremes(ps, p, i) for p in range(n)]
            box = IT(np.array([[a for a, _ in ext]], dtype=object), np.array([[b for _, b in ext]], dtype=object), ps.exp)
            rows = []
            for p in range(n):
                col = [ps.ent[p][i]] if p == ps.qpos else list(ps.ent[p][:, i])
                rows.append(IT.exact(np.array([int(x) for x in col], dtype=object), ps.exp))
            return Soft(box, None, 1, ("query", soft.gid, i), rows), ts
        if soft.rows is not None:
            rows = list(soft.rows)
            rows[qp] = IT.exact(soft.rows[qp].lo[i:i + 1], soft.rows[qp].exp)
            return Soft(soft.box, None, 1, soft.gid, rows), ts
        return soft, ts

    def fixed_levels(self, views: list, acc, outputs: list, label: int, n_out: int, e0: int) -> dict:
        """Levels 0 to 3 for one query token (views from query_view), for the given outputs: per output, a lower
        bound (an integer at 2**e0) of its margin over the leaf's inputs with that token."""
        j0 = min(outputs, key=lambda j: acc[j])
        self.charge(len(outputs) - 1)
        base = acc[j0] + sum(self.group_bound_all(s, ts, label, e0) for s, ts in views)
        if base > 0:
            return {j: base for j in outputs}
        exact = {}
        if all(s.rows is not None for s, _ in views):
            g1 = 0
            for idx, (s, ts) in enumerate(views):
                exact[idx] = self.exact_setup(s, ts, label)
                g = self.exact_bound_all(exact[idx], ts, label, e0)
                if g is None:
                    g1 = None
                    break
                g1 += g
            if g1 is not None and acc[j0] + g1 > 0:
                return {j: acc[j0] + g1 for j in outputs}
        cheap = [self.group_bound(s, ts, label, n_out, e0, None, outputs) for s, ts in views]
        out = {j: acc[j] + sum(c[j] for c in cheap) for j in outputs}
        for j in outputs:
            if out[j] > 0:
                continue
            for idx, (s, ts) in enumerate(views):
                if s.rows is None:
                    continue
                if idx not in exact:
                    exact[idx] = self.exact_setup(s, ts, label)
                g = self.exact_bound(exact[idx], j, e0)
                self.charge(2)  # the comparison with the level-2 value and the update
                if g is not None and g > cheap[idx][j]:
                    out[j] += g - cheap[idx][j]
        return out


def check_leaf(prog, ranges, label, counter):
    """(certified, lowest margin bound as a Fraction, the other output reaching it) for one token_convex leaf."""
    if not isinstance(prog, GeneralProgram):
        raise CheckError("token_convex is only for networks beyond linear maps")
    return prog.run_token_leaf(ranges, label, counter, ConvexEvaluator)
