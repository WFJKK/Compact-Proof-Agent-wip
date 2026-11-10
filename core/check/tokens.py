"""Token-exact evaluation for token_interval leaves of networks beyond linear maps.

An interval leaf turns each position's set of tokens into a box of entrywise
minima and maxima at the first lookup, and the box widens through every later
product. A token_interval leaf keeps the tokens apart for as long as the graph
allows. Next to ordinary interval tensors (IT) it uses four kinds of values:

- Sep: a tensor of shape (1, positions, ...) whose row p depends only on the
  token at position p, held exactly for every token the leaf allows at p. The
  first lookup x @ W makes one; adding a constant, a product with a constant
  on the right, an elementwise product with an exact tensor and a sum over a
  non-position dimension keep it one.
- Mix: const + the sum over terms k of w_k * R_k[t], where const is an IT,
  w_k a weight and R_k[t] an exact row for each allowed token t of the term's
  position. Selecting one position of a Sep, or summing a weighted Sep over the
  positions, makes one. Products with a constant matrix act on every row
  exactly (by linearity), so the rows reach the logits without being boxed.
- WSep: a Sep times a weight that is a scalar per position (an attention
  weight), waiting for its sum over the positions.
- Var, only in leaves where at most one position p* holds more than one token:
  a tensor with one extra leading axis over p*'s tokens, so every input of the
  leaf keeps its own exact value (up to the rounding of exp and softmax).

Rows that depend on their token alone (a lookup, then constants) are pure: the
checker keeps them for the rest of the proof and charges their work once, to
the category tables. All other work is charged to token_interval, per leaf.

When an operation meets a Sep or Mix in a way these rules do not cover, the
value becomes a Var if at most one position varies, and otherwise an IT: the
box of its rows per position (a Mix: the interval sum of its terms' boxes, or
its exact value when each term has one row and an exact weight). Both are sound.

Deciding. For a Var output, the margin is computed per input and the lowest is
taken. For a Mix output, each other output j gets the lower bound of
const[label] - const[j] plus, per term, of w * (R[t, label] - R[t, j]). If at
most one position varies, the terms are summed token by token first (each
term's weight and row belong to the same input), so the bound is per input.
Otherwise each term is bounded over its own tokens and weight interval
separately, which is sound and only loses precision.
"""

from __future__ import annotations

import math
from fractions import Fraction

import numpy as np

from .cost import Counter
from .interval import IT, _obj, exp, softmax
from .trace import UnsupportedOp

TABLES = "tables"
LEAF = "token_interval"


class TokenBox:
    """The input of a token_interval leaf: per position, the allowed tokens lo..hi."""

    def __init__(self, ranges, values: int):
        self.ranges = [(int(lo), int(hi)) for lo, hi in ranges]
        self.values = values
        self.tokens = [list(range(lo, hi + 1)) for lo, hi in self.ranges]

    @property
    def shape(self) -> tuple:
        return (1, len(self.ranges), self.values)


class Sep:
    """(1, positions, *rest); rows[p] is an exact IT of shape (tokens at p, *rest)."""

    def __init__(self, rows: list, tokens: list, pure: bool, origin: str):
        self.rows, self.tokens, self.pure, self.origin = rows, tokens, pure, origin

    @property
    def rest(self) -> tuple:
        return tuple(self.rows[0].shape[1:])

    @property
    def shape(self) -> tuple:
        return (1, len(self.rows)) + self.rest


class Term:
    """w * R[t] for t among tokens at position pos. R is exact, shape (len(tokens), *rest).
    w is an IT of shape () or, in a leaf with one varying position, (tokens there,): one weight per input.
    origin is the node where the term began and chain the constant matrix products applied since, in order:
    together with pos they determine its rows (two terms of one Mix can share origin and pos, as in
    h @ A + h @ B, and differ only in their chains)."""

    def __init__(self, w: IT, pos: int, tokens: list, rows: IT, pure: bool, origin: str, chain: tuple = ()):
        self.w, self.pos, self.tokens, self.rows, self.pure, self.origin = w, pos, tokens, rows, pure, origin
        self.chain = chain


class Mix:
    """const + the sum of its terms; shape (1, *rest)."""

    def __init__(self, const: IT, terms: list):
        self.const, self.terms = const, terms

    @property
    def shape(self) -> tuple:
        return tuple(self.const.shape)


class WSep:
    """w * sep with w broadcastable to sep's shape and a scalar per position (per input, if a Var)."""

    def __init__(self, w, sep: Sep):
        self.w, self.sep = w, sep

    @property
    def shape(self) -> tuple:
        return self.sep.shape


class Var:
    """A value per input of a leaf with one varying position: it has shape (tokens there, *shape)."""

    def __init__(self, it: IT):
        self.it = it

    @property
    def shape(self) -> tuple:
        return tuple(self.it.shape[1:])


DOMAIN = (TokenBox, Sep, Mix, WSep, Var)


def _one() -> IT:
    return IT.exact(_obj(np.array(1)), 0)


def _size(shape) -> int:
    return int(math.prod(shape)) if shape else 1


def _f(it: IT) -> int:
    """Cost factor: 1 for exact values, 2 for intervals (lower and upper ends)."""
    return 1 if it.is_exact else 2


def _min_max(r: IT) -> IT:
    """The box of an IT's entries over its first axis, keeping that axis with length 1."""
    if r.shape[0] == 1:
        return r
    lo = _obj(np.min(r.lo, axis=0))[None]
    if r.is_exact:
        return IT(lo, _obj(np.max(r.lo, axis=0))[None], r.exp)
    return IT(lo, _obj(np.max(r.hi, axis=0))[None], r.exp)


class TokenEvaluator:
    """Evaluates one token_interval leaf; memo (shared by the proof's leaves) holds the pure rows.

    An adopted rule (core/check/plugins.py) may subclass it: domain lists the kinds of values the evaluator
    keeps, category is where its per-leaf work is charged, and intercept may take over a node before the token
    rules see it (it returns None to decline, which is all this class does)."""

    domain = DOMAIN
    category = LEAF

    def intercept(self, n, env):
        return None

    def __init__(self, prog, memo: dict, counter: Counter, box: TokenBox):
        self.prog, self.memo, self.counter = prog, memo, counter
        varying = [p for p, toks in enumerate(box.tokens) if len(toks) > 1]
        self.pstar = varying[0] if len(varying) == 1 else None
        self.aligned = len(varying) <= 1  # every value can be kept per input
        self.k = len(box.tokens[self.pstar]) if self.pstar is not None else 1

    def charge(self, n) -> None:
        self.counter.add(self.category, int(n))

    # memoized rows ------------------------------------------------------------------------
    def rows(self, key: tuple, tokens: list, prev: IT, fn, cost_per_row: int, pure: bool) -> IT:
        """fn(prev), row by row; pure rows are kept under key and charged once per proof."""
        if not pure:
            out = fn(prev)
            self.charge(cost_per_row * len(tokens))
            return out
        store = self.memo.setdefault(key, {})
        missing = [i for i, t in enumerate(tokens) if t not in store]
        if missing:
            sub = fn(prev[missing])
            self.counter.add(TABLES, cost_per_row * len(missing))
            for r, i in enumerate(missing):
                store[tokens[i]] = (sub.lo[r], sub.exp)
        e = min(store[t][1] for t in tokens)
        lo = np.stack([_obj(store[t][0]) * (1 << (store[t][1] - e)) for t in tokens])
        return IT.exact(_obj(lo), e)

    # leaving the token domain ------------------------------------------------------------
    def to_var(self, v) -> Var:
        """A Sep, WSep or Mix as one value per input (only when at most one position varies)."""
        k = self.k
        if isinstance(v, Var):
            return v
        if isinstance(v, Sep):
            e = min(r.exp for r in v.rows)
            parts = []
            for r in v.rows:
                lo = r.at(e).lo  # (1 or k, *rest)
                parts.append(np.broadcast_to(lo, (k,) + lo.shape[1:]))
            lo = _obj(np.stack(parts, axis=1))[:, None]  # (k, 1, positions, *rest)
            return Var(IT.exact(lo, e))
        if isinstance(v, WSep):
            w = v.w.it if isinstance(v.w, Var) else v.w
            out = w * self.to_var(v.sep).it
            self.charge(_size(out.shape) * _f(out))
            return Var(out)
        if isinstance(v, Mix):
            out = v.const.unsqueeze(0)
            for t in v.terms:
                r = IT.exact(t.rows.lo[:, None], t.rows.exp)  # (1 or k, 1, *rest)
                w = _lead(t.w, len(r.shape))
                prod = w * r
                out = out + prod
                self.charge(2 * _size((k,) + tuple(r.shape[1:])) * _f(prod))
            if out.shape[0] != k:
                lo = np.broadcast_to(out.lo, (k,) + out.shape[1:])
                out = IT.exact(_obj(lo), out.exp) if out.is_exact else IT(_obj(lo), _obj(np.broadcast_to(out.hi, (k,) + out.shape[1:])), out.exp)
            return Var(out)
        raise UnsupportedOp("in token_interval leaves the input may only be multiplied by a weight matrix")

    def collapse(self, v) -> IT:
        """The value as an interval tensor without the token axis: sound, and exact when nothing varies."""
        if isinstance(v, TokenBox):
            raise UnsupportedOp("in token_interval leaves the input may only be multiplied by a weight matrix")
        if isinstance(v, Var):
            box = _min_max(v.it)
            if v.it.shape[0] > 1:
                self.charge(2 * _size(v.it.shape))
            return box[0]
        if isinstance(v, Sep):
            e = min(r.exp for r in v.rows)
            boxes = []
            for r in v.rows:
                if r.shape[0] > 1:
                    self.charge(2 * _size(r.shape))
                boxes.append(_min_max(r.at(e)))
            exact = all(b.is_exact for b in boxes)
            lo = _obj(np.concatenate([b.lo for b in boxes]))[None]
            if exact:
                return IT.exact(lo, e)
            return IT(lo, _obj(np.concatenate([b.hi for b in boxes]))[None], e)
        if isinstance(v, WSep):
            w = self.collapse(v.w) if isinstance(v.w, Var) else v.w
            box = self.collapse(v.sep)
            out = w * box
            self.charge(_size(out.shape) * _f(out))
            return out
        if isinstance(v, Mix):
            exact = self.concretize(v)
            if exact is not None:
                return exact
            out = v.const
            for t in v.terms:
                box = _min_max(t.rows)
                if t.rows.shape[0] > 1:
                    self.charge(2 * _size(t.rows.shape))
                w = t.w if t.w.ndim == 0 else IT(_obj(np.min(t.w.lo)), _obj(np.max(t.w.hi)), t.w.exp)
                prod = w * box
                out = out + prod
                self.charge(2 * _size(box.shape) * _f(prod))
            return out
        return v

    def concretize(self, v):
        """A Mix whose terms each hold one row with an exact scalar weight is one exact value; else None."""
        if not isinstance(v, Mix) or not v.const.is_exact:
            return None
        if not all(t.rows.shape[0] == 1 and t.w.is_exact and t.w.ndim == 0 for t in v.terms):
            return None
        out = v.const
        for t in v.terms:
            # the one row, keeping its leading axis: (1, *rest), also when the rows are scalars (rest empty)
            out = out + t.w * IT.exact(t.rows.lo[0:1], t.rows.exp)
            self.charge(2 * _size(v.const.shape))
        return out

    def leave(self, v):
        """What a domain value becomes for an operation the token rules do not cover."""
        if isinstance(v, Var):
            return v
        if isinstance(v, Mix):
            exact = self.concretize(v)
            if exact is not None:
                return exact
        if self.aligned and isinstance(v, (Sep, WSep, Mix)):
            return self.to_var(v)
        return self.collapse(v)

    # operations ---------------------------------------------------------------------------
    def evaluate(self, n, args, kwargs, free: list):
        """The node's value in the token domain, or None to leave the domain (see leave)."""
        k = n.kind
        a0 = args[0] if args else None
        if isinstance(a0, TokenBox):
            if k == "matmul":
                return self.lookup(n, a0, self.prog._tensor(args[1]), free[1])
            if k == "linear":
                w = self.prog.weights[f"{n.target}.weight"]
                out = self.lookup(n, a0, w.T, True)
                bias = self.prog.weights.get(f"{n.target}.bias")
                return out if bias is None else self.add_const(n, out, bias, True)
            raise UnsupportedOp("in token_interval leaves the input may only be multiplied by a weight matrix")
        if k == "mul" and len(args) == 2:
            x, y = args
            if isinstance(x, Var) and isinstance(y, Sep):
                return self.mul_var_sep(x, y)
            if isinstance(y, Var) and isinstance(x, Sep):
                return self.mul_var_sep(y, x)
        if any(isinstance(a, Var) for a in args) or any(isinstance(v, Var) for v in kwargs.values()):
            return self.var_op(n, args, kwargs)
        if k == "linear" and isinstance(a0, (Sep, Mix)):
            w = self.prog.weights[f"{n.target}.weight"]
            out = self.matmul(n, a0, w.T, True)
            bias = self.prog.weights.get(f"{n.target}.bias")
            if bias is None:
                return out
            return self.add_const(n, out, bias, True) if isinstance(out, Sep) else self.add_mix(out, bias)
        if k == "matmul" and isinstance(a0, (Sep, Mix)) and not isinstance(args[1], DOMAIN):
            b = self.prog._tensor(args[1])
            if b.ndim == 2 and b.is_exact:
                return self.matmul(n, a0, b, free[1])
            return None
        if k == "add":
            x, y = args
            if isinstance(x, Mix) and isinstance(y, Mix):
                return self.add_mixes(x, y)
            if isinstance(x, Mix) and not isinstance(y, DOMAIN):
                return self.add_mix(x, self.prog._tensor(y))
            if isinstance(y, Mix) and not isinstance(x, DOMAIN):
                return self.add_mix(y, self.prog._tensor(x))
            if isinstance(x, Sep) and not isinstance(y, DOMAIN):
                return self.add_const(n, x, self.prog._tensor(y), free[1])
            if isinstance(y, Sep) and not isinstance(x, DOMAIN):
                return self.add_const(n, y, self.prog._tensor(x), free[0])
            return None
        if k == "mul":
            x, y = args
            if isinstance(x, DOMAIN) and isinstance(y, DOMAIN):
                return None
            if isinstance(x, DOMAIN):
                v, c, c_free = x, self.prog._tensor(y), free[1]
            else:
                v, c, c_free = y, self.prog._tensor(x), free[0]
            if isinstance(v, Mix) and _size(c.shape) == 1:
                lo = _obj(c.lo.reshape(()))
                s = IT.exact(lo, c.exp) if c.is_exact else IT(lo, _obj(c.hi.reshape(())), c.exp)
                return self.scale_mix(v, s)
            if isinstance(v, Sep):
                return self.mul_sep(n, v, c, c_free)
            return None
        if k == "neg" and isinstance(a0, Mix):
            return self.scale_mix(a0, IT.exact(_obj(np.array(-1)), 0))
        if k == "sum" and isinstance(a0, (Sep, WSep)):
            dim = kwargs.get("dim", args[1] if len(args) > 1 else None)
            if dim is None or kwargs.get("keepdim"):
                return None
            nd = len(a0.shape)
            dim = int(dim)
            dim = dim if dim >= 0 else nd + dim
            if dim == 1:
                return self.sum_positions(n, a0)
            if isinstance(a0, Sep) and dim >= 2:
                return self.sum_rows(n, a0, dim)
            return None
        if k == "getitem" and isinstance(a0, Sep):
            idx = args[1]
            if (
                isinstance(idx, tuple)
                and len(idx) == 2
                and idx[0] == slice(None, None, None)
                and isinstance(idx[1], int)
                and not isinstance(idx[1], bool)
            ):
                p = idx[1] if idx[1] >= 0 else len(a0.rows) + idx[1]
                if not 0 <= p < len(a0.rows):
                    raise UnsupportedOp("position index out of range")
                const = IT.zeros((1,) + a0.rest)
                return Mix(const, [Term(_one(), p, a0.tokens[p], a0.rows[p], a0.pure, n.name)])
            return None
        return None

    def lookup(self, n, box: TokenBox, w: IT, w_free: bool) -> Sep:
        """x @ W on the leaf's tokens: row t of W, a lookup costing W's output size, once per token."""
        if w.ndim != 2 or w.shape[0] != box.values or not w.is_exact or not w_free:
            raise UnsupportedOp("in token_interval leaves the input may only be multiplied by a weight matrix")
        rows = []
        for p, toks in enumerate(box.tokens):
            ids = IT.exact(_obj(np.array(toks)), 0)  # the tokens themselves; fn reads W's rows at them
            rows.append(
                self.rows(
                    (n.name, n.name, p), toks, ids,
                    lambda sel: IT.exact(_obj(w.lo[[int(x) for x in sel.lo]]), w.exp),
                    w.shape[1], True,
                )
            )
        return Sep(rows, box.tokens, True, n.name)

    def add_const(self, n, sep: Sep, c: IT, c_free: bool):
        if not c.is_exact:
            return None
        try:
            b = np.broadcast_to(c.lo, sep.shape)
        except ValueError:
            return None
        pure = sep.pure and c_free
        rows = []
        for p, r in enumerate(sep.rows):
            cp = IT.exact(_obj(np.array(b[0, p])), c.exp)
            # "+" keeps these rows apart from the rows a linear node's own product keeps under (node, origin, p):
            # an nn.Linear with a bias multiplies and then adds the bias at the same node
            rows.append(self.rows((n.name, "+", sep.origin, p), sep.tokens[p], r, lambda R, cp=cp: R + cp, _size(sep.rest), pure))
        return Sep(rows, sep.tokens, pure, sep.origin)

    def mul_sep(self, n, sep: Sep, c: IT, c_free: bool):
        shape = sep.shape
        try:
            lo = np.broadcast_to(c.lo, shape)
            hi = np.broadcast_to(c.hi, shape)
        except ValueError:
            return None
        rest = shape[2:]
        first = (slice(None), slice(None)) + (slice(0, 1),) * len(rest)
        w_lo, w_hi = lo[first], hi[first]
        if np.all(lo == w_lo) and np.all(hi == w_hi):  # one weight per position
            w = IT.exact(_obj(np.array(w_lo)), c.exp) if c.is_exact else IT(_obj(np.array(w_lo)), _obj(np.array(w_hi)), c.exp)
            return WSep(w, sep)
        if not c.is_exact:
            return None
        pure = sep.pure and c_free
        rows = []
        for p, r in enumerate(sep.rows):
            cp = IT.exact(_obj(np.array(lo[0, p])), c.exp)
            rows.append(self.rows((n.name, sep.origin, p), sep.tokens[p], r, lambda R, cp=cp: R * cp, _size(rest), pure))
        return Sep(rows, sep.tokens, pure, sep.origin)

    def mul_var_sep(self, w: Var, sep: Sep):
        """Per-input weights times a Sep: kept apart (a WSep) when they are one weight per position."""
        shape = (w.it.shape[0],) + sep.shape
        try:
            lo = np.broadcast_to(w.it.lo, shape)
            hi = np.broadcast_to(w.it.hi, shape)
        except ValueError:
            return None
        rest = sep.shape[2:]
        first = (slice(None), slice(None), slice(None)) + (slice(0, 1),) * len(rest)
        w_lo, w_hi = lo[first], hi[first]
        if not (np.all(lo == w_lo) and np.all(hi == w_hi)):
            return None
        it = IT.exact(_obj(np.array(w_lo)), w.it.exp) if w.it.is_exact else IT(_obj(np.array(w_lo)), _obj(np.array(w_hi)), w.it.exp)
        return WSep(Var(it), sep)

    def sum_rows(self, n, sep: Sep, dim: int) -> Sep:
        axis = dim - 1  # a row holds the tokens in axis 0 where the tensor has its batch and positions
        rows = []
        for p, r in enumerate(sep.rows):
            size = _size(r.shape[1:])
            per_row = size - size // r.shape[axis]
            rows.append(self.rows((n.name, sep.origin, p), sep.tokens[p], r, lambda R, a=axis: R.sum(a), per_row, sep.pure))
        return Sep(rows, sep.tokens, sep.pure, sep.origin)

    def sum_positions(self, n, v) -> Mix:
        sep = v.sep if isinstance(v, WSep) else v
        rest = sep.rest
        terms = []
        for p, r in enumerate(sep.rows):
            if not isinstance(v, WSep):
                w = _one()
            elif isinstance(v.w, Var):
                w = v.w.it[(slice(None), 0, p) + (0,) * len(rest)]  # one weight per input
            else:
                w = v.w[(0, p) + (0,) * len(rest)]
            terms.append(Term(w, p, sep.tokens[p], r, sep.pure, n.name))
        return Mix(IT.zeros((1,) + rest), terms)

    def matmul(self, n, v, b: IT, b_free: bool):
        cost = b.shape[0] * b.shape[1]
        if isinstance(v, Sep):
            pure = v.pure and b_free
            rows = [self.rows((n.name, v.origin, p), v.tokens[p], r, lambda R: R @ b, cost, pure) for p, r in enumerate(v.rows)]
            return Sep(rows, v.tokens, pure, v.origin)
        terms = []
        for t in v.terms:
            pure = t.pure and b_free
            # kept under the term's whole chain, not just (node, origin, pos): see Term
            rows = self.rows((n.name, t.origin, t.pos, t.chain), t.tokens, t.rows, lambda R: R @ b, cost, pure)
            terms.append(Term(t.w, t.pos, t.tokens, rows, pure, t.origin, t.chain + (n.name,)))
        if v.const.is_exact and not np.any(v.const.lo):  # a zero constant stays zero (checked entry by entry)
            const = IT.zeros(v.const.shape[:-1] + (b.shape[1],))
            self.charge(_size(v.const.shape))
        else:
            const = v.const @ b
            self.charge(_size(const.shape) * b.shape[0] * _f(v.const))
        return Mix(const, terms)

    def add_mix(self, v: Mix, c: IT) -> Mix:
        const = v.const + c
        self.charge(_size(const.shape) * _f(const))
        return Mix(const, list(v.terms))

    def add_mixes(self, x: Mix, y: Mix) -> Mix:
        const = x.const + y.const
        self.charge(_size(const.shape) * _f(const))
        return Mix(const, list(x.terms) + list(y.terms))

    def scale_mix(self, v: Mix, s: IT) -> Mix:
        terms = [Term(t.w * s, t.pos, t.tokens, t.rows, t.pure, t.origin, t.chain) for t in v.terms]
        const = v.const * s
        self.charge((sum(_size(t.w.shape) for t in v.terms) + _size(const.shape)) * _f(s))
        return Mix(const, terms)

    # values per input (one varying position) ------------------------------------------------
    def var_op(self, n, args, kwargs):
        """An operation on Var values: the same operation on the leading token axis's every entry."""
        k = n.kind
        if not self.aligned:
            raise RuntimeError("internal error: a Var in a leaf with several varying positions")

        def it(a):
            if isinstance(a, Var):
                return a.it
            if isinstance(a, DOMAIN):
                return self.to_var(a).it
            return self.prog._tensor(a).unsqueeze(0)

        def shift(d, nd):
            d = int(d)
            return d + 1 if d >= 0 else d  # negative dimensions count from the end and stay put

        if k in ("add", "sub", "mul"):
            x, y = it(args[0]), it(args[1])
            out = x + y if k == "add" else x - y if k == "sub" else x * y
            self.charge(_size(out.shape) * _f(out))
            return Var(out)
        if k == "neg":
            out = -it(args[0])
            self.charge(_size(out.shape))
            return Var(out)
        if k == "matmul":
            x = it(args[0])
            if isinstance(args[1], DOMAIN):
                return None
            b = self.prog._tensor(args[1])
            out = x @ b
            self.charge(_size(out.shape) * b.shape[0] * (1 if (x.is_exact and b.is_exact) else 2))
            return Var(out)
        if k == "unsqueeze":
            d = kwargs.get("dim", args[1] if len(args) > 1 else None)
            return Var(it(args[0]).unsqueeze(shift(d, None)))
        if k == "sum":
            d = kwargs.get("dim", args[1] if len(args) > 1 else None)
            if d is None or kwargs.get("keepdim"):
                return None
            x = it(args[0])
            dd = shift(d, None)
            out = x.sum(dd)
            self.charge(_size(out.shape) * (x.shape[dd] - 1) * _f(x))
            return Var(out)
        if k == "softmax":
            d = kwargs.get("dim", args[1] if len(args) > 1 else None)
            x = it(args[0])
            dd = shift(d, None)
            dd = dd if dd >= 0 else x.ndim + dd
            self.charge(6 * _size(x.shape))
            return Var(softmax(x, dd))
        if k == "exp":
            x = it(args[0])
            self.charge(2 * _size(x.shape))
            return Var(exp(x))
        if k == "getitem":
            idx = args[1]
            idx = idx if isinstance(idx, tuple) else (idx,)
            if any(isinstance(i, DOMAIN) for i in idx):
                return None
            return Var(it(args[0])[(slice(None),) + idx])
        return None

    # the decision ------------------------------------------------------------------------------
    def lower_margin(self, v, label: int):
        """(lowest margin bound as a Fraction, the other output reaching it)."""
        if isinstance(v, (Sep, WSep)):
            v = self.leave(v)
        if isinstance(v, Var):
            x = v.it
            lo = _obj(x.lo.reshape(x.shape[0], -1))
            out = IT.exact(lo, x.exp) if x.is_exact else IT(lo, _obj(x.hi.reshape(x.shape[0], -1)), x.exp)
            margins = self.prog._lower_margins(out, [label] * out.shape[0])
            self.charge(out.shape[0] * out.shape[1])
            m, j = min(margins, key=lambda x: (x[0] is None, x[0]))
            if m is None:
                return Fraction(1), -1
            return Fraction(m) * Fraction(2) ** out.exp, j
        if isinstance(v, IT):
            n_out = v.shape[1]
            (m, j), = self.prog._lower_margins(v, [label])
            self.charge(n_out - 1)
            if m is None:
                return Fraction(1), -1
            return Fraction(m) * Fraction(2) ** v.exp, j
        n_out = v.shape[1]
        if not 0 <= label < n_out:
            raise UnsupportedOp("label outside the network's outputs")
        c = v.const
        exps = [c.exp] + [t.w.exp + t.rows.exp for t in v.terms]
        e0 = min(exps)
        cm = (_obj(c.lo[0, label]) - _obj(c.hi[0])) * (1 << (c.exp - e0))  # (n_out,)
        self.charge(n_out - 1)
        if self.aligned:
            acc = np.broadcast_to(cm, (self.k, n_out)).astype(object)
        else:
            acc = cm.astype(object)
        for t in v.terms:
            R = t.rows.lo  # (tokens, n_out)
            D = R[:, [label]] - R
            wl = _obj(t.w.lo).reshape(-1, 1)
            wh = _obj(t.w.hi).reshape(-1, 1)
            sh = 1 << (t.w.exp + t.rows.exp - e0)
            if self.aligned:
                # rows and weights both have 1 entry or one per input of the leaf: line them up per input
                exact_w = t.w.is_exact
                lo = (wl * D if exact_w else np.minimum(wl * D, wh * D)) * sh
                acc = acc + np.broadcast_to(lo, (self.k, n_out))
                # per input and other output: a difference, the products with the weight's ends, their minimum, a sum
                self.charge((3 if exact_w else 5) * max(R.shape[0], wl.shape[0]) * (n_out - 1))
            else:
                dmin, dmax = np.min(D, axis=0), np.max(D, axis=0)
                w_lo, w_hi = wl.min(), wh.max()
                lo = np.minimum(np.minimum(w_lo * dmin, w_lo * dmax), np.minimum(w_hi * dmin, w_hi * dmax)) * sh
                acc = acc + lo
                self.charge((3 * R.shape[0] + 8) * (n_out - 1))
        acc = acc.reshape(-1, n_out)
        acc[:, label] = None
        best, arg = None, -1
        for row in acc:
            for j, b in enumerate(row):
                if b is not None and (best is None or b < best):
                    best, arg = b, j
        self.charge(acc.shape[0] * (n_out - 1))
        if best is None:
            return Fraction(1), -1
        return Fraction(best) * Fraction(2) ** e0, arg


def _lead(w: IT, nd: int) -> IT:
    """A weight of shape () or (k,) reshaped to broadcast against (k, 1, *rest) of nd dimensions."""
    shape = (w.shape[0],) + (1,) * (nd - 1) if w.ndim == 1 else (1,) * nd
    lo = _obj(np.asarray(w.lo).reshape(shape))
    if w.is_exact:
        return IT.exact(lo, w.exp)
    return IT(lo, _obj(np.asarray(w.hi).reshape(shape)), w.exp)
