"""Networks beyond linear maps: a sound interval interpreter over the traced graph.

A network whose model.py uses only nn.Linear, sums and additions is checked by
core.check.evaluate, exactly. Any other network is traced here with torch.fx
and must use only the operations in OPS below. The interpreter evaluates the
traced graph on interval tensors (core.check.interval): sums and products are
exact, exp and the division in softmax are enclosed by rational bounds rounded
outwards, so every value the network computes lies inside the interval the
interpreter computes for it.

Single leaves run the graph on concrete inputs. Interval leaves run it on a
box of inputs: the input may then only be multiplied by a weight matrix (a
lookup of one-hot rows), which gives, per position, the smallest and largest
value of each entry over the allowed tokens; everything after that is interval
arithmetic. The parts of the graph that do not depend on the input are
computed once per proof and charged to extract.

The contract and approximate rules need a network of linear maps and are
refused here; symmetry is refused too (the check that the input is used only
through a sum over positions is made for linear graphs only).
"""

from __future__ import annotations

import builtins
import math
import operator
from fractions import Fraction

import numpy as np

from .arith import Exact
from .cost import Counter
from .evaluate import CheckError
from .interval import IT, concat, exp, softmax
from .tokens import TokenBox, TokenEvaluator, Var
from .trace import UnsupportedOp

# (fx op, target) -> name used by the interpreter
_FUNCTIONS = {
    operator.getitem: "getitem",
    builtins.getattr: "getattr",
    operator.add: "add",
    operator.sub: "sub",
    operator.mul: "mul",
    operator.neg: "neg",
    operator.matmul: "matmul",
}
_METHODS = {"unsqueeze", "expand", "sum", "softmax", "exp", "size", "transpose"}

# Per operation: the most positional arguments and the keyword arguments accepted. Anything else is
# refused when the graph is traced, so no argument is ever silently ignored (torch.cat(..., axis=1),
# say, would otherwise be read as dim 0).
_SIGNATURES = {
    "getitem": (2, set()),
    "getattr": (2, set()),
    "add": (2, set()),
    "sub": (2, set()),
    "mul": (2, set()),
    "neg": (1, set()),
    "matmul": (2, set()),
    "linear": (1, set()),
    "cat": (2, {"dim"}),
    "stack": (2, {"dim"}),
    "softmax": (2, {"dim", "dtype", "_stacklevel"}),
    "exp": (1, set()),
    "sum": (2, {"dim"}),
    "zeros_like": (1, set()),
    "unsqueeze": (2, {"dim"}),
    "expand": (None, set()),
    "size": (2, {"dim"}),
    "transpose": (3, {"dim0", "dim1"}),
}


def _check_signature(name: str, kind: str, args, kwargs) -> None:
    most, allowed = _SIGNATURES[kind]
    extra = set(kwargs) - allowed
    if extra:
        raise UnsupportedOp(f"{name}: {kind} with keyword arguments {sorted(extra)}")
    if most is not None and len(args) > most:
        raise UnsupportedOp(f"{name}: {kind} with {len(args)} arguments")
    if kind == "softmax" and kwargs.get("dtype") is not None:
        raise UnsupportedOp(f"{name}: softmax with a dtype")
_ATTRIBUTES = {"shape", "T"}


def _torch_functions() -> dict:
    import torch

    return {
        torch.matmul: "matmul",
        torch.add: "add",
        torch.sub: "sub",
        torch.mul: "mul",
        torch.cat: "cat",
        torch.stack: "stack",
        torch.softmax: "softmax",
        torch.nn.functional.softmax: "softmax",
        torch.exp: "exp",
        torch.sum: "sum",
        torch.zeros_like: "zeros_like",
        torch.unsqueeze: "unsqueeze",
    }


class Node:
    def __init__(self, name, kind, args, kwargs, target=None):
        self.name, self.kind, self.args, self.kwargs, self.target = name, kind, args, kwargs, target


class GeneralGraph:
    """The traced graph of a network with operations beyond linear maps."""

    general = True

    def __init__(self, nodes: list[Node], input: str, output, params: list[str]):
        self.nodes, self.input, self.output, self.params = nodes, input, output, params

    def summed_over_positions_first(self) -> bool:
        return False

    def linear_names(self) -> list[str]:
        return []

    def describe(self) -> list[dict]:
        return [{"name": n.name, "op": n.kind, "args": [str(a) for a in n.args]} for n in self.nodes]


def build_general_graph(module) -> GeneralGraph:
    import torch.fx

    fns = {**_FUNCTIONS, **_torch_functions()}
    gm = torch.fx.symbolic_trace(module)
    params = dict(module.named_parameters())
    params.update(dict(module.named_buffers()))
    nodes, inp, out = [], None, None

    def conv(a):
        if isinstance(a, torch.fx.Node):
            return ("node", a.name)
        if isinstance(a, (list, tuple)):
            return type(a)(conv(x) for x in a)
        if isinstance(a, slice):
            return slice(conv(a.start), conv(a.stop), conv(a.step))
        if a is None or a is Ellipsis or isinstance(a, (bool, int, float, str)):
            return a
        raise UnsupportedOp(f"an argument of type {type(a).__name__}")

    for fx in gm.graph.nodes:
        args, kwargs = conv(tuple(fx.args)), {k: conv(v) for k, v in fx.kwargs.items()}
        if fx.op == "placeholder":
            if inp is not None:
                raise UnsupportedOp("the module must take exactly one input")
            inp = fx.name
            nodes.append(Node(fx.name, "input", (), {}))
        elif fx.op == "get_attr":
            if fx.target not in params:
                raise UnsupportedOp(f"{fx.target} is not a parameter")
            nodes.append(Node(fx.name, "param", (), {}, fx.target))
        elif fx.op == "call_function":
            kind = fns.get(fx.target)
            if kind is None:
                raise UnsupportedOp(f"function {getattr(fx.target, '__name__', fx.target)}")
            if kind == "getattr" and (len(args) != 2 or args[1] not in _ATTRIBUTES):
                raise UnsupportedOp(f"attribute {args[1:]!r}")
            _check_signature(fx.name, kind, args, kwargs)
            nodes.append(Node(fx.name, kind, args, kwargs))
        elif fx.op == "call_module":
            sub = gm.get_submodule(fx.target)
            if not isinstance(sub, torch.nn.Linear) or len(args) != 1 or kwargs:
                raise UnsupportedOp(f"module {fx.target} of type {type(sub).__name__}")
            _check_signature(fx.name, "linear", args, kwargs)
            nodes.append(Node(fx.name, "linear", args, {}, fx.target))
        elif fx.op == "call_method":
            if fx.target not in _METHODS:
                raise UnsupportedOp(f"method {fx.target}")
            _check_signature(fx.name, fx.target, args, kwargs)
            nodes.append(Node(fx.name, fx.target, args, kwargs))
        elif fx.op == "output":
            out = conv(fx.args[0])
        else:
            raise UnsupportedOp(f"{fx.op} {fx.target}")
    if inp is None or out is None or not (isinstance(out, tuple) and len(out) == 2 and out[0] == "node"):
        raise UnsupportedOp("the module needs one input and one output tensor")
    return GeneralGraph(nodes, inp, out[1], sorted(params))


class OneHotBox:
    """A box of one-hot inputs: per position, the tokens lo..hi (inclusive)."""

    def __init__(self, ranges, values: int):
        self.ranges = [(int(lo), int(hi)) for lo, hi in ranges]
        self.values = values

    @property
    def shape(self) -> tuple:
        return (1, len(self.ranges), self.values)


def _dim(args, kwargs, pos: int, name: str = "dim"):
    if name in kwargs:
        return kwargs[name]
    if len(args) > pos:
        return args[pos]
    raise UnsupportedOp(f"{name} must be given")


class GeneralProgram:
    """The interpreter, with the weights converted exactly and the input-free part computed once."""

    def __init__(self, graph: GeneralGraph, weights: dict[str, np.ndarray], counter: Counter, space: list[int]):
        self.graph = graph
        if len(set(space)) != 1:
            raise UnsupportedOp("one-hot inputs need the same number of values at every position")
        self._n_values = int(space[0])
        missing = [p for p in graph.params if p not in weights]
        if missing:
            raise CheckError(f"weights {missing} are missing")
        self.weights = {k: IT.from_exact(Exact.from_float(weights[k])) for k in graph.params}
        n_params = int(sum(np.asarray(weights[k]).size for k in graph.params))
        counter.add("extract", n_params)
        self.n_params = n_params
        # Which nodes depend on the input.
        self.depends = {}
        for n in graph.nodes:
            self.depends[n.name] = n.kind == "input" or any(self._refs_input(a) for a in (*n.args, *n.kwargs.values()))
        # Rows of token_interval leaves that depend on their token alone, kept for the whole proof.
        self._token_memo = {}
        # Compute the input-free nodes once, charged to extract.
        self.const = {}
        for n in graph.nodes:
            if not self.depends[n.name]:
                self.const[n.name] = self._eval(n, self.const, counter, "extract", 1)

    def _refs_input(self, a) -> bool:
        if isinstance(a, tuple) and len(a) == 2 and a[0] == "node":
            return self.depends[a[1]]
        if isinstance(a, (list, tuple)):
            return any(self._refs_input(x) for x in a)
        if isinstance(a, slice):
            return any(self._refs_input(x) for x in (a.start, a.stop, a.step))
        return False

    # rules that need a linear network -------------------------------------------
    def contract(self, cname, chain, counter):
        raise CheckError("the contract rule needs a network built only from linear maps, sums and additions")

    def linear(self, name: str):
        raise KeyError(name)

    # evaluation ------------------------------------------------------------------------
    def _value(self, a, env):
        if isinstance(a, tuple) and len(a) == 2 and a[0] == "node":
            return env[a[1]]
        if isinstance(a, list):
            return [self._value(x, env) for x in a]
        if isinstance(a, tuple):
            return tuple(self._value(x, env) for x in a)
        if isinstance(a, slice):
            return slice(self._value(a.start, env), self._value(a.stop, env), self._value(a.step, env))
        return a

    @staticmethod
    def _tensor(v) -> IT:
        if isinstance(v, IT):
            return v
        if isinstance(v, (int, float)) and not isinstance(v, bool):
            return IT.from_exact(Exact.from_float(np.asarray(v, dtype=np.float64)))
        raise UnsupportedOp(f"a value of type {type(v).__name__} where a tensor is needed")

    def _eval(self, n: Node, env: dict, counter: Counter, category: str, factor: int):
        args = self._value(n.args, env)
        kwargs = {k: self._value(v, env) for k, v in n.kwargs.items()}
        k = n.kind

        def charge(ops):
            if ops:
                counter.add(category, factor * int(ops))

        if k == "param":
            return self.weights[n.target]
        if k == "linear":  # an nn.Linear submodule: x @ weight.T + bias
            w = self.weights[f"{n.target}.weight"]
            if isinstance(args[0], OneHotBox):
                out = self._onehot_lookup(args[0], w.T, counter)
            else:
                x = self._tensor(args[0])
                out = x @ w.T
                lookup = n.args[0] == ("node", self.graph.input)
                charge(math.prod(out.shape) * (1 if lookup else w.shape[1]))
            bias = self.weights.get(f"{n.target}.bias")
            if bias is not None:
                out = out + bias
                charge(math.prod(out.shape))
            return out
        if k == "getattr":
            x, attr = args
            if attr == "shape":
                return tuple(x.shape)
            if not isinstance(x, IT) or x.ndim > 2:
                raise UnsupportedOp(".T of something other than a matrix")
            return x.T
        if k == "getitem":
            x, idx = args
            if isinstance(x, (tuple, list)):
                return x[idx]
            if isinstance(x, OneHotBox):
                raise UnsupportedOp("in interval leaves the input may only be multiplied by a weight matrix")
            return self._tensor(x)[idx]
        if k == "size":
            x = args[0]
            dim = kwargs.get("dim", args[1] if len(args) > 1 else None)
            return tuple(x.shape) if dim is None else x.shape[int(dim)]
        if any(isinstance(a, OneHotBox) for a in args) and not (k in ("matmul", "linear") and isinstance(args[0], OneHotBox)):
            raise UnsupportedOp("in interval leaves the input may only be multiplied by a weight matrix")
        if k == "matmul":
            a, b = args
            if isinstance(a, OneHotBox):
                return self._onehot_lookup(a, self._tensor(b), counter)
            a, b = self._tensor(a), self._tensor(b)
            out = a @ b
            if n.args[0] == ("node", self.graph.input):  # a one-hot input picks rows: a lookup per position
                charge(math.prod(out.shape))
            else:
                charge(math.prod(out.shape) * (a.shape[-1] if a.ndim else 1))
            return out
        if k in ("add", "sub", "mul"):
            if kwargs:
                raise UnsupportedOp(f"{k} with keyword arguments")
            a, b = self._tensor(args[0]), self._tensor(args[1])
            out = a + b if k == "add" else a - b if k == "sub" else a * b
            charge(math.prod(out.shape))
            return out
        if k == "neg":
            out = -self._tensor(args[0])
            charge(math.prod(out.shape))
            return out
        if k == "unsqueeze":
            return self._tensor(args[0]).unsqueeze(int(_dim(args, kwargs, 1)))
        if k == "expand":
            sizes = args[1:]
            if len(sizes) == 1 and isinstance(sizes[0], (tuple, list)):
                sizes = sizes[0]
            return self._tensor(args[0]).expand([int(s) for s in sizes])
        if k == "transpose":
            x = self._tensor(args[0])
            d0 = kwargs.get("dim0", args[1] if len(args) > 1 else None)
            d1 = kwargs.get("dim1", args[2] if len(args) > 2 else None)
            if d0 is None or d1 is None:
                raise UnsupportedOp("transpose needs two dimensions")
            d0, d1 = int(d0), int(d1)
            if x.ndim != 2 or not (-2 <= d0 < 2 and -2 <= d1 < 2) or d0 % 2 == d1 % 2:
                raise UnsupportedOp("transpose of something other than a matrix")
            return x.T
        if k in ("cat", "stack"):
            parts = [self._tensor(v) for v in args[0]]
            dim = int(_dim(args, kwargs, 1)) if (len(args) > 1 or "dim" in kwargs) else 0
            if k == "cat":
                return concat(parts, dim)
            d = dim if dim >= 0 else parts[0].ndim + 1 + dim
            return concat(parts, d, stack=True)
        if k == "sum":
            if kwargs.get("keepdim") or (set(kwargs) - {"dim"}) or len(args) > 2:
                raise UnsupportedOp("sum with keepdim or extra arguments")
            x = self._tensor(args[0])
            dim = int(_dim(args, kwargs, 1))
            out = x.sum(dim)
            charge(math.prod(out.shape) * (x.shape[dim] - 1))
            return out
        if k == "exp":
            x = self._tensor(args[0])
            charge(math.prod(x.shape))
            return exp(x)
        if k == "softmax":
            x = self._tensor(args[0])
            dim = int(_dim(args, kwargs, 1))
            charge(3 * math.prod(x.shape))
            return softmax(x, dim if dim >= 0 else x.ndim + dim)
        if k == "zeros_like":
            return IT.zeros(self._tensor(args[0]).shape)
        raise UnsupportedOp(k)

    def _onehot_lookup(self, box: OneHotBox, w: IT, counter: Counter) -> IT:
        """x @ W for every x in the box: per position, the min and max of W's rows over the allowed tokens."""
        if w.ndim != 2 or w.shape[0] != box.values or not w.is_exact:
            raise UnsupportedOp("in interval leaves the input may only be multiplied by a weight matrix")
        d = w.shape[1]
        lo_rows, hi_rows = [], []
        for lo, hi in box.ranges:
            block = w.lo[lo : hi + 1]
            lo_rows.append(np.min(block, axis=0))
            hi_rows.append(np.max(block, axis=0))
            counter.add("interval", d if lo == hi else 2 * d * (hi - lo + 1))
        lo = np.array(lo_rows, dtype=object)[None]
        hi = np.array(hi_rows, dtype=object)[None]
        return IT(lo, hi, w.exp)

    def _run(self, x, counter: Counter, category: str, factor: int) -> IT:
        env = dict(self.const)
        for n in self.graph.nodes:
            if n.name in env:
                continue
            env[n.name] = x if n.kind == "input" else self._eval(n, env, counter, category, factor)
        out = env[self.graph.output]
        if not isinstance(out, IT) or out.ndim != 2:
            raise UnsupportedOp("the network's output must be (batch, outputs) logits")
        return out

    @staticmethod
    def _lower_margins(out: IT, labels) -> list[tuple[int, int]]:
        """Per row: (lower bound of label output minus the largest other upper bound, the other output), at out.exp."""
        res = []
        n_out = out.shape[1]
        for r, lab in enumerate(labels):
            own = int(out.lo[r, lab])
            best, j = None, -1
            for o in range(n_out):
                if o == lab:
                    continue
                v = own - int(out.hi[r, o])
                if best is None or v < best:
                    best, j = v, o
            res.append((best, j))
        return res

    # leaves --------------------------------------------------------------------------
    def run_singles(self, tokens: np.ndarray, labels: np.ndarray, counter: Counter, chunk: int = 512):
        ok = np.zeros(len(tokens), dtype=bool)
        margins = np.zeros(len(tokens), dtype=float)
        for i in range(0, len(tokens), chunk):
            t, lab = tokens[i : i + chunk], labels[i : i + chunk]
            onehot = np.zeros((len(t), t.shape[1], self._n_values), dtype=object)
            for r in range(len(t)):
                for p in range(t.shape[1]):
                    onehot[r, p, int(t[r, p])] = 1
            out = self._run(IT.exact(onehot, 0), counter, "single", 1)
            n_out = out.shape[1]
            if out.shape[0] != len(t):
                raise UnsupportedOp("the network's output must be (batch, outputs) logits")
            if lab.min() < 0 or lab.max() >= n_out:
                raise CheckError("labels outside the network's outputs")
            for r, (m, _) in enumerate(self._lower_margins(out, lab)):
                ok[i + r] = m is None or m > 0
                margins[i + r] = float("inf") if m is None else _to_float(m, out.exp)
            counter.add("single", len(t) * (n_out - 1))
        return ok, margins

    def run_interval(self, ranges: list, label: int, counter: Counter, approx=None):
        if approx is not None:
            raise CheckError("the approximate rule needs a network built only from linear maps")
        out = self._run(OneHotBox(ranges, self._n_values), counter, "interval", 2)
        if out.shape[0] != 1:
            raise UnsupportedOp("the network's output must be (batch, outputs) logits")
        n_out = out.shape[1]
        if not 0 <= label < n_out:
            raise CheckError("label outside the network's outputs")
        (m, j), = self._lower_margins(out, [label])
        counter.add("interval", n_out - 1)
        if m is None:
            return True, Fraction(1), -1
        return bool(m > 0), Fraction(m) * Fraction(2) ** out.exp, j


    def run_token_interval(self, ranges: list, label: int, counter: Counter):
        """A token_interval leaf (core.check.tokens): (certified, lowest margin bound, the other output reaching it)."""
        return self.run_token_leaf(ranges, label, counter, TokenEvaluator)

    def run_token_leaf(self, ranges: list, label: int, counter: Counter, evaluator=TokenEvaluator, memo: dict | None = None):
        """One leaf evaluated in a token domain: token_interval's (TokenEvaluator) or an adopted rule's subclass of
        it, which may keep more kinds of values (evaluator.domain) and take over nodes before the token rules see
        them (evaluator.intercept). Returns (certified, lowest margin bound, the other output reaching it)."""
        box = TokenBox(ranges, self._n_values)
        ev = evaluator(self, self._token_memo if memo is None else memo, counter, box)
        env = dict(self.const)
        for n in self.graph.nodes:
            if n.name in env:
                continue
            env[n.name] = box if n.kind == "input" else self._eval_token(n, env, ev, counter)
        out = env[self.graph.output]
        if len(out.shape) != 2 or out.shape[0] != 1:
            raise UnsupportedOp("the network's output must be (batch, outputs) logits")
        if not 0 <= label < out.shape[1]:
            raise CheckError("label outside the network's outputs")
        m, j = ev.lower_margin(out, label)
        return bool(m > 0), m, j

    def _eval_token(self, n: Node, env: dict, ev: TokenEvaluator, counter: Counter):
        domain = ev.domain
        v = ev.intercept(n, env)
        if v is not None:
            return v
        names = _node_refs((*n.args, *n.kwargs.values()))
        if not any(isinstance(env.get(x), domain) for x in names):
            return self._eval(n, env, counter, ev.category, 2)
        args = self._value(n.args, env)
        kwargs = {k: self._value(v, env) for k, v in n.kwargs.items()}
        if n.kind == "getattr" and args[1] == "shape" and isinstance(args[0], domain):
            return tuple(args[0].shape)
        if n.kind == "size" and isinstance(args[0], domain):
            dim = kwargs.get("dim", args[1] if len(args) > 1 else None)
            return tuple(args[0].shape) if dim is None else args[0].shape[int(dim)]
        free = [not self._refs_input(a) for a in n.args]
        v = ev.evaluate(n, args, kwargs, free)
        if v is not None:
            return v
        env2 = dict(env)
        for x in names:
            if isinstance(env.get(x), domain):
                env2[x] = ev.leave(env[x])
        if any(isinstance(env2.get(x), Var) for x in names):
            args2 = self._value(n.args, env2)
            kwargs2 = {k: self._value(v, env2) for k, v in n.kwargs.items()}
            v = ev.var_op(n, args2, kwargs2)
            if v is not None:
                return v
            for x in names:
                if isinstance(env2.get(x), Var):
                    env2[x] = ev.collapse(env2[x])
        return self._eval(n, env2, counter, ev.category, 2)


def _node_refs(a) -> list[str]:
    if isinstance(a, tuple) and len(a) == 2 and a[0] == "node":
        return [a[1]]
    if isinstance(a, (list, tuple)):
        return [x for v in a for x in _node_refs(v)]
    if isinstance(a, slice):
        return _node_refs((a.start, a.stop, a.step))
    return []


def _to_float(m: int, exp: int) -> float:
    try:
        return float(Fraction(m) * Fraction(2) ** exp)
    except OverflowError:
        return float("inf") if m > 0 else float("-inf")
