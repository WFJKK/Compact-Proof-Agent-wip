"""The network's computation graph, traced from its model.py with torch.fx.

The graph has one input, the one-hot tokens of shape (batch, positions,
values), and one output, the logits of shape (batch, outputs). Supported
operations, a list that grows only when a model needs more:

    linear   a torch.nn.Linear submodule (with or without bias)
    sum      x.sum(dim) or torch.sum(x, dim), over one dimension
    add      x + y or torch.add(x, y), both operands computed by the graph

An unsupported operation stops the check with its name; there is no float
fallback.
"""

from __future__ import annotations

import operator
from dataclasses import dataclass, field


class UnsupportedOp(ValueError):
    pass


@dataclass
class Node:
    name: str
    op: str  # input | linear | sum | add
    args: list[str] = field(default_factory=list)
    weight: str | None = None
    bias: str | None = None
    in_features: int | None = None
    out_features: int | None = None
    dim: int | None = None


@dataclass
class Graph:
    nodes: list[Node]
    input: str
    output: str

    def node(self, name: str) -> Node:
        for n in self.nodes:
            if n.name == name:
                return n
        raise KeyError(name)

    def users(self, name: str) -> list[str]:
        return [n.name for n in self.nodes if name in n.args]

    def linear_names(self) -> list[str]:
        return [n.name for n in self.nodes if n.op == "linear"]

    def describe(self) -> list[dict]:
        out = []
        for n in self.nodes:
            d = {"name": n.name, "op": n.op, "args": list(n.args)}
            if n.op == "linear":
                d.update(in_features=n.in_features, out_features=n.out_features, bias=n.bias is not None)
            if n.op == "sum":
                d["dim"] = n.dim
            out.append(d)
        return out

    def summed_over_positions_first(self) -> bool:
        """True if the input is used only by a sum over the positions dimension.

        Then the output depends on the input only through that sum, so it is
        the same for every reordering of the input's positions.
        """
        users = self.users(self.input)
        if len(users) != 1:
            return False
        u = self.node(users[0])
        return u.op == "sum" and u.dim in (1, -2)


def build_graph(module) -> Graph:
    import torch
    import torch.fx

    gm = torch.fx.symbolic_trace(module)
    nodes: list[Node] = []
    names: dict = {}
    inp = out = None
    for fx in gm.graph.nodes:
        if fx.op == "placeholder":
            if inp is not None:
                raise UnsupportedOp("the module must take exactly one input")
            inp = fx.name
            nodes.append(Node(fx.name, "input"))
        elif fx.op == "call_module":
            sub = gm.get_submodule(fx.target)
            if not isinstance(sub, torch.nn.Linear):
                raise UnsupportedOp(f"module {fx.target} of type {type(sub).__name__}")
            if len(fx.args) != 1 or fx.kwargs or not isinstance(fx.args[0], torch.fx.Node):
                raise UnsupportedOp(f"call of {fx.target} with unexpected arguments")
            nodes.append(
                Node(
                    fx.name,
                    "linear",
                    [fx.args[0].name],
                    weight=f"{fx.target}.weight",
                    bias=f"{fx.target}.bias" if sub.bias is not None else None,
                    in_features=sub.in_features,
                    out_features=sub.out_features,
                )
            )
        elif (fx.op == "call_method" and fx.target == "sum") or (fx.op == "call_function" and fx.target is torch.sum):
            args = list(fx.args)
            kwargs = dict(fx.kwargs)
            if not args or not isinstance(args[0], torch.fx.Node):
                raise UnsupportedOp("sum of something that is not a graph value")
            dim = args[1] if len(args) > 1 else kwargs.pop("dim", None)
            if kwargs.pop("keepdim", False) or kwargs or len(args) > 2:
                raise UnsupportedOp("sum with keepdim or extra arguments")
            if not isinstance(dim, int):
                raise UnsupportedOp("sum must be over exactly one dimension")
            nodes.append(Node(fx.name, "sum", [args[0].name], dim=dim))
        elif fx.op == "call_function" and fx.target in (operator.add, torch.add):
            if len(fx.args) != 2 or fx.kwargs or not all(isinstance(a, torch.fx.Node) for a in fx.args):
                raise UnsupportedOp("add must combine two graph values")
            nodes.append(Node(fx.name, "add", [a.name for a in fx.args]))
        elif fx.op == "output":
            res = fx.args[0]
            if not isinstance(res, torch.fx.Node):
                raise UnsupportedOp("the module must return a single tensor")
            out = res.name
        else:
            target = getattr(fx.target, "__name__", fx.target)
            raise UnsupportedOp(f"{fx.op} {target}")
        names[fx.name] = True
    if inp is None or out is None:
        raise UnsupportedOp("the module needs one input and one output")
    return Graph(nodes=nodes, input=inp, output=out)


def build_any(module):
    """The network's graph: linear (core.check.evaluate) when it uses only nn.Linear, sums and
    additions, otherwise general (core.check.general), or UnsupportedOp naming what is missing."""
    try:
        return build_graph(module)
    except UnsupportedOp:
        from .general import build_general_graph

        return build_general_graph(module)


def make_program(graph, weights, counter, space):
    """The evaluator for a graph from build_any."""
    if getattr(graph, "general", False):
        from .general import GeneralProgram

        return GeneralProgram(graph, weights, counter, space)
    from .evaluate import Program

    return Program(graph, weights, counter)
