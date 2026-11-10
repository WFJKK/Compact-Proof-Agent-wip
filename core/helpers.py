"""Helpers for recipes: building proof trees and running the network in floats.

A read-only copy of this file sits next to the recipe in the sandbox, so a
recipe can `import helpers`. Nothing here is trusted: the checker recomputes
everything a proof claims.
"""

from __future__ import annotations

import importlib
import inspect
from fractions import Fraction

import numpy as np

SCHEMA = "split-tree-v1"


# proof trees ----------------------------------------------------------------
def leaf(rule: str, approx: str | None = None) -> dict:
    node = {"leaf": rule}
    if approx is not None:
        node["approx"] = approx
    return node


def split(position: int, cuts: list[int], children: list[dict]) -> dict:
    """Divide the current range [lo, hi] of a position at the cuts: [lo, c1-1], [c1, c2-1], ..., [ck, hi]."""
    return {"split": {"position": int(position), "cuts": [int(c) for c in cuts]}, "children": children}


def split_values(position: int, lo: int, hi: int, child) -> dict:
    """Split [lo, hi] of a position into single values; child(value) builds each subtree."""
    if lo == hi:
        return child(lo)
    return split(position, list(range(lo + 1, hi + 1)), [child(v) for v in range(lo, hi + 1)])


def split_ranges(position: int, lo: int, hi: int, pieces: list[tuple[int, int]], child) -> dict:
    """Split [lo, hi] into consecutive pieces [(a, b), ...] covering it; child(a, b) builds each subtree."""
    assert pieces[0][0] == lo and pieces[-1][1] == hi
    if len(pieces) == 1:
        return child(*pieces[0])
    return split(position, [a for a, _ in pieces[1:]], [child(a, b) for a, b in pieces])


def full_tree(space: list[int], rule: str = "single") -> dict:
    """Every input in its own leaf: brute force."""

    def build(p, ):
        if p == len(space):
            return leaf(rule)
        return split_values(p, 0, space[p] - 1, lambda v: build(p + 1))

    return build(0)


def proof(tree: dict, symmetry: bool = False, contract=None, approximate=None, notes: str | None = None) -> dict:
    out = {"schema": SCHEMA, "tree": tree}
    if symmetry:
        out["symmetry"] = True
    if contract:
        out["contract"] = contract
    if approximate:
        out["approximate"] = approximate
    if notes:
        out["notes"] = notes
    return out


def fraction(x, max_denominator: int | None = None) -> str:
    """An exact fraction string for a float (or a nearby simpler fraction)."""
    f = Fraction(float(x))
    if max_denominator:
        f = f.limit_denominator(max_denominator)
    return f"{f.numerator}/{f.denominator}"


# the network in floats ------------------------------------------------------
def module_class():
    mod = importlib.import_module("model")
    import torch

    classes = [c for _, c in inspect.getmembers(mod, inspect.isclass) if issubclass(c, torch.nn.Module) and c.__module__ == mod.__name__]
    if len(classes) != 1:
        raise RuntimeError("model.py should define exactly one module")
    return classes[0]


def float_module(weights: dict, info: dict):
    """The network as a torch module, built from model.py (float64 if the weights are)."""
    import torch

    m = module_class()(**info["sizes"])
    if any(np.asarray(v).dtype == np.float64 for v in weights.values()):
        m = m.double()
    m.load_state_dict({k: torch.from_numpy(np.asarray(v)) for k, v in weights.items()})
    m.eval()
    return m


def graph_nodes(weights: dict, info: dict) -> list[dict]:
    """The network's traced graph: node names (as used by the contract rule), ops and arguments."""
    import torch.fx

    gm = torch.fx.symbolic_trace(float_module(weights, info))
    out = []
    for n in gm.graph.nodes:
        out.append({"name": n.name, "op": n.op, "target": str(n.target), "args": [str(a) for a in n.args]})
    return out


def all_inputs(space: list[int]) -> np.ndarray:
    grids = np.meshgrid(*[np.arange(v) for v in space], indexing="ij")
    return np.stack([g.reshape(-1) for g in grids], axis=1)


def logits(weights: dict, info: dict, tokens: np.ndarray) -> np.ndarray:
    """Float logits for a batch of inputs given as token arrays (N, positions)."""
    import torch

    m = float_module(weights, info)
    x = torch.nn.functional.one_hot(torch.as_tensor(np.asarray(tokens, dtype=np.int64)), num_classes=info["input_space"][0])
    x = x.to(next(m.parameters()).dtype)
    with torch.no_grad():
        return m(x).numpy()
