"""Proof files and their split trees.

    {
      "schema": "split-tree-v1",
      "network": "<network id>",       # written by the runner
      "symmetry": false,               # optional, see the symmetry rule
      "contract": [...],               # optional, see the contract rule
      "approximate": [...],            # optional, see the approximate rule
      "tree": <node>,
      "notes": "..."                   # optional, ignored
    }

    <node> = {"split": {"position": p, "cuts": [c1, ..., ck]}, "children": [<node>, ...]}
           | {"leaf": "single"} | {"leaf": "skip"}
           | {"leaf": "interval"} | {"leaf": "interval", "approx": "<name>"}
           | {"leaf": "token_interval"}

The root covers every input. A split divides the current range [lo, hi] of
position p into [lo, c1-1], [c1, c2-1], ..., [ck, hi], so the leaves always
partition the inputs and no input is counted twice.
"""

from __future__ import annotations

import itertools
import math
from dataclasses import dataclass
from fractions import Fraction

import numpy as np

from .evaluate import CheckError

SCHEMA = "split-tree-v1"
TOP_KEYS = {"schema", "network", "symmetry", "contract", "approximate", "tree", "notes"}
LEAF_KEYS = {"leaf", "approx"}


@dataclass
class Leaf:
    path: str
    ranges: list  # [(lo, hi), ...] inclusive, one per position
    rule: str
    approx: str | None = None

    @property
    def size(self) -> int:
        return math.prod(hi - lo + 1 for lo, hi in self.ranges)

    def is_single(self) -> bool:
        return all(lo == hi for lo, hi in self.ranges)


def _is_int(x) -> bool:
    return isinstance(x, int) and not isinstance(x, bool)


def walk(tree, space: list[int], max_nodes: int) -> tuple[list[Leaf], int]:
    """Validate the tree and list its leaves. Returns (leaves, number of nodes)."""
    leaves: list[Leaf] = []
    root_ranges = [(0, v - 1) for v in space]
    stack = [(tree, root_ranges, "root")]
    n_nodes = 0
    while stack:
        node, ranges, path = stack.pop()
        n_nodes += 1
        if n_nodes > max_nodes:
            raise CheckError(f"the tree has more than {max_nodes} nodes")
        if not isinstance(node, dict):
            raise CheckError(f"{path}: a node must be an object")
        if "leaf" in node:
            extra = set(node) - LEAF_KEYS
            if extra:
                raise CheckError(f"{path}: unknown leaf keys {sorted(extra)}")
            rule = node["leaf"]
            if not isinstance(rule, str):
                raise CheckError(f"{path}: the leaf rule must be a name")
            approx = node.get("approx")
            if approx is not None and (rule != "interval" or not isinstance(approx, str)):
                raise CheckError(f"{path}: only interval leaves take an approximation name")
            leaves.append(Leaf(path, list(ranges), rule, approx))
            continue
        if set(node) != {"split", "children"}:
            raise CheckError(f"{path}: a node is a leaf or a split with children")
        sp, children = node["split"], node["children"]
        if not isinstance(sp, dict) or set(sp) != {"position", "cuts"}:
            raise CheckError(f"{path}: split needs exactly position and cuts")
        p, cuts = sp["position"], sp["cuts"]
        if not _is_int(p) or not 0 <= p < len(space):
            raise CheckError(f"{path}: split position out of range")
        if not isinstance(cuts, list) or not cuts or not all(_is_int(c) for c in cuts):
            raise CheckError(f"{path}: cuts must be a non-empty list of integers")
        lo, hi = ranges[p]
        if not (lo < cuts[0] and cuts[-1] <= hi and all(a < b for a, b in zip(cuts, cuts[1:]))):
            raise CheckError(f"{path}: cuts must increase strictly inside ({lo}, {hi}]")
        if not isinstance(children, list) or len(children) != len(cuts) + 1:
            raise CheckError(f"{path}: a split with {len(cuts)} cuts needs {len(cuts) + 1} children")
        bounds = [lo] + list(cuts) + [hi + 1]
        for i in reversed(range(len(children))):
            sub = list(ranges)
            sub[p] = (bounds[i], bounds[i + 1] - 1)
            stack.append((children[i], sub, f"{path}/{i}"))
    return leaves, n_nodes


def sorted_orbit_count(ranges: list) -> int:
    """Sum, over inputs in the box whose tokens are in non-decreasing order, of the
    number of distinct reorderings of each: the inputs certified under symmetry."""
    P = len(ranges)
    if P == 1:
        return ranges[0][1] - ranges[0][0] + 1
    if P == 2:
        (a1, b1), (a2, b2) = ranges
        lt = _count_less(a1, b1, a2, b2)
        eq = max(0, min(b1, b2) - max(a1, a2) + 1)
        return 2 * lt + eq
    return _orbit_count_dp(ranges)


def _count_less(a1, b1, a2, b2) -> int:
    """#{(x, y) : a1 <= x <= b1, a2 <= y <= b2, x < y}."""
    if a1 > b1 or a2 > b2:
        return 0
    total = 0
    # x <= a2 - 1: every y in [a2, b2] is larger
    hi = min(b1, a2 - 1)
    if hi >= a1:
        total += (hi - a1 + 1) * (b2 - a2 + 1)
    # a2 <= x <= b2 - 1: y in [x + 1, b2], count b2 - x
    lo, hi = max(a1, a2), min(b1, b2 - 1)
    if hi >= lo:
        n = hi - lo + 1
        total += n * b2 - (lo + hi) * n // 2
    return total


def _orbit_count_dp(ranges: list) -> int:
    P = len(ranges)
    states = {}  # (last value, run length) -> product of 1/(m!) over completed runs
    lo0, hi0 = ranges[0]
    for v in range(lo0, hi0 + 1):
        states[(v, 1)] = Fraction(1)
    for lo, hi in ranges[1:]:
        nxt = {}
        for (v, r), w in states.items():
            for x in range(max(lo, v), hi + 1):
                key, val = ((x, r + 1), w) if x == v else ((x, 1), w / math.factorial(r))
                nxt[key] = nxt.get(key, 0) + val
        states = nxt
    total = sum(w / math.factorial(r) for (v, r), w in states.items()) * math.factorial(P)
    assert total.denominator == 1
    return int(total)


def certified_mask(space: list[int], ranges_list: list, symmetry: bool) -> np.ndarray:
    """Which inputs (in the order of core.inputs.all_inputs) the accepted leaves certify."""
    cert = np.zeros(space, dtype=bool)
    for ranges in ranges_list:
        sl = tuple(slice(lo, hi + 1) for lo, hi in ranges)
        if not symmetry:
            cert[sl] = True
            continue
        axes = [np.arange(lo, hi + 1) for lo, hi in ranges]
        grids = np.meshgrid(*axes, indexing="ij")
        ordered = np.ones(grids[0].shape, dtype=bool)
        for a, b in zip(grids, grids[1:]):
            ordered &= a <= b
        cert[sl] |= ordered
    if symmetry:
        full = cert.copy()
        for perm in itertools.permutations(range(len(space))):
            full |= np.transpose(cert, perm)
        cert = full
    return cert.reshape(-1)


def full_tree(space: list[int], leaf: dict | None = None, positions: list[int] | None = None) -> dict:
    """The tree that splits every position into single tokens (used for brute force)."""
    leaf = leaf or {"leaf": "single"}
    positions = list(range(len(space))) if positions is None else positions

    def build(k):
        if k == len(positions):
            return dict(leaf)
        p = positions[k]
        v = space[p]
        if v == 1:
            return build(k + 1)
        return {"split": {"position": p, "cuts": list(range(1, v))}, "children": [build(k + 1) for _ in range(v)]}

    return build(0)
