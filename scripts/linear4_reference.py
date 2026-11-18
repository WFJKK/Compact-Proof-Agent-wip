#!/usr/bin/env python3
"""Reference numbers for a linear network on four tokens (models/max4, models/min4): what the convexity
arguments certify, counted exactly from the zoo's mask of right inputs, and an estimate of their lengths.

    python3 scripts/linear4_reference.py models/max4 max4-v64-s0

The network's logits are a sum over the tokens, logits(t) = M[:, t1] + ... + M[:, t4] with M = U L E, so the
inputs on which one output wins form a convex set. For an input with label m (one of its tokens) and other
tokens a, b, c:

  pure inputs     it is the average of (a,a,a,m), (b,b,b,m), (c,c,c,m): right when those and (m,m,m,m) are
  doubled inputs  it is the average of (a,a,b,m), (b,b,c,m), (c,c,a,m): right when those three are
                  (in either orientation)
  multisets       the output depends on the multiset of tokens only: every multiset tested with M

Counts are exact: they use the mask the pipeline stored when the network was trained (float32), and the
script checks that neither argument certifies an input the mask says is wrong. Lengths are a simple count of
operations (one per multiply-add, addition, comparison), not measured by the Lean service: estimates.
Cost of finishing charges each right input left out a forward pass, as the pilot's score does.
Needs about 2 GB at 64 tokens. Nothing here is shown to an agent.
"""

from __future__ import annotations

import argparse
import sys
from math import comb
from pathlib import Path

import numpy as np

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))

from core.model_folder import load_model_folder  # noqa: E402
from core.zoo import correct_mask, network_entry  # noqa: E402


def reference(folder, network_id: str, allow_held_out: bool = False) -> dict:
    entry = network_entry(folder, network_id)
    sizes = folder.sizes(entry["setting"])
    space = folder.input_space(entry["setting"])
    if len(space) != 4 or len(set(space)) != 1:
        raise ValueError("this script is for four positions over one vocabulary")
    v, d = space[0], sizes["d_model"]
    n = v ** 4
    mask = np.asarray(correct_mask(folder, network_id, allow_held_out=allow_held_out), dtype=bool)
    t = np.indices((v, v, v, v), dtype=np.int16).reshape(4, n)
    label = np.asarray(folder.task.label(t.T, sizes), dtype=np.int64)
    if not (t == label[None, :]).any(axis=0).all():
        raise ValueError("the label is not one of the tokens: the convexity arguments here do not apply")
    first = np.argmax(t == label[None, :], axis=0)  # the first position holding the label
    others = np.empty((3, n), dtype=np.int64)
    for p in range(4):
        sel = first == p
        for k, q in enumerate([q for q in range(4) if q != p]):
            others[k, sel] = t[q, sel]
    a, b, c = others

    def at(w, x, y, z):
        return mask[((w * v + x) * v + y) * v + z]

    pure = at(label, label, label, label) & at(a, a, a, label) & at(b, b, b, label) & at(c, c, c, label)
    doubled = (at(a, a, b, label) & at(b, b, c, label) & at(c, c, a, label)) | (
        at(a, a, c, label) & at(c, c, b, label) & at(b, b, a, label))
    if (pure & ~mask).any() or (doubled & ~mask).any():
        raise AssertionError("a convexity argument certified an input the mask says is wrong")
    right = int(mask.sum())
    left = mask & ~doubled
    s = np.sort(t[:, left].astype(np.int64), axis=0)
    left_multisets = int(np.unique(((s[0] * v + s[1]) * v + s[2]) * v + s[3]).size)

    E, B = entry["E"], entry["B"]
    per_input = (B - E) / n
    table = v * d * (d + v)  # M = U (L E): d d v and v v d multiply-adds
    pairs = v * (v - 1) // 2
    lengths = {
        "pure inputs": table + pairs * (v - 1) * 3 + v * (v - 1) + E,
        "doubled inputs": table + pairs * v + sum((k + 1) ** 2 for k in range(v)) * (v - 1) * 2 + E,
        "every multiset": table + comb(v + 3, 4) * (v - 1) * 4 + E,
    }
    lengths["doubled inputs, then the multisets left over"] = lengths["doubled inputs"] + left_multisets * (v - 1) * 4
    certified = {"pure inputs": int(pure.sum()), "doubled inputs": int(doubled.sum()), "every multiset": right,
                 "doubled inputs, then the multisets left over": right}
    rows = []
    for name in ("pure inputs", "doubled inputs", "doubled inputs, then the multisets left over", "every multiset"):
        finishing = lengths[name] + per_input * (right - certified[name])
        rows.append({"proof": name, "length": lengths[name], "B_over_length": B / lengths[name], "certified": certified[name],
                     "share_of_right": certified[name] / right if right else 0.0, "cost_of_finishing_score": B / finishing})
    return {"network": network_id, "inputs": n, "right": right, "E": E, "B": B, "forward_pass": per_input,
            "left_after_doubled": int(left.sum()), "left_multisets": left_multisets, "rows": rows}


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    ap.add_argument("model_folder")
    ap.add_argument("network")
    args = ap.parse_args(argv)
    r = reference(load_model_folder(args.model_folder), args.network)
    print(f"{r['network']}: {r['right']:,} of {r['inputs']:,} inputs right ({r['right'] / r['inputs']:.4%}); "
          f"E {r['E']:,}, B {r['B']:,} (a forward pass {r['forward_pass']:.0f})")
    for row in r["rows"]:
        print(f"  {row['proof']:45s} length about {row['length']:>14,}  B / {row['B_over_length']:>9,.0f}  "
              f"certifies {row['share_of_right']:8.3%} of the right inputs  score today {row['cost_of_finishing_score']:8.1f}")
    print(f"  after the doubled inputs: {r['left_after_doubled']:,} right inputs left, in {r['left_multisets']:,} multisets")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
