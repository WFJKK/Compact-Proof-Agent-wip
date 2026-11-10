CLAIM: The network is linear in the sum of its one-hot inputs, with logits M[:, t1] + M[:, t2] for the product M of its three linear maps; it outputs the larger token.

WHY IT HELPS: Computing M once replaces a forward pass per input with column lookups, and grouping inputs by their larger token v lets one interval leaf check all t1 <= v at once: with t2 = v fixed, the bound for each output is the exact minimum over t1.

PREDICTION: Certified accuracy close to the real accuracy at about B/15. Groups containing a misclassified pair fail as a whole unless the knob splits them.

KNOB: How deep to split a group that contains a misclassified pair, from 0 (never; the whole group fails) to 1 (until the bad pairs are isolated).

RECIPE:
```python
import numpy as np

import helpers


def make_proof(weights, info, knob):
    V = info["input_space"][0]
    E = np.asarray(weights["embedding.weight"], dtype=np.float64)
    W = np.asarray(weights["linear.weight"], dtype=np.float64)
    U = np.asarray(weights["unembedding.weight"], dtype=np.float64)
    M = U @ W @ E  # logits for (t1, t2) are M[:, t1] + M[:, t2]
    depth = int(round(knob * np.ceil(np.log2(V))))

    def all_correct(v, lo, hi):
        t1 = np.arange(lo, hi + 1)
        logit = M[:, t1] + M[:, [v]]
        own = logit[v]
        others = np.delete(logit, v, axis=0).max(axis=0)
        return bool(np.all(own > others))

    def refine(v, lo, hi, d):
        if all_correct(v, lo, hi):
            return helpers.leaf("interval")
        if lo == hi:
            return helpers.leaf("skip")
        if d == 0:
            return helpers.leaf("interval")  # will fail; costs little
        mid = (lo + hi + 1) // 2
        return helpers.split(0, [mid], [refine(v, lo, mid - 1, d - 1), refine(v, mid, hi, d - 1)])

    def group(v):
        # t2 = v: inputs with t1 <= v are sorted and have label v; t1 > v are swaps
        left = refine(v, 0, v, depth)
        if v == V - 1:
            return left
        return helpers.split(0, [v + 1], [left, helpers.leaf("skip")])

    tree = helpers.split_values(1, 0, V - 1, group)
    contract = [{"name": "M", "chain": ["embedding", "linear", "unembedding"]}]
    return helpers.proof(tree, symmetry=True, contract=contract)
```

NOTES: Baseline 3 of 3.
