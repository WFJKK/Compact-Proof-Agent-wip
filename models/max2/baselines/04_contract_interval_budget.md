CLAIM: The network is linear in the sum of its one-hot inputs, with logits M[:, t1] + M[:, t2] for the product M of its three linear maps; it outputs the larger token.

WHY IT HELPS: The same proof as baseline 3 (contraction, symmetry, one interval leaf per larger token v over t1 <= v, misclassified pairs isolated), but the knob is a budget: the groups are checked from the largest v down, since a group costs about 2V(v+1) operations and certifies 2v+1 inputs, so the largest groups certify the most inputs per operation. Whatever the budget leaves is skipped. This gives the hand-written proof the same partial-proof points that Q rewards an agent for, so a comparison against it shows only what a new idea adds.

PREDICTION: At knob 1 the same proof as baseline 3. Below it, certified accuracy falls with the budget: about one percent of the leaf work certifies about ten percent of the inputs.

KNOB: The budget, as a fraction of the full proof's leaf work: 100^(knob - 1), so knobs 0, 0.25, 0.5, 0.75, 1 give 1%, 3.2%, 10%, 32% and all of it. When the run scores at fixed budgets, info["budget"] is used instead: the leaf work is whatever the budget leaves after the contraction and the weights, and a budget too small for the contraction gets a proof that skips everything. Groups are taken from the largest v down; the last group that does not fit is checked on the largest t1 that do.

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
    depth = int(np.ceil(np.log2(V)))

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

    # The budget: a fraction of the full proof's leaf work, which is about 2V per (t1, v) pair,
    # or, at a fixed budget in checker operations, what that leaves after the fixed costs
    # (the contraction, reading the weights, and a margin for the tree and the leaves' decisions).
    full_work = sum(2 * V * (v + 1) for v in range(V))
    d = E.shape[0]
    if info.get("budget") is not None:
        # Fixed costs first: the contraction, converting the weights, reading and walking the tree.
        # Then each group costs its range check plus about 2V for the decision, its nodes and symmetry.
        fixed = V * d * d + V * V * d + 2 * V * d + d * d + 8 * V
        budget = min(full_work + 2 * V * V, 0.98 * (info["budget"] - fixed))
        overhead = 2 * V
        if budget < 2 * V + overhead:  # not even the contraction fits: the cheapest proof, which certifies nothing
            return helpers.proof(helpers.leaf("skip"))
    else:
        budget = full_work * 100.0 ** (knob - 1)
        overhead = 0
    plan = {}  # v -> lowest t1 to check (0 for the whole group)
    for v in range(V - 1, -1, -1):
        cost = 2 * V * (v + 1) + overhead
        if cost <= budget:
            plan[v] = 0
            budget -= cost
        else:
            m = int((budget - overhead) // (2 * V))  # how many of the largest t1 still fit
            if m > 0:
                plan[v] = v - m + 1
            break

    def group(v):
        # t2 = v: inputs with t1 <= v are sorted and have label v; t1 > v are swaps
        if v not in plan:
            return helpers.leaf("skip")
        lo = plan[v]
        checked = refine(v, lo, v, depth)
        left = checked if lo == 0 else helpers.split(0, [lo], [helpers.leaf("skip"), checked])
        if v == V - 1:
            return left
        return helpers.split(0, [v + 1], [left, helpers.leaf("skip")])

    tree = helpers.split_values(1, 0, V - 1, group)
    contract = [{"name": "M", "chain": ["embedding", "linear", "unembedding"]}]
    return helpers.proof(tree, symmetry=True, contract=contract)
```

NOTES: Baseline 3 with a budget knob, for a fair comparison under Q.
