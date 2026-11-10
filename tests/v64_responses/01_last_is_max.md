CLAIM: Attention concentrates on the largest token and the value path copies it.

WHY IT HELPS: Every input whose last token is the largest, with the others at least 4 below it, shares a label with a whole box of inputs.

PREDICTION: About a fifth of the inputs certified, at a tiny fraction of B.

KNOB: Unused.

RECIPE:
```python
import helpers


def make_proof(weights, info, knob):
    V = info["sizes"]["d_vocab"]
    n = info["sizes"]["n_ctx"]
    last = n - 1
    kids = []
    gap = 4  # the other tokens at least this far below the largest
    for m in range(V):
        if m < gap:
            kids.append(helpers.leaf("skip"))
            continue
        sub = helpers.leaf("token_interval")
        for p in reversed(range(last)):
            sub = helpers.split(p, [m - gap + 1], [sub, helpers.leaf("skip")])
        kids.append(sub)
    return helpers.proof(helpers.split(last, list(range(1, V)), kids))
```

NOTES: Test response for the v64 setting.
