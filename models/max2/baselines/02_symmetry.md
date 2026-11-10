CLAIM: The network sums the two one-hot tokens before anything else, so swapping them never changes its output.

WHY IT HELPS: Only inputs with t1 <= t2 need checking; each of the others is the swap of one of them. That halves the inputs checked.

PREDICTION: Certified accuracy equal to the real accuracy, at about half of B.

KNOB: Unused.

RECIPE:
```python
import helpers


def make_proof(weights, info, knob):
    V = info["input_space"][0]

    def row(t1):
        singles = helpers.split_values(1, t1, V - 1, lambda v: helpers.leaf("single"))
        if t1 == 0:
            return singles
        # inputs with t2 < t1 are swaps of inputs checked elsewhere
        return helpers.split(1, [t1], [helpers.leaf("skip"), singles])

    return helpers.proof(helpers.split_values(0, 0, V - 1, row), symmetry=True)
```

NOTES: Baseline 2 of 3: the notebook's symmetry proof, for accuracy.
