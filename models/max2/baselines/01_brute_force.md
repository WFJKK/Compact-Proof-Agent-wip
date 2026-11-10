CLAIM: No claim about the network: every input is checked on its own.

WHY IT HELPS: It does not. This is the brute-force reference, the longest proof, which every other proof is measured against.

PREDICTION: Certified accuracy equal to each network's real accuracy, at length B.

KNOB: Unused.

RECIPE:
```python
import helpers


def make_proof(weights, info, knob):
    return helpers.proof(helpers.full_tree(info["input_space"]))
```

NOTES: Baseline 1 of 3.
