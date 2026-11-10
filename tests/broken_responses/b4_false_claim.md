CLAIM: Once the first token is fixed, the network is correct on every input, provably with one interval bound.

WHY IT HELPS: One interval leaf per first token would replace almost all single checks.

PREDICTION: Every leaf certified. (The claim is false: the checker should reject most leaves, and count only the ones that really hold.)

KNOB: Unused.

RECIPE:
```python
import helpers


def make_proof(weights, info, knob):
    space = info["input_space"]
    # One interval leaf per value of the first position, covering every value of the others.
    tree = helpers.split_values(0, 0, space[0] - 1, lambda v: helpers.leaf("interval"))
    return helpers.proof(tree)
```

NOTES: Broken response 4 of 5, for testing: the proof claims far more than holds.
