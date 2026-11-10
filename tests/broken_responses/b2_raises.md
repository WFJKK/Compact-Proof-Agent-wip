CLAIM: No claim; this recipe fails on purpose.

WHY IT HELPS: It does not.

PREDICTION: Status crash on every network, with the error message below.

KNOB: Unused.

RECIPE:
```python
def make_proof(weights, info, knob):
    raise RuntimeError("deliberate failure inside the recipe")
```

NOTES: Broken response 2 of 5, for testing: the recipe raises.
