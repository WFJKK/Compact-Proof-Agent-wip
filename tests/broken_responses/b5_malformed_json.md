CLAIM: No claim; this recipe returns a proof that is not valid JSON.

WHY IT HELPS: It does not.

PREDICTION: Status bad_output: a NaN cannot be written as JSON.

KNOB: Unused.

RECIPE:
```python
import helpers


def make_proof(weights, info, knob):
    proof = helpers.proof(helpers.full_tree(info["input_space"]))
    proof["notes"] = float("nan")  # as if a bound had come out as NaN
    return proof
```

NOTES: Broken response 5 of 5, for testing: the proof file is malformed JSON.
