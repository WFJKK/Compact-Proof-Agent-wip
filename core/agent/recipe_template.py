"""Recipe template.

Define make_proof(weights, info, knob) and return a proof (a JSON-serialisable dict).

    weights  dict of numpy float32 (or float64) arrays, keyed by the module's parameter names
    info     {"sizes": the module's constructor arguments, "input_space": number of tokens per position}
    knob     float in [0, 1]: trade proof length against certified accuracy

You may import numpy, torch, the standard library, `model` (the network's
source, as shown) and `helpers` (proof-tree builders and float helpers:
leaf, split, split_values, split_ranges, full_tree, proof, fraction,
float_module, graph_nodes, all_inputs, logits).
Inside make_proof anything goes: float analysis, search, trial and error.
Only checking the returned proof counts towards its length.
"""

import numpy as np

import helpers


def make_proof(weights, info, knob):
    space = info["input_space"]
    # Brute force: every input in its own leaf, checked with the single rule.
    return helpers.proof(helpers.full_tree(space))
