"""MAJORITY on 12 bits, for the xorformer model: 1 exactly when at least 7 of the 12 bits are 1.

With an even number of bits, majority needs a rule for ties; this is the strict
one, the threshold function T(12, 7) of the xorformer README.
"""

import numpy as np

DESCRIPTION = (
    "Each input is a sequence of n_bits bits, given as one-hot vectors; the correct output is 1 when more than "
    "half of the bits are 1 (at least 7 of 12), else 0. The network outputs the logit pair (0, S) and answers 1 "
    "exactly when S > 0."
)
GROUPING = "by the number of bits that are 1"
ENCODING = "one_hot"
GROUP_LABEL = "number of ones"
LABEL_SYMMETRIC = True  # reordering the bits never changes the label (the network itself has positional embeddings)


def _threshold(sizes):
    return sizes["n_bits"] // 2 + 1


def input_space(sizes):
    return [2] * sizes["n_bits"]


def label(tokens, sizes):
    return (np.asarray(tokens).sum(axis=1) >= _threshold(sizes)).astype(np.int64)


def constant_label(ranges, sizes):
    """The label is the same for every input in the box exactly when even the fewest possible
    ones reach the threshold, or even the most possible ones stay below it."""
    fewest = sum(int(r[0]) for r in ranges)
    most = sum(int(r[1]) for r in ranges)
    t = _threshold(sizes)
    if fewest >= t:
        return 1
    if most < t:
        return 0
    return None


def group(tokens, sizes):
    return np.asarray(tokens).sum(axis=1)
