"""The max2 task: output the larger of two tokens."""

import numpy as np

DESCRIPTION = (
    "Each input is a sequence of n_ctx tokens in {0, ..., d_vocab - 1}, given as one-hot vectors; "
    "the correct output is the largest token."
)
GROUPING = "by the largest token"
ENCODING = "one_hot"
GROUP_LABEL = "largest token"  # how diagnostics name one group
LABEL_SYMMETRIC = True  # reordering the tokens never changes the label


def input_space(sizes):
    return [sizes["d_vocab"]] * sizes["n_ctx"]


def label(tokens, sizes):
    return np.asarray(tokens).max(axis=1)


def constant_label(ranges, sizes):
    """The largest token is the same for every input in the product of ranges
    exactly when the largest lower end equals the largest upper end."""
    lo = max(r[0] for r in ranges)
    hi = max(r[1] for r in ranges)
    return int(lo) if lo == hi else None


def group(tokens, sizes):
    return np.asarray(tokens).max(axis=1)
