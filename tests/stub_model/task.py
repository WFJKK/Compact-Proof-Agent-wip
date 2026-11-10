"""Stub task for the core's tests: output the smaller of the tokens."""

import numpy as np

DESCRIPTION = "Each input is a sequence of tokens; the correct output is the smallest token."
GROUPING = "by the smallest token"
ENCODING = "one_hot"
GROUP_LABEL = "smallest token"  # how diagnostics name one group
LABEL_SYMMETRIC = True  # reordering the tokens never changes the label


def input_space(sizes):
    return [sizes["d_vocab"]] * sizes["n_ctx"]


def label(tokens, sizes):
    return np.asarray(tokens).min(axis=1)


def constant_label(ranges, sizes):
    lo = min(r[0] for r in ranges)
    hi = min(r[1] for r in ranges)
    return int(lo) if lo == hi else None


def group(tokens, sizes):
    return np.asarray(tokens).min(axis=1)
