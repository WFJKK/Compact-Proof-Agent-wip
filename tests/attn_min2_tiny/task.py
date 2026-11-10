"""Min-of-K: output the smallest of the n_ctx tokens, on Gross et al.'s model."""

import numpy as np

DESCRIPTION = (
    "Each input is a sequence of n_ctx tokens in {0, ..., d_vocab - 1}, given as one-hot vectors; "
    "the correct output is the smallest token. The network's output is read at the last position."
)
GROUPING = "by the smallest token"
ENCODING = "one_hot"
GROUP_LABEL = "smallest token"
LABEL_SYMMETRIC = True  # reordering the tokens never changes the label (the network itself has positional embeddings)


def input_space(sizes):
    return [sizes["d_vocab"]] * sizes["n_ctx"]


def label(tokens, sizes):
    return np.asarray(tokens).min(axis=1)


def constant_label(ranges, sizes):
    """The smallest token is the same for every input in the product of ranges
    exactly when the smallest lower end equals the smallest upper end."""
    lo = min(r[0] for r in ranges)
    hi = min(r[1] for r in ranges)
    return int(lo) if lo == hi else None


def group(tokens, sizes):
    return np.asarray(tokens).min(axis=1)
