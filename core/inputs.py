"""Input spaces: every model's inputs are sequences of discrete values.

An input space is a list giving the number of values each position can take.
Inputs are represented as integer arrays of shape (N, positions).
"""

from __future__ import annotations

import math

import numpy as np

SUPPORTED_ENCODINGS = ("one_hot",)


def n_inputs(space: list[int]) -> int:
    return math.prod(space)


def all_inputs(space: list[int]) -> np.ndarray:
    """Every input in lexicographic order, shape (n_inputs, positions)."""
    grids = np.meshgrid(*[np.arange(v) for v in space], indexing="ij")
    return np.stack([g.reshape(-1) for g in grids], axis=1).astype(np.int64)


def input_index(tokens: np.ndarray, space: list[int]) -> np.ndarray:
    """Position of each input in the lexicographic order of all_inputs."""
    idx = np.zeros(len(tokens), dtype=np.int64)
    for p, v in enumerate(space):
        idx = idx * v + tokens[:, p]
    return idx


def random_inputs(space: list[int], n: int, rng: np.random.Generator) -> np.ndarray:
    cols = [rng.integers(0, v, size=n) for v in space]
    return np.stack(cols, axis=1).astype(np.int64)


def encode(tokens: np.ndarray, space: list[int], encoding: str):
    """The module input for a batch of inputs (a float torch tensor)."""
    import torch

    if encoding != "one_hot":
        raise ValueError(f"unsupported encoding {encoding!r}; supported: {SUPPORTED_ENCODINGS}")
    if len(set(space)) != 1:
        raise ValueError("one_hot encoding needs the same number of values at every position")
    t = torch.as_tensor(np.asarray(tokens, dtype=np.int64))
    return torch.nn.functional.one_hot(t, num_classes=space[0]).float()
