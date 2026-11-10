"""Install hand-made networks into a model folder's zoo, for checker tests."""

import numpy as np

from core.util import sha256_file
from core.zoo import read_manifest, write_manifest


def install(folder, nid: str, weights: dict, setting: str, split: str = "dev", correct=None) -> str:
    folder.zoo_dir().mkdir(parents=True, exist_ok=True)
    path = folder.zoo_dir() / f"{nid}.npz"
    np.savez(path, **{k: np.asarray(v, dtype=np.float32) for k, v in weights.items()})
    n = folder.n_inputs(setting)
    cpath = folder.zoo_dir() / f"{nid}.correct.npy"
    np.save(cpath, np.zeros(n, dtype=bool) if correct is None else correct)
    m = read_manifest(folder)
    m["networks"] = [e for e in m.get("networks", []) if e["id"] != nid]
    m["networks"].append(
        {
            "id": nid,
            "setting": setting,
            "seed": -1,
            "split": split,
            "weights": path.name,
            "sha256": sha256_file(path),
            "correct": cpath.name,
            "n_inputs": n,
            "real_correct": None,
            "real_accuracy": None,
        }
    )
    write_manifest(folder, m)
    return nid


def min_task_weights(V: int, out_bias=None, a=2.0, b=1.0, c=0.0) -> dict:
    """A perfect stub network for "smallest token": identity, then M[j,t] = a (j=t), b (j<t), c (j>t)."""
    M = np.where(np.eye(V, dtype=bool), a, np.where(np.arange(V)[:, None] < np.arange(V)[None, :], b, c))
    return {
        "inp.weight": np.eye(V),
        "inp.bias": np.zeros(V),
        "out.weight": M,
        "out.bias": np.zeros(V) if out_bias is None else np.asarray(out_bias, dtype=float),
    }
