"""The zoo: a model's trained networks, their manifest and the development/held-out split.

Weights are stored as .npz files (no pickle). The manifest pins each file's
SHA-256; loading a network verifies it. Held-out networks are refused unless
the caller passes allow_held_out=True, which only core.final does.
"""

from __future__ import annotations

from pathlib import Path

import numpy as np

from .model_folder import ModelFolder
from .util import read_json, sha256_bytes, sha256_file, write_json


class ZooError(RuntimeError):
    pass


def split_assignment(folder: ModelFolder) -> dict[tuple[str, int], str]:
    """Deterministic development/held-out split, drawn once per size setting from split.seed."""
    split = folder.config["split"]
    seeds = list(folder.config["seeds"])
    out = {}
    for setting in folder.setting_names():
        salt = int(sha256_bytes(setting.encode())[:8], 16)
        rng = np.random.default_rng([split["seed"], salt])
        held = set(rng.choice(seeds, size=split["held_out_per_setting"], replace=False).tolist())
        for s in seeds:
            out[(setting, s)] = "held_out" if s in held else "dev"
    return out


def read_manifest(folder: ModelFolder) -> dict:
    p = folder.manifest_path()
    if not p.exists():
        return {"model": folder.name, "networks": []}
    return read_json(p)


def write_manifest(folder: ModelFolder, manifest: dict) -> None:
    write_json(folder.manifest_path(), manifest)


def network_entry(folder: ModelFolder, network_id: str) -> dict:
    for n in read_manifest(folder)["networks"]:
        if n["id"] == network_id:
            return n
    raise ZooError(f"{network_id} is not in the zoo of {folder.name}")


def networks(folder: ModelFolder, split: str | None = "dev", setting: str | None = None) -> list[dict]:
    out = []
    for n in read_manifest(folder)["networks"]:
        if split is not None and n["split"] != split:
            continue
        if setting is not None and n["setting"] != setting:
            continue
        out.append(n)
    return out


def weights_path(folder: ModelFolder, entry: dict) -> Path:
    return folder.zoo_dir() / entry["weights"]


def load_weights(folder: ModelFolder, network_id: str, allow_held_out: bool = False) -> dict[str, np.ndarray]:
    entry = network_entry(folder, network_id)
    if entry["split"] == "held_out" and not allow_held_out:
        raise ZooError(f"{network_id} is held out; only the final evaluation may load it")
    path = weights_path(folder, entry)
    if sha256_file(path) != entry["sha256"]:
        raise ZooError(f"weights of {network_id} do not match the manifest hash")
    with np.load(path, allow_pickle=False) as z:
        return {k: z[k] for k in z.files}


def load_module(folder: ModelFolder, network_id: str, allow_held_out: bool = False):
    """The network as a torch module (float), for training-side and float analysis."""
    import torch

    entry = network_entry(folder, network_id)
    weights = load_weights(folder, network_id, allow_held_out=allow_held_out)
    module = folder.build(entry["setting"])
    if any(v.dtype == np.float64 for v in weights.values()):
        module = module.double()  # weights stored in float64 stay float64
    module.load_state_dict({k: torch.from_numpy(v) for k, v in weights.items()})
    module.eval()
    return module


def correct_mask(folder: ModelFolder, network_id: str, allow_held_out: bool = False) -> np.ndarray:
    """Float-evaluated correctness of every input (diagnostics only, never a score)."""
    entry = network_entry(folder, network_id)
    if entry["split"] == "held_out" and not allow_held_out:
        raise ZooError(f"{network_id} is held out")
    path = folder.zoo_dir() / entry["correct"]
    if path.suffix == ".npz":
        with np.load(path, allow_pickle=False) as z:
            return z["correct"]
    return np.load(path, allow_pickle=False)
