"""Train a model's zoo from its folder alone.

    python -m core.train models/<name> [--settings S ...] [--seeds N ...] [--force]

Every network is trained from its own seed (parameter initialisation and data),
on fresh uniformly random inputs each step, with the settings in the model's
config.yaml. Training is resumable: finished networks are skipped unless their
training settings changed or --force is given. The manifest is rewritten
atomically after each network.

Optional training settings, all off by default:

- full_batch: true trains on every input at every step instead of random batches.
- dtype: float64 builds and trains the module in float64 (the initial weights are
  drawn in float64 too) and stores float64 weights.
- keep_best: true keeps the parameters with the highest accuracy on all inputs,
  and among those the lowest loss, over all steps.
"""

from __future__ import annotations

import argparse
import time

import torch

import numpy as np

from . import inputs
from .model_folder import ModelFolder, load_model_folder
from .util import sha256_file, sha256_json
from .zoo import read_manifest, split_assignment, write_manifest

TRAINER_VERSION = "train-v1"
# Correctness masks over more inputs than this are stored compressed (.npz); not a size of any model.
LARGE_MASK = 1 << 20


def training_key(folder: ModelFolder, setting: str, seed: int) -> str:
    """What a network's training depends on; a change means it must be retrained."""
    return sha256_json(
        {
            "trainer": TRAINER_VERSION,
            "model_source": folder.source(),
            "task_source": (folder.path / "task.py").read_text(),
            "sizes": folder.sizes(setting),
            "training": folder.config["training"],
            "seed": seed,
        }
    )


def train_network(folder: ModelFolder, setting: str, seed: int, log=print):
    import torch

    cfg = folder.config["training"]
    dtype = getattr(torch, str(cfg.get("dtype", "float32")))
    if dtype not in (torch.float32, torch.float64):
        raise ValueError("training dtype must be float32 or float64")
    torch.manual_seed(seed)
    rng = np.random.default_rng(seed)
    previous = torch.get_default_dtype()
    torch.set_default_dtype(dtype)  # so the initial weights are drawn in the training dtype
    try:
        module = folder.build(setting).to(dtype)
    finally:
        torch.set_default_dtype(previous)
    opt_cls = getattr(torch.optim, cfg["optimizer"])
    opt_kwargs = {"lr": cfg["lr"]}
    if "weight_decay" in cfg:
        opt_kwargs["weight_decay"] = cfg["weight_decay"]
    opt = opt_cls(module.parameters(), **opt_kwargs)
    space = folder.input_space(setting)
    sizes = folder.sizes(setting)
    loss_fn = torch.nn.CrossEntropyLoss()
    full_batch = bool(cfg.get("full_batch", False))
    keep_best = bool(cfg.get("keep_best", False))
    if full_batch or keep_best:
        all_tokens = inputs.all_inputs(space)
        x_all = folder.encode(all_tokens, setting).to(dtype)
        y_all = torch.as_tensor(np.asarray(folder.task.label(all_tokens, sizes), dtype=np.int64))
    best, best_state = None, None
    module.train()
    steps = int(cfg["steps"])
    report_every = max(1, steps // 5)
    loss = None
    for step in range(steps):
        if full_batch:
            x, y = x_all, y_all
        else:
            tokens = inputs.random_inputs(space, int(cfg["batch_size"]), rng)
            x = folder.encode(tokens, setting).to(dtype)
            y = torch.as_tensor(np.asarray(folder.task.label(tokens, sizes), dtype=np.int64))
        loss = loss_fn(module(x), y)
        opt.zero_grad()
        loss.backward()
        opt.step()
        if keep_best:
            with torch.no_grad():
                logits = module(x_all)
                own = logits.gather(1, y_all[:, None])[:, 0]
                others = logits.scatter(1, y_all[:, None], float("-inf")).max(dim=1).values
                score = (float((own > others).double().mean()), -float(loss_fn(logits, y_all)))
            if best is None or score > best:
                best = score
                best_state = {k: v.detach().clone() for k, v in module.state_dict().items()}
        if (step + 1) % report_every == 0:
            log(f"    step {step + 1}/{steps} loss {loss.item():.4f}")
    if best_state is not None:
        module.load_state_dict(best_state)
        module.eval()
        return module, -best[1]
    module.eval()
    return module, float(loss.item()) if loss is not None else float("nan")


def module_dtype(module):
    return next(module.parameters()).dtype


def float_correct(folder: ModelFolder, setting: str, module, batch: int = 8192) -> np.ndarray:
    """Whether each input's label logit is strictly larger than every other logit (float32)."""
    import torch

    space = folder.input_space(setting)
    sizes = folder.sizes(setting)
    toks = inputs.all_inputs(space)
    out = np.zeros(len(toks), dtype=bool)
    with torch.no_grad():
        for i in range(0, len(toks), batch):
            t = toks[i : i + batch]
            logits = module(folder.encode(t, setting).to(module_dtype(module))).numpy()
            lab = np.asarray(folder.task.label(t, sizes))
            own = logits[np.arange(len(t)), lab]
            others = logits.copy()
            others[np.arange(len(t)), lab] = -np.inf
            out[i : i + batch] = own > others.max(axis=1)
    return out


def train_zoo(folder: ModelFolder, settings=None, seeds=None, force=False, log=print) -> dict:
    split = split_assignment(folder)
    manifest = read_manifest(folder)
    manifest["model"] = folder.name
    by_id = {n["id"]: n for n in manifest.get("networks", [])}
    folder.zoo_dir().mkdir(parents=True, exist_ok=True)
    for setting in settings or folder.setting_names():
        for seed in seeds if seeds is not None else folder.config["seeds"]:
            nid = folder.network_id(setting, seed)
            key = training_key(folder, setting, seed)
            old = by_id.get(nid)
            wpath = folder.zoo_dir() / f"{nid}.npz"
            if (
                not force
                and old is not None
                and old.get("training_key") == key
                and wpath.exists()
                and sha256_file(wpath) == old.get("sha256")
            ):
                log(f"{nid}: up to date")
                continue
            log(f"{nid}: training")
            t0 = time.time()
            module, final_loss = train_network(folder, setting, seed, log=log)
            store = np.float64 if module_dtype(module) == torch.float64 else np.float32
            weights = {k: v.detach().cpu().numpy().astype(store) for k, v in module.state_dict().items()}
            np.savez(wpath, **weights)
            correct = float_correct(folder, setting, module)
            if len(correct) > LARGE_MASK:  # millions of inputs: store the mask compressed (it is nearly all True)
                cpath = folder.zoo_dir() / f"{nid}.correct.npz"
                np.savez_compressed(cpath, correct=correct)
            else:
                cpath = folder.zoo_dir() / f"{nid}.correct.npy"
                np.save(cpath, correct)
            entry = {
                "id": nid,
                "setting": setting,
                "seed": seed,
                "split": split[(setting, seed)],
                "weights": wpath.name,
                "sha256": sha256_file(wpath),
                "correct": cpath.name,
                "n_inputs": int(len(correct)),
                "real_correct": int(correct.sum()),
                "real_accuracy": float(correct.mean()),
                "final_loss": final_loss,
                "training_key": key,
                "train_seconds": round(time.time() - t0, 2),
                "E": old.get("E") if old else None,
                "B": old.get("B") if old else None,
            }
            # A retrained network invalidates its costs.
            if old is not None and old.get("sha256") != entry["sha256"]:
                entry["E"] = entry["B"] = None
            by_id[nid] = entry
            manifest["networks"] = sorted(by_id.values(), key=lambda n: (n["setting"], n["seed"]))
            write_manifest(folder, manifest)
            log(f"{nid}: real accuracy {entry['real_accuracy']:.4f} ({entry['split']})")
    return manifest


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("model_folder")
    ap.add_argument("--settings", nargs="*")
    ap.add_argument("--seeds", nargs="*", type=int)
    ap.add_argument("--force", action="store_true")
    args = ap.parse_args(argv)
    folder = load_model_folder(args.model_folder)
    train_zoo(folder, settings=args.settings, seeds=args.seeds, force=args.force)


if __name__ == "__main__":
    main()
