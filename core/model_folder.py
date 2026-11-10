"""Loading and validating a model folder.

Everything model-specific lives in one folder, `models/<name>/`:

    model.py     the architecture: exactly one torch nn.Module, whose
                 constructor takes the sizes as keyword arguments
    task.py      the task (see TASK_ATTRIBUTES and TASK_FUNCTIONS); optionally
                 LABEL_SYMMETRIC = True if reordering an input's positions never
                 changes its label (needed by the symmetry rule), and
                 GROUP_LABEL, a short name for a diagnostic group such as
                 "largest token" (default "group")
    config.yaml  sizes, training, seeds, split, zoo path, cost model, hygiene
    rules.py     optional rules of the model's own (trusted)
    baselines/   optional fake-agent responses for round 0
    zoo/         the manifest written by core.train, and small weight files
    lean/        optional soundness proofs

The core reads nothing else about a model.
"""

from __future__ import annotations

import importlib.util
import inspect
import sys
from dataclasses import dataclass, field
from pathlib import Path
from types import ModuleType

import numpy as np

from . import inputs
from .util import read_yaml, sha256_bytes, sha256_files

REQUIRED_FILES = ("model.py", "task.py", "config.yaml")

TASK_ATTRIBUTES = {
    "DESCRIPTION": "one sentence describing the task, shown to the agent",
    "GROUPING": "how diagnostics group inputs, shown to the agent",
    "ENCODING": "how an input becomes the module's input tensor",
}

TASK_FUNCTIONS = {
    "input_space": "input_space(sizes) -> number of values at each position",
    "label": "label(tokens, sizes) -> correct output for each input",
    "constant_label": "constant_label(ranges, sizes) -> the label if it is the same for every input "
    "in the product of inclusive ranges, else None",
    "group": "group(tokens, sizes) -> diagnostic group of each input",
}

CONFIG_KEYS = {
    "size_settings": dict,
    "seeds": list,
    "split": dict,
    "training": dict,
    "zoo_path": str,
    "cost_model": str,
}

TRAINING_KEYS = ("optimizer", "lr", "batch_size", "steps")


class ModelFolderError(ValueError):
    pass


def _import_file(path: Path, tag: str) -> ModuleType:
    name = f"_cpl_{tag}_{sha256_bytes(str(path.resolve()).encode())[:12]}"
    spec = importlib.util.spec_from_file_location(name, path)
    if spec is None or spec.loader is None:
        raise ModelFolderError(f"cannot import {path}")
    module = importlib.util.module_from_spec(spec)
    sys.modules[name] = module
    try:
        spec.loader.exec_module(module)
    except Exception as exc:  # report import errors as folder errors
        del sys.modules[name]
        raise ModelFolderError(f"{path.name} failed to import: {exc!r}") from exc
    return module


@dataclass
class ModelFolder:
    name: str
    path: Path
    config: dict
    module_class: type
    task: ModuleType
    rules: ModuleType | None = None
    _source: str = field(default="", repr=False)

    # sizes and networks ---------------------------------------------------
    def setting_names(self) -> list[str]:
        return list(self.config["size_settings"])

    def sizes(self, setting: str) -> dict:
        try:
            return dict(self.config["size_settings"][setting])
        except KeyError:
            raise ModelFolderError(f"{self.name}: unknown size setting {setting!r}") from None

    def build(self, setting: str):
        return self.module_class(**self.sizes(setting))

    def input_space(self, setting: str) -> list[int]:
        return [int(v) for v in self.task.input_space(self.sizes(setting))]

    def n_inputs(self, setting: str) -> int:
        return inputs.n_inputs(self.input_space(setting))

    def encode(self, tokens: np.ndarray, setting: str):
        return inputs.encode(tokens, self.input_space(setting), self.task.ENCODING)

    def network_id(self, setting: str, seed: int) -> str:
        return f"{self.name}-{setting}-s{seed}"

    # files ----------------------------------------------------------------
    def source(self) -> str:
        return self._source

    def zoo_dir(self) -> Path:
        z = Path(self.config["zoo_path"])
        return z if z.is_absolute() else self.path / z

    def manifest_path(self) -> Path:
        return self.zoo_dir() / "manifest.json"

    def identity_files(self) -> list[Path]:
        """Files that define the model folder: everything except caches and weights."""
        out = []
        zoo = self.zoo_dir().resolve()
        for p in self.path.rglob("*"):
            if not p.is_file() or "__pycache__" in p.parts or p.suffix == ".pyc":
                continue
            if any(part.startswith(".") for part in p.relative_to(self.path).parts):
                continue  # editor and OS files such as .DS_Store
            rp = p.resolve()
            if zoo in rp.parents and p.name != "manifest.json":
                continue
            out.append(p)
        if self.manifest_path().exists() and self.manifest_path() not in out:
            out.append(self.manifest_path())
        return out

    def folder_hash(self) -> str:
        return sha256_files(self.path, [p for p in self.identity_files() if self.path in p.parents])

    def group_label(self) -> str:
        label = getattr(self.task, "GROUP_LABEL", None)
        return label if isinstance(label, str) and label else "group"

    def hygiene_terms(self) -> list[str]:
        return [str(t) for t in self.config.get("hygiene", []) or []]


def load_model_folder(path: str | Path) -> ModelFolder:
    """Load a model folder and check it against the contract above."""
    path = Path(path).resolve()
    if not path.is_dir():
        raise ModelFolderError(f"{path} is not a folder")
    missing = [f for f in REQUIRED_FILES if not (path / f).is_file()]
    if missing:
        raise ModelFolderError(f"{path.name}: missing {', '.join(missing)}")

    config = read_yaml(path / "config.yaml")
    if not isinstance(config, dict):
        raise ModelFolderError(f"{path.name}: config.yaml must be a mapping")
    for key, typ in CONFIG_KEYS.items():
        if key not in config:
            raise ModelFolderError(f"{path.name}: config.yaml lacks {key!r}")
        if not isinstance(config[key], typ):
            raise ModelFolderError(f"{path.name}: config.yaml {key!r} must be a {typ.__name__}")
    if not config["size_settings"]:
        raise ModelFolderError(f"{path.name}: config.yaml needs at least one size setting")
    for setting, sizes in config["size_settings"].items():
        if not isinstance(sizes, dict):
            raise ModelFolderError(f"{path.name}: size setting {setting!r} must be a mapping")
    for key in TRAINING_KEYS:
        if key not in config["training"]:
            raise ModelFolderError(f"{path.name}: config.yaml training lacks {key!r}")
    seeds = config["seeds"]
    if len(set(seeds)) != len(seeds) or not all(isinstance(s, int) for s in seeds):
        raise ModelFolderError(f"{path.name}: seeds must be distinct integers")
    held = config["split"].get("held_out_per_setting")
    if not isinstance(held, int) or not 0 <= held < len(seeds):
        raise ModelFolderError(f"{path.name}: split.held_out_per_setting must be an integer below the number of seeds")
    if not isinstance(config["split"].get("seed"), int):
        raise ModelFolderError(f"{path.name}: split.seed must be an integer")

    model_mod = _import_file(path / "model.py", "model")
    import torch

    classes = [
        c
        for _, c in inspect.getmembers(model_mod, inspect.isclass)
        if issubclass(c, torch.nn.Module) and c.__module__ == model_mod.__name__
    ]
    if len(classes) != 1:
        raise ModelFolderError(
            f"{path.name}: model.py must define exactly one nn.Module, found {[c.__name__ for c in classes]}"
        )

    task_mod = _import_file(path / "task.py", "task")
    for attr in TASK_ATTRIBUTES:
        if not isinstance(getattr(task_mod, attr, None), str):
            raise ModelFolderError(f"{path.name}: task.py must define {attr} as a string")
    for fn in TASK_FUNCTIONS:
        if not callable(getattr(task_mod, fn, None)):
            raise ModelFolderError(f"{path.name}: task.py must define {fn}()")
    if task_mod.ENCODING not in inputs.SUPPORTED_ENCODINGS:
        raise ModelFolderError(
            f"{path.name}: unsupported ENCODING {task_mod.ENCODING!r}; supported: {inputs.SUPPORTED_ENCODINGS}"
        )

    rules_mod = _import_file(path / "rules.py", "rules") if (path / "rules.py").is_file() else None

    folder = ModelFolder(
        name=path.name,
        path=path,
        config=config,
        module_class=classes[0],
        task=task_mod,
        rules=rules_mod,
        _source=(path / "model.py").read_text(),
    )

    # Every size setting must build, and labels must fit the module's outputs.
    rng = np.random.default_rng(0)
    for setting in folder.setting_names():
        try:
            module = folder.build(setting)
        except Exception as exc:
            raise ModelFolderError(f"{path.name}: size setting {setting!r} does not build: {exc!r}") from exc
        space = folder.input_space(setting)
        if not space or min(space) < 1:
            raise ModelFolderError(f"{path.name}: input_space must list at least one position with values")
        tokens = inputs.random_inputs(space, 8, rng)
        with torch.no_grad():
            out = module(folder.encode(tokens, setting))
        labels = np.asarray(task_mod.label(tokens, folder.sizes(setting)))
        if out.ndim != 2 or out.shape[0] != len(tokens):
            raise ModelFolderError(f"{path.name}: the module must return (batch, outputs) logits")
        if labels.shape != (len(tokens),) or labels.min() < 0 or labels.max() >= out.shape[1]:
            raise ModelFolderError(f"{path.name}: labels must be one output index per input")
        if getattr(task_mod, "LABEL_SYMMETRIC", False):
            many = inputs.random_inputs(space, 256, rng)
            base = np.asarray(task_mod.label(many, folder.sizes(setting)))
            for perm in ([len(space) - 1 - i for i in range(len(space))], list(np.roll(np.arange(len(space)), 1))):
                if not np.array_equal(base, np.asarray(task_mod.label(many[:, perm], folder.sizes(setting)))):
                    raise ModelFolderError(f"{path.name}: LABEL_SYMMETRIC is declared but reordering changes labels")
    return folder
