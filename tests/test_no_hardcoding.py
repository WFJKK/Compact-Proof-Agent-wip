"""The core must not name a model or hardcode a model's sizes."""

import ast
import re
from pathlib import Path

import yaml

REPO = Path(__file__).resolve().parent.parent
CORE = REPO / "core"
MODEL_ROOTS = [REPO / "models", REPO / "tests"]


def _model_folders():
    out = []
    for root in MODEL_ROOTS:
        if root.exists():
            out += [p for p in root.iterdir() if (p / "config.yaml").is_file() and (p / "model.py").is_file()]
    return out


def _sizes(folder):
    """Distinctive size values (small ones like 8 or 16 also appear in generic code)."""
    cfg = yaml.safe_load((folder / "config.yaml").read_text())
    vals = set()
    for sizes in cfg.get("size_settings", {}).values():
        for v in sizes.values():
            if isinstance(v, int) and not isinstance(v, bool) and v >= 32:
                vals.add(v)
    return vals


def _size_names(folder):
    cfg = yaml.safe_load((folder / "config.yaml").read_text())
    return {k for sizes in cfg.get("size_settings", {}).values() for k in sizes}


def test_core_names_no_model():
    names = {p.name.lower() for p in _model_folders()}
    assert names, "expected at least one model folder"
    offenders = []
    for py in CORE.rglob("*.py"):
        text = py.read_text().lower()
        for name in names:
            if re.search(rf"\b{re.escape(name)}\b", text):
                offenders.append(f"{py.relative_to(REPO)} mentions {name}")
    assert not offenders, offenders


def test_core_hardcodes_no_size():
    sizes = set()
    for folder in _model_folders():
        if folder.parent.name == "models":
            sizes |= _sizes(folder)
    offenders = []
    for py in CORE.rglob("*.py"):
        source = py.read_text()
        lines = source.splitlines()
        tree = ast.parse(source)
        for node in ast.walk(tree):
            if isinstance(node, ast.Constant) and type(node.value) is int and node.value in sizes:
                if "not a size" in lines[node.lineno - 1]:
                    continue  # a literal the author has marked as unrelated to any model size (a bit count, a syscall number)
                offenders.append(f"{py.relative_to(REPO)}:{node.lineno} literal {node.value}")
    assert not offenders, offenders


def test_core_names_no_size_parameter():
    names = set()
    for folder in _model_folders():
        names |= _size_names(folder)
    offenders = []
    for py in CORE.rglob("*.py"):
        text = py.read_text()
        for name in names:
            if re.search(rf"\b{re.escape(name)}\b", text):
                offenders.append(f"{py.relative_to(REPO)} mentions {name}")
    assert not offenders, offenders
