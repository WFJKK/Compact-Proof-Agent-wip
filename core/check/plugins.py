"""Rules adopted through the rule route, loaded next to the generic rules.

A rule that an agent proposes, a separate implementer writes, and the route's
audits and review accept (core/rules_route) lives in rules/<name>/:

    rule.py        NAME (the folder's name), DESCRIPTION (shown to the agent
                   verbatim, like the generic rules' descriptions), CATEGORY (the
                   cost category its per-leaf work is charged to), APPLIES_TO
                   ("general": networks beyond linear maps, the only kind so far)
                   and check_leaf(prog, ranges, label, counter), which returns
                   (certified, lowest margin bound as a Fraction, the other output
                   reaching it) for one leaf
    SOUNDNESS.md   the soundness argument
    test_rule.py   the rule's tests
    PROPOSAL.md    the idea it implements and where it came from
    status.json    written when the rule is adopted: its tier, provenance, the
                   audits and review it passed, and the SHA-256 of each file above

The checker uses a rule only if its status is "adopted", its files still have
the hashes recorded at adoption (so any edit takes it out of use until the route
adopts it again), and rule.py passes the static guard below. A leaf with an
adopted rule needs a constant label, like an interval leaf; check_leaf does the
rest. Work it shares across leaves goes to the category tables, like
token_interval's reused rows.

The static guard keeps accidents out (file, process or network access, dynamic
code); it is not what makes a rule trustworthy. That comes from the route: the
written argument, the audits against brute force on trained, random and
perturbed networks, an adversarial review, and, in every run that uses the rule,
runtime_audit below, which compares each accepted leaf's claimed bound with the
float margins of its inputs and halts the run on any disagreement.
"""

from __future__ import annotations

import ast
import importlib.util
import json
import sys
from dataclasses import dataclass, field
from pathlib import Path

import numpy as np

from ..util import REPO_ROOT, sha256_file
from . import cost

RULES_DIR = REPO_ROOT / "rules"
HASHED_FILES = ("rule.py", "SOUNDNESS.md", "test_rule.py", "PROPOSAL.md")
TIERS = ("python-checked",)
APPLIES = ("general",)
# The categories every rule shares; an adopted rule's own category must be new.
SHARED_CATEGORIES = ("tables",)

# `import X` is allowed for these (the standard library's pure helpers and numpy) ...
ALLOWED_IMPORTS = (
    "math", "fractions", "itertools", "functools", "collections", "dataclasses", "typing",
    "heapq", "bisect", "operator", "numpy",
)
# ... and `from M import names` for these and the core's checker modules, never a name that is itself a module
# (a module object would reach everything it imports: the general evaluator imports builtins, say).
ALLOWED_FROM = ALLOWED_IMPORTS + (
    "__future__", "core.check.tokens", "core.check.interval", "core.check.general", "core.check.cost",
    "core.check.evaluate", "core.check.arith", "core.check.trace",
)
BANNED_NAMES = {
    "open", "exec", "eval", "compile", "__import__", "globals", "locals", "vars", "input", "breakpoint",
    "exit", "quit", "help", "getattr", "setattr", "delattr", "memoryview", "__builtins__", "type", "super",
}
ALLOWED_CALLS_OF_BANNED = {"super"}  # super() inside a method is how a subclass reaches its base
# numpy's file and process entry points, the names of modules reachable as attributes, and anything else that
# reaches outside the process
BANNED_ATTRIBUTES = {
    "load", "loads", "save", "savez", "savez_compressed", "fromfile", "tofile", "memmap", "loadtxt",
    "savetxt", "genfromtxt", "fromregex", "DataSource", "ctypeslib", "f2py", "testing", "distutils",
    "system", "popen", "lib", "char", "rec", "ma", "core", "strings", "typing", "exceptions", "dtypes",
    "os", "sys", "builtins", "subprocess", "importlib", "ctypes", "socket", "shutil", "pathlib", "io",
    "pickle", "marshal", "tempfile", "signal", "threading", "multiprocessing", "inspect", "gc", "types",
    "weakref", "torch", "hub", "urllib", "http", "code", "pdb", "resource", "fx",
}
ALLOWED_DUNDERS = {"__init__", "__name__", "__future__"}
RUNTIME_TOLERANCE = 1e-4  # float32 margins against an exact bound


class PluginError(ValueError):
    pass


@dataclass
class AdoptedRule:
    name: str
    path: Path
    module: object
    description: str
    category: str
    applies_to: str
    status: dict = field(default_factory=dict)

    def check_leaf(self, prog, ranges, label, counter):
        return self.module.check_leaf(prog, ranges, label, counter)


def static_guard(source: str) -> list[str]:
    """Problems that keep a rule's source out of the checker (empty when it passes)."""
    try:
        tree = ast.parse(source)
    except SyntaxError as exc:
        return [f"syntax error: {exc}"]
    problems = []
    calls = {id(n.func) for n in ast.walk(tree) if isinstance(n, ast.Call) and isinstance(n.func, ast.Name)}
    for node in ast.walk(tree):
        if isinstance(node, ast.Import):
            for a in node.names:
                if a.name not in ALLOWED_IMPORTS:
                    problems.append(f"line {node.lineno}: import {a.name} is not allowed")
        elif isinstance(node, ast.ImportFrom):
            if node.level:
                problems.append(f"line {node.lineno}: relative imports are not allowed")
            elif (node.module or "") not in ALLOWED_FROM:
                problems.append(f"line {node.lineno}: import from {node.module} is not allowed")
            else:
                for a in node.names:
                    if a.name == "*":
                        problems.append(f"line {node.lineno}: import * is not allowed")
                    elif node.module != "__future__" and _is_module(node.module, a.name):
                        problems.append(f"line {node.lineno}: {a.name} from {node.module} is a module, which is not allowed")
        elif isinstance(node, ast.Name) and node.id in BANNED_NAMES:
            if not (node.id in ALLOWED_CALLS_OF_BANNED and id(node) in calls):
                problems.append(f"line {node.lineno}: {node.id} is not allowed")
        elif isinstance(node, ast.Attribute):
            a = node.attr
            if a in BANNED_ATTRIBUTES or (a.startswith("__") and a.endswith("__") and a not in ALLOWED_DUNDERS):
                problems.append(f"line {node.lineno}: attribute {a} is not allowed")
        elif isinstance(node, (ast.Global, ast.Nonlocal)):
            problems.append(f"line {node.lineno}: global and nonlocal are not allowed")
    return problems


def _is_module(module: str, name: str) -> bool:
    import importlib
    import types

    try:
        return isinstance(getattr(importlib.import_module(module), name, None), types.ModuleType)
    except ImportError:
        return True  # cannot tell: refuse


def file_hashes(path: Path) -> dict:
    return {f: sha256_file(path / f) for f in HASHED_FILES if (path / f).is_file()}


def _load_module(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(f"adopted_rule_{name}", path / "rule.py")
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def inspect_rule(path: Path, require_adopted: bool = True) -> tuple[AdoptedRule | None, list[str]]:
    """Load one rule folder; returns (the rule or None, the reasons it cannot be used)."""
    path = Path(path)
    name = path.name
    problems = []
    status = {}
    if require_adopted:
        try:
            status = json.loads((path / "status.json").read_text())
        except (OSError, ValueError) as exc:
            return None, [f"no readable status.json ({type(exc).__name__})"]
        if status.get("status") != "adopted":
            return None, [f"status is {status.get('status')!r}, not 'adopted'"]
        if status.get("tier") not in TIERS:
            problems.append(f"unknown tier {status.get('tier')!r}")
        recorded = status.get("files_sha256") or {}
        now = file_hashes(path)
        missing = [f for f in HASHED_FILES if f not in now]
        if missing:
            problems.append(f"missing files {missing}")
        changed = sorted(f for f in now if recorded.get(f) != now[f])
        if changed:
            problems.append(f"files changed since adoption: {changed} (run the route again to re-adopt)")
    if not (path / "rule.py").is_file():
        return None, problems + ["no rule.py"]
    problems += static_guard((path / "rule.py").read_text())
    if problems:
        return None, problems
    try:
        module = _load_module(name, path)
    except Exception as exc:  # a rule that does not even import is reported, never used
        return None, [f"rule.py does not import: {type(exc).__name__}: {exc}"]
    for attr, kind in (("NAME", str), ("DESCRIPTION", str), ("CATEGORY", str), ("APPLIES_TO", str)):
        if not isinstance(getattr(module, attr, None), kind):
            problems.append(f"rule.py must define {attr} as a {kind.__name__}")
    if not callable(getattr(module, "check_leaf", None)):
        problems.append("rule.py must define check_leaf(prog, ranges, label, counter)")
    if problems:
        return None, problems
    if module.NAME != name:
        problems.append(f"NAME is {module.NAME!r}; it must be the folder's name {name!r}")
    if module.APPLIES_TO not in APPLIES:
        problems.append(f"APPLIES_TO must be one of {APPLIES}")
    if module.CATEGORY in cost.CATEGORIES and module.CATEGORY not in SHARED_CATEGORIES:
        problems.append(f"CATEGORY {module.CATEGORY!r} is a core category; use a new one (the rule's name, say)")
    from .rules import GENERIC_RULES

    if name in GENERIC_RULES or name == "split":
        problems.append(f"{name!r} is a generic rule's name")
    if problems:
        return None, problems
    return AdoptedRule(name, path, module, module.DESCRIPTION, module.CATEGORY, module.APPLIES_TO, status), []


_CACHE: dict = {}
# Candidates the route's audit (and experiments) enable in their own process; a run's checker never does.
_CANDIDATES: dict = {}


def adopted(rules_dir: Path | None = None, reload: bool = False) -> dict[str, AdoptedRule]:
    """The usable adopted rules, by name (cached per folder; reload=True looks again)."""
    root = Path(rules_dir or RULES_DIR)
    key = str(root.resolve()) if root.exists() else str(root)
    if reload or key not in _CACHE:
        found, skipped = {}, {}
        if root.is_dir():
            for path in sorted(p for p in root.iterdir() if p.is_dir() and not p.name.startswith((".", "_"))):
                rule, problems = inspect_rule(path)
                if rule is None:
                    skipped[path.name] = problems
                else:
                    found[rule.name] = rule
                    cost.EXTRA_CATEGORIES.add(rule.category)
        _CACHE[key] = (found, skipped)
    return {**_CACHE[key][0], **_CANDIDATES}


def use_candidate(path: Path) -> AdoptedRule:
    """Enable a rule folder that is not adopted yet, in this process only (audits and experiments)."""
    rule = load_for_tests(path)
    _CANDIDATES[rule.name] = rule
    return rule


def drop_candidates() -> None:
    for name in list(_CANDIDATES):
        forget(name)
    _CANDIDATES.clear()


def skipped(rules_dir: Path | None = None) -> dict[str, list[str]]:
    """Rule folders that exist but cannot be used, with the reasons."""
    adopted(rules_dir)
    root = Path(rules_dir or RULES_DIR)
    key = str(root.resolve()) if root.exists() else str(root)
    return dict(_CACHE[key][1])


def names() -> tuple[str, ...]:
    return tuple(sorted(adopted()))


def runtime_audit(outcomes: list, margins: np.ndarray, space: list[int], rule_names) -> list[dict]:
    """Accepted leaves of adopted rules whose claimed bound exceeds the float margin of one of their inputs.

    margins are the float margins of every input (core.diagnostics.float_margins), in input order. A sound
    rule's bound never exceeds the true smallest margin of its leaf, and the float margin is within float
    rounding of the true one; so any leaf found here means the rule is wrong, and the caller halts.
    """
    rule_names = set(rule_names)
    if not rule_names:
        return []
    grid = np.asarray(margins).reshape(tuple(space))
    bad = []
    for o in outcomes:
        if not o["accepted"] or o["rule"] not in rule_names or o["margin"] is None:
            continue
        lowest = float(grid[tuple(slice(lo, hi + 1) for lo, hi in o["ranges"])].min())
        if o["margin"] > lowest + RUNTIME_TOLERANCE * max(1.0, abs(lowest)):
            bad.append({"rule": o["rule"], "ranges": o["ranges"], "claimed": o["margin"], "float_min": lowest})
    return bad


def load_for_tests(path: Path) -> AdoptedRule:
    """A rule folder loaded without status checks (the route's audit uses this on candidates)."""
    rule, problems = inspect_rule(Path(path), require_adopted=False)
    if rule is None:
        raise PluginError("; ".join(problems))
    cost.EXTRA_CATEGORIES.add(rule.category)
    return rule


def forget(name: str) -> None:
    """Drop a loaded candidate's module (tests load several versions of one rule)."""
    sys.modules.pop(f"adopted_rule_{name}", None)
