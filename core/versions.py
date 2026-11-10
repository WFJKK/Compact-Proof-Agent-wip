"""What produced a result: hashes of the trusted code, the sandbox code, the model folder and the rules.

Every result record carries these, and a run refuses to continue if the
trusted hashes change under it, so results from different versions never
share a frontier silently.
"""

from __future__ import annotations

from .check.cost import VERSION as COST_VERSION
from .check.rules import describe
from .model_folder import ModelFolder
from .util import REPO_ROOT, sha256_bytes, sha256_files

CHECKER_FILES = (
    "core/check/*.py",
    "rules/*/rule.py",  # rules adopted through the rule route (core/check/plugins.py), and their status
    "rules/*/status.json",
    "core/diagnostics.py",
    "core/inputs.py",
    "core/model_folder.py",
    "core/versions.py",
    "core/zoo.py",
    "core/util.py",
)
SANDBOX_FILES = ("core/runner.py", "core/harness.py", "core/helpers.py", "core/sandbox.py")


def _files(patterns) -> list:
    out = []
    for pattern in patterns:
        found = sorted(REPO_ROOT.glob(pattern))
        if pattern.startswith("rules/"):
            # only the folders core.check.plugins loads: a replaced rule (rules/.replaced-<name>-<time>) is not one
            found = [p for p in found if not p.relative_to(REPO_ROOT).parts[1].startswith((".", "_"))]
        out += found
    return out


def checker_hash() -> str:
    return sha256_files(REPO_ROOT, _files(CHECKER_FILES))


def sandbox_hash() -> str:
    return sha256_files(REPO_ROOT, _files(SANDBOX_FILES))


def rule_set_id(rule_set, folder: ModelFolder) -> str:
    text = describe(tuple(rule_set))
    if folder.rules is not None:
        text += "\n" + (folder.path / "rules.py").read_text()
    return sha256_bytes(text.encode())[:16]


def trusted(folder: ModelFolder) -> dict:
    """Hashes that must not change while a run is going."""
    return {"checker": checker_hash(), "sandbox": sandbox_hash(), "model_folder": folder.folder_hash()}


def collect(folder: ModelFolder, cfg: dict, config_sha: str) -> dict:
    return {
        **trusted(folder),
        "cost_model": COST_VERSION,
        "rule_set": rule_set_id(cfg["rule_set"], folder),
        "prompt_template": cfg["prompt_template"],
        "agent_model": cfg["agent_model"] if cfg["backend"] in ("api", "claude_code") else cfg["backend"],
        "config": config_sha,
    }


def changed(expected: dict, folder: ModelFolder) -> list[str]:
    """The trusted hashes that differ from the ones a run started with."""
    now = trusted(folder)
    return [k for k in now if expected.get(k) != now[k]]
