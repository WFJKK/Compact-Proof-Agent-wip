"""Adopted rules in the core (core/check/plugins.py): only adopted, unedited rules load; the checker, run
configs and the prompt see them; the runtime audit catches a bound above the float margins; and every adopted
rule's own tests pass."""

import json
import shutil
import subprocess
import sys
from pathlib import Path

import numpy as np
import pytest

from core.check import plugins
from core.check.checker import check_proof
from core.check.proof import SCHEMA
from core.check.rules import describe, generic_rules
from core.model_folder import load_model_folder
from core.zoo import networks

REPO = Path(__file__).resolve().parent.parent
FAKE_RULE = REPO / "tests" / "rule_route" / "implementer_sound" / "01.md"


def _write_rule(root: Path, adopted: bool = True) -> Path:
    from core.rules_route.implement import parse

    files = parse(FAKE_RULE.read_text(), "test_bound")
    d = root / "test_bound"
    d.mkdir(parents=True)
    for f in ("rule.py", "SOUNDNESS.md", "test_rule.py"):
        (d / f).write_text(files[f])
    (d / "PROPOSAL.md").write_text("a test")
    if adopted:
        status = {"name": "test_bound", "status": "adopted", "tier": "python-checked", "files_sha256": plugins.file_hashes(d)}
        (d / "status.json").write_text(json.dumps(status))
    return d


@pytest.fixture
def rules_dir(tmp_path, monkeypatch):
    root = tmp_path / "rules"
    root.mkdir()
    monkeypatch.setattr(plugins, "RULES_DIR", root)
    plugins._CACHE.clear()
    yield root
    plugins._CACHE.clear()
    plugins.forget("test_bound")


def test_only_adopted_unedited_rules_load(rules_dir):
    d = _write_rule(rules_dir, adopted=False)
    assert plugins.adopted(reload=True) == {}
    assert "not adopted" in " ".join(plugins.skipped()["test_bound"]) or "status.json" in " ".join(plugins.skipped()["test_bound"])
    shutil.rmtree(d)
    d = _write_rule(rules_dir)
    assert set(plugins.adopted(reload=True)) == {"test_bound"}
    (d / "SOUNDNESS.md").write_text("changed")
    assert plugins.adopted(reload=True) == {}


def test_the_checker_run_configs_and_prompt_see_an_adopted_rule(rules_dir):
    _write_rule(rules_dir)
    plugins.adopted(reload=True)
    assert "test_bound" in generic_rules()
    assert "Exactly token_interval, charged to test_bound" in describe(("single", "test_bound"))
    folder = load_model_folder(REPO / "models" / "attn-max4")
    e = networks(folder, setting="v16")[0]
    V = folder.sizes("v16")["d_vocab"]
    tree = {"split": {"position": 0, "cuts": [V - 1]}, "children": [{"leaf": "skip"}, {"leaf": "test_bound"}]}
    proof = {"schema": SCHEMA, "network": e["id"], "tree": tree}
    res = check_proof(proof, folder, e["id"], rule_set=("single", "test_bound"))
    assert res["status"] == "ok" and res["length_by_rule"].get("test_bound", 0) > 0
    res2 = check_proof(proof, folder, e["id"], rule_set=("single", "token_interval"))
    assert res2["status"] == "rejected"


def test_runtime_audit_catches_an_overclaiming_leaf():
    margins = np.array([1.0, 2.0, 3.0, 0.5])
    outcomes = [
        {"accepted": True, "rule": "r", "margin": 0.4, "ranges": [[0, 1], [0, 1]]},
        {"accepted": True, "rule": "r", "margin": 0.6, "ranges": [[1, 1], [0, 1]]},
        {"accepted": True, "rule": "other", "margin": 9.0, "ranges": [[0, 0], [0, 0]]},
    ]
    bad = plugins.runtime_audit(outcomes, margins, [2, 2], ["r"])
    assert len(bad) == 1 and bad[0]["claimed"] == 0.6 and bad[0]["float_min"] == 0.5


def test_adopted_rules_pass_their_own_tests():
    for name in plugins.adopted(reload=True):
        r = subprocess.run([sys.executable, "-m", "pytest", "-q", "-x", "-p", "no:cacheprovider", str(REPO / "rules" / name / "test_rule.py")],
                           cwd=REPO, capture_output=True, text=True, timeout=3600)
        assert r.returncode == 0, r.stdout[-3000:]


def test_the_checker_hash_ignores_replaced_rule_folders(tmp_path, monkeypatch):
    """A rule adopted again with replace: true leaves its old folder as rules/.replaced-<name>-<time>, which the
    loader skips; the checker hash skips it too, so it changes nothing about what produced a result."""
    from core import versions

    for name in ("token_convex", ".replaced-token_convex-20261019-000000", "_scratch"):
        (tmp_path / "rules" / name).mkdir(parents=True)
        (tmp_path / "rules" / name / "rule.py").write_text("x = 1\n")
        (tmp_path / "rules" / name / "status.json").write_text("{}\n")
    monkeypatch.setattr(versions, "REPO_ROOT", tmp_path)
    found = [p.relative_to(tmp_path).as_posix() for p in versions._files(("rules/*/rule.py", "rules/*/status.json"))]
    assert found == ["rules/token_convex/rule.py", "rules/token_convex/status.json"]
