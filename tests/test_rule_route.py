"""The rule route (core/rules_route) with fake backends: no API calls. A sound candidate is adopted, an unsound
one is caught by the audit and its revision adopted, a candidate that breaks the static guard never runs,
proposals are collected from run folders, a finished route is not run again, and the static guard and
plugin loading refuse what they should."""

import json
from pathlib import Path

import pytest
import yaml

from core.check.plugins import inspect_rule, static_guard
from core.rules_route import implement, proposals, review
from core.rules_route.route import load_config, run

HERE = Path(__file__).resolve().parent
FAKE = HERE / "rule_route"


def config(tmp_path, implementer, **kw) -> dict:
    cfg = {
        "route_id": "t",
        "name": "test_bound",
        "proposal": {"text": "Bound a leaf like token_interval, charged to its own category."},
        "implementer": {"backend": "fake", "responses": str(FAKE / implementer)},
        "reviewer": {"backend": "fake", "responses": str(FAKE / "reviewer_sound")},
        "revisions": 0,
        "audit_level": "small",
        "audit_folders": ["attn-max4"],
        "checks_sandbox": "auto",
        "work_dir": str(tmp_path / "work"),
        "rules_dir": str(tmp_path / "rules"),
        **kw,
    }
    path = tmp_path / "route.yaml"
    path.write_text(yaml.safe_dump(cfg))
    return load_config(path)


def test_a_sound_candidate_is_adopted(tmp_path):
    status = run(config(tmp_path, "implementer_sound"), log=lambda *a: None)
    assert status["status"] == "adopted"
    folder = tmp_path / "rules" / "test_bound"
    assert {"rule.py", "SOUNDNESS.md", "test_rule.py", "PROPOSAL.md", "status.json", "AUDIT.json", "REVIEW.md"} <= {p.name for p in folder.iterdir()}
    st = json.loads((folder / "status.json").read_text())
    assert st["tier"] == "python-checked" and st["checks"]["audit"]["passed"] and st["reviews"][0]["verdict"] == "SOUND"
    rule, problems = inspect_rule(folder)
    assert rule is not None, problems
    # editing an adopted rule takes it out of use until the route adopts it again
    (folder / "rule.py").write_text((folder / "rule.py").read_text() + "\n# edited\n")
    rule, problems = inspect_rule(folder)
    assert rule is None and "changed since adoption" in problems[0]
    # a finished route is not run again
    again = run(config(tmp_path, "implementer_sound"), log=lambda *a: None)
    assert again == status


def test_an_unsound_candidate_is_caught_and_its_revision_adopted(tmp_path):
    status = run(config(tmp_path, "implementer_revise", revisions=1), log=lambda *a: None)
    assert status["status"] == "adopted" and status["provenance"]["attempt"] == 1
    first = json.loads((tmp_path / "work" / "t" / "attempt_0" / "decision.json").read_text())
    assert not first["passed"] and "violations" in first["reasons"][0]
    prompt = json.loads((tmp_path / "work" / "t" / "attempt_1" / "implement" / "prompt.json").read_text())
    assert "WHAT WENT WRONG" in prompt["part2"] and "violations" in prompt["part2"]


def test_a_candidate_that_breaks_the_static_guard_never_runs(tmp_path):
    out = run(config(tmp_path, "implementer_guard"), log=lambda *a: None)
    assert out["adopted"] is False
    checks = json.loads((tmp_path / "work" / "t" / "attempt_0" / "checks" / "checks.json").read_text())
    assert checks["static_guard"] and "sandbox" not in checks
    assert not (tmp_path / "rules" / "test_bound").exists()


def test_proposals_from_a_run_folder(tmp_path):
    for k, idea in enumerate(["Keep per-token rows.", "Keep per-token rows.", "", "Pessimise attention once."]):
        d = tmp_path / "run" / f"round_{k:03d}" / "attempt_0"
        d.mkdir(parents=True)
        (d / "parsed.json").write_text(json.dumps({"claim": "c", "new_rule_idea": idea}))
    items = proposals.collect(tmp_path / "run")
    assert [i["text"] for i in items] == ["Keep per-token rows.", "Pessimise attention once."]
    assert items[0]["attempts"] == ["round_000/attempt_0", "round_001/attempt_0"]
    assert proposals.pick(items, "latest")["text"] == "Pessimise attention once."


def test_responses_are_parsed_strictly_where_it_matters():
    text = (FAKE / "implementer_sound" / "01.md").read_text()
    files = implement.parse(text, "test_bound")
    assert "def check_leaf" in files["rule.py"] and "def test_it_loads" in files["test_rule.py"]
    with pytest.raises(implement.ImplementError):
        implement.parse(text, "another_name")
    with pytest.raises(implement.ImplementError):
        implement.parse(text.replace("```python", "```python\n```\n```python", 1), "test_bound")
    r = review.parse((FAKE / "reviewer_sound" / "01.md").read_text())
    assert r["verdict"] == "SOUND" and len(r["counterexamples"]) == 1
    assert review.parse("VERDICT: probably fine")["verdict"] == "UNSURE"


@pytest.mark.parametrize(
    "source",
    [
        "import os",
        "import core.check.general\ncore.check.general.builtins.open('x')",
        "from core.check.general import builtins",
        "import numpy as np\nnp.load('x')",
        "x = (1).__class__",
        "f = eval",
        "from core.zoo import load_weights",
        "def f():\n    global x",
    ],
)
def test_static_guard_refuses(source):
    assert static_guard(source)


def test_the_prompts_carry_the_contract_and_the_proposal(tmp_path):
    p = implement.build("test_bound", "An idea.", feedback="It failed.")
    assert "check_leaf(prog, ranges, label, counter)" in p.part1 and "core/check/tokens.py" in p.part1
    assert "An idea." in p.part2 and "It failed." in p.part2
    assert not any(f"{{{k}}}" in p.part1 + p.part2 for k in ("CONTEXT", "PROPOSAL", "NAME", "FEEDBACK"))
    folder = tmp_path / "c" / "test_bound"
    folder.mkdir(parents=True)
    for f in ("rule.py", "SOUNDNESS.md", "test_rule.py", "PROPOSAL.md"):
        (folder / f).write_text(f"contents of {f}")
    r = review.build(folder)
    assert "contents of rule.py" in r.part2 and "VERDICT" in r.part1 and "zoo:" in r.part1
