"""Step 4 of the route: an adversarial reviewer tries to break the candidate; its counterexamples are audited.

The reviewer is another agent (prompts/review.md). Its verdict is SOUND, UNSOUND or UNSURE; its
counterexamples are run by the audit in the check box, and a single confirmed violation rejects the rule
whatever the verdict says.
"""

from __future__ import annotations

import json
from pathlib import Path

from .common import checker_context, fill, file_block, models_summary, one_code_block, prompt, split_sections, template

SECTIONS = ("VERDICT", "COUNTEREXAMPLES", "CRITIQUE")
VERDICTS = ("SOUND", "UNSOUND", "UNSURE")
MAX_CASES = 50


def build(candidate: Path, rules_dir=None):
    part1, part2 = template("review")
    part1 = fill(part1, {"CONTEXT": checker_context(rules_dir, exclude=Path(candidate).name), "MODELS": models_summary()})
    files = "".join(
        file_block(f"rules/{Path(candidate).name}/{f}", (Path(candidate) / f).read_text())
        for f in ("rule.py", "SOUNDNESS.md", "test_rule.py", "PROPOSAL.md")
        if (Path(candidate) / f).is_file()
    )
    return prompt(part1, fill(part2, {"CANDIDATE": files}))


def parse(text: str) -> dict:
    """{'verdict', 'counterexamples', 'critique', 'problems'}: lenient; an unreadable verdict counts as UNSURE."""
    s = split_sections(text, SECTIONS)
    problems = []
    words = (s.get("VERDICT") or "").upper().replace("*", " ").split()
    verdict = next((w.strip(".:,") for w in words if w.strip(".:,") in VERDICTS), None)
    if verdict is None:
        problems.append("no verdict; read as UNSURE")
        verdict = "UNSURE"
    cases = []
    if s.get("COUNTEREXAMPLES"):
        try:
            data = json.loads(one_code_block(s["COUNTEREXAMPLES"], "COUNTEREXAMPLES"))
            if not isinstance(data, list):
                raise ValueError("COUNTEREXAMPLES must hold a list")
            cases = [c for c in data if isinstance(c, dict)][:MAX_CASES]
        except ValueError as exc:
            problems.append(f"counterexamples unreadable: {exc}")
    return {"verdict": verdict, "counterexamples": cases, "critique": s.get("CRITIQUE", ""), "problems": problems}


def write_cases(cases: list, path: Path) -> Path:
    Path(path).write_text(json.dumps(cases))
    return Path(path)
