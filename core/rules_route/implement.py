"""Step 2 of the route: a separate implementer agent writes the rule for one proposal.

The prompt (prompts/implement.md) gives the plugin contract, the hard constraints, the checker's code and the
adopted rules as worked examples (part 1, the same for every attempt), then the proposal, the rule's name and,
on a revision, what went wrong last time (part 2). The response's sections become the candidate folder.
"""

from __future__ import annotations

import re
from pathlib import Path

from .common import checker_context, fill, one_code_block, prompt, split_sections, template

SECTIONS = ("NAME", "RULE", "SOUNDNESS", "TESTS", "NOTES")
NAME_RE = re.compile(r"^[a-z][a-z0-9_]{1,40}$")


class ImplementError(ValueError):
    pass


def build(name: str, proposal_text: str, feedback: str = "", rules_dir=None):
    part1, part2 = template("implement")
    part1 = fill(part1, {"CONTEXT": checker_context(rules_dir, exclude=name)})
    fb = f"\nWHAT WENT WRONG WITH YOUR LAST VERSION\n\n{feedback.strip()}\n" if feedback.strip() else ""
    part2 = fill(part2, {"PROPOSAL": proposal_text.strip(), "NAME": name, "FEEDBACK": fb})
    return prompt(part1, part2)


def parse(text: str, name: str) -> dict:
    """{'rule.py': ..., 'SOUNDNESS.md': ..., 'test_rule.py': ..., 'notes': ...}; raises ImplementError."""
    s = split_sections(text, SECTIONS)
    missing = [k for k in ("NAME", "RULE", "SOUNDNESS", "TESTS") if not s.get(k)]
    if missing:
        raise ImplementError(f"the response lacks {missing}")
    got = s["NAME"].split()[0].strip("`*") if s["NAME"].split() else ""
    if got != name:
        raise ImplementError(f"NAME is {got!r}; it must be {name!r}")
    try:
        rule = one_code_block(s["RULE"], "RULE")
        tests = one_code_block(s["TESTS"], "TESTS")
    except ValueError as exc:
        raise ImplementError(str(exc)) from exc
    return {"rule.py": rule, "SOUNDNESS.md": s["SOUNDNESS"].strip() + "\n", "test_rule.py": tests, "notes": s.get("NOTES", "")}


def write_candidate(where: Path, name: str, files: dict, proposal_md: str) -> Path:
    """The candidate folder <where>/<name>/ with the rule's files and its proposal."""
    if not NAME_RE.match(name):
        raise ImplementError(f"{name!r} is not a rule name (lower case, digits and underscores)")
    folder = Path(where) / name
    folder.mkdir(parents=True, exist_ok=True)
    for f in ("rule.py", "SOUNDNESS.md", "test_rule.py"):
        (folder / f).write_text(files[f])
    (folder / "PROPOSAL.md").write_text(proposal_md)
    return folder
