from pathlib import Path

import pytest

from core.agent.backends import BackendError
from core.agent.backends.fake import FakeBackend
from core.agent.parse import ParseError, parse_response

REPO = Path(__file__).resolve().parent.parent

RECIPE = '''```python
import helpers


def make_proof(weights, info, knob):
    return helpers.proof(helpers.full_tree(info["input_space"]))
```'''


def response(**sections):
    order = ["CLAIM", "WHY IT HELPS", "PREDICTION", "KNOB", "RECIPE", "NOTES", "NEW RULE IDEA"]
    parts = []
    for name in order:
        key = name.lower().replace(" ", "_")
        if key in sections and sections[key] is not None:
            parts.append(f"{name}: {sections[key]}" if name != "RECIPE" else f"RECIPE:\n{sections[key]}")
    return "\n\n".join(parts)


FULL = dict(
    claim="It sums the tokens.",
    why_it_helps="Fewer checks.",
    prediction="Full accuracy at B/2.",
    knob="Unused.",
    recipe=RECIPE,
    notes="First try.",
)


def test_every_baseline_parses():
    for path in sorted((REPO / "models").glob("*/baselines/*.md")) + sorted((REPO / "tests").glob("stub_model/baselines/*.md")):
        p = parse_response(path.read_text())
        assert "def make_proof" in p.recipe and p.claim and p.notes, path
        assert not p.warnings, (path, p.warnings)


def test_sections_are_read():
    p = parse_response(response(**FULL, new_rule_idea="A rule for sorted inputs."))
    assert p.claim == "It sums the tokens."
    assert p.why == "Fewer checks."
    assert p.prediction == "Full accuracy at B/2."
    assert p.knob == "Unused."
    assert p.notes == "First try."
    assert p.new_rule_idea == "A rule for sorted inputs."
    assert p.recipe.startswith("import helpers")
    assert "recipe" not in p.summary()


@pytest.mark.parametrize(
    "recipe, message",
    [
        (None, "no RECIPE section"),
        ("Here is the idea, but no code.", "no fenced code block"),
        (RECIPE + "\n\n" + RECIPE, "exactly one"),
        ("```python\ndef make_proof(w, i, k):\n    return {}\n", "never closed"),
        ("```python\ndef make_proof(w, i, k)\n    return {}\n```", "not valid Python"),
        ("```python\ndef other(w, i, k):\n    return {}\n```", "no top-level function make_proof"),
    ],
)
def test_bad_recipes_are_parse_errors(recipe, message):
    with pytest.raises(ParseError, match=message):
        parse_response(response(**{**FULL, "recipe": recipe}))


def test_empty_response():
    with pytest.raises(ParseError, match="empty"):
        parse_response("   ")


def test_headings_inside_code_are_code():
    recipe = '''```python
# NOTES: this comment is not a heading
CLAIM = "not a heading either"


def make_proof(weights, info, knob):
    """
    RECIPE:
    """
    return {}
```'''
    p = parse_response(response(**{**FULL, "recipe": recipe}))
    assert "# NOTES: this comment" in p.recipe and 'CLAIM = "not a heading' in p.recipe
    assert p.notes == "First try."


def test_markdown_headings_are_accepted():
    text = f"""## Claim
It sums the tokens.

**WHY IT HELPS:** Fewer checks.

### PREDICTION:
Full accuracy.

**Knob**: unused

## RECIPE
{RECIPE}

NOTES
Learned nothing yet.
"""
    p = parse_response(text)
    assert p.claim == "It sums the tokens."
    assert p.why == "Fewer checks."
    assert p.prediction == "Full accuracy."
    assert p.knob == "unused"
    assert p.notes == "Learned nothing yet."
    assert not p.warnings


def test_lenient_about_everything_but_the_recipe():
    p = parse_response("RECIPE:\n" + RECIPE + "\n\nNOTES: short\n\nNOTES: again\nPREDICTION: late")
    assert "NOTES appears more than once" in " ".join(p.warnings)
    assert "missing sections" in " ".join(p.warnings)
    assert "not in the expected order" in " ".join(p.warnings)
    assert p.notes.startswith("short") and "NOTES: again" in p.notes


def test_prose_lines_in_lower_case_are_not_headings():
    p = parse_response(response(**{**FULL, "claim": "It sums.\nNotes: this line belongs to the claim."}))
    assert "Notes: this line belongs to the claim." in p.claim
    assert p.notes == "First try."


def test_untagged_or_other_tagged_block():
    p = parse_response(response(**{**FULL, "recipe": RECIPE.replace("```python", "```")}))
    assert not p.warnings
    p = parse_response(response(**{**FULL, "recipe": RECIPE.replace("```python", "```text")}))
    assert "marked 'text'" in p.warnings[0]


def test_fake_backend_replays_in_order(tmp_path):
    (tmp_path / "b.md").write_text("second")
    (tmp_path / "a.md").write_text("first")
    (tmp_path / "skip.txt").write_text("not a response")
    extra = tmp_path / "c.txt"
    extra.write_text("third")
    fake = FakeBackend([tmp_path, extra])
    assert len(fake) == 3 and fake.available(2) and not fake.available(3)
    assert [fake.respond(None, i).text for i in range(3)] == ["first", "second", "third"]
    assert fake.respond("prompt", 0).meta["source"] == "a.md"
    with pytest.raises(BackendError):
        fake.respond(None, 3)
    with pytest.raises(BackendError):
        FakeBackend([tmp_path / "missing"])
