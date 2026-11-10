"""Split an agent response into its sections.

The response has these headings, in this order: CLAIM, WHY IT HELPS,
PREDICTION, KNOB, RECIPE, NOTES and, optionally, NEW RULE IDEA.

The parser is lenient about everything except the recipe. A heading counts in
capitals followed by a colon ("CLAIM: ..."), on a line of its own, or as a
markdown heading or bold text in any case ("## Claim", "**CLAIM:**"). Text
inside code fences is never a heading. A heading that appears twice counts
the first time; later copies are ordinary text. Missing sections other than
RECIPE only produce warnings.

RECIPE must hold exactly one fenced code block, which must parse as Python and
define a top-level function make_proof. Anything else raises ParseError, and
the round records the attempt with status "parse".
"""

from __future__ import annotations

import ast
import re
from dataclasses import asdict, dataclass, field

SECTIONS = {
    "CLAIM": "claim",
    "WHY IT HELPS": "why",
    "PREDICTION": "prediction",
    "KNOB": "knob",
    "RECIPE": "recipe",
    "NOTES": "notes",
    "NEW RULE IDEA": "new_rule_idea",
}
EXPECTED = ("CLAIM", "WHY IT HELPS", "PREDICTION", "KNOB", "RECIPE", "NOTES")
PYTHON_TAGS = ("", "python", "py", "python3")

_NAMES = "|".join(re.escape(s) for s in sorted(SECTIONS, key=len, reverse=True))
_PLAIN = re.compile(rf"^[ \t]*({_NAMES})[ \t]*:(.*)$")
_BARE = re.compile(rf"^[ \t]*({_NAMES})[ \t]*$")
_HASH = re.compile(rf"^[ \t]*#{{1,6}}[ \t]+(?:\*\*|__)?[ \t]*({_NAMES})[ \t]*:?[ \t]*(?:\*\*|__)?[ \t]*:?(.*)$", re.IGNORECASE)
_BOLD = re.compile(rf"^[ \t]*(?:\*\*|__)[ \t]*({_NAMES})[ \t]*:?[ \t]*(?:\*\*|__)[ \t]*:?(.*)$", re.IGNORECASE)
_FENCE_OPEN = re.compile(r"^[ \t]{0,3}(`{3,}|~{3,})[ \t]*([^`]*)$")
_FENCE_CLOSE = re.compile(r"^[ \t]{0,3}(`{3,}|~{3,})[ \t]*$")


class ParseError(ValueError):
    pass


@dataclass
class Parsed:
    claim: str = ""
    why: str = ""
    prediction: str = ""
    knob: str = ""
    recipe: str = ""
    notes: str = ""
    new_rule_idea: str = ""
    warnings: list[str] = field(default_factory=list)

    def summary(self) -> dict:
        """Everything but the recipe source, for parsed.json."""
        d = asdict(self)
        d.pop("recipe")
        return d


def _heading(line: str):
    for pattern in (_PLAIN, _BARE, _HASH, _BOLD):
        m = pattern.match(line)
        if m:
            name = m.group(1).upper()
            rest = m.group(2) if m.lastindex and m.lastindex >= 2 else ""
            return name, (rest or "").strip()
    return None


class _Fences:
    """Tracks whether a line is inside a fenced code block."""

    def __init__(self):
        self.open = None  # (character, length, info string)

    def feed(self, line: str):
        """Returns "open", "close" or None for this line, and updates the state."""
        if self.open is None:
            m = _FENCE_OPEN.match(line)
            if m:
                self.open = (m.group(1)[0], len(m.group(1)), m.group(2).strip())
                return "open"
            return None
        m = _FENCE_CLOSE.match(line)
        if m and m.group(1)[0] == self.open[0] and len(m.group(1)) >= self.open[1]:
            self.open = None
            return "close"
        return None


def split_sections(text: str) -> tuple[dict[str, list[str]], list[str], list[str]]:
    """Section name -> its lines, the order the sections appeared in, and warnings."""
    sections: dict[str, list[str]] = {}
    order: list[str] = []
    warnings: list[str] = []
    current = None
    fences = _Fences()
    for line in text.splitlines():
        if fences.open is None:
            h = _heading(line)
            if h is not None:
                name, rest = h
                if name not in sections:
                    current = name
                    sections[name] = [rest] if rest else []
                    order.append(name)
                    continue
                warnings.append(f"{name} appears more than once; later copies are read as text")
        fences.feed(line)
        if current is not None:
            sections[current].append(line)
    return sections, order, warnings


def code_blocks(lines: list[str]) -> tuple[list[tuple[str, str]], bool]:
    """The fenced code blocks in some lines, as (info string, code), and whether one is left open."""
    blocks, buf = [], []
    fences = _Fences()
    for line in lines:
        info = fences.open[2] if fences.open else None
        event = fences.feed(line)
        if event == "open":
            buf = []
        elif event == "close":
            blocks.append((info or "", "\n".join(buf) + "\n"))
        elif fences.open is not None:
            buf.append(line)
    return blocks, fences.open is not None


def check_recipe_source(code: str) -> None:
    try:
        tree = ast.parse(code, filename="recipe.py")
    except SyntaxError as exc:
        raise ParseError(f"the recipe is not valid Python: line {exc.lineno}: {exc.msg}") from None
    except (RecursionError, MemoryError, ValueError) as exc:
        raise ParseError(f"the recipe could not be parsed: {type(exc).__name__}") from None
    if not any(isinstance(n, ast.FunctionDef) and n.name == "make_proof" for n in tree.body):
        raise ParseError("the recipe defines no top-level function make_proof(weights, info, knob)")


def parse_response(text: str) -> Parsed:
    if not isinstance(text, str) or not text.strip():
        raise ParseError("the response is empty")
    sections, order, warnings = split_sections(text)
    if "RECIPE" not in sections:
        raise ParseError("the response has no RECIPE section")
    blocks, unclosed = code_blocks(sections["RECIPE"])
    if unclosed:
        raise ParseError("the RECIPE code block is never closed (was the response cut off?)")
    if not blocks:
        raise ParseError("the RECIPE section holds no fenced code block")
    if len(blocks) > 1:
        raise ParseError(f"the RECIPE section holds {len(blocks)} code blocks; it must hold exactly one")
    tag, code = blocks[0]
    language = tag.split()[0].lower() if tag.split() else ""
    if language not in PYTHON_TAGS:
        warnings.append(f"the recipe's code block is marked {language!r}; it is run as Python")
    check_recipe_source(code)

    out = Parsed(recipe=code, warnings=warnings)
    for name, key in SECTIONS.items():
        if name == "RECIPE" or name not in sections:
            continue
        setattr(out, key, "\n".join(sections[name]).strip())
    missing = [s for s in EXPECTED if s not in sections]
    if missing:
        out.warnings.append(f"missing sections: {', '.join(missing)}")
    expected_order = [s for s in SECTIONS if s in sections]
    if order != expected_order:
        out.warnings.append("the sections are not in the expected order")
    return out
