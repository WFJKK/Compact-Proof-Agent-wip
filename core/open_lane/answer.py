"""The sections of an answer in the open lane: the code review's VERDICT, FOUND and NOTES, and the scaling
steps' CLAIM, SCALING, WHY IT HELPS and NOTES.

A session's answer is the text of its assistant messages joined, and what an agent writes before a tool call
can run straight into its answer (`...then the checker's modules.**VERDICT:** clean`). Agents also put
headings in markdown bold. So a heading counts where it is the section's name in capitals followed by a
colon, plain or in bold (`NAME:`, `**NAME:**`, `**NAME**:`), at the start of a line or after other text on it
(after anything but a letter, a digit or an underscore, so `RESCALING:` is not `SCALING:`), and as a markdown
heading in any case at the start of a line (`## Name`). Text inside code fences is never a heading. The first
copy of a heading counts; later copies are ordinary text. A section's text runs from its heading to the next
heading; text before the first heading belongs to no section.
"""

from __future__ import annotations

import re

_FENCE = re.compile(r"^[ \t]{0,3}(`{3,}|~{3,})")
_CLOSE = re.compile(r"^[ \t]{0,3}(`{3,}|~{3,})[ \t]*$")
_BOLD = r"(?:\*\*|__)"


def _patterns(names: tuple[str, ...]):
    alt = "|".join(re.escape(n) for n in sorted(names, key=len, reverse=True))
    inline = re.compile(rf"(?<![A-Za-z0-9_]){_BOLD}?({alt}){_BOLD}?[ \t]*:{_BOLD}?")
    marked = re.compile(rf"^[ \t]*#{{1,6}}[ \t]+{_BOLD}?[ \t]*({alt})[ \t]*:?[ \t]*{_BOLD}?[ \t]*:?", re.IGNORECASE)
    return inline, marked


def _new_headings(line: str, inline, marked, canonical: dict, seen) -> list[tuple[int, int, str]]:
    """(start, end, name) of the headings in a line that open a section, in order: a name not seen before,
    at most once per line."""
    found = []
    m = marked.match(line)
    candidates = ([m] if m else []) + list(inline.finditer(line, m.end() if m else 0))
    for c in candidates:
        name = canonical.get(c.group(1).upper())
        if name is not None and name not in seen and all(name != f[2] for f in found):
            found.append((c.start(), c.end(), name))
    return found


def sections(text: str, names) -> dict[str, str]:
    """Section name -> its text, stripped, for the headings found; a section without a heading is absent."""
    names = tuple(names)
    inline, marked = _patterns(names)
    canonical = {n.upper(): n for n in names}
    out: dict[str, list[str]] = {}
    current, fence = None, None
    for line in (text or "").splitlines():
        if fence is None:
            opened = _new_headings(line, inline, marked, canonical, out)
            if opened:
                at = 0
                for start, end, name in opened:
                    if current is not None and line[at:start].strip():
                        out[current].append(line[at:start].strip() if at else line[:start].rstrip())
                    current, at = name, end
                    out[name] = []
                if line[at:].strip():
                    out[current].append(line[at:].strip())
                continue
            f = _FENCE.match(line)
            if f:
                fence = f.group(1)
        else:
            f = _CLOSE.match(line)
            if f and f.group(1)[0] == fence[0] and len(f.group(1)) >= len(fence):
                fence = None
        if current is not None:
            out[current].append(line)
    return {k: "\n".join(v).strip() for k, v in out.items()}


def first_word(text: str) -> str:
    """The first word of a section's text, in lower case, without the punctuation and markdown around it."""
    words = (text or "").split()
    return words[0].strip(".,;:!?()[]*_`\"'").lower() if words else ""
