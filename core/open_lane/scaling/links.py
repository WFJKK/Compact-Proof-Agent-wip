"""The links of a scaling result, and what a lemma's statement names.

The result for a size is four links, each a theorem the service accepted or missing:

- `general`: a checker with the size as a parameter, proved to be the submitted checker at the network's value;
- `cost`: the exact bill of that checker's run at every value, as a function defined in Lean;
- `formula`: that function in closed form, or between proved bounds;
- `brute`: brute force's cost as a function of the size, and the comparison.

A session's answer names, in its THEOREMS section, the theorem that holds each link (`<size> <link>: <full
name>`, `as submitted` for a checker that is general as it is, `none`). Recorded here: whether that theorem is
the named theorem of a lemma submission the service accepted (the service checks the axioms of that theorem
alone). That the theorem says what the link asks stays the agent's account.

Per accepted lemma: which of the proofs' checkers its statement names. Only a lemma whose statement names a
checker that Lean found in its modules says anything about a submitted proof; one that names none may compare
two formulas of the agent's own.
"""

from __future__ import annotations

import re

LINKS = ("general", "cost", "formula", "brute")
AS_SUBMITTED = "as submitted"
_THEOREM_NAME = re.compile(r"[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)+")


def parse(text: str, symbols: list[str]) -> list[dict]:
    """The THEOREMS section's lines `<size> <link>: <theorem>`, for the sizes' symbols: for each, the theorem's
    full name, or none; a checker said to be general `as submitted` is kept as that. Lines of another form are
    not links."""
    if not symbols:
        return []
    line_form = re.compile(r"^[\s\-*`]*(" + "|".join(re.escape(s) for s in sorted(symbols, key=len, reverse=True))
                           + r")[\s`*]+(" + "|".join(LINKS) + r")[\s`*]*:[\s`*]*(.*)$")
    out = []
    for line in (text or "").splitlines():
        m = line_form.match(line)
        if not m:
            continue
        value = m.group(3).strip().lstrip("`*( ")
        name = _THEOREM_NAME.match(value)
        out.append({"size": m.group(1), "link": m.group(2), "theorem": name.group(0) if name else None,
                    "as_submitted": name is None and value.lower().startswith(AS_SUBMITTED)})
    return out


def accepted_theorems(records: list[dict], upto: int) -> dict:
    """Theorem name -> the round the service accepted it in as the named theorem of a lemma submission, in the
    run's proof rounds or in a scaling session up to round `upto`."""
    out: dict = {}
    for r in sorted(records, key=lambda r: r.get("round") or 0):
        if r.get("status") == "lemma" and r.get("theorem") and (r.get("round") or 0) <= upto:
            out.setdefault(r["theorem"], r["round"])
    return out


def of_answer(text: str, symbols: list[str], records: list[dict], k: int) -> list[dict]:
    """A session's links: the lines of its THEOREMS section, each with whether its theorem is an accepted
    submission's (None where it names none)."""
    accepted = accepted_theorems(records, k)
    return [{**l, "accepted": (l["theorem"] in accepted) if l["theorem"] else None} for l in parse(text, symbols)]


def table(steps: list[dict]) -> dict:
    """Per size and link, what the sessions' answers say holds it: the latest line that names an accepted theorem
    (or says `as submitted`), else the latest line: {theorem, accepted, as_submitted, round}. Empty for sessions
    that were not asked for the links."""
    out: dict = {}
    for s in sorted((s for s in steps if s.get("result")), key=lambda s: s["round"]):
        for l in s["result"].get("links") or []:
            row = out.setdefault(l["size"], {})
            good = l.get("accepted") or l.get("as_submitted")
            had = row.get(l["link"])
            if good or had is None or not (had.get("accepted") or had.get("as_submitted")):
                row[l["link"]] = {**{key: l.get(key) for key in ("theorem", "accepted", "as_submitted")}, "round": s["round"]}
    return out


def held(cell: dict | None) -> bool:
    return bool(cell and (cell.get("accepted") or cell.get("as_submitted")))


def cell_text(cell: dict | None, code: bool = False) -> str:
    if cell is None:
        return "not said"
    if cell.get("as_submitted"):
        return "the submitted checker, as it is"
    if not cell.get("theorem"):
        return "none"
    name = f"`{cell['theorem']}`" if code else cell["theorem"]
    return name if cell.get("accepted") else f"{name} (named, not an accepted submission's theorem)"


def names_in(statement: str | None, proofs: list[dict]) -> list[str]:
    """The proofs whose checker's name a statement holds as a whole name (their record ids)."""
    return [p["record_id"] for p in proofs
            if p.get("checker") and re.search(r"(?<![\w.'])" + re.escape(p["checker"]) + r"(?![\w'.])", statement or "")]


def about(lemma: dict, proofs: list[dict]) -> list[str]:
    """The proofs a lemma says something about: its statement names their checker, and Lean found that checker,
    term for term, in the modules the service compiled for it. (A result from before the names were recorded
    is read from its statement.)"""
    names = lemma["names"] if "names" in lemma else names_in(lemma.get("statement"), proofs)
    return [rid for rid in names if (lemma["checkers"].get(rid) or {}).get("verified")]
