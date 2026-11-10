"""The NEW RULE IDEA answers of a run, with where each came from.

    python -m core.rules_route proposals <run folder> [--json]

A run folder holds round_<k>/attempt_<j>/parsed.json, whose new_rule_idea is the agent's proposal for that
attempt (often the same idea, reworded, in every round). Identical texts are listed once, with every attempt
that gave them.
"""

from __future__ import annotations

import json
from pathlib import Path


def collect(run_dir: Path) -> list[dict]:
    run_dir = Path(run_dir).expanduser()
    seen: dict[str, dict] = {}
    for parsed in sorted(run_dir.glob("round_*/attempt_*/parsed.json")):
        try:
            d = json.loads(parsed.read_text())
        except (OSError, ValueError):
            continue
        idea = (d.get("new_rule_idea") or "").strip()
        if not idea:
            continue
        where = f"{parsed.parent.parent.name}/{parsed.parent.name}"
        if idea in seen:
            seen[idea]["attempts"].append(where)
            continue
        seen[idea] = {"index": len(seen), "run": run_dir.name, "attempts": [where], "claim": d.get("claim", ""), "text": idea}
    return list(seen.values())


def pick(items: list[dict], which) -> dict:
    """which: an index, or "latest" (the proposal of the most recent attempt)."""
    if not items:
        raise ValueError("the run has no NEW RULE IDEA answers")
    if which in (None, "latest"):
        return max(items, key=lambda d: d["attempts"][-1])
    i = int(which)
    if not 0 <= i < len(items):
        raise ValueError(f"proposal {i} does not exist; the run has {len(items)}")
    return items[i]


def render(items: list[dict]) -> str:
    out = []
    for d in items:
        out.append(f"[{d['index']}] {d['run']}: {', '.join(d['attempts'])}\n{d['text']}\n")
    return "\n".join(out) if out else "(no NEW RULE IDEA answers)"
