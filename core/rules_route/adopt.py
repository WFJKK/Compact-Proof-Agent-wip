"""Step 5 of the route: a candidate that passed every check becomes rules/<name>/, which the checker loads.

status.json records the tier, where the idea and the code came from, the checks it passed and the SHA-256 of
rule.py, SOUNDNESS.md, test_rule.py and PROPOSAL.md; the checker uses the rule only while those hashes match
(core/check/plugins.py). AUDIT.json (the audit's summary) and REVIEW.md (each review's verdict and critique)
sit next to them as the record. Nothing here commits or publishes anything.
"""

from __future__ import annotations

import datetime as dt
import json
import shutil
from pathlib import Path

from ..check.plugins import RULES_DIR, file_hashes, inspect_rule

TIER = "python-checked"


class AdoptError(RuntimeError):
    pass


def adopt(candidate: Path, provenance: dict, checks: dict, reviews: list, rules_dir: Path | None = None,
          replace: bool = False) -> dict:
    candidate = Path(candidate)
    name = candidate.name
    root = Path(rules_dir or RULES_DIR)
    target = root / name
    in_place = target.exists() and target.resolve() == candidate.resolve()
    for f in ("rule.py", "SOUNDNESS.md", "test_rule.py", "PROPOSAL.md"):
        if not (candidate / f).is_file():
            raise AdoptError(f"the candidate has no {f}")
    if in_place:
        if (target / "status.json").is_file() and not replace:
            raise AdoptError(f"{target} is adopted already; adopting it again needs replace: true in the route config")
    else:
        if target.exists():
            if not replace:
                raise AdoptError(f"{target} exists; adopting over it needs replace: true in the route config")
            old = target.with_name(f".replaced-{name}-{dt.datetime.now().strftime('%Y%m%d-%H%M%S')}")
            target.rename(old)  # kept, never deleted: the record of what earlier runs used
        target.mkdir(parents=True)
        for f in ("rule.py", "SOUNDNESS.md", "test_rule.py", "PROPOSAL.md"):
            shutil.copy2(candidate / f, target / f)
    audit = checks.get("audit") or {}
    summary = {k: audit.get(k) for k in ("level", "seed", "leaves", "by_outcome", "certified", "exact_singles", "by_kind", "smallest_slack", "passed")}
    (target / "AUDIT.json").write_text(json.dumps({"audit": summary, "counterexamples": checks.get("counterexample_audits", [])}, indent=1) + "\n")
    lines = ["# Reviews\n"]
    for i, r in enumerate(reviews):
        who = r.get("backend") or "?"
        who += f", {r['model']}" if r.get("model") else " backend, model not recorded" if who == "manual" else ""
        lines.append(f"## Review {i + 1}: {r['verdict']} ({who})\n\n{r.get('critique', '').strip()}\n")
    (target / "REVIEW.md").write_text("\n".join(lines))
    status = {
        "name": name,
        "status": "adopted",
        "tier": TIER,
        "adopted_at": dt.datetime.now(dt.timezone.utc).isoformat(timespec="seconds"),
        "provenance": provenance,
        "checks": {
            "static_guard": checks.get("static_guard", []),
            "tests": checks.get("tests", {}),
            "audit": {k: summary.get(k) for k in ("level", "leaves", "certified", "exact_singles", "passed")},
            "sandbox": checks.get("sandbox"),
        },
        "reviews": [{k: r.get(k) for k in ("verdict", "backend", "model", "counterexamples")} for r in reviews],
        "files_sha256": file_hashes(target),
    }
    (target / "status.json").write_text(json.dumps(status, indent=2, sort_keys=True) + "\n")
    rule, problems = inspect_rule(target)
    if rule is None:
        raise AdoptError(f"the adopted rule does not load: {problems}")
    return status
