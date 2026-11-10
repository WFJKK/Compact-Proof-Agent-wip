"""The rule route, from a config file, resumably.

    python -m core.rules_route run <config.yaml>
    python -m core.rules_route status <config.yaml>
    python -m core.rules_route proposals <run folder>
    python -m core.rules_route build-image

Steps, each in its own folder under work_dir/<route_id>/ and skipped once its DONE marker exists, so a route
stopped at any point (a crash, a lost connection) resumes without repeating a paid call:

    proposal/                 the proposal's text and where it came from
    attempt_<k>/implement/    the implementer's prompt, response (saved before parsing) and candidate/<name>/
    attempt_<k>/checks/       the static guard, the candidate's tests and the audit, in the check box
    attempt_<k>/review_<i>/   each review: prompt, response, verdict, and the audit of its counterexamples
    attempt_<k>/decision.json passed, or why not (the next attempt's implementer gets the reasons)
    adopted.json | failed.json

A candidate is adopted only if the static guard, its tests and the audit pass, no counterexample is confirmed,
and every review's verdict is in adopt_on (SOUND by default). Nothing is committed or pushed.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

from ..check.plugins import RULES_DIR, file_hashes, static_guard
from ..util import REPO_ROOT, read_yaml, sha256_file, write_json
from . import adopt as adopt_mod
from . import box, implement, proposals, review
from .common import make_backend

DEFAULTS = {
    "revisions": 1,
    "reviewers": 1,
    "audit_level": "full",
    "audit_seed": 0,
    "checks_sandbox": "hardened",
    "checks_timeout_s": 7200,
    "checks_memory_mb": 4096,
    "adopt_on": ["SOUND"],
    "replace": False,
    "work_dir": "~/auto-research-compact-proof-runs/rule-route",
    "audit_folders": None,  # model folders the audit samples (default: every folder beyond linear maps)
    "rules_dir": None,  # where adopted rules go (default: the repository's rules/)
}
REQUIRED = ("route_id", "name", "proposal")


class RouteError(RuntimeError):
    pass


def load_config(path: Path) -> dict:
    raw = read_yaml(Path(path)) or {}
    cfg = {**DEFAULTS, **raw}
    missing = [k for k in REQUIRED if k not in cfg]
    if missing:
        raise RouteError(f"the route config lacks {missing}")
    if "candidate" not in cfg and "implementer" not in cfg:
        raise RouteError("the route config needs an implementer (or a candidate folder to check)")
    if "reviewer" not in cfg:
        raise RouteError("the route config needs a reviewer")
    if not implement.NAME_RE.match(cfg["name"]):
        raise RouteError(f"{cfg['name']!r} is not a rule name")
    cfg["_config_sha256"] = sha256_file(Path(path))
    return cfg


def _done(d: Path) -> bool:
    return (d / "DONE").is_file()


def _mark(d: Path) -> None:
    (d / "DONE").write_text("")


def _commit() -> str | None:
    try:
        return subprocess.run(["git", "rev-parse", "HEAD"], cwd=REPO_ROOT, capture_output=True, text=True, check=True).stdout.strip()
    except (OSError, subprocess.CalledProcessError):
        return None


def _respond(backend, prompt, index: int, where: Path, log):
    """The backend's response, saved before anything else; an existing response.md is reused (resume).
    The prompt goes to where/prompt.md; a manual backend waits for where/answer/response.md, and the API
    backend keeps its raw response in where/answer/."""
    where.mkdir(parents=True, exist_ok=True)
    resp_path = where / "response.md"
    if resp_path.is_file() and resp_path.stat().st_size > 0:
        return resp_path.read_text(), json.loads((where / "meta.json").read_text()) if (where / "meta.json").is_file() else {}
    write_json(where / "prompt.json", prompt.as_json())
    (where / "prompt.md").write_text(prompt.text)
    (where / "answer").mkdir(exist_ok=True)
    r = backend.respond(prompt, index, where / "answer")
    resp_path.write_text(r.text)
    write_json(where / "meta.json", r.meta)
    log(f"  response saved: {resp_path} ({r.meta.get('output_tokens', 0)} output tokens, ${r.meta.get('cost_usd') or 0:.2f})")
    return r.text, r.meta


def get_proposal(cfg: dict, d: Path, log) -> dict:
    if _done(d):
        return json.loads((d / "proposal.json").read_text())
    d.mkdir(parents=True, exist_ok=True)
    p = cfg["proposal"]
    if "text" in p:
        out = {"text": p["text"], "source": "the route config"}
    elif "file" in p:
        path = Path(p["file"]).expanduser()
        path = path if path.is_absolute() else REPO_ROOT / path
        out = {"text": path.read_text(), "source": str(path)}
    elif "run" in p:
        items = proposals.collect(Path(p["run"]).expanduser())
        item = proposals.pick(items, p.get("pick", "latest"))
        out = {"text": item["text"], "source": f"run {item['run']}, {', '.join(item['attempts'])}"}
    else:
        raise RouteError("proposal needs text, file or run")
    write_json(d / "proposal.json", out)
    _mark(d)
    log(f"proposal: {out['source']}")
    return out


def proposal_md(prop: dict, cfg: dict, implemented_by: str) -> str:
    return (f"# Proposal: {cfg['name']}\n\n**Source.** {prop['source']}\n\n**Implemented by.** {implemented_by}\n\n"
            f"## NEW RULE IDEA\n\n{prop['text'].strip()}\n")


def run_checks(cfg: dict, candidate: Path, d: Path, log) -> dict:
    if _done(d):
        return json.loads((d / "checks.json").read_text())
    d.mkdir(parents=True, exist_ok=True)
    out = {"static_guard": static_guard((candidate / "rule.py").read_text()), "files_sha256": file_hashes(candidate)}
    if out["static_guard"]:
        out.update(passed=False, reasons=[f"static guard: {p}" for p in out["static_guard"]])
        write_json(d / "checks.json", out)
        _mark(d)
        return out
    mode, rt = box.choose_mode(cfg["checks_sandbox"])
    out["sandbox"] = mode
    b = box.make_box(candidate)
    try:
        name = candidate.name
        log(f"  tests ({mode})")
        t = box.run(b, "pytest", [f"{{box}}/repo/rules/{name}/test_rule.py", "-q", "-p", "no:cacheprovider", "--basetemp",
                                  "{box}/tmp/pytest"], mode, rt, cfg["checks_timeout_s"], cfg["checks_memory_mb"])
        (d / "tests.txt").write_text(t.stdout + "\n--- stderr ---\n" + t.stderr)
        out["tests"] = {"returncode": t.returncode, "timed_out": t.timed_out, "tail": t.stdout.strip().splitlines()[-1:] or []}
        log(f"  audit ({cfg['audit_level']}, {mode})")
        extra = ["--folders", *cfg["audit_folders"]] if cfg["audit_folders"] else []
        a = box.run(b, "core.rules_route.audit", [f"{{box}}/repo/rules/{name}", "--level", cfg["audit_level"], "--seed",
                                                    str(cfg["audit_seed"]), "--out", "{box}/out/audit.json", *extra],
                    mode, rt, cfg["checks_timeout_s"], cfg["checks_memory_mb"])
        (d / "audit.txt").write_text(a.stdout + "\n--- stderr ---\n" + a.stderr)
        report = json.loads((b / "out" / "audit.json").read_text()) if (b / "out" / "audit.json").is_file() else None
        if report is not None:
            write_json(d / "audit.json", report)
        out["audit"] = {k: v for k, v in (report or {}).items() if k != "records"} or None
    finally:
        box.discard(b)
    reasons = []
    if out["tests"]["returncode"] != 0:
        reasons.append("its tests failed:\n" + "\n".join((d / "tests.txt").read_text().splitlines()[-40:]))
    if not out["audit"]:
        reasons.append("the audit did not finish:\n" + "\n".join((d / "audit.txt").read_text().splitlines()[-20:]))
    elif not out["audit"].get("loaded", False):
        reasons.append(f"the rule did not load: {out['audit'].get('problems')}")
    elif not out["audit"].get("passed"):
        reasons.append("the audit found violations:\n" + json.dumps(out["audit"]["violations"][:5], indent=1))
    out.update(passed=not reasons, reasons=reasons)
    write_json(d / "checks.json", out)
    _mark(d)
    return out


def run_review(cfg: dict, candidate: Path, d: Path, index: int, log) -> dict:
    if _done(d):
        return json.loads((d / "review.json").read_text())
    d.mkdir(parents=True, exist_ok=True)
    backend = make_backend(cfg["reviewer"], cfg, log)
    text, meta = _respond(backend, review.build(candidate), index, d, log)
    parsed = review.parse(text)
    cases = [c for c in parsed["counterexamples"] if not str(c.get("network", "")).startswith("file:")]
    parsed["backend"] = cfg["reviewer"].get("backend")
    parsed["model"] = meta.get("model") or cfg["reviewer"].get("agent_model")
    parsed["counterexamples"] = len(cases)
    audits = None
    if cases:
        mode, rt = box.choose_mode(cfg["checks_sandbox"])
        b = box.make_box(candidate)
        try:
            review.write_cases(cases, b / "tmp" / "cases.json")
            a = box.run(b, "core.rules_route.audit", [f"{{box}}/repo/rules/{candidate.name}", "--only-counterexamples",
                                                        "--counterexamples", "{box}/tmp/cases.json", "--out", "{box}/out/cases.json"],
                        mode, rt, cfg["checks_timeout_s"], cfg["checks_memory_mb"])
            (d / "cases_audit.txt").write_text(a.stdout + "\n--- stderr ---\n" + a.stderr)
            if (b / "out" / "cases.json").is_file():
                audits = json.loads((b / "out" / "cases.json").read_text())
        finally:
            box.discard(b)
        write_json(d / "cases.json", cases)
        if audits is not None:
            write_json(d / "cases_audit.json", audits)
    parsed["confirmed"] = [] if audits is None else audits.get("violations", [])
    parsed["cases_audited"] = audits is not None
    write_json(d / "review.json", parsed)
    _mark(d)
    log(f"  review {index}: {parsed['verdict']}, {len(cases)} counterexamples, {len(parsed['confirmed'])} confirmed")
    return parsed


def decide(cfg: dict, checks: dict, reviews: list) -> tuple[bool, list]:
    reasons = list(checks.get("reasons", []))
    for i, r in enumerate(reviews):
        if r["confirmed"]:
            reasons.append(f"review {i + 1}: confirmed counterexamples:\n" + json.dumps(r["confirmed"][:3], indent=1))
        elif r["counterexamples"] and not r["cases_audited"]:
            reasons.append(f"review {i + 1}: its counterexamples could not be audited")
        if r["verdict"] not in cfg["adopt_on"]:
            reasons.append(f"review {i + 1}: verdict {r['verdict']}:\n{r['critique'].strip()[:6000]}")
    return not reasons, reasons


def run(cfg: dict, log=print) -> dict:
    root = Path(cfg["work_dir"]).expanduser() / cfg["route_id"]
    root.mkdir(parents=True, exist_ok=True)
    for f in ("adopted.json", "failed.json"):
        if (root / f).is_file():
            log(f"the route has finished: {root / f}")
            return json.loads((root / f).read_text())
    prop = get_proposal(cfg, root / "proposal", log)
    name = cfg["name"]
    feedback = ""
    attempts = 1 + int(cfg["revisions"]) if "candidate" not in cfg else 1
    for k in range(attempts):
        a = root / f"attempt_{k}"
        if "candidate" in cfg:
            candidate = Path(cfg["candidate"]).expanduser()
            candidate = candidate if candidate.is_absolute() else REPO_ROOT / candidate
            implemented_by = cfg.get("implemented_by", "provided as a folder")
        else:
            d = a / "implement"
            candidate = d / "candidate" / name
            implemented_by = f"{cfg['implementer'].get('backend')} {cfg['implementer'].get('agent_model', '')}".strip()
            if not _done(d):
                backend = make_backend(cfg["implementer"], cfg, log)
                log(f"attempt {k}: implementer")
                text, _ = _respond(backend, implement.build(name, prop["text"], feedback), k, d, log)
                try:
                    files = implement.parse(text, name)
                except implement.ImplementError as exc:
                    write_json(a / "decision.json", {"passed": False, "reasons": [f"unreadable response: {exc}"]})
                    feedback = f"Your response could not be read: {exc}"
                    _mark(d)
                    continue
                implement.write_candidate(d / "candidate", name, files, proposal_md(prop, cfg, implemented_by))
                (d / "notes.md").write_text(files["notes"])
                _mark(d)
            elif not candidate.is_dir():
                feedback = json.loads((a / "decision.json").read_text())["reasons"][0]
                continue
        log(f"attempt {k}: checks")
        checks = run_checks(cfg, candidate, a / "checks", log)
        reviews = []
        if checks["passed"]:
            before = sum(len(list((root / f"attempt_{j}").glob("review_*"))) for j in range(k))  # reviews answered so far
            for i in range(int(cfg["reviewers"])):
                log(f"attempt {k}: review {i + 1}")
                reviews.append(run_review(cfg, candidate, a / f"review_{i}", before + i, log))
        passed, reasons = decide(cfg, checks, reviews)
        write_json(a / "decision.json", {"passed": passed, "reasons": reasons})
        if passed and file_hashes(candidate) != checks.get("files_sha256"):
            passed, reasons = False, ["the candidate's files changed after they were checked; start a new route to check them"]
            write_json(a / "decision.json", {"passed": passed, "reasons": reasons})
            out = {"adopted": False, "attempts": k + 1, "last_reasons": reasons[0]}
            write_json(root / "failed.json", out)
            log(reasons[0])
            return out
        if passed:
            provenance = {"route_id": cfg["route_id"], "proposal": prop["source"], "implemented_by": implemented_by,
                          "route_config_sha256": cfg["_config_sha256"], "commit": _commit(), "attempt": k}
            rules_dir = Path(cfg["rules_dir"]).expanduser() if cfg["rules_dir"] else RULES_DIR
            status = adopt_mod.adopt(candidate, provenance, {**checks, "counterexample_audits": [r["confirmed"] for r in reviews]},
                                     reviews, rules_dir, replace=bool(cfg["replace"]))
            write_json(root / "adopted.json", status)
            log(f"adopted: rules/{name}/ (commit it to keep it; nothing was committed)")
            return status
        feedback = "\n\n".join(reasons)
        log(f"attempt {k}: not adopted")
    out = {"adopted": False, "attempts": attempts, "last_reasons": feedback[:20000]}
    write_json(root / "failed.json", out)
    log(f"not adopted after {attempts} attempt(s): {root / 'failed.json'}")
    return out


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    r = sub.add_parser("run")
    r.add_argument("config")
    s = sub.add_parser("status")
    s.add_argument("config")
    p = sub.add_parser("proposals")
    p.add_argument("run_dir")
    p.add_argument("--json", action="store_true")
    sub.add_parser("build-image")
    args = ap.parse_args(argv)
    if args.cmd == "proposals":
        items = proposals.collect(Path(args.run_dir))
        print(json.dumps(items, indent=1) if args.json else proposals.render(items))
        return 0
    if args.cmd == "build-image":
        box.build_image()
        return 0
    cfg = load_config(Path(args.config))
    if args.cmd == "status":
        root = Path(cfg["work_dir"]).expanduser() / cfg["route_id"]
        for p in sorted(root.rglob("*.json")) if root.exists() else []:
            if p.name in ("decision.json", "adopted.json", "failed.json"):
                print(p.relative_to(root), json.loads(p.read_text()).get("passed", ""))
        return 0
    res = run(cfg)
    return 0 if res.get("status") == "adopted" else 1


if __name__ == "__main__":
    sys.exit(main())
