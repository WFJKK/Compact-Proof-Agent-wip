"""What a scaling session's workspace starts with, and its compilation before the session begins.

Beyond the locked proof's modules (put there by the session itself, as for every stage after the proof rounds):

- the modules of the run's other scored proofs, and of the lemmas the earlier scaling sessions had accepted;
- the modules the earlier sessions left without having them accepted (drafts), with whether their last compile
  succeeded;
- the files the earlier sessions left in their Python workspaces, and every proof's certificate and plan
  (py/handed_in_proofs.json).

Then every module of the workspace is compiled, in import order, as a lean_check of it with no edits would be
(the lock applied), at no charge to the session's budgets and before its clock starts: the first scaling
sessions spent a third of their compiles on building the locked proof's modules one at a time. A draft whose last
compile failed is not tried, and other drafts get a short limit: one of the first drafts held a kernel
computation that ran into Lean's own limit after eight minutes.
"""

from __future__ import annotations

import json
import time
from pathlib import Path

from ...archive import RunDir
from ..session import MODULE_PATH, PY_DIR, Session, last_compiles, module_imports, module_name, workspace_files

PROOFS_FILE = "handed_in_proofs.json"
COMPILE_SECONDS = 1200.0  # for compiling a workspace before its session, all modules together
DRAFT_SECONDS = 180.0  # of it, for one draft


def session_dir(run: RunDir, step: dict) -> Path:
    return run.round_path(step["round"]) / "attempt_0" / "open_lane"


def earlier(sp: dict, step: dict) -> list[dict]:
    """The sessions done before a step, in order."""
    return sorted((s for s in sp["steps"] if s["round"] < step["round"] and s.get("result")), key=lambda s: s["round"])


def submitted(sub: Path) -> tuple[dict, dict]:
    return json.loads((sub / "manifest.json").read_text()), json.loads((sub / "receipt.json").read_text())


def carried_modules(run: RunDir, sp: dict, step: dict, locked: dict) -> dict:
    """The accepted modules a step's workspace starts with beyond the locked proof's: the other offered proofs',
    and those of the lemmas earlier steps had accepted (the later step's version of a path, the proofs' own
    version where a proof has one). Path -> text."""
    out = {}
    for s in earlier(sp, step):
        for l in s["result"]["lemmas"]:
            sub = Path(l["submission_dir"])
            for rel in l.get("modules") or []:
                if (sub / rel).is_file():
                    out[rel] = (sub / rel).read_text()
    for p in sp["proofs"]:
        if p["offered"] and not p["locked"]:
            sub = Path(p["submission_dir"])
            for rel in p["modules"]:
                if (sub / rel).is_file():
                    out[rel] = (sub / rel).read_text()
    return {rel: text for rel, text in out.items() if rel not in locked["modules"]}


def draft_modules(run: RunDir, sp: dict, step: dict, locked: dict, held: dict) -> dict:
    """What the earlier steps' sessions left in their workspaces without having it accepted: path -> {text,
    compiled}, the latest session's version, with whether the last compile of that text succeeded (None when
    none is on record). A path the locked proof or a carried module holds stays that module's."""
    out: dict = {}
    for s in earlier(sp, step):
        root = session_dir(run, s) / "workspace"
        if not (root / "Candidate").is_dir():
            continue
        last = last_compiles(session_dir(run, s))
        for f in sorted((root / "Candidate").rglob("*.lean")):
            rel = f.relative_to(root).as_posix()
            if not (f.is_file() and not f.is_symlink() and MODULE_PATH.match(rel)):
                continue
            text = f.read_text()
            if rel in last:
                compiled = bool(last[rel].get("ok"))
            else:  # not compiled in that session: as the session before left it, if it is the same text
                compiled = out[rel]["compiled"] if rel in out and out[rel]["text"] == text else None
            out[rel] = {"text": text, "compiled": compiled}
    taken = set(locked["modules"]) | set(locked.get("free") or []) | set(held)
    return {rel: d for rel, d in out.items() if rel not in taken}


def earlier_python(run: RunDir, sp: dict, step: dict) -> list[dict]:
    """The files the earlier steps' sessions left in their Python workspaces (the latest session's version of a
    path), but for the two the pipeline writes afresh."""
    out = {}
    for s in earlier(sp, step):
        files, _ = workspace_files(session_dir(run, s) / PY_DIR)
        for rel, path in files.items():
            if rel not in (PROOFS_FILE, Session.LOCKED_PROOF):
                out[rel] = str(path)
    return [{"path": rel, "source": src} for rel, src in sorted(out.items())]


def proofs_file(sp: dict) -> str:
    items = []
    for p in sp["proofs"]:
        manifest, receipt = submitted(Path(p["submission_dir"]))
        block = manifest.get("scored") if isinstance(manifest.get("scored"), dict) else {}
        scoring = receipt.get("scoring") if isinstance(receipt.get("scoring"), dict) else {}
        items.append({"record_id": p["record_id"], "locked": p["locked"], "in_workspace": p["offered"], "checker": p["checker"],
                      "sound": p["sound"], "certificate": block.get("certificate") or [], "plan": block.get("plan"),
                      "certified_count": receipt.get("certified_count"), "bill": scoring.get("bill"), "length": scoring.get("length"),
                      "description_size": scoring.get("description_size"), "plan_bits": scoring.get("plan_bits"),
                      "modules": p["modules"]})
    return json.dumps({"what": "The run's scored proofs these sessions are about: each one's certificate and plan as submitted, "
                               "and what the service's receipt says of it.", "proofs": items}, indent=1)


def compile_beforehand(session: Session, drafts: dict) -> list[dict]:
    """Compile a session's workspace before it begins: per module {path, compiled, seconds, errors}, in the
    order compiled (import order). A module that does not compile, imports one that did not, or comes after
    the time for this is used up, is left as it is. `drafts`: path -> whether its last compile succeeded (None:
    not known). Only in a run whose checkers the service runs compiled (elsewhere a compile names a claimed
    count): [] otherwise. Nothing of the session's budgets or clock is used; running it again compiles again."""
    if not session.compiled:
        return []
    root = session.workspace / "Candidate"
    files = sorted(f.relative_to(session.workspace).as_posix() for f in root.rglob("*.lean")) if root.is_dir() else []
    names = {module_name(rel): rel for rel in files if MODULE_PATH.match(rel)}
    imports = {n: [i for i in module_imports((session.workspace / rel).read_text()) if i in names] for n, rel in names.items()}
    order: list[str] = []
    seen: dict[str, int] = {}

    def visit(n: str) -> None:
        if seen.get(n):  # done, or on the current path (a cycle, which the compiler will report)
            return
        seen[n] = 1
        for dep in imports[n]:
            visit(dep)
        seen[n] = 2
        order.append(n)

    for n in sorted(names):
        visit(n)
    out, failed, start = [], set(), time.monotonic()
    for n in order:
        rel = names[n]
        entry = {"path": rel, "compiled": False, "seconds": 0.0, "errors": []}
        broken = [d for d in imports[n] if d in failed]
        left = COMPILE_SECONDS - (time.monotonic() - start)
        if broken:
            entry["errors"] = [f"it imports {', '.join(broken)}, which did not compile"]
        elif drafts.get(rel) is False:
            entry["errors"] = ["not tried: a draft whose last compile, in the session that left it, did not succeed"]
        elif left <= 0:
            entry["errors"] = ["not tried: the time for compiling before the session was used up"]
        else:
            entry.update(session.compile_uncharged(rel, min(left, DRAFT_SECONDS if rel in drafts else session.compile_seconds())))
        if not entry["compiled"]:
            failed.add(n)
        out.append(entry)
    return out


def text(built: list[dict], drafts: dict, python: list[dict]) -> str:
    """For the prompt: what the workspace holds beyond the proofs' modules, and what of it is compiled."""
    lines = []
    if built:
        bad = [b for b in built if not b["compiled"]]
        lines.append("Every module in your workspace was compiled before this session began, in import order, at no "
                     "charge to your budgets: import them as they are (a lean_check of one with `edits: []` compiles it again)."
                     if not bad else
                     f"The modules in your workspace were compiled before this session began, in import order, at no charge to "
                     f"your budgets: {len(built) - len(bad)} of {len(built)} compiled. Not compiled: "
                     + "; ".join(f"{b['path']} ({(b['errors'] or ['no message'])[0][:160]})" for b in bad) + ".")
    if drafts:
        lines.append("Left by the earlier sessions without being accepted (drafts: nothing in one is proved until the "
                     "service accepts it, and one may not compile): " + ", ".join(sorted(drafts)) + ".")
    if python:
        lines.append("Your Python workspace also holds the earlier sessions' files: " + ", ".join("py/" + f["path"] for f in python) + ".")
    return "\n".join(lines)
