"""The lock of the seed check: a scored proof's checker, taken unchanged to another network.

A scored open-lane proof has two parts. The general part is the checker `D`, its soundness theorem and
everything they use: definitions and lemmas that hold for every weight. The instance is the kernel's run of
`D` on one network's weights and the theorem that follows from it. The seed check keeps the first part and
replaces the second: the same checker, another network of the same sizes, a new instance.

Which part a module belongs to is asked of Lean, never read off the source (core.open_lane.inspect): Lean
lets `Candidate.Check.D` be declared in any file, by a macro as well as by a `def`, text inside a string can
look like a declaration, and an import can span lines. From the modules the acceptance service compiled:

- the module that declares the checker, and the one that declares the soundness theorem;
- the locked modules: those two and every submitted module they import, directly or not;
- a proof can be locked when its instance theorem is declared outside the locked modules.

The lock then holds two things. The locked modules' source text, which a session under the lock cannot
change (core.open_lane.session writes it into the workspace again before every compile and submission).
And the checker's fingerprints (`inspect.fingerprints`): digests of the kernel terms of the checker and of
everything of the candidate's it depends on, of the soundness statement and what it is written in, and of
the protected graph and task they reach. The text is what keeps a session from editing the checker; the
fingerprints are what establishes, afterwards, that the checker a seed-check submission was accepted with
is the locked one (`same_checker`). A result counts only with that.

A locked module may import the protected module of the network it was written for (the checker reads that
module's `graph` and `task`). On another network the protected module has another name, so the locked text
is taken over with that one name replaced and nothing else: `renamed`. The name of a network's protected
module is the Lean project's to give (scripts/make_protected.py), and it is asked for there.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

from . import inspect


class LockError(ValueError):
    """Why a proof cannot be locked, in words for the agent and the log."""


class LockUnread(LockError):
    """The lock could not be read for a reason that is not the proof's: Lean could not be run, or the modules
    the service compiled are not where it keeps them. Nothing is known about the proof; it is no ground to
    pass a proof over, and asking again later may work."""


def _module_name(rel: str) -> str:
    return rel[: -len(".lean")].replace("/", ".")


def read_lock(submission: Path, lean_project: Path) -> dict:
    """The lock of the accepted, scored submission in folder `submission` (manifest.json, receipt.json and
    its Candidate/ modules), from what Lean says about the modules the service compiled for it. Raises
    LockError, with the reason, when the proof cannot be locked. The reason is shown to the agent."""
    submission = Path(submission)
    try:
        manifest = json.loads((submission / "manifest.json").read_text())
    except (OSError, ValueError) as exc:
        raise LockError(f"its manifest cannot be read ({exc})")
    scored = manifest.get("scored")
    if not isinstance(scored, dict):
        raise LockError("it is not a scored proof")
    names = {}
    for rel in manifest.get("modules") or []:
        f = submission / rel
        if not isinstance(rel, str) or not rel.endswith(".lean") or f.is_symlink() or not f.is_file():
            raise LockError(f"its module {rel!r} is missing")
        names[_module_name(rel)] = rel
    roots = {key: scored.get(key) for key in ("checker", "sound", "instance")}
    if not all(isinstance(v, str) for v in roots.values()):
        raise LockError("its manifest does not name a checker, a soundness theorem and an instance")
    try:
        info = inspect.inspect_submission(lean_project, submission, where=list(roots.values()),
                                          closure=[roots["checker"], roots["sound"]])
    except inspect.Refused as exc:
        raise LockError(f"what its modules declare does not single out its checker: {exc}")
    except inspect.InspectError as exc:
        raise LockUnread(f"Lean could not be asked what its modules declare: {exc}")
    home = {}
    for key, constant in roots.items():
        where = [m for m in (info["where"].get(constant) or []) if m in names]
        if len(where) != 1:
            found = "none of the submitted modules" if not where else " and ".join(names[w] for w in where)
            raise LockError(f"{constant} must be declared in exactly one submitted module; Lean finds it in {found}")
        home[key] = where[0]
    try:
        prints, constants = inspect.fingerprints(info, roots["checker"], roots["sound"])
    except inspect.Refused as exc:
        raise LockError(f"its checker cannot be told from another: {exc}")
    imports = {m: [i for i in (info["modules"].get(m) or {}).get("imports", []) if i in names] for m in names}
    locked, todo = [], [home["checker"], home["sound"]]
    while todo:
        name = todo.pop()
        if name in locked:
            continue
        locked.append(name)
        todo += imports[name]
    if home["instance"] in locked:
        raise LockError(f"the instance theorem {roots['instance']} is in {names[home['instance']]}, a module the checker "
                        "and its soundness proof are in or import; the instance belongs in a module of its own that "
                        "imports them")
    used = {m for key in ("checker", "sound") for e in info["closures"][roots[key]]["constants"] for m in e["modules"]}
    outside = sorted(m for m in used if m in names and m not in locked)
    if outside:  # cannot happen for modules that compiled: what a definition uses, its module imports
        raise LockError(f"the checker depends on {', '.join(names[m] for m in outside)}, which its module does not import")
    protected = info.get("protected")
    modules = {names[name]: (submission / names[name]).read_text() for name in sorted(locked)}
    digest = hashlib.sha256(json.dumps(modules, sort_keys=True).encode()).hexdigest()
    return {
        "checker": roots["checker"], "sound": roots["sound"], "instance": roots["instance"],
        "home": {key: names[home[key]] for key in ("checker", "sound")},
        "network": manifest.get("network"), "claimed_count": manifest.get("claimed_count"),
        "protected": protected[len("Protected."):] if protected else None,
        "modules": modules,
        "free": sorted(rel for name, rel in names.items() if name not in locked),
        "fingerprints": prints,
        "constants": constants,
        "digest": digest,
    }


_lockable: dict[tuple[str, str], str | None] = {}


def lockable(submission: Path, lean_project: Path) -> str | None:
    """None when the scored submission can be locked, else the reason it cannot. Asked of Lean once per
    submission and process: a submission's folder does not change once its receipt is written. Raises
    LockUnread when Lean could not be asked: that says nothing about the proof."""
    key = (str(Path(submission).resolve()), str(Path(lean_project).resolve()))
    if key not in _lockable:
        try:
            read_lock(submission, lean_project)
            _lockable[key] = None
        except LockUnread:
            raise
        except LockError as exc:
            _lockable[key] = str(exc)
    return _lockable[key]


def _difference(was: dict, now: dict) -> str:
    """Which constants differ between two closures (name to digest), in a few words."""
    def some(names):
        names = sorted(names)
        return ", ".join(names[:4]) + (f" and {len(names) - 4} more" if len(names) > 4 else "")

    parts = []
    changed = [n for n in was if n in now and was[n] != now[n]]
    if changed:
        parts.append(f"changed: {some(changed)}")
    if set(was) - set(now):
        parts.append(f"no longer among them: {some(set(was) - set(now))}")
    if set(now) - set(was):
        parts.append(f"new among them: {some(set(now) - set(was))}")
    return "; ".join(parts)


def same_checker(lock: dict, submission: Path, lean_project: Path, scored: bool = True) -> dict:
    """Whether an accepted submission made under the lock has the locked checker, by Lean's account of the
    modules the service compiled for it. `verified` is True only if the submission names the locked checker
    and soundness theorem, Lean finds each declared in the module it was locked in and nowhere else, and the
    three fingerprints are the lock's: the kernel terms of the checker and of what it depends on, the
    soundness statement with what it is written in, and the graph and task they reach. It is False when one
    of these fails, and `why` says which, with the constants that differ. It is None when Lean could not be
    asked: then nothing is known, and the question is to be asked again.

    With `scored` False the submission is a lemma (the scaling question): it names no checker, and the
    question is whether the constants its statement may mention are the locked ones."""
    submission = Path(submission)
    try:
        block = json.loads((submission / "manifest.json").read_text()).get("scored") or {}
    except (OSError, ValueError) as exc:
        return {"verified": False, "why": f"its manifest cannot be read ({exc})"}
    named = [f"the submission names {block.get(key)} as its {what}, not the locked {lock[key]}"
             for key, what in (("checker", "checker"), ("sound", "soundness theorem")) if block.get(key) != lock[key]]
    if scored and named:
        return {"verified": False, "why": "; ".join(named)}
    try:
        info = inspect.inspect_submission(lean_project, submission, where=[lock["checker"], lock["sound"]],
                                          closure=[lock["checker"], lock["sound"]])
        prints, constants = inspect.fingerprints(info, lock["checker"], lock["sound"])
    except inspect.Refused as exc:
        return {"verified": False, "why": f"what the submission declares does not single out its checker: {exc}"}
    except inspect.InspectError as exc:
        return {"verified": None, "why": f"Lean could not be asked what the submission declares: {exc}"}
    out = {"verified": True, "why": None, "fingerprints": prints, "constants": {key: len(value) for key, value in constants.items()}}
    problems = []
    for key in ("checker", "sound"):
        where = info["where"].get(lock[key]) or []
        expected = _module_name(lock["home"][key])
        if where != [expected]:
            problems.append(f"{lock[key]} is declared in {', '.join(where) or 'no module'}, not only in {expected}")
    for key, what in (("checker", "the checker's kernel terms differ from the locked checker's"),
                      ("sound_statement", "the soundness statement, or a constant it is written in, differs from the locked one"),
                      ("context", "the network's graph or task, as the checker uses them, differ from the first network's")):
        if prints[key] != lock["fingerprints"][key]:
            detail = _difference((lock.get("constants") or {}).get(key) or {}, constants[key])
            problems.append(what + (f" ({detail})" if detail else ""))
    if problems:
        out.update(verified=False, why="; ".join(problems))
    return out


def renamed(text: str, old: str | None, new: str) -> str:
    """A locked module's text for another network: the protected module's name replaced wherever it stands
    as a whole identifier, and nothing else."""
    if not old or old == new:
        return text
    return re.sub(rf"(?<![A-Za-z0-9_]){re.escape(old)}(?![A-Za-z0-9_])", new, text)


def protected_name(lean_project: Path, network: str, claimed: int, certificate: list | None = None) -> str:
    """The name of the protected module the Lean service builds for a network, a claimed count and a
    certificate (`N_<network>_c<claimed>`, with the certificate's hash when there is one), asked of the Lean
    project's own scripts/make_protected.py."""
    code = ("import json, sys; sys.path.insert(0, sys.argv[1]); import make_protected as m; a = json.loads(sys.argv[2]); "
            "print(m.module_name(a['network'], a['claimed'], m.canonical_cert(a['certificate'])))")
    args = json.dumps({"network": network, "claimed": int(claimed), "certificate": list(certificate or [])})
    try:
        r = subprocess.run([sys.executable, "-B", "-c", code, str(Path(lean_project) / "scripts"), args],
                           capture_output=True, text=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise LockError(f"the Lean project did not name the protected module: {exc}")
    name = r.stdout.strip()
    if r.returncode != 0 or not re.fullmatch(r"[A-Za-z][A-Za-z0-9_]*", name):
        raise LockError(f"the Lean project did not name the protected module: {(r.stderr or r.stdout)[-300:]}")
    return name
