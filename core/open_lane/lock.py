"""The lock of the seed check: a scored proof's checker, taken unchanged to another network.

A scored open-lane proof has two parts. The general part is the checker `D`, its soundness theorem and
everything they use: definitions and lemmas that hold for every weight. The instance is the kernel's run of
`D` on one network's weights and the theorem that follows from it. The seed check keeps the first part and
replaces the second: the same checker, another network of the same sizes, a new instance.

The parts are told apart by module. The locked modules are the ones that declare the checker and the
soundness theorem (the manifest names both) and every submitted module they import, directly or not. A
proof can be locked when its instance theorem is declared outside them, in a module that imports them. A
constant is taken to be declared in the module it is named after: `Candidate.Check.D` in `Candidate/Check.lean`
(the longest prefix of the name that is a submitted module).

A locked module may import the protected module of the network it was written for (the checker reads that
module's `graph` and `task`). On another network the protected module has another name, so the locked text
is taken over with that one name replaced and nothing else: `renamed`. Two networks of the same sizes have
the same graph and task, so a checker and a soundness proof that never look at the weights compile as they
are. The name of a network's protected module is the Lean project's to give (scripts/make_protected.py),
and it is asked for there, never rebuilt here.
"""

from __future__ import annotations

import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

PROTECTED_IMPORT = re.compile(r"^\s*import\s+Protected\.([A-Za-z0-9_]+)\s*$", re.M)
CANDIDATE_IMPORT = re.compile(r"^\s*import\s+(Candidate(?:\.[A-Za-z0-9_]+)+)\s*$", re.M)


class LockError(ValueError):
    """Why a proof cannot be locked, in words for the agent and the log."""


def _module_name(rel: str) -> str:
    return rel[: -len(".lean")].replace("/", ".")


def declaring_module(constant: str, modules: dict[str, str]) -> str | None:
    """The submitted module a constant is named after: the longest proper prefix of its name that is the name
    of one of `modules` (module name to path). None when there is none."""
    parts = constant.split(".")
    for n in range(len(parts) - 1, 0, -1):
        name = ".".join(parts[:n])
        if name in modules:
            return name
    return None


def read_lock(submission: Path) -> dict:
    """The lock of the scored submission in folder `submission` (manifest.json and its Candidate/ modules).
    Raises LockError, with the reason, when the proof cannot be locked."""
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
    texts = {name: (submission / rel).read_text() for name, rel in names.items()}
    home = {}
    for key in ("checker", "sound", "instance"):
        constant = scored.get(key)
        home[key] = declaring_module(constant, names) if isinstance(constant, str) else None
        if home[key] is None:
            raise LockError(f"no submitted module is named like {constant} (name each constant after its module: "
                            "Candidate.Name.D in Candidate/Name.lean)")
    locked, todo = [], [home["checker"], home["sound"]]
    while todo:
        name = todo.pop()
        if name in locked:
            continue
        locked.append(name)
        todo += [m for m in CANDIDATE_IMPORT.findall(texts[name]) if m in names]
    if home["instance"] in locked:
        raise LockError(f"the instance theorem {scored['instance']} is in {names[home['instance']]}, a module the checker "
                        "and its soundness proof are in or import; the instance belongs in a module of its own that "
                        "imports them")
    protected = sorted({p for name in locked for p in PROTECTED_IMPORT.findall(texts[name])})
    if len(protected) > 1:
        raise LockError(f"its checker's modules import more than one protected module ({', '.join(protected)})")
    modules = {names[name]: texts[name] for name in sorted(locked)}
    digest = hashlib.sha256(json.dumps(modules, sort_keys=True).encode()).hexdigest()
    return {
        "checker": scored["checker"], "sound": scored["sound"], "instance": scored["instance"],
        "network": manifest.get("network"), "claimed_count": manifest.get("claimed_count"),
        "protected": protected[0] if protected else None,
        "modules": modules,
        "free": sorted(rel for name, rel in names.items() if name not in locked),
        "digest": digest,
    }


def lockable(submission: Path) -> str | None:
    """None when the scored submission can be locked, else the reason it cannot."""
    try:
        read_lock(submission)
    except LockError as exc:
        return str(exc)
    return None


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
