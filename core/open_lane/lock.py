"""The lock of the seed check: a scored proof's checker, taken unchanged to another network.

A scored open-lane proof has two parts. The general part is the checker `D`, its soundness theorem and
everything they use: definitions and lemmas that hold for every weight. The instance is the kernel's run of
`D` on one network's weights and the theorem that follows from it. The seed check keeps the first part and
replaces the second: the same checker, another network of the same sizes, a new instance.

The parts are told apart by module. The locked modules are the ones that declare the checker and the
soundness theorem (the manifest names both) and every submitted module they import, directly or not. A
proof can be locked when its instance theorem is declared outside them, in a module that imports them.

Where a constant is declared is read from the modules' text, never guessed from its name: Lean lets
`Candidate.Check.D` be declared in any file. Each module is read with its comments removed, following its
`namespace` and `section` commands, and a constant's module is the one module with a declaration of that
full name (`declared_names`). A proof whose checker, soundness theorem or instance cannot be placed this way
(no such declaration in the text, or one in two modules, or a module that ends early with `#exit`) is not
locked, and the reason says so. Imports are read the same way, with any comment after them and several
modules on one line (`imports_of`).

This reading of Lean source is a careful approximation, not Lean's parser, so the lock does not rest on it
alone. The locked modules go into every submission of the session, and the service refuses a submission that
declares a constant twice; and the seed check counts a result only when the checker's description size in
its receipt equals the locked proof's (core.open_lane.stages).

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

class LockError(ValueError):
    """Why a proof cannot be locked, in words for the agent and the log."""


def _module_name(rel: str) -> str:
    return rel[: -len(".lean")].replace("/", ".")


def without_comments(text: str) -> str:
    """Lean source with its comments blanked out: `--` to the end of the line and `/- ... -/` blocks, which
    nest. String literals are kept and a comment marker inside one is not a comment. Line breaks stay."""
    out, i, n, depth, in_string = [], 0, len(text), 0, False
    while i < n:
        c, two = text[i], text[i:i + 2]
        if depth:
            if two == "/-":
                depth, i = depth + 1, i + 2
            elif two == "-/":
                depth, i = depth - 1, i + 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            out.append(c)
            if c == "\\" and i + 1 < n:
                out.append(text[i + 1])
                i += 1
            elif c == '"':
                in_string = False
            i += 1
        elif two == "/-":
            depth, i = 1, i + 2
        elif two == "--":
            while i < n and text[i] != "\n":
                i += 1
        else:
            in_string = c == '"'
            out.append(c)
            i += 1
    return "".join(out)


IMPORT = re.compile(r"^\s*(?:(?:public|private|meta|protected)\s+)*import\b(.*)$")
MODULE = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$")


def imports_of(text: str) -> list[str]:
    """The modules a Lean module imports: every module named on the import lines at its head, whatever
    comment follows them and however many stand on one line."""
    out = []
    for line in without_comments(text).splitlines():
        if not line.strip():
            continue
        m = IMPORT.match(line)
        if not m:
            break
        out += [t for t in m.group(1).split() if t != "all" and MODULE.match(t)]
    return out


DECLARATION = re.compile(
    r"^\s*(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|partial|unsafe|nonrec|public|meta|local|scoped)\s+)*)"
    r"(def|abbrev|theorem|lemma|opaque|axiom|instance|structure|inductive|class|alias)\s+([^\s:({\[⦃]+)")
SCOPE = re.compile(r"^\s*(namespace|section|end|mutual)\b\s*([A-Za-z_][A-Za-z0-9_.]*)?")


def declared_names(text: str) -> set[str]:
    """The full names of the constants a Lean module declares, as far as its text shows: the declarations
    that start a line (def, abbrev, theorem, lemma, opaque, axiom, instance, structure, inductive, class,
    alias), each under the namespaces open at that point. A private declaration has no public name and is
    left out. Raises LockError on `#exit`, after which a module's text is not what it declares."""
    plain = without_comments(text)
    if re.search(r"^\s*#exit\b", plain, re.M):
        raise LockError("a module uses #exit, so its text does not show what it declares")
    names, scopes = set(), []  # scopes: the namespace parts each open scope adds (none for a section)
    for line in plain.splitlines():
        m = SCOPE.match(line)
        if m:
            kind, name = m.group(1), m.group(2)
            if kind == "namespace" and name:
                scopes.append(name.split("."))
            elif kind in ("section", "mutual"):
                scopes.append([])
            elif kind == "end" and scopes:
                scopes.pop()
            continue
        m = DECLARATION.match(line)
        if not m or "private" in m.group(1).split():
            continue
        name = m.group(3)
        if name.startswith("_root_."):
            names.add(name[len("_root_."):])
        else:
            names.add(".".join([part for scope in scopes for part in scope] + [name]))
    return names


def declaring_modules(constant: str, declared: dict[str, set[str]]) -> list[str]:
    """The modules whose text declares the constant (`declared`: module name to its declared names)."""
    return sorted(name for name, names in declared.items() if constant in names)


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
    declared = {name: declared_names(text) for name, text in texts.items()}
    home = {}
    for key in ("checker", "sound", "instance"):
        constant = scored.get(key)
        where = declaring_modules(constant, declared) if isinstance(constant, str) else []
        if len(where) != 1:
            found = "none of the submitted modules" if not where else " and ".join(names[w] for w in where)
            raise LockError(f"{constant} must be declared in exactly one submitted module, in plain view (a def or "
                            f"theorem that starts a line, under its namespace); found in {found}")
        home[key] = where[0]
    locked, todo = [], [home["checker"], home["sound"]]
    while todo:
        name = todo.pop()
        if name in locked:
            continue
        locked.append(name)
        todo += [m for m in imports_of(texts[name]) if m in names]
    if home["instance"] in locked:
        raise LockError(f"the instance theorem {scored['instance']} is in {names[home['instance']]}, a module the checker "
                        "and its soundness proof are in or import; the instance belongs in a module of its own that "
                        "imports them")
    protected = sorted({m[len("Protected."):] for name in locked for m in imports_of(texts[name]) if m.startswith("Protected.")})
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
        "declared": sorted(set().union(*(declared[name] for name in locked))),
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
