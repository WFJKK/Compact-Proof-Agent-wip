"""What an accepted submission declares, asked of Lean itself.

The lock of the seed check (core.open_lane.lock) needs three facts about a submission: which module declares
a constant, which modules a module imports, and whether a checker is the same checker in two submissions.
None of them can be read off Lean source reliably (a declaration can come from a macro, a string can look
like one, an import can span lines), so none of them is: they are read from the .olean files the acceptance
service compiled and checked, by a Lean program (inspect_oleans.lean, next to this file) run with the
service's own Lean.

`inspect_submission` finds those files from the submission's receipt: the service keeps the modules it
compiled under <work>/submissions/<receipt name>/out, next to its copy of their sources, and the protected
module under <work>/protected. The copy must be the modules that were submitted. It refuses a submission in
which Lean's answer would be ambiguous: a constant declared by two modules, or a constant named under the
marker that stands for the protected module.

`constant_digests` and `fingerprints` reduce the program's canonical texts to digests:

- `checker`: the checker constant and every constant of the candidate's it depends on (definitions with
  their values, theorems with their statements), as kernel terms, with the protected module's name left out;
- `sound_statement`: the same for the soundness theorem, which counts with its statement, so this is the
  statement and every constant of the candidate's it is written in;
- `context`: the constants of the protected module either of them reaches (the network's graph and task).

Two submissions with the same three digests have, term for term, the same checker, applied to the same graph
and task, with the same soundness statement, whatever their source text says. A constant whose body the
compiled module does not show (an axiom, or a definition of a file written in Lean's module system, which
keeps bodies out of the .olean) has no such text, and a checker that depends on one is refused.

What this does not give: the program is the pipeline's, not the acceptance service's, and it trusts the
service's work folder to hold what the service compiled. A receipt does not carry these digests.
"""

from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from pathlib import Path

SCRIPT = Path(__file__).with_name("inspect_oleans.lean")
TIMEOUT_S = 900
_lean: dict[str, str] = {}


class InspectError(RuntimeError):
    """Lean could not be asked about a submission (no Lean, no compiled modules, a program that failed):
    nothing is known about the submission, and asking again later may work."""


class Refused(InspectError):
    """Lean answered, and its answer does not single out the constants asked about (a name declared twice, a
    definition whose body the compiled module hides): the submission's own doing, in words for the agent."""


def lean_binary(lean_project: Path) -> str:
    """The Lean the acceptance service compiles with, asked of the service's own scripts/accept.py."""
    key = str(Path(lean_project).resolve())
    if key not in _lean:
        code = "import sys; sys.path.insert(0, sys.argv[1]); import accept; print(accept.lean_binary())"
        try:
            r = subprocess.run([sys.executable, "-B", "-c", code, str(Path(lean_project) / "scripts")],
                               capture_output=True, text=True, timeout=120)
        except (OSError, subprocess.TimeoutExpired) as exc:
            raise InspectError(f"the Lean project did not say where its Lean is: {exc}")
        path = r.stdout.strip().splitlines()[-1] if r.stdout.strip() else ""
        if r.returncode != 0 or not path or not Path(path).is_file():
            raise InspectError(f"the Lean project did not say where its Lean is: {(r.stderr or r.stdout)[-300:]}")
        _lean[key] = path
    return _lean[key]


def inspect_oleans(lean: str, oleans: dict[str, Path], protected: str | None = None, where=(), closure=(),
                   cwd: Path | None = None, extra=(), timeout_s: float = TIMEOUT_S) -> dict:
    """Run inspect_oleans.lean on compiled modules (module name to .olean file) and return what it prints.
    `protected` is the name of the protected module among them, left out of the canonical texts. `cwd` is
    the Lean project: a `lean` that is elan's proxy picks its toolchain from the folder it is started in.
    `extra` is further arguments for the program (core.open_lane.offered: the library and what a run shows)."""
    missing = [str(f) for f in oleans.values() if not Path(f).is_file()]
    if missing:
        raise InspectError(f"compiled modules are missing: {', '.join(missing[:3])}")
    cmd = [str(lean), "--run", str(SCRIPT)]
    for module, f in oleans.items():
        cmd += ["--olean", f"{module}={f}"]
    if protected:
        cmd += ["--protected", protected]
    for flag, names in (("--where", where), ("--closure", closure)):
        for n in names:
            cmd += [flag, n]
    cmd += list(extra)
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout_s,
                           cwd=str(cwd) if cwd is not None and Path(cwd).is_dir() else None)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise InspectError(f"Lean could not read the compiled modules: {exc}")
    if r.returncode != 0:
        raise InspectError(f"Lean could not read the compiled modules: {(r.stderr or r.stdout)[-500:]}")
    try:
        info = json.loads(r.stdout.strip().splitlines()[-1])
    except (ValueError, IndexError):
        raise InspectError(f"Lean's answer about the compiled modules is not JSON: {r.stdout[-300:]}")
    if not _well_formed(info):
        raise InspectError("Lean's answer about the compiled modules is not of the expected shape")
    return info


def _well_formed(info) -> bool:
    """Whether Lean's answer has the shape inspect_oleans.lean prints, so that what reads it need not ask."""
    def strings(x):
        return isinstance(x, list) and all(isinstance(v, str) for v in x)

    try:
        return (isinstance(info, dict)
                and all(isinstance(m, dict) and strings(m["imports"]) and isinstance(m["is_module"], bool) for m in info["modules"].values())
                and all(isinstance(d["name"], str) and strings(d["modules"]) for d in info["duplicates"])
                and strings(info["reserved"])
                and all(strings(v) for v in info["where"].values())
                and all(isinstance(c["found"], bool) and all(
                    isinstance(e["name"], str) and isinstance(e["declared"], str) and strings(e["modules"])
                    and isinstance(e["kind"], str) and isinstance(e["text"], str) for e in c["constants"])
                    for c in info["closures"].values()))
    except (KeyError, TypeError, AttributeError):
        return False


def submission_oleans(submission: Path) -> tuple[dict[str, Path], str | None]:
    """The compiled modules of an accepted submission, from its manifest and its receipt: module name to
    .olean file, the protected module included, and the protected module's name."""
    submission = Path(submission)
    try:
        manifest = json.loads((submission / "manifest.json").read_text())
        receipt = json.loads((submission / "receipt.json").read_text())
    except (OSError, ValueError) as exc:
        raise InspectError(f"its manifest or receipt cannot be read ({exc})")
    if receipt.get("status") != "accepted" or not receipt.get("receipt_path"):
        raise InspectError("it has no accepted receipt of the acceptance service")
    saved = Path(receipt["receipt_path"])
    work = saved.parent.parent
    ws = work / "submissions" / saved.stem  # the service's workspace of this submission: its copy of the modules, and out/
    oleans = {}
    for rel in manifest.get("modules") or []:
        name = rel[: -len(".lean")].replace("/", ".")
        try:
            same = (ws / rel).read_bytes() == (submission / rel).read_bytes()
        except OSError as exc:
            raise InspectError(f"the service's workspace {ws} does not hold the submitted {rel} ({exc})")
        if not same:
            raise InspectError(f"{rel} in the service's workspace {ws} is not the module that was submitted")
        oleans[name] = ws / "out" / (rel[: -len(".lean")] + ".olean")
    protected = next((s.get("module") for s in receipt.get("steps") or [] if s.get("step") == "protected"), None)
    if protected:
        short = protected[len("Protected."):]
        oleans[protected] = work / "protected" / short / "out" / "Protected" / f"{short}.olean"
    return oleans, protected


def self_check(lean_project: Path) -> None:
    """The inspection program with the service's Lean, on one module the Lean project's own build compiled
    (none if it has no build here): it must run, read the module and answer. For a run's preflight, so that
    a Lean the program does not run with, or one that cannot read what the project's Lean compiles, is found
    before the proof rounds and not after them."""
    built = sorted(Path(lean_project).glob(".lake/build/lib/**/*.olean"))[:1]
    info = inspect_oleans(lean_binary(lean_project), {"Built": built[0]} if built else {}, cwd=lean_project)
    if built and "Built" not in info["modules"]:  # a module of imports alone declares nothing: that it was read is enough
        raise InspectError(f"Lean did not read {built[0]}")


def inspect_submission(lean_project: Path, submission: Path, where=(), closure=(), timeout_s: float = TIMEOUT_S) -> dict:
    """What Lean says about an accepted submission's compiled modules: see inspect_oleans.lean. Adds
    `protected`, the protected module's name. Raises Refused when the answer would be ambiguous."""
    oleans, protected = submission_oleans(submission)
    info = inspect_oleans(lean_binary(lean_project), oleans, protected, where, closure, cwd=lean_project, timeout_s=timeout_s)
    info["protected"] = protected
    unambiguous(info)
    return info


def unambiguous(info: dict) -> None:
    """Refuse an answer in which a name does not say which constant is meant. The acceptance service refuses
    a candidate that declares a constant twice, so neither happens to a submission it accepted."""
    if info.get("duplicates"):
        d = info["duplicates"][0]
        raise Refused(f"{d['name']} is declared by more than one module ({', '.join(d['modules'])})")
    if info.get("reserved"):
        raise Refused(f"{info['reserved'][0]} is named under Protected._, which stands for the protected module")


def _digest(text: str) -> str:
    return hashlib.sha256(text.encode()).hexdigest()


def constant_digests(info: dict, root: str) -> tuple[dict[str, str], dict[str, str]]:
    """The closure of `root` in Lean's answer (asked for with `closure=[root]`), as digests of the constants'
    canonical texts by name: the candidate's own constants, and the protected module's. Raises Refused when
    the compiled modules do not show what one of the candidate's constants is."""
    c = (info.get("closures") or {}).get(root) or {}
    if not c.get("found"):
        raise Refused(f"the compiled modules declare no {root}")
    protected = info.get("protected")
    own, context = {}, {}
    for e in c["constants"]:
        home = e["modules"][0] if len(e["modules"]) == 1 else None
        if home is None:
            raise Refused(f"{e['declared']} is declared by more than one module ({', '.join(e['modules'])})")
        if protected and home == protected:
            context[e["name"]] = _digest(e["text"])
            continue
        if e["kind"] == "axiom" or (info["modules"].get(home) or {}).get("is_module"):
            raise Refused(f"the compiled module {home} does not show what {e['declared']} is (an axiom, or a file "
                               f"written in Lean's module system, which keeps the bodies of its definitions out of the "
                               f"compiled module); {root} depends on it")
        own[e["name"]] = _digest(e["text"])
    return own, context


def _together(digests: dict[str, str]) -> str:
    return _digest(json.dumps(sorted(digests.items())))


def fingerprints(info: dict, checker: str, sound: str) -> tuple[dict, dict]:
    """The digests that say which checker a submission has (module docstring), from Lean's answer for
    `closure=[checker, sound]`: the three fingerprints, and the per-constant digests they are made of
    (`checker`, `sound_statement`, `context`: name to digest), kept to say what differs when they do."""
    own, context = constant_digests(info, checker)
    stated, more = constant_digests(info, sound)
    context = {**context, **more}
    parts = {"checker": own, "sound_statement": stated, "context": context}
    return {key: _together(value) for key, value in parts.items()}, parts
