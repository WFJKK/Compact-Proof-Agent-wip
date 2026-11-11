"""Whether a proof uses only what its run offers of the Lean project's library.

A run shows the agent a surface of the Lean project (core.open_lane.surface). Its library is compiled as one
package, though, and every module the agent compiles has all of it in scope: the fixed rules' operations,
their definitions and their soundness lemmas, whether or not the agent can read their sources. Until the Lean
project separates a base from its rules, the pipeline holds the line itself: in a run whose surface names a
library, a proof is counted only if none of its own constants mentions a constant of that library which the
surface does not show.

Lean is asked, as for the lock (core.open_lane.inspect, inspect_oleans.lean): the library's compiled modules
say which module declares a constant and on which line, the surface says which lines the run shows, and the
modules the acceptance service compiled for a submission say what its constants mention, in their types,
their values and their proofs. A library constant is

- shown, when its module is shown whole or the line that declares it is a line of the module's excerpt. A
  constant Lean made itself (a recursor, a matcher, an equation) goes with the declaration its name extends,
  in whichever module Lean keeps it: an equation of `f` that Lean makes on demand is kept by the first
  module that asked for it. The Lean project's soundness file keeps equations of the rules' definitions,
  and the rules' files keep equations of the base's;
- exposed, when it is not shown but the type or the value of a shown constant mentions it: unfolding a shown
  definition puts such a constant into a term without anyone having looked for it;
- closed otherwise. A constant of the submission that mentions a closed constant is a use of what the run
  does not offer.

This is a rule of the run, not of the acceptance service: the proof stays accepted and its receipt stays as
the service wrote it. The verdict is kept next to it (`offered.json`), and the records leave a proof that is
not clean without a length. What it does not do: it does not keep the agent from looking at the library
through Lean (`#print`), only from building on what it finds there.
"""

from __future__ import annotations

import json
from pathlib import Path

from . import inspect, surface as surfaces
from .inspect import InspectError  # what this module raises when Lean could not be asked

FILE = "offered.json"
MAX_SHOWN = 12  # constants named to the agent and in a record; the file holds all of them


def applies(surface: dict | None) -> bool:
    """Whether the run holds proofs to its surface: a surface that names the Lean project's library."""
    return bool(surface and surface.get("library"))


def library_args(surface: dict, lean_project: Path) -> list[str]:
    """The inspection program's arguments for a surface: the library's compiled modules, and what the surface
    shows of each. Raises InspectError without a built library, SurfaceError for an excerpt that is not a part
    of its file."""
    modules = surfaces.library_modules(lean_project, surface["library"])
    if not modules:
        raise inspect.InspectError(f"the Lean project at {lean_project} has no compiled {surface['library']} library "
                                   "(.lake/build/lib): build it first")
    args = []
    for module, f in modules.items():
        args += ["--library", f"{module}={f}"]
    shown = surfaces.shown_lines(surface, lean_project)
    unbuilt = sorted(m for m in shown if m not in modules)
    if unbuilt:
        raise inspect.InspectError(f"the surface shows {', '.join(unbuilt)}, which the Lean project at {lean_project} has not compiled")
    for module, lines in shown.items():
        args += ["--shown-whole", module] if lines is None else ["--shown-lines", f"{module}={','.join(map(str, lines))}"]
    return args


def _answer(info: dict) -> dict:
    s = info.get("surface")
    ok = (isinstance(s, dict) and isinstance(s.get("classes"), dict) and isinstance(s.get("library"), dict)
          and isinstance(s.get("uses"), list)
          and all(isinstance(u, dict) and isinstance(u.get("constant"), str) and isinstance(u.get("module"), str)
                  and isinstance(u.get("closed"), list) and all(isinstance(c, str) for c in u["closed"]) for u in s["uses"]))
    if not ok:
        raise inspect.InspectError("Lean's answer about the library is not of the expected shape")
    return s


def classify(surface: dict, lean_project: Path, names: list[str]) -> dict:
    """Per name: shown, exposed, closed, or absent (no constant of the library). With `library`, the counts."""
    extra = library_args(surface, lean_project)
    for n in names:
        extra += ["--classify", n]
    info = inspect.inspect_oleans(inspect.lean_binary(lean_project), {}, cwd=lean_project, extra=extra)
    s = _answer(info)
    return {"classes": s["classes"], "library": s["library"]}


def self_check(surface: dict, lean_project: Path) -> dict:
    """A run's preflight: Lean reads the library the project built, and the surface's probes come out as the
    surface says, shown or closed. Raises InspectError (Lean could not be asked) or SurfaceError (it answered,
    and the excerpts, the source and the build do not fit together)."""
    probes = surface.get("probes") or {}
    want = {n: "shown" for n in probes.get("shown") or []} | {n: "closed" for n in probes.get("closed") or []}
    got = classify(surface, lean_project, list(want))
    off = [f"{n} is {got['classes'].get(n, 'absent')}, not {w}" for n, w in want.items() if got["classes"].get(n) != w]
    if off:
        raise surfaces.SurfaceError(
            f"the {surface['knowledge']}-knowledge surface and Lean's reading of the library the Lean project at {lean_project} "
            "built do not fit together (an excerpt, the source or the build is not the one the others were made for, or "
            "the reading is at fault): " + "; ".join(off[:8]) + (f" (and {len(off) - 8} more)" if len(off) > 8 else ""))
    return got["library"]


def of_oleans(surface: dict, lean_project: Path, oleans: dict, protected: str | None = None,
              timeout_s: float = inspect.TIMEOUT_S) -> dict:
    """What compiled modules (module name to .olean file; the protected module among them is left out) use of
    the library beyond the surface: {"clean": bool, "uses": [{constant, module, kind, closed: [...]}],
    "library": counts}. Raises InspectError when Lean could not be asked: then nothing is known."""
    info = inspect.inspect_oleans(inspect.lean_binary(lean_project), oleans, protected, cwd=lean_project,
                                  extra=library_args(surface, lean_project), timeout_s=timeout_s)
    s = _answer(info)
    return {"clean": not s["uses"], "uses": s["uses"], "library": s["library"]}


def of_submission(surface: dict, lean_project: Path, submission: Path) -> dict:
    """The same of an accepted submission, from the modules the acceptance service compiled for it."""
    oleans, protected = inspect.submission_oleans(Path(submission))
    return of_oleans(surface, lean_project, oleans, protected)


def note(verdict: dict) -> str:
    """The verdict in words, for the agent and the record: which of its constants mention what, so that it
    can write them another way. (A constant it did not write by name can come from a tactic that searched
    the library for it.)"""
    if verdict.get("clean"):
        return "This submission uses nothing of the Lean project's library beyond the files this run offers."
    uses = verdict.get("uses") or []
    parts = [f"{u['constant']} mentions {', '.join(u['closed'][:3])}" + (" and more" if len(u["closed"]) > 3 else "")
             for u in uses[:MAX_SHOWN]]
    more = f"; and {len(uses) - MAX_SHOWN} more of your constants" if len(uses) > MAX_SHOWN else ""
    apart = any(takes_apart(c) for u in uses for c in u["closed"])
    return ("not counted in this run: it uses what the files this run offers do not show of the Lean project's library ("
            + "; ".join(parts) + more + ")" + (APART_HINT if apart else ""))


# What takes a structure apart (inspect_oleans.lean, apartOfStructure and apartOfConstructor): a structure with
# a field the run does not show may not be taken apart either, since that binds every field.
APART = ("rec", "casesOn", "recOn", "brecOn", "below", "binductionOn", "noConfusion", "noConfusionType")
APART_OF_CONSTRUCTOR = ("inj", "injEq", "noConfusion")
APART_HINT = (". Taking apart a structure with fields this run does not show (a pattern match or `cases` on it) uses "
              "them all: use its projections instead")


def takes_apart(name: str) -> bool:
    parts = name.split(".")
    return parts[-1] in APART or (len(parts) >= 3 and parts[-1] in APART_OF_CONSTRUCTOR and parts[-2] == "mk")


def summary(verdict: dict) -> dict:
    """The verdict as a record keeps it: whether the proof is clean, and the first uses."""
    uses = verdict.get("uses") or []
    return {"clean": bool(verdict.get("clean")), "uses": uses[:MAX_SHOWN], "count": len(uses)}


def read(submission: Path) -> dict | None:
    """The verdict kept with a submission, or None if it was not asked for yet."""
    f = Path(submission) / FILE
    try:
        return json.loads(f.read_text()) if f.is_file() else None
    except ValueError:
        return None


def ask(surface: dict, lean_project: Path, submission: Path) -> dict:
    """The verdict of a submission, asked of Lean once and kept in its folder. Raises InspectError when Lean
    could not be asked; nothing is written then."""
    kept = read(submission)
    if kept is not None and isinstance(kept.get("clean"), bool):
        return kept
    verdict = of_submission(surface, lean_project, submission)
    tmp = Path(submission) / (FILE + ".tmp")
    tmp.write_text(json.dumps(verdict, indent=1))
    tmp.replace(Path(submission) / FILE)
    return verdict
