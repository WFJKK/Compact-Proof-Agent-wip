"""What a run shows the agent of the Lean project.

The agent is not told what the model does, by any route (docs/decisions/agent-told-nothing.md). The Lean
project was written around the fixed rules lane: its docs, its README and most of its sources describe rules
that work on these networks (contraction, symmetry, interval bounds over groups of inputs) and earlier proofs.
So what the agent's tools can read and search, and what the prompt pastes, is not "the Lean project" but a
named surface, one per knowledge condition, in core/open_lane/surface/<condition>/SURFACE.yaml:

- `whole`: files of the Lean project shown as they are;
- `excerpts`: files shown as an excerpt kept in this repository, under the same path in the surface's
  folder. Every line of an excerpt is a line of the Lean project's file, in the file's order, except lines
  that say `[excerpt]`, which are the excerpt's own notes. So an excerpt can leave things out and cannot
  change the code it shows;
- `prefixes`: folders of the Lean project shown whole (the maximum-knowledge condition, where the rules are
  supplied);
- `forbidden`: regular expressions (case ignored) that nothing shown to the agent may match;
- `library`: the name of the Lean project's own library. With it, a proof that uses a constant of that
  library which the run does not show is not counted (core.open_lane.offered), and `probes` names constants
  that must come out shown and closed, as a check of that reading against the library the project built.

A run's worked examples (open_lane.example, split_example, second_example) are added: each file alone, or,
for a surface of folders, the example's folder.

`check` is the run's preflight: the excerpts are parts of the real files, and neither the prompt nor any
file of the surface matches a forbidden expression. A run does not start otherwise, so a change in the Lean
project or in a template that brings a hint back is found before an agent reads it.

What this does not close: the compiled Lean library is one package, so the fixed rules' definitions and
lemmas are in scope of every module the agent compiles, whether or not it can read their sources. Keeping
them out of scope needs the Lean project to separate its base from its rules.
"""

from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path, PurePosixPath

import yaml

SURFACES = Path(__file__).with_name("surface")
NOTE = "[excerpt]"


class SurfaceError(ValueError):
    """Why a run may not start: something shown to the agent is not what the surface allows."""


def definition(knowledge: str) -> dict:
    """The surface of a knowledge condition, as its SURFACE.yaml states it."""
    path = SURFACES / knowledge / "SURFACE.yaml"
    if not path.is_file():
        raise SurfaceError(f"no surface is defined for the {knowledge}-knowledge condition ({path})")
    d = yaml.safe_load(path.read_text()) or {}
    probes = d.get("probes") or {}
    out = {"knowledge": knowledge, "whole": list(d.get("whole") or []), "excerpts": list(d.get("excerpts") or []),
           "prefixes": list(d.get("prefixes") or []), "forbidden": list(d.get("forbidden") or []),
           "library": d.get("library") or None,
           "probes": {"shown": list(probes.get("shown") or []), "closed": list(probes.get("closed") or [])}}
    if out["library"] is not None and not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", str(out["library"])):
        raise SurfaceError(f"{path}: library {out['library']!r} is not the name of a Lean library")
    for rel in out["whole"] + out["excerpts"] + out["prefixes"]:
        if not isinstance(rel, str) or rel.startswith("/") or ".." in rel:
            raise SurfaceError(f"{path}: {rel!r} is not a path inside the Lean project")
    for rel in out["excerpts"]:
        if not (SURFACES / knowledge / rel).is_file():
            raise SurfaceError(f"{path} lists the excerpt {rel}, but {SURFACES / knowledge / rel} is missing")
    for rx in out["forbidden"]:
        try:
            re.compile(rx, re.I)
        except re.error as exc:
            raise SurfaceError(f"{path}: {rx!r} is not a regular expression ({exc})")
    return out


def examples(ol: dict) -> list[str]:
    """The run's worked examples, as files of the Lean project under examples/."""
    out = []
    for key in ("example", "split_example", "second_example"):
        rel = ol.get(key)
        if isinstance(rel, str) and rel.startswith("examples/") and ".." not in rel and rel not in out:
            out.append(rel)
    return out


def example_folders(ol: dict) -> list[str]:
    """The folders of the run's worked examples (a candidate folder: the parent of Candidate/), as prefixes."""
    out = []
    for rel in examples(ol):
        p = PurePosixPath(rel)
        folder = p.parent.parent if p.parent.name == "Candidate" else p.parent
        prefix = str(folder) + "/"
        if prefix.startswith("examples/") and prefix not in out:
            out.append(prefix)
    return out


def of_run(cfg: dict) -> dict:
    """The surface of a run: its knowledge condition's, with the run's worked examples. `files` maps each
    path the agent may name to the file it is served from (the Lean project's, or an excerpt's). A surface
    of single files gets each example's file; a surface of folders gets each example's folder."""
    ol = cfg["open_lane"]
    d = definition(ol.get("knowledge", "minimal"))
    project = Path(ol["lean_project"]).expanduser().resolve()
    prefixes = list(d["prefixes"])
    if prefixes:
        prefixes += [f for f in example_folders(ol) if not f.startswith(tuple(prefixes))]
    files = {rel: str(project / rel) for rel in d["whole"] + ([] if prefixes else examples(ol))}
    files.update({rel: str(SURFACES / d["knowledge"] / rel) for rel in d["excerpts"]})
    return {"knowledge": d["knowledge"], "files": dict(sorted(files.items())), "excerpts": d["excerpts"],
            "prefixes": prefixes, "forbidden": d["forbidden"], "library": d["library"], "probes": d["probes"]}


def legacy(readable: list[str], knowledge: str = "minimal") -> dict:
    """The surface of a session made before surfaces existed: the folders it listed as readable."""
    return {"knowledge": knowledge, "files": {}, "excerpts": [], "prefixes": list(readable), "forbidden": [],
            "library": None, "probes": {"shown": [], "closed": []}}


def served(surface: dict, lean_project: Path, path: str) -> Path | None:
    """The file a path of the surface is read from, or None if the surface does not show it."""
    if not isinstance(path, str) or ".." in path or path.startswith("/"):
        return None
    if path in surface["files"]:
        return Path(surface["files"][path])
    if any(path.startswith(prefix) for prefix in surface.get("prefixes") or []):
        return Path(lean_project) / path
    return None


def listing(surface: dict, lean_project: Path) -> list[tuple[str, Path]]:
    """Every file of the surface that exists, as (the path the agent names, the file): what search covers."""
    out = {rel: Path(p) for rel, p in surface["files"].items()}
    for prefix in surface.get("prefixes") or []:
        root = Path(lean_project) / prefix
        found = [root] if root.is_file() else sorted(p for p in root.rglob("*") if p.suffix in (".lean", ".md", ".txt")) if root.is_dir() else []
        for p in found:
            out.setdefault(str(p.relative_to(lean_project)), p)
    return [(rel, p) for rel, p in sorted(out.items()) if p.is_file() and not p.is_symlink()]


def names(surface: dict) -> list[str]:
    """The surface as the agent is told it: its files, an excerpt marked as one, and its folders."""
    marked = [rel + (" (an excerpt)" if rel in surface["excerpts"] else "") for rel in surface["files"]]
    return marked + [prefix + ("..." if prefix.endswith("/") else "") for prefix in surface.get("prefixes") or []]


def describe(surface: dict) -> str:
    """For the prompt: what read_file and search_library reach of the Lean project in this run, and, for a
    surface with a library, that the rest of the library is not part of the run."""
    text = "Of the Lean project, read_file and search_library reach these files and no others:\n" + "\n".join(
        f"  {name}" for name in names(surface))
    if surface["excerpts"]:
        text += ("\nAn excerpt holds the lines of a file that this run offers, with line numbers of its own. Docs and "
                 "other files that these files mention are not part of this run.")
    if surface.get("library"):
        text += (f"\nThe compiled library {surface['library']} holds more than these files show, since it serves other "
                 "experiments as well. What it holds beyond them is not part of this run. Do not go looking for it (#print or "
                 "#check of names you were not shown, or listing its constants), and if a search tactic such as exact? offers "
                 "you one of its constants that is not shown here, leave it. A proof in which a definition, a statement or a "
                 "proof of yours mentions such a constant is not counted: lean_check and submit_candidate say so in their "
                 "answer (`offered`), with the constants. Lean's own library and Mathlib are yours to use.")
    return text


def digest(surface: dict, lean_project: Path) -> str:
    """A digest of what a run shows the agent: the surface's definition and every file of it as it is served.
    A run records it when it starts and keeps it: what was shown is one thing for the whole run."""
    h = hashlib.sha256()
    h.update(json.dumps({key: surface.get(key) for key in ("knowledge", "excerpts", "prefixes", "forbidden", "library", "probes")},
                        sort_keys=True).encode())
    for rel, p in listing(surface, lean_project):
        h.update(rel.encode() + b"\0" + p.read_bytes() + b"\0")
    return h.hexdigest()[:16]


# checks ----------------------------------------------------------------------------------------
def aligned(excerpt: str, real: str) -> list[int] | str:
    """The lines of the real file that the excerpt shows, by number from 1: every line of the excerpt, its
    own notes and blank lines apart, must be a line of the real file, in order (each is matched to the first
    such line after the one before). Or, as a string, the first line of the excerpt that is not."""
    lines = [ln.rstrip() for ln in real.splitlines()]
    at, out = 0, []
    for n, ln in enumerate(excerpt.splitlines(), 1):
        ln = ln.rstrip()
        if not ln.strip() or NOTE in ln:
            continue
        try:
            at = lines.index(ln, at) + 1
        except ValueError:
            return f"line {n} is not a line of the file at that place: {ln.strip()[:120]!r}"
        out.append(at)
    return out


def excerpt_problem(excerpt: str, real: str) -> str | None:
    """None if every line of the excerpt, its own notes apart, is a line of the real file, in order; else the
    first line that is not."""
    found = aligned(excerpt, real)
    return found if isinstance(found, str) else None


def shown_lines(surface: dict, lean_project: Path) -> dict[str, list[int] | None]:
    """Per module of the surface's library that the surface shows: None for a module shown whole, else the
    lines of its source that the excerpt shows. Raises SurfaceError for an excerpt that is not a part of
    its file."""
    library, out = surface.get("library"), {}
    if not library:
        return out
    for rel, served_from in surface["files"].items():
        if not rel.endswith(".lean") or rel.split("/")[0] != library:
            continue
        module = rel[: -len(".lean")].replace("/", ".")
        if rel not in surface["excerpts"]:
            out[module] = None
            continue
        real = Path(lean_project) / rel
        found = aligned(Path(served_from).read_text(), real.read_text()) if real.is_file() else f"the Lean project has no {rel}"
        if isinstance(found, str):
            raise SurfaceError(f"the excerpt of {rel} is not a part of the Lean project's file: {found}")
        out[module] = found
    return out


def library_modules(lean_project: Path, library: str) -> dict[str, Path]:
    """The modules of the Lean project's library as its build compiled them: module name to .olean file."""
    for root in (Path(lean_project) / ".lake" / "build" / "lib" / "lean", Path(lean_project) / ".lake" / "build" / "lib"):
        found = sorted((root / library).rglob("*.olean")) if (root / library).is_dir() else []
        if (root / f"{library}.olean").is_file():
            found.append(root / f"{library}.olean")
        if found:
            return {".".join(f.relative_to(root).with_suffix("").parts): f for f in found}
    return {}


def matches(text: str, forbidden: list[str]) -> list[tuple[int, str, str]]:
    """Where a text matches a forbidden expression: (line number, the expression, the line)."""
    out = []
    compiled = [(rx, re.compile(rx, re.I)) for rx in forbidden]
    for n, ln in enumerate(text.splitlines(), 1):
        for rx, c in compiled:
            if c.search(ln):
                out.append((n, rx, ln.strip()[:160]))
                break
    return out


def check(surface: dict, lean_project: Path, shown: dict[str, str], extra_forbidden: list[str] | None = None) -> None:
    """The preflight of a run's surface. `shown` is every text the run sends the agent itself (the prompt's
    parts, by name); the files of the surface are read here. Raises SurfaceError with what is wrong."""
    lean_project = Path(lean_project)
    problems = []
    for rel in surface["excerpts"]:
        real = lean_project / rel
        if not real.is_file():
            problems.append(f"{rel}: the Lean project has no such file to take an excerpt of")
            continue
        why = excerpt_problem(Path(surface["files"][rel]).read_text(), real.read_text())
        if why:
            problems.append(f"the excerpt of {rel} is not a part of the Lean project's file: {why}")
    missing = [rel for rel, p in surface["files"].items() if not Path(p).is_file()]
    problems += [f"{rel}: no such file ({surface['files'][rel]})" for rel in missing]
    forbidden = list(surface["forbidden"]) + [re.escape(t) for t in extra_forbidden or [] if t]
    if forbidden:
        texts = dict(shown)
        for rel, p in listing(surface, lean_project):
            try:
                texts[rel] = p.read_text()
            except (OSError, UnicodeDecodeError) as exc:
                problems.append(f"{rel} cannot be read ({exc})")
        for name, text in texts.items():
            for n, rx, ln in matches(text, forbidden)[:5]:
                problems.append(f"{name}, line {n}, matches the forbidden {rx!r}: {ln}")
    if problems:
        more = f" (and {len(problems) - 12} more)" if len(problems) > 12 else ""
        raise SurfaceError(f"what this run would show the agent is not what the {surface['knowledge']}-knowledge condition "
                           "allows:\n  " + "\n  ".join(problems[:12]) + more)
