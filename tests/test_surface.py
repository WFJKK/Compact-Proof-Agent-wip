"""What a run shows the agent of the Lean project, and what a proof may use of it.

The agent is told nothing about what works on a network (docs/decisions/agent-told-nothing.md). Three things
keep that, and each is tested here:

- the surface (core/open_lane/surface.py): the files the agent's tools reach and the prompt pastes are a named
  list per knowledge condition, some of them as excerpts, which are parts of the Lean project's files;
- the check before a run starts: an excerpt that is not a part of its file, or anything shown that matches an
  expression the surface forbids, and the run does not start;
- the rule on proofs (core/open_lane/offered.py): the compiled library holds everything, shown or not, so Lean
  is asked what a submission's constants mention, and a proof that mentions what the run does not show is
  recorded without a length.

The first tests need nothing but this repository. The tests of the minimal-knowledge surface as it is need
the Lean project's sources (at COMPACT_PROOF_LEAN, else next to this repository, else at the pilots' path);
the tests of the rule on proofs need its Lean, and compile a small library of their own; the last ones need
the library the Lean project built. Each is skipped without what it needs.
"""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path

import pytest
import yaml

from core import loop
from core.open_lane import inspect, offered, surface
from core.open_lane.session import Session, ToolError
from core.run_config import merge, read_run_config_file
from core.util import REPO_ROOT

import test_lock_lean as lean_tests
import test_stages as stand_ins


def _project() -> Path | None:
    if os.environ.get("COMPACT_PROOF_LEAN"):
        places = [Path(os.environ["COMPACT_PROOF_LEAN"]).expanduser()]
    else:
        places = [REPO_ROOT.parent / "Compact-Proof-Checker", REPO_ROOT.parent / "auto-research-compact-proof-in-lean",
                  Path("~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck").expanduser()]
    return next((p for p in places if (p / "scripts" / "accept.py").is_file()), None)


PROJECT = _project()
LEAN = lean_tests.LEAN
BUILT = surface.library_modules(PROJECT, "CompactCheck") if PROJECT else {}
needs_project = pytest.mark.skipif(PROJECT is None, reason="needs the Lean project's sources (COMPACT_PROOF_LEAN or its usual places)")
needs_lean = pytest.mark.skipif(LEAN is None, reason="needs the Lean project's Lean")
needs_library = pytest.mark.skipif(LEAN is None or "CompactCheck.CountedOps" not in BUILT, reason="needs the library the Lean project built")
# everything the surface shows is compiled only where the whole project is built (some of it needs Mathlib)
WHOLE_BUILD = {"CompactCheck.Spec", "CompactCheck.Soundness"} <= set(BUILT)
needs_whole = pytest.mark.skipif(LEAN is None or not WHOLE_BUILD, reason="needs the whole library the Lean project built (some of it needs Mathlib)")


# ---- an excerpt, a definition, the check -------------------------------------------------------------
REAL = """import Base

namespace Lib

/-- The first rule. -/
def one : Nat := 1

/-- The second rule, which a run may not show. -/
def two : Nat := 2

theorem one_pos : 0 < one := by decide

end Lib
"""


def test_an_excerpt_is_lines_of_the_file_in_the_files_order():
    """An excerpt may leave lines out and may add notes of its own, marked. Every other line must be a line of
    the file, in the file's order: an excerpt cannot change the code it shows, or show it rearranged."""
    excerpt = "-- [excerpt] Lib as this run offers it.\nnamespace Lib\n\n/-- The first rule. -/\ndef one : Nat := 1\n-- [excerpt] (more)\n\nend Lib\n"
    assert surface.aligned(excerpt, REAL) == [3, 5, 6, 13] and surface.excerpt_problem(excerpt, REAL) is None
    changed = excerpt.replace("def one : Nat := 1", "def one : Nat := 2")
    assert "line 5 is not a line of the file" in surface.excerpt_problem(changed, REAL)
    reordered = "theorem one_pos : 0 < one := by decide\ndef one : Nat := 1\n"
    assert "line 2 is not a line of the file at that place" in surface.excerpt_problem(reordered, REAL)
    assert surface.excerpt_problem("def one : Nat := 1   \n", REAL) is None  # trailing blanks are not content
    assert surface.aligned("", REAL) == []


def stand_in(tmp_path: Path, monkeypatch, definition: dict, excerpts: dict | None = None, files: dict | None = None) -> Path:
    """A stand-in Lean project with `files`, and the minimal-knowledge surface defined as `definition` with
    these excerpts. Returns the project."""
    d = tmp_path / "surfaces"
    (d / "minimal").mkdir(parents=True, exist_ok=True)
    (d / "minimal" / "SURFACE.yaml").write_text(yaml.safe_dump(definition))
    for rel, text in (excerpts or {}).items():
        (d / "minimal" / rel).parent.mkdir(parents=True, exist_ok=True)
        (d / "minimal" / rel).write_text(text)
    monkeypatch.setattr(surface, "SURFACES", d)
    project = tmp_path / "lean"
    for rel, text in {"scripts/accept.py": "", **(files or {})}.items():
        (project / rel).parent.mkdir(parents=True, exist_ok=True)
        (project / rel).write_text(text)
    return project


def run_of(project: Path, **open_lane) -> dict:
    return {"open_lane": {"knowledge": "minimal", "lean_project": str(project), "example": None, "split_example": None,
                          "second_example": None, **open_lane}}


def test_a_surface_is_its_whole_files_its_excerpts_and_the_runs_examples(tmp_path, monkeypatch):
    project = stand_in(tmp_path, monkeypatch, {"whole": ["Lib/Spec.lean"], "excerpts": ["Lib/Rules.lean"], "forbidden": ["second rule"]},
                       excerpts={"Lib/Rules.lean": "-- [excerpt] the first rule\ndef one : Nat := 1\n"},
                       files={"Lib/Spec.lean": "-- the specification\n", "Lib/Rules.lean": REAL, "Lib/Other.lean": "-- not shown\n",
                              "examples/a/Candidate/A.lean": "-- an example\n", "examples/a/Candidate/Helper.lean": "-- its neighbour\n"})
    s = surface.of_run(run_of(project, example="examples/a/Candidate/A.lean"))
    assert list(s["files"]) == ["Lib/Rules.lean", "Lib/Spec.lean", "examples/a/Candidate/A.lean"] and s["prefixes"] == []
    assert surface.served(s, project, "Lib/Spec.lean") == project.resolve() / "Lib" / "Spec.lean"
    assert surface.served(s, project, "Lib/Rules.lean") == tmp_path / "surfaces" / "minimal" / "Lib" / "Rules.lean"  # the excerpt, not the file
    for hidden in ("Lib/Other.lean", "examples/a/Candidate/Helper.lean", "../surfaces/minimal/SURFACE.yaml", "/etc/passwd", "Lib/", ""):
        assert surface.served(s, project, hidden) is None, hidden
    assert [rel for rel, _ in surface.listing(s, project)] == list(s["files"])
    surface.check(s, project, {"the prompt": "The first rule is shown."})
    assert "Lib/Rules.lean (an excerpt)" in surface.describe(s) and "Lib/Other.lean" not in surface.describe(s)


def test_a_run_does_not_start_when_what_it_shows_is_not_what_the_surface_allows(tmp_path, monkeypatch):
    """The check before a run: an excerpt that is not a part of its file; a file of the surface, or a text
    the run sends, that matches a forbidden expression (case ignored; the model folder's own terms are added);
    a file that is not there. Each is refused with the place it was found."""
    definition = {"whole": ["Lib/Spec.lean"], "excerpts": ["Lib/Rules.lean"], "forbidden": [r"second rule", r"\bpilot"]}
    files = {"Lib/Spec.lean": "-- the specification\n", "Lib/Rules.lean": REAL}
    good = {"Lib/Rules.lean": "def one : Nat := 1\n"}
    project = stand_in(tmp_path, monkeypatch, definition, good, files)
    s = surface.of_run(run_of(project))
    surface.check(s, project, {"the prompt": "nothing to see"})
    with pytest.raises(surface.SurfaceError, match="the prompt, line 2, matches the forbidden .*: In the Pilot, columns worked"):
        surface.check(s, project, {"the prompt": "A proof.\nIn the Pilot, columns worked.\n"})
    with pytest.raises(surface.SurfaceError, match="the prompt, line 1, matches the forbidden 'Gross'"):
        surface.check(s, project, {"the prompt": "as Gross et al. do"}, extra_forbidden=["Gross"])
    (project / "Lib" / "Spec.lean").write_text("-- the specification\n-- (the second rule covers the rest)\n")
    with pytest.raises(surface.SurfaceError, match=r"Lib/Spec.lean, line 2, matches the forbidden 'second rule'"):
        surface.check(s, project, {})
    (project / "Lib" / "Spec.lean").write_text("-- the specification\n")
    (tmp_path / "surfaces" / "minimal" / "Lib" / "Rules.lean").write_text("def one : Nat := 1\ndef two : Nat := 3\n")
    with pytest.raises(surface.SurfaceError, match="the excerpt of Lib/Rules.lean is not a part of the Lean project's file: line 2"):
        surface.check(s, project, {})
    (tmp_path / "surfaces" / "minimal" / "Lib" / "Rules.lean").write_text("def two : Nat := 2\n/-- The second rule, which a run may not show. -/\n")
    with pytest.raises(surface.SurfaceError, match="not a part of the Lean project's file"):  # the lines are the file's, the order is not
        surface.check(s, project, {})
    (tmp_path / "surfaces" / "minimal" / "Lib" / "Rules.lean").write_text("/-- The second rule, which a run may not show. -/\ndef two : Nat := 2\n")
    with pytest.raises(surface.SurfaceError, match=r"Lib/Rules.lean, line 1, matches the forbidden 'second rule'"):  # an excerpt is scanned as it is served
        surface.check(s, project, {})
    (tmp_path / "surfaces" / "minimal" / "Lib" / "Rules.lean").write_text(good["Lib/Rules.lean"])
    (project / "Lib" / "Spec.lean").unlink()
    with pytest.raises(surface.SurfaceError, match="Lib/Spec.lean: no such file"):
        surface.check(s, project, {})


def test_a_surfaces_definition_is_checked_when_it_is_read(tmp_path, monkeypatch):
    project = stand_in(tmp_path, monkeypatch, {"whole": ["../outside.lean"]})
    with pytest.raises(surface.SurfaceError, match="is not a path inside the Lean project"):
        surface.of_run(run_of(project))
    stand_in(tmp_path, monkeypatch, {"excerpts": ["Lib/Rules.lean"]})
    with pytest.raises(surface.SurfaceError, match="lists the excerpt Lib/Rules.lean, but .* is missing"):
        surface.of_run(run_of(project))
    stand_in(tmp_path, monkeypatch, {"forbidden": ["(unclosed"]})
    with pytest.raises(surface.SurfaceError, match="is not a regular expression"):
        surface.of_run(run_of(project))
    stand_in(tmp_path, monkeypatch, {"library": "Not A Name"})
    with pytest.raises(surface.SurfaceError, match="is not the name of a Lean library"):
        surface.of_run(run_of(project))
    with pytest.raises(surface.SurfaceError, match="no surface is defined for the everything-knowledge condition"):
        surface.of_run(run_of(project, knowledge="everything"))


def test_both_knowledge_conditions_have_a_surface_and_only_the_minimal_one_holds_proofs_to_it():
    minimal, maximum = surface.definition("minimal"), surface.definition("maximum")
    assert minimal["library"] == "CompactCheck" and minimal["prefixes"] == [] and len(minimal["forbidden"]) > 20
    assert not any(rel.startswith("docs/") or rel == "README.md" for rel in minimal["whole"] + minimal["excerpts"])
    assert minimal["probes"]["closed"] and minimal["probes"]["shown"]
    assert maximum["library"] is None and "docs/" in maximum["prefixes"] and "CompactCheck/" in maximum["prefixes"]
    assert "README.md" not in maximum["prefixes"]  # it names the paper this work follows, which no prompt may
    assert offered.applies(minimal) and not offered.applies(maximum) and not offered.applies(None)


def session_on(tmp_path: Path, project: Path, **open_lane) -> Session:
    cfg = merge({"run_id": "surface-test", "model": "tests/max2_tiny", "backend": "fake", "rule_set": ["single", "skip"],
                 "prompt_template": "open_lane_v1", "baselines": False, "runs_dir": str(tmp_path / "runs"), "sandbox": "auto",
                 "open_lane": {"enabled": True, "lean_project": str(project), "work_dir": str(tmp_path / "work"), **open_lane}})
    return Session.create(tmp_path / "attempt" / "open_lane", cfg, "tests/max2_tiny",
                          [{"id": "max2_tiny-v8-s0", "setting": "v8", "n_inputs": 64}], tmp_path / "run")


def test_a_session_made_before_runs_had_a_surface_reads_what_it_read(tmp_path, monkeypatch):
    """session.json of an older run lists folders (`readable`) and has no surface: it keeps what it had."""
    files = {"docs/COUNTED.md": "# The counted language\n", "CompactCheck/Spec.lean": "-- spec\n",
             "examples/open_lane/max2_tiny_scored/Candidate/Max2TinyScored.lean": "-- example\n", "scripts/secret.py": "no\n"}
    project = stand_in(tmp_path, monkeypatch, {"whole": ["CompactCheck/Spec.lean"]}, files=files)
    session = session_on(tmp_path, project)
    assert session.surface()["files"] and "docs/COUNTED.md" not in session.surface()["files"]
    with pytest.raises(ToolError, match="one of the files of the Lean project that this run offers: CompactCheck/Spec.lean"):
        session.read_file("docs/COUNTED.md")
    state = json.loads(session.state_path.read_text())
    del state["surface"]
    state["readable"] = ["CompactCheck/", "docs/"]
    session.state_path.write_text(json.dumps(state))
    old = Session(session.path)
    assert old.read_file("docs/COUNTED.md")["text"] == "1: # The counted language"
    assert old.search_library("counted")["text"] == "docs/COUNTED.md:1: # The counted language"
    with pytest.raises(ToolError):
        old.read_file("scripts/secret.py")


# ---- the minimal-knowledge surface as it is, on the Lean project's sources ---------------------------
def pilot_config(project: Path, tmp_path: Path) -> dict:
    raw = read_run_config_file(REPO_ROOT / "config" / "pilot" / "linear-max2.yaml")
    raw["open_lane"] = {**raw["open_lane"], "lean_project": str(project), "work_dir": str(tmp_path / "work")}
    return merge({**raw, "runs_dir": str(tmp_path / "runs")})


# what the minimal-knowledge agent must not be able to read: docs, the README, the fixed rules' sources, earlier proofs
OUT_OF_REACH = ("docs/COUNTED.md", "docs/OPEN_LANE.md", "docs/RULES.md", "README.md", "CompactCheck/Symmetry.lean",
                "CompactCheck/SymmetrySound.lean", "CompactCheck/Contract.lean", "CompactCheck/ContractSound.lean",
                "CompactCheck/Interval.lean", "CompactCheck/IntervalSound.lean", "CompactCheck/Approx.lean",
                "CompactCheck/TokensCost.lean", "CompactCheck/General.lean", "accept/allowlist-maximum.txt",
                "examples/open_lane/max2_tiny_cols23_v3/Candidate/Cols23.lean", "examples/open_lane/max2_tiny_decision_tree/manifest.json",
                "examples/open_lane/max2_tiny_scored/manifest.json", "scripts/accept.py", "lakefile.toml")


@needs_project
def test_the_minimal_surface_fits_the_lean_project_and_shows_no_method(tmp_path):
    """The surface of the pilot's run against the Lean project as it is: every excerpt is a part of its file,
    and neither the prompt's first part nor any file the tools reach matches a forbidden expression. The
    files left out do: the list is not a formality."""
    from core.agent.build_prompt import fill, forbidden, load_template
    from core.model_folder import load_model_folder
    from core.open_lane.prompt import static_values

    cfg = pilot_config(PROJECT, tmp_path)
    s = surface.of_run(cfg)
    assert set(s["files"]) == {
        "CompactCheck/Spec.lean", "CompactCheck/Counted.lean", "CompactCheck/Tensor.lean", "CompactCheck/Network.lean",
        "CompactCheck/Eval.lean", "CompactCheck/Semantics.lean", "lean-toolchain", "CompactCheck/CountedOps.lean",
        "CompactCheck/Task.lean", "CompactCheck/Walk.lean", "CompactCheck/LinAlg.lean", "CompactCheck/Check.lean",
        "CompactCheck/CountedCheck.lean", "CompactCheck/CountedGeneral.lean", "CompactCheck/CountedGeneralSound.lean",
        "CompactCheck/Soundness.lean", "accept/allowlist.txt",
        "examples/open_lane/max2_tiny_scored/Candidate/Max2TinyScored.lean",
        "examples/open_lane/attn_max2_tiny_scored/Candidate/AttnTinyScored.lean"}
    folder = load_model_folder(REPO_ROOT / cfg["model"])
    entries = loop.select_networks(folder, cfg)
    part1 = fill(load_template(cfg["prompt_template"])[0], static_values(cfg, folder, entries))
    surface.check(s, PROJECT, {"the prompt's first part": part1}, extra_forbidden=forbidden(folder))
    for rel in ("docs/COUNTED.md", "docs/OPEN_LANE.md", "docs/RULES.md", "README.md", "CompactCheck/Symmetry.lean",
                "CompactCheck/ContractSound.lean", "CompactCheck/CountedOps.lean", "CompactCheck/Task.lean", "CompactCheck/Walk.lean",
                "CompactCheck/CountedGeneral.lean", "CompactCheck/CountedGeneralSound.lean"):
        assert surface.matches((PROJECT / rel).read_text(), s["forbidden"] + ["Gross"]), f"{rel} whole would pass"
    lines = surface.shown_lines(s, PROJECT)
    assert lines["CompactCheck.Spec"] is None and len(lines["CompactCheck.CountedOps"]) > 150 and len(lines["CompactCheck.Walk"]) < 20


@needs_project
def test_the_minimal_session_reads_the_surface_and_nothing_else(tmp_path):
    """read_file and search_library on the Lean project, in the minimal-knowledge condition: the
    specification and the counted language; the interface as an excerpt, without the rules for groups of
    inputs; no docs, no README, none of the fixed rules' sources, no earlier proof."""
    session = session_on(tmp_path, PROJECT)
    assert "namespace CompactCheck" in session.read_file("CompactCheck/Spec.lean", lines=400)["text"]
    ops = session.read_file("CompactCheck/CountedOps.lean", lines=400)["text"]
    assert "[excerpt]" in ops and "single : Graph → Task → Input → M B" in ops and "structure Interp" in ops
    assert "ginterval" not in ops and "gtokenIntervals" not in ops and "Box" not in ops
    general = session.read_file("CompactCheck/CountedGeneral.lean", lines=400)["text"]  # the single rule on a general network
    assert "theorem gsingle_run_of" in general and "def gsingleRun" in general and "ginterval" not in general and "Box" not in general
    assert "theorem gsingle_correct" in session.read_file("CompactCheck/CountedGeneralSound.lean")["text"]
    task = session.read_file("CompactCheck/Task.lean")["text"]
    assert "label : Input → Nat" in task and "constantLabel" not in task and "labelSymmetric" not in task
    allow = "".join(session.read_file("accept/allowlist.txt", start=s, lines=400)["text"] for s in (1, 401))
    assert "CompactCheck.Interp.single" in allow and "CompactCheck.Interp.interval" not in allow and "CompactCheck.Box" not in allow
    assert "def D : Checker" in session.read_file("examples/open_lane/max2_tiny_scored/Candidate/Max2TinyScored.lean")["text"]
    for rel in OUT_OF_REACH:
        with pytest.raises(ToolError, match="one of the files of the Lean project that this run offers"):
            session.read_file(rel)
    assert session.search_library("numCorrect")["matches"] > 0 and session.search_library("singleOk_correct")["matches"] > 0
    for query in ("ginterval|gtokenIntervals", "[Ss]ymmetr", "[Cc]ontract", "pilot", "check_sound", "singleOk_perm", "matMul"):
        assert session.search_library(query)["text"] == "(no match)", query
    hits = session.search_library("structure Interp")["text"]
    assert hits.startswith("CompactCheck/CountedOps.lean:") and session.read_file("CompactCheck/CountedOps.lean", start=int(hits.split(":")[1]), lines=1)["text"].endswith("structure Interp : Type 1 where")


@needs_project
def test_the_pilots_prompt_shows_the_interface_without_the_rules_and_points_to_no_doc(tmp_path):
    from core.agent.build_prompt import fill, load_template
    from core.model_folder import load_model_folder
    from core.open_lane.prompt import static_values

    cfg = pilot_config(PROJECT, tmp_path)
    folder = load_model_folder(REPO_ROOT / cfg["model"])
    values = static_values(cfg, folder, loop.select_networks(folder, cfg))
    assert "[excerpt]" in values["COUNTED_OPS"] and "ginterval" not in values["COUNTED_OPS"]
    assert values["COUNTED_OPS"].strip("`lean\n") == (surface.SURFACES / "minimal" / "CompactCheck" / "CountedOps.lean").read_text().strip()
    assert "interval" not in values["KNOWLEDGE"].lower() and "not counted in this run" in values["KNOWLEDGE"]
    assert "never leave it to the kernel" in values["SPLIT_EXAMPLE"] and "attn_max2_tiny_scored" in values["SPLIT_EXAMPLE"]
    assert "shorter than brute force" not in values["MODEL_NOTES"]
    tools = values["TOOLS"]
    assert "CompactCheck/CountedOps.lean (an excerpt)" in tools and "is not counted" in tools and "docs/" not in tools
    # the pipeline's own words point to no doc; the files of the Lean project it pastes mention one in passing,
    # and the prompt says that docs these files mention are not part of the run
    pasted = ("SPEC", "COUNTED", "COUNTED_OPS", "EXAMPLE", "EXTRA_SOURCES")
    own = fill(load_template(cfg["prompt_template"])[0], {**values, **{key: "" for key in pasted}})
    assert "docs/" not in own and "README" not in own and "COUNTED.md" not in own
    assert "Docs and other files that these files mention are not part of this run" in own


@needs_project
def test_a_run_that_would_paste_a_file_its_surface_does_not_show_does_not_start(tmp_path):
    """open_lane.extra_sources are pasted into the prompt, so each must be a file of the surface. The general
    single rule's two files are (as excerpts, without the rules for groups of inputs next to it), which is
    what the attention models paste; a file of the fixed rules is not, and the run is refused with the reason."""
    from core.agent.build_prompt import fill, forbidden, load_template
    from core.model_folder import load_model_folder
    from core.open_lane.prompt import static_values

    cfg = pilot_config(PROJECT, tmp_path)
    folder = load_model_folder(REPO_ROOT / cfg["model"])
    entries = loop.select_networks(folder, cfg)
    cfg["open_lane"]["extra_sources"] = ["CompactCheck/CountedGeneral.lean", "CompactCheck/CountedGeneralSound.lean"]
    values = static_values(cfg, folder, entries)
    assert "theorem gsingle_run_of" in values["EXTRA_SOURCES"] and "ginterval" not in values["EXTRA_SOURCES"]
    surface.check(surface.of_run(cfg), PROJECT, {"the prompt's first part": fill(load_template(cfg["prompt_template"])[0], values)},
                  extra_forbidden=forbidden(folder))
    cfg["open_lane"]["extra_sources"] = ["CompactCheck/TokensCost.lean"]
    with pytest.raises(loop.LoopError, match="the minimal-knowledge surface does not show CompactCheck/TokensCost.lean"):
        loop.check_surface(cfg, folder, entries, log=lambda line: None)


@needs_project
def test_a_run_whose_run_python_folder_names_a_rule_does_not_start(tmp_path, monkeypatch):
    """The folder the agent's run_python code runs in is read like the prompt: its model.py, its harness and
    the wrapper around the agent's code are scanned before the run starts, and a forbidden expression in one
    of them refuses the run, with the file and line (model.py is also pasted in the prompt, so it is found
    there too). The fixed rules lane's helpers.py, which names its rules, is not in that folder at all."""
    from core.model_folder import load_model_folder
    from core.open_lane.session import run_python_folder

    cfg = pilot_config(PROJECT, tmp_path)
    folder = load_model_folder(REPO_ROOT / cfg["model"])
    entries = loop.select_networks(folder, cfg)
    assert "helpers.py" not in run_python_folder(folder.source())
    named = folder.source() + "\n# the two tokens' rows are symmetric, so one half of the inputs is enough\n"
    monkeypatch.setattr(type(folder), "source", lambda self: named)
    with pytest.raises(loop.LoopError, match=r"run_python's folder: model.py, line \d+, matches the forbidden .*symmetr"):
        loop.check_surface(cfg, folder, entries, log=lambda line: None)


# ---- the rule on proofs, with Lean and a small library of the tests' own ------------------------------
TOY_BASE = """namespace Toy

/-- An interpreter: the operations a checker may call. -/
structure Interp where
  /-- One step. -/
  step : Nat → Nat
  /-- Many steps at once: the rule for groups. -/
  leap : Nat → Nat → Nat

/-- Count to `n`, a step at a time. -/
def count (I : Interp) : Nat → Nat
  | 0 => 0
  | n + 1 => I.step (count I n)

/-- What the rule for groups computes. -/
def leapBy (k n : Nat) : Nat := n + k

/-- The interpreter the service runs. -/
def counting : Interp where
  step := Nat.succ
  leap := leapBy

theorem count_counting (n : Nat) : count counting n = n := by
  induction n with
  | zero => rfl
  | succ n ih => show Nat.succ (count counting n) = n + 1; rw [ih]

theorem leap_counting (k n : Nat) : counting.leap k n = n + k := rfl

end Toy
"""
TOY_RULES = """import Toy.Base
import Lean

namespace Toy

/-- A rule of its own module, and its lemma. -/
def shortcut (n : Nat) : Nat := n

theorem shortcut_eq (n : Nat) : shortcut n = n := rfl

/-- A proof of the rules that unfolds a definition of the base. The equations Lean makes of `count` for
    it (`Toy.count.eq_1` and the like) are kept in this module, not in the base. -/
theorem count_one (I : Interp) : count I 1 = I.step 0 := by simp [count]

end Toy

-- constants that no source line declares and no declaration stands behind, as a command can make them: one
-- named as the library names its own, one named outside it
open Lean Elab Command in
run_cmd liftCoreM do
  for n in [`Toy.unwritten, `Elsewhere.unwritten] do
    addDecl <| .defnDecl { name := n, levelParams := [], type := mkConst ``Nat, value := mkNatLit 0,
                           hints := .abbrev, safety := .safe }
"""
# a module shown in part, as the Lean project's soundness file is: one lemma of the base, and a proof about
# the rule, which unfolds it, so that this module keeps the equations Lean makes of the rule
TOY_SOUND = """import Toy.Rules

namespace Toy

/-- Shown: counting two steps. -/
theorem count_two : count counting 2 = 2 := count_counting 2

/-- Not shown: a proof about the rule. -/
theorem shortcut_two : shortcut 2 = 2 := by simp [shortcut]

end Toy
"""
TOY_SOUND_EXCERPT = """-- [excerpt] Toy/Sound.lean as this run offers it.
namespace Toy

/-- Shown: counting two steps. -/
theorem count_two : count counting 2 = 2 := count_counting 2

end Toy
"""
# what a run shows of Toy/Base.lean: everything but the rule for groups
TOY_EXCERPT = """-- [excerpt] Toy/Base.lean as this run offers it.
namespace Toy

/-- An interpreter: the operations a checker may call. -/
structure Interp where
  /-- One step. -/
  step : Nat → Nat
-- [excerpt] (The structure has a further field.)

/-- Count to `n`, a step at a time. -/
def count (I : Interp) : Nat → Nat
  | 0 => 0
  | n + 1 => I.step (count I n)

/-- The interpreter the service runs. -/
def counting : Interp where
  step := Nat.succ
-- [excerpt] (and the further field)

theorem count_counting (n : Nat) : count counting n = n := by
  induction n with
  | zero => rfl
  | succ n ih => show Nat.succ (count counting n) = n + 1; rw [ih]

end Toy
"""
TOY_SHOWN = ["Toy.Interp", "Toy.Interp.step", "Toy.Interp.mk", "Toy.count", "Toy.counting", "Toy.count_counting",
             "Toy.count_two"]
# the recursor and casesOn take the interpreter apart, which binds its hidden field `leap` too
TOY_CLOSED = ["Toy.Interp.leap", "Toy.leap_counting", "Toy.shortcut", "Toy.shortcut_eq", "Toy.count_one", "Toy.shortcut_two",
              "Toy.Interp.rec", "Toy.Interp.casesOn"]
TOY_SURFACE = {"excerpts": ["Toy/Base.lean", "Toy/Sound.lean"], "library": "Toy", "forbidden": [r"\bleap", "shortcut", "rule for groups"],
               "probes": {"shown": TOY_SHOWN, "closed": TOY_CLOSED}}


def compile_lean(root: Path, rel: str, out: Path, path: list[Path]) -> None:
    olean = out / (rel[: -len(".lean")] + ".olean")
    olean.parent.mkdir(parents=True, exist_ok=True)
    r = subprocess.run([LEAN, "-DElab.async=false", "-R", str(root), "-o", str(olean), str(root / rel)], capture_output=True, text=True,
                       env={**os.environ, "LEAN_PATH": ":".join(str(p) for p in path)}, timeout=600)
    assert r.returncode == 0, f"{rel} does not compile:\n{r.stdout}{r.stderr}"


@pytest.fixture(scope="module")
def toy(tmp_path_factory) -> Path:
    """A Lean project with a library `Toy` of two modules, built where lake builds a library."""
    project = tmp_path_factory.mktemp("toy")
    for rel, text in (("Toy/Base.lean", TOY_BASE), ("Toy/Rules.lean", TOY_RULES), ("Toy/Sound.lean", TOY_SOUND), ("scripts/accept.py", "")):
        (project / rel).parent.mkdir(parents=True, exist_ok=True)
        (project / rel).write_text(text)
    lib = project / ".lake" / "build" / "lib" / "lean"
    for rel in ("Toy/Base.lean", "Toy/Rules.lean", "Toy/Sound.lean"):
        compile_lean(project, rel, lib, [lib])
    return project


@pytest.fixture
def toy_surface(toy, tmp_path, monkeypatch) -> dict:
    """The minimal-knowledge surface, defined for the toy library, and Lean as the tests have it."""
    d = tmp_path / "surfaces" / "minimal"
    (d / "Toy").mkdir(parents=True)
    (d / "SURFACE.yaml").write_text(yaml.safe_dump(TOY_SURFACE))
    (d / "Toy" / "Base.lean").write_text(TOY_EXCERPT)
    (d / "Toy" / "Sound.lean").write_text(TOY_SOUND_EXCERPT)
    monkeypatch.setattr(surface, "SURFACES", tmp_path / "surfaces")
    monkeypatch.setattr(inspect, "lean_binary", lambda project: LEAN)
    return surface.of_run(run_of(toy))


@needs_lean
def test_lean_says_which_constants_of_the_library_a_run_shows(toy, toy_surface):
    """A constant is shown when the line that declares it is a line of its module's excerpt; one Lean made
    itself goes with the declaration its name extends. A constant that is not shown but that a shown
    definition's value mentions is exposed. Everything else of the library is closed, a hidden field of a
    shown structure and a whole module that is not shown among it, and so is what takes apart a shown
    structure that has a hidden field (its recursor, casesOn, its constructor's injectivity lemmas)."""
    surface.check(toy_surface, toy, {})
    assert surface.shown_lines(toy_surface, toy) == {"Toy.Base": [1, 3, 4, 5, 6, 10, 11, 12, 13, 18, 19, 20, 23, 24, 25, 26, 30],
                                                     "Toy.Sound": [3, 5, 6, 11]}
    # the equations Lean made on demand: of the shown `count`, kept by the module of the rules, which is not
    # shown; of the rule `shortcut`, kept by the module that is shown in part
    made = ["Toy.count.eq_1", "Toy.shortcut.eq_1"]
    names = TOY_SHOWN + TOY_CLOSED + made + ["Toy.leapBy", "Toy.Interp.casesOn", "Toy.count.match_1", "Nat.succ", "Toy.nothing"]
    got = offered.classify(toy_surface, toy, names)
    assert {n: got["classes"][n] for n in TOY_SHOWN} == {n: "shown" for n in TOY_SHOWN}
    assert {n: got["classes"][n] for n in TOY_CLOSED} == {n: "closed" for n in TOY_CLOSED}
    # a constant Lean made goes with the declaration its name extends, in whichever module Lean keeps it: an
    # equation of a shown definition is shown, and an equation of the rule shows nothing of the rule
    assert {n: got["classes"][n] for n in made} == {"Toy.count.eq_1": "shown", "Toy.shortcut.eq_1": "closed"}
    # with no declaration of the library behind it: a constant in the library's namespace goes by the module
    # that keeps it (here the rules', which is not shown); one named outside it is nothing the library wrote
    unwritten = offered.classify(toy_surface, toy, ["Toy.unwritten", "Elsewhere.unwritten"])["classes"]
    assert unwritten == {"Toy.unwritten": "closed", "Elsewhere.unwritten": "shown"}
    assert got["classes"]["Toy.leapBy"] == "exposed" and got["library"]["exposed"] == ["Toy.leapBy"]
    assert got["classes"]["Toy.Interp.casesOn"] == "closed" and got["classes"]["Nat.succ"] == "absent" == got["classes"]["Toy.nothing"]
    assert got["library"]["taken_apart_closed"] == ["Toy.Interp"]
    assert got["library"]["modules"] == 3 and got["library"]["shown"] < got["library"]["constants"]
    assert offered.self_check(toy_surface, toy) == got["library"]


@needs_lean
def test_excerpts_source_and_build_must_fit_together_before_a_run_starts(toy, toy_surface, tmp_path):
    """The probes: constants the surface says are shown and closed, asked of the library as it was built. An
    excerpt that shows a line more, a source that moved under its build, a library that was not built: the
    reading would be wrong, and the run does not start."""
    excerpt = tmp_path / "surfaces" / "minimal" / "Toy" / "Base.lean"
    excerpt.write_text(TOY_EXCERPT.replace("-- [excerpt] (The structure has a further field.)", "  leap : Nat → Nat → Nat"))
    with pytest.raises(surface.SurfaceError, match="do not fit together .*Toy.Interp.leap is shown, not closed"):
        offered.self_check(toy_surface, toy)
    excerpt.write_text(TOY_EXCERPT)
    moved = tmp_path / "moved"
    for rel in ("Toy/Base.lean", "Toy/Rules.lean", "Toy/Sound.lean", ".lake/build/lib/lean/Toy/Base.olean",
                ".lake/build/lib/lean/Toy/Rules.olean", ".lake/build/lib/lean/Toy/Sound.olean"):
        (moved / rel).parent.mkdir(parents=True, exist_ok=True)
        (moved / rel).write_bytes((toy / rel).read_bytes())
    (moved / "Toy" / "Base.lean").write_text(TOY_BASE.replace("namespace Toy\n", "namespace Toy\n\n-- a line the build has not seen\n", 1))
    with pytest.raises(surface.SurfaceError, match="do not fit together"):
        offered.self_check(toy_surface, moved)
    with pytest.raises(inspect.InspectError, match="has no compiled Toy library"):
        offered.self_check(toy_surface, tmp_path)


CLEAN = """import Toy.Base
namespace Candidate.Clean
def D (n : Nat) : Nat := Toy.count Toy.counting n
theorem D_sound (n : Nat) : D n = n := Toy.count_counting n
/-- Unfolding what is shown puts what it is made of into the term: no use of what is not shown. -/
theorem unfolded : Toy.counting.step 0 = 1 := by unfold Toy.counting; rfl
theorem by_projection (I : Toy.Interp) : I.step 0 = I.step 0 := rfl
end Candidate.Clean
"""
# a proof as every real one is: it imports the library's proofs, the rules' among them, and rewrites with a
# shown definition. The equation of `count` it rewrites with is the one the module of the rules keeps
CLEAN_TOO = """import Toy.Sound
namespace Candidate.CleanToo
theorem one_step (I : Toy.Interp) (n : Nat) : Toy.count I (n + 1) = I.step (Toy.count I n) := by rw [Toy.count]
theorem two (n : Nat) (h : n = 2) : Toy.count Toy.counting n = 2 := by subst h; exact Toy.count_two
end Candidate.CleanToo
"""
BEYOND = """import Toy.Rules
import Lean
namespace Candidate.Beyond
/-- A checker that calls the rule for groups. -/
def D (n : Nat) : Nat := Toy.counting.leap 0 n
theorem D_sound (n : Nat) : D n = n := Toy.leap_counting 0 n
-- the same field reached by its number, without its name
open Lean Elab Term in
elab "second_field% " t:term : term => do
  let e ← elabTerm t none
  return .proj ``Toy.Interp 1 e
def byNumber (I : Toy.Interp) : Nat → Nat → Nat := second_field% I
/-- A lemma of a module the run does not show, in a statement and in a proof. -/
theorem stated (n : Nat) : Toy.shortcut n = n := rfl
theorem proved (n : Nat) : n = n := (Toy.shortcut_eq n).symm.trans (Toy.shortcut_eq n)
def fine (n : Nat) : Nat := Toy.count Toy.counting n
/-- Taking the interpreter apart binds its hidden field, whether a field is used or not. -/
theorem by_cases (I : Toy.Interp) : I.step 0 = I.step 0 := by cases I; rfl
end Candidate.Beyond
"""


@needs_lean
def test_a_module_that_mentions_what_the_run_does_not_show_is_found_constant_by_constant(toy, toy_surface, tmp_path):
    lib = toy / ".lake" / "build" / "lib" / "lean"
    for name, text in (("Clean", CLEAN), ("CleanToo", CLEAN_TOO), ("Beyond", BEYOND)):
        (tmp_path / "Candidate").mkdir(exist_ok=True)
        (tmp_path / "Candidate" / f"{name}.lean").write_text(text)
        compile_lean(tmp_path, f"Candidate/{name}.lean", tmp_path / "out", [lib])
    oleans = {f"Candidate.{name}": tmp_path / "out" / "Candidate" / f"{name}.olean" for name in ("Clean", "CleanToo", "Beyond")}
    clean = offered.of_oleans(toy_surface, toy, {name: oleans[name] for name in ("Candidate.Clean", "Candidate.CleanToo")})
    assert clean["clean"] is True and clean["uses"] == [] and "uses nothing of the Lean project's library beyond" in offered.note(clean)
    # the equation the second proof rewrites with is not its own: Lean made it for the rules' module and keeps it there
    info = inspect.inspect_oleans(LEAN, {"Candidate.CleanToo": oleans["Candidate.CleanToo"], "Toy.Rules": lib / "Toy" / "Rules.olean"},
                                  where=["Toy.count.eq_2"])
    assert info["where"] == {"Toy.count.eq_2": ["Toy.Rules"]} and info["modules"]["Candidate.CleanToo"]["constants"] == 2
    verdict = offered.of_oleans(toy_surface, toy, oleans)
    uses = {u["constant"]: u["closed"] for u in verdict["uses"]}
    assert verdict["clean"] is False and uses == {
        "Candidate.Beyond.D": ["Toy.Interp.leap"], "Candidate.Beyond.D_sound": ["Toy.leap_counting"],
        "Candidate.Beyond.byNumber": ["Toy.Interp.leap"], "Candidate.Beyond.stated": ["Toy.shortcut"],
        "Candidate.Beyond.proved": ["Toy.shortcut", "Toy.shortcut_eq"],  # the lemma, and what its statement is about
        "Candidate.Beyond.by_cases": ["Toy.Interp.casesOn"]}  # the interpreter taken apart, its hidden field bound
    said = offered.note(verdict)
    assert said.startswith("not counted in this run") and "Candidate.Beyond.D mentions Toy.Interp.leap" in said
    assert said.endswith("use its projections instead")
    assert offered.summary(verdict) == {"clean": False, "uses": verdict["uses"], "count": 6}


def toy_run(tmp_path: Path, monkeypatch, toy: Path, scripts: list[dict], rounds_max: int) -> tuple[Path, Path]:
    """A run of the pilot's kind on stand-ins (tests/test_stages.py), with the toy library built into its
    stand-in Lean project and the minimal-knowledge surface defined for it. Returns the config and the project."""
    import shutil

    path = stand_ins.pilot_run(tmp_path, monkeypatch, scripts, rounds_max=rounds_max, seed_check=None, scaling=False)
    project = tmp_path / "lean"
    shutil.copytree(toy / "Toy", project / "Toy")
    shutil.copytree(toy / ".lake" / "build" / "lib", project / ".lake" / "build" / "lib")
    d = tmp_path / "surfaces" / "minimal"
    (d / "Toy").mkdir(parents=True)
    whole = ["CompactCheck/Spec.lean", "CompactCheck/Counted.lean", "CompactCheck/CountedOps.lean"]  # what the prompt pastes
    (d / "SURFACE.yaml").write_text(yaml.safe_dump({**TOY_SURFACE, "whole": whole}))
    (d / "Toy" / "Base.lean").write_text(TOY_EXCERPT)
    (d / "Toy" / "Sound.lean").write_text(TOY_SOUND_EXCERPT)
    monkeypatch.setattr(surface, "SURFACES", tmp_path / "surfaces")
    return path, project


PA = "N_max2_ladder_n2v24d8_s0_c576"
COL = f"""import Toy.Base
import Protected.{PA}
namespace Candidate.Col
open Protected.{PA}
def D (ws : List Nat) : Nat := Toy.count Toy.counting (graph.length + task) + ws.length * 0
theorem D_sound : ∀ ws, D ws = 5 := by
  intro ws; simp [D, Toy.count_counting, graph, task]
end Candidate.Col
"""
LEAP = f"""import Toy.Base
import Protected.{PA}
namespace Candidate.Leap
open Protected.{PA}
def D (ws : List Nat) : Nat := Toy.counting.leap 0 (graph.length + task) + ws.length * 0
theorem D_sound : ∀ ws, D ws = 5 := by
  intro ws; simp [D, Toy.leap_counting, graph, task]
end Candidate.Leap
"""


def instance_of(name: str) -> str:
    return f"""import Candidate.{name}
namespace Candidate.{name}Run
open Protected.{PA}
theorem D_instance : Candidate.{name}.D weights = 5 := Candidate.{name}.D_sound weights
theorem performance : Target := by unfold Target claimedCount; decide
end Candidate.{name}Run
"""


LEMMA = "import Toy.Rules\nnamespace Candidate.Lemma\ntheorem viaRule (n : Nat) : Toy.shortcut n = n := Toy.shortcut_eq n\nend Candidate.Lemma\n"


@needs_lean
def test_a_whole_run_counts_only_proofs_within_what_it_offers(toy, tmp_path, monkeypatch):
    """A scripted run with Lean. Round 1 submits a scored proof within what the run shows; then a far shorter
    one whose checker calls the rule the run does not show, and a lemma from a module it does not show. The
    service accepts all three (they are true). The agent is told at the compile already, and again with the
    receipt; the short proof is recorded without a length, so the score rests on the first; round 2's prompt
    says which submissions are not counted and why. Last, the session asks Lean to print the interface: that
    cannot be kept from it, and the log marks the compile for whoever reviews the run."""
    A, call = stand_ins.A, stand_ins.call

    def scored(name: str, bill: int) -> dict:
        return {"checker": f"Candidate.{name}.D", "sound": f"Candidate.{name}.D_sound", "instance": f"Candidate.{name}Run.D_instance",
                "certificate": [], "claimed_bill": bill}

    round_1 = {"calls": [
        call("lean_check", path="Candidate/Col.lean", source=COL, network=A, claimed_count=576),
        call("lean_check", path="Candidate/ColRun.lean", source=instance_of("Col"), network=A, claimed_count=576),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.ColRun.performance",
             modules=["Candidate/ColRun.lean", "Candidate/Col.lean"], scored=scored("Col", 20000)),
        call("lean_check", path="Candidate/Leap.lean", source=LEAP, network=A, claimed_count=576),
        call("lean_check", path="Candidate/LeapRun.lean", source=instance_of("Leap"), network=A, claimed_count=576),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.LeapRun.performance",
             modules=["Candidate/LeapRun.lean", "Candidate/Leap.lean"], scored=scored("Leap", 100)),
        call("lean_check", path="Candidate/Lemma.lean", source=LEMMA, network=A, claimed_count=576),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.Lemma.viaRule", modules=["Candidate/Lemma.lean"], kind="auxiliary"),
        call("lean_check", path="Candidate/Look.lean", source="import Toy.Base\n#print Toy.Interp\n", network=A, claimed_count=576),
    ], "response": "CLAIM: two proofs and a lemma.\nWHY IT HELPS: -\nNOTES: none."}
    nothing = {"calls": [], "response": "CLAIM: nothing.\nWHY IT HELPS: -\nNOTES: none."}
    path, project = toy_run(tmp_path, monkeypatch, toy, [round_1, nothing], rounds_max=2)
    monkeypatch.setattr(inspect, "lean_binary", lambda p: LEAN)
    lib = project / ".lake" / "build" / "lib" / "lean"
    monkeypatch.setattr(Session, "_service", lean_tests.lean_service({}, library=(lib,), compiles=True))
    lines = []
    ctx = loop.start(path, log=lines.append)
    assert any("the minimal-knowledge surface" in l and "a proof that uses another is not counted" in l for l in lines), lines
    loop.drive(ctx)
    run = ctx.run
    assert run.done_rounds() == [0, 1, 2], lines[-6:]
    session = run.round_path(1) / "attempt_0" / "open_lane"
    tools = [json.loads(l) for l in (session / "tools.jsonl").read_text().splitlines()]
    assert [(t["tool"], t["outcome"].get("offered", "-")) for t in tools] == [
        ("lean_check", "-"), ("lean_check", "-"), ("submit_candidate", True), ("lean_check", False), ("lean_check", "-"),
        ("submit_candidate", False), ("lean_check", False), ("submit_candidate", False), ("lean_check", "-")]
    # Lean printed the interface with the field the run does not show: nothing is held back, the compile is marked
    assert ["showed" in t["outcome"] for t in tools] == [False] * 8 + [True] and any("leap" in line for line in tools[8]["outcome"]["showed"])
    assert sum("in 1 compile(s) of this session Lean's output matched what the run does not show the agent" in l for l in lines) == 1
    kept = [json.loads((session / "submissions" / n / "offered.json").read_text()) for n in ("000", "001", "002")]
    assert [k["clean"] for k in kept] == [True, False, False]
    uses = {u["constant"]: u["closed"] for u in kept[1]["uses"]}  # the checker, its soundness proof, the equation simp made of it
    assert uses["Candidate.Leap.D"] == ["Toy.Interp.leap"] and "Candidate.Leap.D_sound" in uses and all(c.startswith("Candidate.Leap.") for c in uses)
    records = [r for r in run.read_archive() if r["round"] == 1]
    assert [(r["status"], r["offered"]["clean"], r["length"]) for r in records] == [("ok", True, 20448), ("verified", False, None), ("lemma", False, None)]
    assert records[1]["error"].startswith("not counted in this run") and "the service scored it at length 548" in records[1]["error"]
    assert records[1]["receipt"]["scoring"]["length"] == 548 and records[1]["certified"] == 576  # the service's verdict is kept as it was
    assert records[2]["error"].startswith("not counted in this run") and "Candidate.Lemma.viaRule mentions Toy.shortcut" in records[2]["error"]
    p2 = run.read(2, "prompt.md")
    assert "length 20,448" in p2 and "length 548" not in p2.split("YOUR SUBMISSIONS SO FAR")[0]  # the score rests on the first proof
    said = p2.split("YOUR SUBMISSIONS SO FAR")[1]
    assert "round 1 submission 1" in said and "verified, certified 576; not counted in this run" in said
    assert "(auxiliary lemma accepted)" in said and said.count("not counted in this run") == 2
    assert said.count("accepted, not counted: it uses what this run does not offer") == 3  # Leap, LeapRun and the lemma, carried over
    assert "- Candidate/Col.lean" in said and "scored proof (576 inputs, length 20,448)" in said


def test_when_lean_cannot_be_asked_what_a_proof_uses_the_run_halts_and_a_resume_asks_again(tmp_path, monkeypatch):
    """No Lean here: the stand-in service, and Lean's account stubbed. Lean not answering says nothing about
    a proof: it is not counted and not held back on that ground. The agent is told the question is open, the
    round does not make its records, the run halts, and a resume asks again without running the session again."""
    A, call = stand_ins.A, stand_ins.call
    round_1 = {"calls": [
        call("lean_check", path="Candidate/One.lean", source=stand_ins.ONE_MODULE, network=A, claimed_count=576),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.One.performance", modules=["Candidate/One.lean"],
             scored={"checker": "Candidate.One.D", "sound": "Candidate.One.D_sound", "instance": "Candidate.One.D_instance",
                     "certificate": [], "claimed_bill": 15000}),
    ], "response": "CLAIM: a proof.\nWHY IT HELPS: -\nNOTES: none."}
    path = stand_ins.pilot_run(tmp_path, monkeypatch, [round_1], seed_check=None, scaling=False)
    d = tmp_path / "surfaces" / "minimal"
    d.mkdir(parents=True)
    (d / "SURFACE.yaml").write_text(yaml.safe_dump({"prefixes": ["CompactCheck/", "examples/"], "library": "Toy"}))
    monkeypatch.setattr(surface, "SURFACES", tmp_path / "surfaces")
    monkeypatch.setattr(offered, "self_check", lambda s, project: {"constants": 9, "shown": 5, "exposed": [], "modules": 1})
    asked = {"n": 0, "answers": False}

    def lean(s, project, submission):
        asked["n"] += 1
        if not asked["answers"]:
            raise inspect.InspectError("no lean binary found (install elan)")
        return {"clean": True, "uses": [], "library": {}}

    monkeypatch.setattr(offered, "of_submission", lean)
    lines = []
    ctx = loop.start(path, log=lines.append)
    with pytest.raises(Exception, match="whether it uses only what the run offers of the Lean project's library is not known .*can be resumed"):
        loop.drive(ctx)
    run = ctx.run
    session = run.round_path(1) / "attempt_0" / "open_lane"
    tools = [json.loads(l) for l in (session / "tools.jsonl").read_text().splitlines()]
    assert tools[1]["outcome"]["status"] == "accepted" and tools[1]["outcome"]["offered"] is None
    assert not (session / "submissions" / "000" / "offered.json").exists() and run.done_rounds() == [0] and asked["n"] == 2
    asked["answers"] = True
    loop.drive(loop.resume(run.path, log=lines.append))
    assert run.done_rounds() == [0, 1] and asked["n"] == 3  # asked once more, and kept
    assert json.loads((session / "submissions" / "000" / "offered.json").read_text())["clean"] is True
    assert [(r["status"], r["offered"]["clean"]) for r in run.read_archive() if r["round"] == 1] == [("ok", True)]
    assert len([t for t in (session / "tools.jsonl").read_text().splitlines()]) == 2  # the session did not run again


def test_a_run_keeps_what_it_showed_the_agent(tmp_path, monkeypatch):
    """What a run shows the agent is one thing for the whole run: the run records a digest of its surface
    (the definition and every file as it is served), its records carry it, and a resume on a surface or a
    file that changed is refused."""
    nothing = {"calls": [], "response": "CLAIM: nothing.\nWHY IT HELPS: -\nNOTES: none."}
    path = stand_ins.pilot_run(tmp_path, monkeypatch, [nothing], seed_check=None, scaling=False)
    d = tmp_path / "surfaces" / "minimal"
    d.mkdir(parents=True)
    (d / "SURFACE.yaml").write_text(yaml.safe_dump({"prefixes": ["CompactCheck/", "examples/"]}))
    monkeypatch.setattr(surface, "SURFACES", tmp_path / "surfaces")
    lines = []
    ctx = loop.start(path, log=lines.append)
    loop.drive(ctx)
    run = ctx.run
    started = json.loads((run.path / "versions.json").read_text())
    assert len(started["surface"]) == 16 and [r["versions"]["surface"] for r in run.read_archive() if r["round"] == 1] == [started["surface"]]
    assert loop.resume(run.path, log=lines.append).versions["surface"] == started["surface"]
    (tmp_path / "lean" / "CompactCheck" / "Spec.lean").write_text("-- spec, and a line the run did not show\n")
    with pytest.raises(loop.LoopError, match="what run stages shows the agent .* changed since it started"):
        loop.resume(run.path, log=lines.append)
    (tmp_path / "lean" / "CompactCheck" / "Spec.lean").write_text("-- spec")
    (d / "SURFACE.yaml").write_text(yaml.safe_dump({"prefixes": ["CompactCheck/", "examples/"], "forbidden": ["column"]}))
    with pytest.raises(loop.LoopError, match="changed since it started"):
        loop.resume(run.path, log=lines.append)


# ---- the rule on proofs, on the library the Lean project built -----------------------------------------
def real_surface(tmp_path: Path) -> dict:
    """The minimal-knowledge surface of the pilot's run on the Lean project. Where only a part of the library
    is built (the modules that need no Mathlib), the modules that are not built are left out of it."""
    s = surface.of_run(pilot_config(PROJECT, tmp_path))
    if not WHOLE_BUILD:
        built = {rel: f for rel, f in s["files"].items() if not rel.startswith("CompactCheck/") or rel[: -len(".lean")].replace("/", ".") in BUILT}
        s = {**s, "files": built}
    return s


@needs_library
def test_the_library_the_lean_project_built_is_read_as_the_minimal_surface_says(tmp_path, monkeypatch):
    """Lean's reading of the real library: the interface's single rule is shown and its rules for groups are
    closed, field by field of one structure; the task's label is shown and its rule fields are closed; the
    fixed rules' modules are closed; what a shown definition unfolds to is exposed; a constant Lean made goes
    with the declaration it belongs to, whichever module keeps it. With the whole project built, the run's
    own check (the surface's probes) passes."""
    monkeypatch.setattr(inspect, "lean_binary", lambda project: LEAN)
    s = real_surface(tmp_path)
    shown = ["CompactCheck.Interp.single", "CompactCheck.Interp.weight", "CompactCheck.Interp.counting",
             "CompactCheck.Interp.counting_single", "CompactCheck.CostM.single", "CompactCheck.CostM.single_spec", "CompactCheck.CostM.run_bind",
             "CompactCheck.Task.label", "CompactCheck.maxTask", "CompactCheck.allInputs", "CompactCheck.strictMaxAt", "CompactCheck.singleOk",
             "CompactCheck.singleCost", "CompactCheck.reachable.go", "CompactCheck.evalGraph"]
    closed = ["CompactCheck.Interp.interval", "CompactCheck.Interp.ginterval", "CompactCheck.Interp.gtokenIntervals",
              "CompactCheck.Interp.counting_interval", "CompactCheck.CostM.interval_spec", "CompactCheck.Task.constantLabel",
              "CompactCheck.Task.labelSymmetric", "CompactCheck.rootBox", "CompactCheck.Range", "CompactCheck.intervalCost", "CompactCheck.matMul",
              "CompactCheck.checkProof", "CompactCheck.symmetricNet",
              # the recursor takes Interp apart, which binds its hidden fields too, though Interp's line is shown
              "CompactCheck.Interp.rec"]
    exposed = ["CompactCheck.CostM.interval", "CompactCheck.Box", "CompactCheck.cornerLabel"]
    # equations Lean made on demand, both kept by the module of the general single rule, which is shown in
    # part: one of a definition the run shows, one of a definition of the general checker, which it does not
    made = {"CompactCheck.Cost.add.eq_1": "shown", "CompactCheck.gevalOps.eq_1": "closed"}
    if WHOLE_BUILD:
        # on the whole library, where about a fifth of the constants are kept by another module than the one of
        # their declaration: the soundness file, shown in part, keeps the equation of `rootBox` (taking it for
        # shown is what first made `rootBox` and `Range` come out exposed there), and a module of the rules,
        # which the run does not show, keeps the equation of `addOp`, which the evaluator's file shows
        made.update({"CompactCheck.rootBox.eq_1": "closed", "CompactCheck.addOp.eq_1": "shown"})
    want = {**{n: "shown" for n in shown}, **{n: "closed" for n in closed}, **{n: "exposed" for n in exposed}, **made}
    got = offered.classify(s, PROJECT, list(want))
    off = {n: f"{got['classes'][n]}, not {w}" for n, w in want.items() if got["classes"][n] != w}
    assert not off, f"{off}; exposed: {got['library']['exposed']}"
    assert len(got["library"]["exposed"]) < 80, got["library"]["exposed"]  # what unfolding the shown definitions reaches
    if WHOLE_BUILD:
        assert offered.self_check(s, PROJECT)["constants"] == got["library"]["constants"]


REAL_CLEAN = """import CompactCheck.CountedOps
namespace Candidate.Clean
open CompactCheck
/-- As the worked example: the single rule on each input. -/
def countSingles (I : Interp) (g : Graph) (task : Task) : List Input → I.M I.N
  | [] => pure I.nzero
  | x :: xs => do
    let ok ← I.single g task x
    let n ← countSingles I g task xs
    pure (I.nadd (I.countB ok) n)
def D (g : Graph) : Checker := fun I => countSingles I g (maxTask 2 4) (allInputs (maxTask 2 4).space)
theorem label_eq (x : Input) : (maxTask 2 4).label x = x.foldl max 0 := by unfold maxTask; rfl
theorem counting_single_eq : Interp.counting.single = CostM.single := by unfold Interp.counting; rfl
theorem single_run (g : Graph) (x : Input) (env : Env) (c c' : Cost)
    (h : (CostM.single g (maxTask 2 4) x).run env c = some (true, c')) :
    singleOk g env.weights (maxTask 2 4) x = true := CostM.single_spec h
theorem cost_unfolded (g : Graph) (w : Weights Rat) : singleCost g w = singleCost g w := by unfold singleCost; rfl
end Candidate.Clean
"""
REAL_BEYOND = """import CompactCheck.CountedOps
import CompactCheck.Symmetry
import Lean
namespace Candidate.Beyond
open CompactCheck
/-- A checker that calls the interval rule. -/
def D (g : Graph) (task : Task) (box : Box) : Checker := fun I => do
  let ok ← I.interval g task box
  pure (I.countB ok)
open Lean Elab Term in
elab "field% " i:num " of " t:term : term => do
  let e ← elabTerm t none
  return .proj ``CompactCheck.Interp i.getNat e
def byNumber (I : Interp) := field% 37 of I
theorem uses_symmetry (g : Graph) (h : symmetricNet g = true) : symmetricNet g = true := h
theorem uses_task_field : (maxTask 2 4).labelSymmetric = true := rfl
def fine (I : Interp) : I.N := I.nzero
end Candidate.Beyond
"""


@needs_library
def test_a_checker_that_calls_the_interval_rule_is_found_on_the_real_library(tmp_path, monkeypatch):
    """Modules compiled against the library the Lean project built. A checker written as the worked example
    is, with proofs that unfold the task and the interpreter, uses nothing beyond the surface. A checker that
    calls `I.interval`, by name or by the field's number, a proof that rests on the symmetry rule's
    definitions and a statement about a rule field of the task are found."""
    monkeypatch.setattr(inspect, "lean_binary", lambda project: LEAN)
    lib = BUILT["CompactCheck.CountedOps"].parent.parent
    for name, text in (("Clean", REAL_CLEAN), ("Beyond", REAL_BEYOND)):
        (tmp_path / "Candidate").mkdir(exist_ok=True)
        (tmp_path / "Candidate" / f"{name}.lean").write_text(text)
        compile_lean(tmp_path, f"Candidate/{name}.lean", tmp_path / "out", [lib])
    s = real_surface(tmp_path)
    oleans = {f"Candidate.{name}": tmp_path / "out" / "Candidate" / f"{name}.olean" for name in ("Clean", "Beyond")}
    assert offered.of_oleans(s, PROJECT, {"Candidate.Clean": oleans["Candidate.Clean"]})["uses"] == []
    uses = {u["constant"]: u["closed"] for u in offered.of_oleans(s, PROJECT, oleans)["uses"]}
    assert uses == {"Candidate.Beyond.D": ["CompactCheck.Interp.interval"], "Candidate.Beyond.byNumber": ["CompactCheck.Interp.interval"],
                    "Candidate.Beyond.uses_symmetry": ["CompactCheck.symmetricNet"],
                    "Candidate.Beyond.uses_task_field": ["CompactCheck.Task.labelSymmetric"]}


# A proof as an agent writes it: it unfolds a definition of the evaluator, whose file the run shows whole. Compiled
# after the soundness file, as the worked example is, Lean rewrites with an equation that a module of the rules keeps.
REAL_UNFOLDS = """import CompactCheck.Soundness
namespace Candidate.Unfolds
open CompactCheck
theorem add_none (a b : Tensor Rat) (h : (a.shape == b.shape && a.data.size == b.data.size) = false) :
    addOp a b = none := by
  rw [addOp]
  simp [h]
end Candidate.Unfolds
"""
# The equation Lean made of `rootBox`, by its name. The soundness file keeps it.
REAL_NAMES = """import CompactCheck.Soundness
namespace Candidate.Names
def theEquation := @CompactCheck.rootBox.eq_1
end Candidate.Names
"""


@needs_whole
def test_on_the_whole_library_an_equation_goes_with_its_definition_not_with_the_module_that_keeps_it(tmp_path, monkeypatch):
    """Modules compiled after the soundness file, as a submission is, on the whole library. A proof that
    unfolds `addOp`, which the run shows, rewrites with the equation Lean made of it, and a module of the
    rules keeps that equation: the proof uses nothing beyond the surface. The equation of `rootBox` is kept
    by the soundness file, which the run shows in part: naming it is a use of `rootBox`. (Going by the module
    that keeps an equation had both wrong: the first proof was not counted and the second was.)"""
    monkeypatch.setattr(inspect, "lean_binary", lambda project: LEAN)
    path = sorted((PROJECT / ".lake" / "packages").glob("*/.lake/build/lib/lean")) + [BUILT["CompactCheck.CountedOps"].parent.parent]
    oleans = {}
    for name, text in (("Unfolds", REAL_UNFOLDS), ("Names", REAL_NAMES)):
        (tmp_path / "Candidate").mkdir(exist_ok=True)
        (tmp_path / "Candidate" / f"{name}.lean").write_text(text)
        compile_lean(tmp_path, f"Candidate/{name}.lean", tmp_path / "out", path)
        oleans[f"Candidate.{name}"] = tmp_path / "out" / "Candidate" / f"{name}.olean"
    s = real_surface(tmp_path)
    assert offered.of_oleans(s, PROJECT, {"Candidate.Unfolds": oleans["Candidate.Unfolds"]})["uses"] == []
    uses = {u["constant"]: u["closed"] for u in offered.of_oleans(s, PROJECT, {"Candidate.Names": oleans["Candidate.Names"]})["uses"]}
    assert list(uses) == ["Candidate.Names.theEquation"]
    assert {"CompactCheck.rootBox", "CompactCheck.rootBox.eq_1"} <= set(uses["Candidate.Names.theEquation"])


# Taking the task apart with a pattern match or `cases`, never naming a hidden projection (the review of e6221f0
# found that this passed the audit), and reading the label by its projection.
REAL_APART = """import CompactCheck.Soundness
namespace Candidate.Apart
open CompactCheck
def symOf (t : Task) : Bool := match t with
  | { labelSymmetric := s, .. } => s
def labelOf (t : Task) : Input → Nat := t.label
theorem byCases (t : Task) : t.label = t.label := by cases t; rfl
end Candidate.Apart
"""


@needs_whole
def test_on_the_whole_library_taking_the_task_apart_is_a_use_of_its_hidden_fields(tmp_path, monkeypatch):
    """A pattern match or `cases` on a Task binds every field, the hidden ones included, without naming their
    projections. Lean's eliminators of a structure with a hidden field therefore count as closed, whatever the
    structure's own line shows; its projections and its constructor do not. Reading the label by its
    projection stays clean; the surface's probes say so before every run."""
    monkeypatch.setattr(inspect, "lean_binary", lambda project: LEAN)
    path = sorted((PROJECT / ".lake" / "packages").glob("*/.lake/build/lib/lean")) + [BUILT["CompactCheck.CountedOps"].parent.parent]
    (tmp_path / "Candidate").mkdir()
    (tmp_path / "Candidate" / "Apart.lean").write_text(REAL_APART)
    compile_lean(tmp_path, "Candidate/Apart.lean", tmp_path / "out", path)
    s = real_surface(tmp_path)
    got = offered.classify(s, PROJECT, ["CompactCheck.Task.casesOn", "CompactCheck.Task.rec", "CompactCheck.Task.mk.injEq",
                                         "CompactCheck.Interp.casesOn", "CompactCheck.Task.mk", "CompactCheck.Task.label",
                                         "CompactCheck.Task._sizeOf_1"])
    assert got["classes"] == {"CompactCheck.Task.casesOn": "closed", "CompactCheck.Task.rec": "closed",
                              "CompactCheck.Task.mk.injEq": "closed", "CompactCheck.Interp.casesOn": "closed",
                              "CompactCheck.Task.mk": "shown", "CompactCheck.Task.label": "shown",
                              "CompactCheck.Task._sizeOf_1": "shown"}
    verdict = offered.of_oleans(s, PROJECT, {"Candidate.Apart": tmp_path / "out" / "Candidate" / "Apart.olean"})
    uses = {u["constant"]: u["closed"] for u in verdict["uses"]}
    assert set(uses) == {"Candidate.Apart.symOf.match_1", "Candidate.Apart.byCases"}, uses
    assert all(offered.takes_apart(c) for cs in uses.values() for c in cs)
    assert "Candidate.Apart.labelOf" not in uses
    assert offered.note(verdict).endswith("use its projections instead")
