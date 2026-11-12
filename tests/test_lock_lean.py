"""The lock of the seed check on modules compiled by Lean: what Lean itself says a submission declares.

tests/test_stages.py tests the pipeline around the lock with a stand-in for Lean's account. Here the account
is Lean's: small modules without Mathlib are compiled by the Lean of the Lean project, laid out as the
acceptance service lays out a submission it accepted (its workspace with the compiled modules, the protected
module, the receipt), and core.open_lane.inspect and core.open_lane.lock read them. The cases are the ones
two reviews of the lock found (10 November 2026): a checker declared in another file than the one named
like it, an import written over two lines, text in a string that looks like declarations, and a checker
that changed while everything a text comparison looked at stayed the same.

The last test is a whole run on these modules: a scripted agent, a service that keeps the acceptance
service's layout and compiles with Lean, and the lock as it is.

Needs the Lean project (at COMPACT_PROOF_LEAN, else next to this repository, else at the pilots' path) for
its Lean; skipped without one. The acceptance service itself is not run.
"""

from __future__ import annotations

import json
import os
import subprocess
from pathlib import Path

import pytest

from core.loop import LEAN_LOCK
from core.loop import check_inspection as the_real_check  # the whole-run test puts it back where a helper replaces it
from core.open_lane import inspect
from core.open_lane.lock import LockError, lockable, read_lock, renamed, same_checker
from core.util import REPO_ROOT


def _lean() -> str | None:
    if os.environ.get("COMPACT_PROOF_LEAN"):
        projects = [Path(os.environ["COMPACT_PROOF_LEAN"]).expanduser()]
    else:
        projects = [REPO_ROOT.parent / "Compact-Proof-Checker", REPO_ROOT.parent / "auto-research-compact-proof-in-lean",
                    Path("~/Desktop/VerifiedMechanisms/LeanFormalisations/CompactCheck").expanduser()]
    for project in projects:
        if (project / "scripts" / "accept.py").is_file():
            try:
                return inspect.lean_binary(project)
            except inspect.InspectError:
                return None
    return None


LEAN = _lean()
pytestmark = pytest.mark.skipif(LEAN is None, reason="needs the Lean project (COMPACT_PROOF_LEAN or its usual places) and its Lean")


@pytest.fixture(autouse=True)
def _surface(stand_in_surface):
    """The whole run at the end is on a stand-in Lean project, so on the stand-in surface (tests/conftest.py)."""

PA, PB = "N_toy_s0_c3", "N_toy_s1_c2"  # the protected modules of two networks of the same sizes
# the identity a run records of its Lean service, as the stand-ins of tests/test_stages.py give it
IDENT = {"commit": json.loads(LEAN_LOCK.read_text())["commit"], "toolchain": "t", "lean_project": "p", "policy": "q", "acceptcheck": "b"}


def protected(short: str, graph: str = "[2, 8, 4]", weights: str = "[1, 2, 3]", claimed: int = 3) -> str:
    return f"""namespace Protected.{short}
def graph : List Nat := {graph}
def task : Nat := 2
def weights : List Nat := {weights}
def claimedCount : Nat := {claimed}
def Target : Prop := claimedCount ≤ 3
end Protected.{short}
"""


HELPERS = """namespace Candidate.Helpers
def twice (n : Nat) : Nat := n + n
theorem twice_eq (n : Nat) : twice n = n + n := rfl
end Candidate.Helpers
"""
# the checker's module: it imports its helpers over two lines, which Lean accepts
COL = f"""import
  Candidate.Helpers
import Protected.{PA} -- the protected module
namespace Candidate.Col
open Protected.{PA}
/-- The checker. -/
def D (ws : List Nat) : Nat := Candidate.Helpers.twice (graph.length + task) + ws.length * 0
theorem D_sound : ∀ ws, D ws = 10 := by
  intro ws; simp [D, Candidate.Helpers.twice, graph, task]
end Candidate.Col
"""
RUN = f"""import Candidate.Col
namespace Candidate.ColRun
open Protected.{PA}
theorem D_instance : Candidate.Col.D weights = 10 := by decide
theorem performance : Target := by unfold Target claimedCount; decide
end Candidate.ColRun
"""
SCORED = {"checker": "Candidate.Col.D", "sound": "Candidate.Col.D_sound", "instance": "Candidate.ColRun.D_instance",
          "certificate": [], "claimed_bill": 1}


class Service:
    """What the acceptance service leaves behind for a submission it accepted, made with Lean alone: the
    protected module compiled under <work>/protected, the candidate's modules compiled in a workspace under
    <work>/submissions, a receipt under <work>/receipts, and the submission's folder with its manifest."""

    def __init__(self, root: Path):
        self.root, self.work, self.count = root, root / "work", 0
        self.protected_done: dict[str, str] = {}

    def compile(self, base: Path, rel: str, path: list[Path]) -> None:
        out = base / "out" / (rel[: -len(".lean")] + ".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        env = {**os.environ, "LEAN_PATH": ":".join(str(p) for p in path)}
        r = subprocess.run([LEAN, "-DElab.async=false", "-R", str(base), "-o", str(out), str(base / rel)],
                           capture_output=True, text=True, env=env, timeout=600)
        assert r.returncode == 0, f"{rel} does not compile:\n{r.stdout}{r.stderr}"

    def protect(self, short: str, source: str) -> Path:
        ws = self.work / "protected" / short
        if self.protected_done.get(short) != source:
            assert short not in self.protected_done, f"{short} is already another protected module"
            (ws / "Protected").mkdir(parents=True)
            (ws / "Protected" / f"{short}.lean").write_text(source)
            self.compile(ws, f"Protected/{short}.lean", [])
            self.protected_done[short] = source
        return ws / "out"

    def accept(self, short: str, source: str, modules: dict[str, str], scored: dict | None = SCORED) -> Path:
        """Compile `modules` (path to text, every module after the ones it imports) against the protected
        module `short` and return the submission's folder, as core.open_lane.session leaves it."""
        prot = self.protect(short, source)
        self.count += 1
        stem = f"attempt_0-s{self.count:03d}-1762780000"
        ws = self.work / "submissions" / stem
        cdir = self.root / "sent" / f"{self.count:03d}"
        for rel, text in modules.items():
            for base in (ws, cdir):
                (base / rel).parent.mkdir(parents=True, exist_ok=True)
                (base / rel).write_text(text)
        for rel in modules:
            self.compile(ws, rel, [prot, ws / "out"])
        manifest = {"schema": "open-lane-candidate-v1", "candidate_id": stem.rsplit("-", 1)[0], "kind": "performance",
                    "network": short, "claimed_count": 3, "theorem": "Candidate.ColRun.performance", "modules": list(modules)}
        if scored is not None:
            manifest["scored"] = scored
        (cdir / "manifest.json").write_text(json.dumps(manifest))
        receipts = self.work / "receipts"
        receipts.mkdir(parents=True, exist_ok=True)
        receipt = {"status": "accepted", "steps": [{"step": "protected", "module": f"Protected.{short}", "cached": False}],
                   "scoring": {"status": "scored"}, "receipt_path": str(receipts / f"{stem}.json")}
        (receipts / f"{stem}.json").write_text(json.dumps(receipt))
        (cdir / "receipt.json").write_text(json.dumps(receipt))
        return cdir


@pytest.fixture(scope="module")
def service(tmp_path_factory):
    return Service(tmp_path_factory.mktemp("lock_lean"))


@pytest.fixture(scope="module")
def first(service):
    """The proof the lock is read from: helpers, the checker, the instance, on the first network."""
    return service.accept(PA, protected(PA), {"Candidate/Helpers.lean": HELPERS, "Candidate/Col.lean": COL, "Candidate/ColRun.lean": RUN})


@pytest.fixture(autouse=True)
def the_projects_lean(monkeypatch):
    monkeypatch.setattr(inspect, "lean_binary", lambda project: LEAN)


PROJECT = Path("/the-lean-project")  # asked only for its Lean, which the fixture above gives


def on_second(modules: dict[str, str]) -> dict[str, str]:
    """Modules written for the first network, as the lock takes them to the second: the name replaced."""
    return {rel: renamed(text, PA, PB) for rel, text in modules.items()}


def test_lean_says_what_a_module_imports_and_declares(first):
    """An import written over two lines is an import: the module it names is locked with the checker's.
    A review's case: `import` and the module's name on separate lines, which a scanner of lines missed, so a
    helper the checker uses stayed editable."""
    info = inspect.inspect_submission(PROJECT, first, where=["Candidate.Col.D", "Candidate.Helpers.twice", "Candidate.Nothing.x"],
                                      closure=["Candidate.Col.D"])
    assert "Candidate.Helpers" in info["modules"]["Candidate.Col"]["imports"] and f"Protected.{PA}" in info["modules"]["Candidate.Col"]["imports"]
    assert info["where"] == {"Candidate.Col.D": ["Candidate.Col"], "Candidate.Helpers.twice": ["Candidate.Helpers"], "Candidate.Nothing.x": []}
    closure = {e["name"]: (e["declared"], e["modules"], e["kind"]) for e in info["closures"]["Candidate.Col.D"]["constants"]}
    assert closure == {"Candidate.Col.D": ("Candidate.Col.D", ["Candidate.Col"], "def"),
                       "Candidate.Helpers.twice": ("Candidate.Helpers.twice", ["Candidate.Helpers"], "def"),
                       "Protected._.graph": (f"Protected.{PA}.graph", [f"Protected.{PA}"], "def"),
                       "Protected._.task": (f"Protected.{PA}.task", [f"Protected.{PA}"], "def")}
    lock = read_lock(first, PROJECT)
    assert sorted(lock["modules"]) == ["Candidate/Col.lean", "Candidate/Helpers.lean"] and lock["free"] == ["Candidate/ColRun.lean"]
    assert lock["home"] == {"checker": "Candidate/Col.lean", "sound": "Candidate/Col.lean"} and lock["protected"] == PA
    assert sorted(lock["constants"]["checker"]) == ["Candidate.Col.D", "Candidate.Helpers.twice"]
    assert sorted(lock["constants"]["sound_statement"]) == ["Candidate.Col.D", "Candidate.Col.D_sound", "Candidate.Helpers.twice"]
    assert sorted(lock["constants"]["context"]) == ["Protected._.graph", "Protected._.task"]


def test_the_locked_checker_on_a_second_network_is_found_to_be_the_same(service, first):
    """The seed check as it should go: the locked text with the protected module's name replaced, a new
    instance, another network of the same sizes (the same graph and task, other weights). Lean finds the same
    kernel terms, so the result counts. A soundness proof written differently, with a lemma of its own, is
    still the same checker: a theorem counts with its statement."""
    lock = read_lock(first, PROJECT)
    second = on_second({"Candidate/Helpers.lean": HELPERS, "Candidate/Col.lean": COL, "Candidate/ColRun.lean": RUN})
    sent = service.accept(PB, protected(PB, weights="[4, 5]", claimed=2), second)
    same = same_checker(lock, sent, PROJECT)
    assert same["verified"] is True and same["why"] is None and same["fingerprints"] == lock["fingerprints"]
    assert same["constants"] == {"checker": 2, "sound_statement": 3, "context": 2}
    proved = second["Candidate/Col.lean"].replace(
        "theorem D_sound : ∀ ws, D ws = 10 := by\n  intro ws; simp [D, Candidate.Helpers.twice, graph, task]",
        "theorem aux (ws : List Nat) : D ws = 10 := by simp [D, Candidate.Helpers.twice, graph, task]\n"
        "theorem D_sound : ∀ ws, D ws = 10 := fun ws => aux ws")
    assert proved != second["Candidate/Col.lean"]
    sent = service.accept(PB, protected(PB, weights="[4, 5]", claimed=2), {**second, "Candidate/Col.lean": proved})
    assert same_checker(lock, sent, PROJECT)["verified"] is True


def test_a_changed_helper_is_another_checker_though_the_checkers_module_reads_the_same(service, first):
    """What the import over two lines put at risk: the checker's own module is the locked text, and a module
    it imports computes something else. The fingerprint is of the kernel terms the checker depends on, so it
    says which constant changed."""
    lock = read_lock(first, PROJECT)
    second = on_second({"Candidate/Helpers.lean": HELPERS.replace("twice (n : Nat) : Nat := n + n", "twice (n : Nat) : Nat := n + n + 0")
                        .replace("twice n = n + n := rfl", "twice n = n + n + 0 := rfl"),
                        "Candidate/Col.lean": COL, "Candidate/ColRun.lean": RUN})
    assert second["Candidate/Col.lean"] == renamed(lock["modules"]["Candidate/Col.lean"], PA, PB)
    other = same_checker(lock, service.accept(PB, protected(PB, weights="[4, 5]", claimed=2), second), PROJECT)
    assert other["verified"] is False
    assert "the checker's kernel terms differ from the locked checker's (changed: Candidate.Helpers.twice)" in other["why"]
    assert other["fingerprints"]["context"] == lock["fingerprints"]["context"] and other["fingerprints"]["checker"] != lock["fingerprints"]["checker"]


def test_another_graph_is_not_the_network_the_checker_was_locked_on(service, first):
    """The checker's own terms can be the same and the graph it reads another: then it is not the same
    check. Two networks of one size setting have the same graph and task; this one does not."""
    lock = read_lock(first, PROJECT)
    short = "N_toy_s2_c3"
    modules = {rel: renamed(text, PA, short) for rel, text in {"Candidate/Helpers.lean": HELPERS, "Candidate/Col.lean": COL, "Candidate/ColRun.lean": RUN}.items()}
    other = same_checker(lock, service.accept(short, protected(short, graph="[2, 8, 5]"), modules), PROJECT)
    assert other["verified"] is False and other["fingerprints"]["checker"] == lock["fingerprints"]["checker"]
    assert "the network's graph or task, as the checker uses them, differ from the first network's (changed: Protected._.graph)" in other["why"]


# A file named like the checker that declares nothing of it: its string reads like the declarations. The
# checker is declared in Real.lean, where no line starts with `def` or `theorem`: the definition follows
# other commands on its line, and the soundness theorem is made by a macro.
LOOKS_LIKE = """namespace Candidate.Decoy
def note : String := "
namespace Candidate.Col
def D (ws : List Nat) : Nat := 0
theorem D_sound : True := trivial
end Candidate.Col
"
end Candidate.Decoy
"""
REAL = f"""import Protected.{PA}
namespace Candidate.Col open Protected.{PA} def D (ws : List Nat) : Nat := graph.length + task + ws.length * 0 end Candidate.Col
macro "declare_sound" : command =>
  `(theorem $(Lean.mkIdent `Candidate.Col.D_sound) : ∀ ws : List Nat, Candidate.Col.D ws = 5 := by
      intro ws; simp [Candidate.Col.D, Protected.{PA}.graph, Protected.{PA}.task])
declare_sound
"""
REAL_RUN = f"""import Candidate.Real
import Candidate.Col
namespace Candidate.ColRun
open Protected.{PA}
theorem D_instance : Candidate.Col.D weights = 5 := by decide
theorem performance : Target := by unfold Target claimedCount; decide
end Candidate.ColRun
"""


def test_the_lock_is_on_the_module_that_declares_the_checker_whatever_the_text_looks_like(service):
    """Two reviews' cases in one proof. `Candidate.Col.D` is declared in Candidate/Real.lean, while
    Candidate/Col.lean holds a string that reads like its declarations. Lean says where the constants are:
    Real.lean is locked, Col.lean is not. And when the definition changes, the fingerprint changes, with the
    look-alike text the same."""
    modules = {"Candidate/Col.lean": LOOKS_LIKE, "Candidate/Real.lean": REAL, "Candidate/ColRun.lean": REAL_RUN}
    lock = read_lock(service.accept(PA, protected(PA), modules), PROJECT)
    assert lock["home"] == {"checker": "Candidate/Real.lean", "sound": "Candidate/Real.lean"}
    assert list(lock["modules"]) == ["Candidate/Real.lean"] and lock["free"] == ["Candidate/Col.lean", "Candidate/ColRun.lean"]
    second = on_second(modules)
    sent = service.accept(PB, protected(PB, weights="[4, 5]", claimed=2), second)
    assert same_checker(lock, sent, PROJECT)["verified"] is True
    changed = {**second, "Candidate/Real.lean": second["Candidate/Real.lean"].replace("graph.length + task + ws.length * 0", "task + graph.length + ws.length * 0")}
    assert changed["Candidate/Col.lean"] == second["Candidate/Col.lean"] and changed["Candidate/Real.lean"] != second["Candidate/Real.lean"]
    other = same_checker(lock, service.accept(PB, protected(PB, weights="[4, 5]", claimed=2), changed), PROJECT)
    assert other["verified"] is False and "the checker's kernel terms differ from the locked checker's (changed: Candidate.Col.D)" in other["why"]


def test_a_constant_declared_twice_or_under_the_markers_name_is_refused(service, first):
    """A name must say which constant is meant. A second module that declares the checker's name (the
    acceptance service refuses such a candidate; here Lean compiled it, as nothing imports both) leaves the
    proof unlockable and a result unverified. So does a constant named under `Protected._`, which the
    canonical texts use for the protected module."""
    again = "namespace Candidate.Col\ndef D (ws : List Nat) : Nat := 0\nend Candidate.Col\n"
    modules = {"Candidate/Helpers.lean": HELPERS, "Candidate/Col.lean": COL, "Candidate/ColRun.lean": RUN, "Candidate/Again.lean": again}
    twice = service.accept(PA, protected(PA), modules)
    assert "Candidate.Col.D is declared by more than one module (Candidate.Col, Candidate.Again)" in lockable(twice, PROJECT)
    lock = read_lock(first, PROJECT)
    result = same_checker(lock, twice, PROJECT)
    assert result["verified"] is False and "declared by more than one module" in result["why"]
    marked = {**modules, "Candidate/Again.lean": "def Protected.«_».graph : List Nat := [1]\n"}
    with pytest.raises(LockError, match="is named under Protected._"):
        read_lock(service.accept(PA, protected(PA), marked), PROJECT)


def test_the_compiled_modules_must_be_the_ones_of_this_submission(service):
    """Lean reads the service's workspace of a submission. If its copy of a module is not the module in the
    submission's folder, or the compiled modules are gone, nothing is read: that is Lean not being asked
    (LockUnread: no ground to call the proof unlockable), not an answer about the proof."""
    from core.open_lane.lock import LockUnread

    sent = service.accept(PA, protected(PA), {"Candidate/Helpers.lean": HELPERS, "Candidate/Col.lean": COL, "Candidate/ColRun.lean": RUN})
    assert read_lock(sent, PROJECT)["free"] == ["Candidate/ColRun.lean"]
    (sent / "Candidate" / "Col.lean").write_text(COL + "-- edited after it was accepted\n")
    with pytest.raises(LockUnread, match="Candidate/Col.lean in the service's workspace .* is not the module that was submitted"):
        read_lock(sent, PROJECT)
    (sent / "Candidate" / "Col.lean").write_text(COL)
    receipt = json.loads((sent / "receipt.json").read_text())
    stem = Path(receipt["receipt_path"]).stem
    (service.work / "submissions" / stem / "out" / "Candidate" / "Col.olean").unlink()
    with pytest.raises(LockUnread, match="compiled modules are missing"):
        read_lock(sent, PROJECT)
    assert same_checker({"checker": SCORED["checker"], "sound": SCORED["sound"]}, sent, PROJECT)["verified"] is None


def test_a_file_that_hides_its_definitions_cannot_be_locked(service):
    """A file written in Lean's module system (it begins with `module`) keeps the bodies of its definitions
    out of the compiled module: Lean shows the checker as a constant without a body. Two different checkers
    would then read the same, so such a proof is refused, never fingerprinted."""
    hidden = "module\nnamespace Candidate.Col\npublic def D (ws : List Nat) : Nat := ws.length * 0 + 7\npublic theorem D_sound : ∀ ws, D ws = D ws := fun _ => rfl\nend Candidate.Col\n"
    run = "import Candidate.Col\nnamespace Candidate.ColRun\ntheorem D_instance : Candidate.Col.D [] = Candidate.Col.D [] := rfl\ntheorem performance : True := trivial\nend Candidate.ColRun\n"
    sent = service.accept(PA, protected(PA), {"Candidate/Col.lean": hidden, "Candidate/ColRun.lean": run})
    reason = lockable(sent, PROJECT)
    assert "its checker cannot be told from another" in reason and "does not show what Candidate.Col.D is" in reason


def test_a_run_checks_before_it_starts_that_its_lean_runs_the_inspection(service, first, tmp_path, monkeypatch):
    """The lock is read when the proof rounds are over. That the inspection program runs with the Lean
    project's Lean, and reads a module that Lean compiled, is found out before the run exists: a run with a
    seed check does not start otherwise."""
    import shutil

    from core import loop

    loop.check_inspection(PROJECT)  # a project without a build here: the program runs and answers
    project = tmp_path / "project"
    built = project / ".lake" / "build" / "lib" / "lean" / "Toy" / "Module.olean"
    built.parent.mkdir(parents=True)
    shutil.copy(service.work / "protected" / PA / "out" / "Protected" / f"{PA}.olean", built)
    loop.check_inspection(project)  # one module of the project's build is read
    # a module that only imports others declares nothing, and is as good: it was read
    (tmp_path / "Root.lean").write_text("import Init\n")
    subprocess.run([LEAN, "-R", str(tmp_path), "-o", str(built), str(tmp_path / "Root.lean")], check=True, capture_output=True, timeout=600)
    loop.check_inspection(project)
    built.write_bytes(b"not a compiled module")
    with pytest.raises(loop.LoopError, match="cannot ask the Lean of .* about compiled modules"):
        loop.check_inspection(project)
    built.unlink()
    monkeypatch.setattr(inspect, "lean_binary", lambda project: shutil.which("false"))
    with pytest.raises(loop.LoopError, match="cannot ask the Lean of .* about compiled modules"):
        loop.check_inspection(project)


RICH = f"""import Protected.{PA}
namespace Candidate.Rich
open Protected.{PA}

structure Box where
  lo : Nat
  hi : Nat
  ok : lo ≤ hi

private def width (b : Box) : Nat := b.hi - b.lo

inductive Shape where
  | leaf (n : Nat)
  | node (l r : Shape)

def Shape.size : Shape → Nat
  | .leaf n => n
  | .node l r => l.size + r.size

def sumTo (n : Nat) : Nat := go n 0
where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | k + 1, acc => go k (acc + k + 1)

def halve (n fuel : Nat) : Nat :=
  if h : fuel = 0 then n else
    if n % 2 = 0 then halve (n / 2) (fuel - 1) else halve (3 * n + 1) (fuel - 1)
termination_by fuel
decreasing_by all_goals omega

def pick (xs : Array Nat) (i : Nat) (h : i < xs.size) : Nat := xs[i]

def D (ws : List Nat) : Nat :=
  let b : Box := ⟨task, task + graph.length, Nat.le_add_right _ _⟩
  width b + (Shape.node (.leaf 1) (.leaf 2)).size + sumTo 3 + halve 6 4 + pick #[7, 8] 1 (by decide) + ws.length * 0

theorem D_sound : ∀ ws, D ws = D [] := by
  intro ws; simp [D]

end Candidate.Rich
"""
RICH_RUN = f"""import Candidate.Rich
namespace Candidate.RichRun
open Protected.{PA}
theorem D_instance : Candidate.Rich.D weights = Candidate.Rich.D [] := Candidate.Rich.D_sound weights
theorem performance : Target := by unfold Target claimedCount; decide
end Candidate.RichRun
"""


def test_a_checker_with_types_recursion_and_proofs_inside_compiles_to_the_same_terms_on_both_networks(service):
    """The fingerprint must not differ where the checker does not: a module with a structure, an inductive
    type, private and local definitions, structural and well-founded recursion and proofs inside definitions
    gives the same kernel terms against two protected modules, their name apart."""
    scored = {"checker": "Candidate.Rich.D", "sound": "Candidate.Rich.D_sound", "instance": "Candidate.RichRun.D_instance",
              "certificate": [], "claimed_bill": 1}
    modules = {"Candidate/Rich.lean": RICH, "Candidate/RichRun.lean": RICH_RUN}
    lock = read_lock(service.accept(PA, protected(PA), modules, scored), PROJECT)
    names = set(lock["constants"]["checker"])
    assert {"Candidate.Rich.D", "Candidate.Rich.Box", "Candidate.Rich.Shape.size", "Candidate.Rich.sumTo.go", "Candidate.Rich.halve",
            "Candidate.Rich.pick"} <= names and any("width" in n and n.startswith("_private") for n in names) and len(names) > 20
    same = same_checker(lock, service.accept(PB, protected(PB, weights="[4, 5]", claimed=2), on_second(modules), scored), PROJECT)
    assert same["verified"] is True and same["fingerprints"] == lock["fingerprints"] and same["constants"]["checker"] == len(names)


def lean_service(counter: dict, library: tuple = (), compiles: bool = False):
    """In place of the acceptance service for a whole run: its layout, with Lean alone. A submission's
    modules are compiled by Lean in a workspace under <work>/submissions, against a protected module under
    <work>/protected (the same graph and task for every network, other weights), and the receipt is written
    under <work>/receipts. Nothing is checked beyond compiling: what is tested is everything around it.
    `library` is further folders of compiled modules the candidates may import (a library standing in for the
    Lean project's); with `compiles`, a lean_check is compiled into the workspace too, as the service does."""
    import hashlib
    import re

    def run_lean(base: Path, rel: str, path: list[Path]) -> tuple[bool, str]:
        out = base / "out" / (rel[: -len(".lean")] + ".olean")
        out.parent.mkdir(parents=True, exist_ok=True)
        r = subprocess.run([LEAN, "-DElab.async=false", "-R", str(base), "-o", str(out), str(base / rel)], capture_output=True,
                           text=True, env={**os.environ, "LEAN_PATH": ":".join(str(p) for p in path)}, timeout=600)
        return r.returncode == 0, r.stdout + r.stderr

    def compile_in(base: Path, rel: str, path: list[Path]) -> str:
        ok, said = run_lean(base, rel, path)
        return "" if ok else said

    def protect(work: Path, network: str, claimed: int) -> tuple[str, Path]:
        short = "N_" + re.sub(r"[^A-Za-z0-9]", "_", network) + f"_c{claimed}"
        prot = work / "protected" / short
        if not (prot / "out" / "Protected" / f"{short}.olean").is_file():
            (prot / "Protected").mkdir(parents=True, exist_ok=True)
            source = protected(short, weights=str([len(network), int(network[-1])]), claimed=claimed)
            (prot / "Protected" / f"{short}.lean").write_text(source.replace("claimedCount ≤ 3", "claimedCount ≤ 600"))
            assert compile_in(prot, f"Protected/{short}.lean", []) == ""
        return short, prot

    def service(self, args, timeout_s):
        if args[0] == "compile" and compiles:
            ws, rel = Path(args[1]), args[2]
            short, prot = protect(Path(self.state["work_dir"]), args[args.index("--network") + 1], int(args[args.index("--claimed") + 1]))
            ok, said = run_lean(ws, rel, [*library, prot / "out", ws / "out"])  # the compiler's messages, as the service returns them
            return {"ok": ok, "messages": said, "module": rel[: -len(".lean")].replace("/", "."),
                    "protected_module": f"Protected.{short}", "seconds": 1.0}
        if args[0] != "submit":
            return {"ok": True, "messages": ""}
        cdir, work = Path(args[1]), Path(self.state["work_dir"])
        m = json.loads((cdir / "manifest.json").read_text())
        short, prot = protect(work, m["network"], m["claimed_count"])
        counter["n"] = counter.get("n", 0) + 1
        stem = f"{m['candidate_id']}-{1762780000 + counter['n']}"
        ws = work / "submissions" / stem
        for rel in m["modules"]:
            (ws / rel).parent.mkdir(parents=True, exist_ok=True)
            (ws / rel).write_bytes((cdir / rel).read_bytes())
        left, problem = list(m["modules"]), ""
        while left:  # every module after the ones it imports: compile what compiles, until nothing more does
            done = [rel for rel in left if compile_in(ws, rel, [*library, prot / "out", ws / "out"]) == ""]
            if not done:
                problem = compile_in(ws, left[0], [*library, prot / "out", ws / "out"])
                break
            left = [rel for rel in left if rel not in done]
        digests = {**IDENT, "modules": {rel[:-5].replace("/", "."): hashlib.sha256((cdir / rel).read_bytes()).hexdigest() for rel in m["modules"]}}
        (work / "receipts").mkdir(parents=True, exist_ok=True)
        receipt = {"status": "rejected" if problem else "accepted", "reason": f"{left[0]} does not compile: {problem[:600]}" if problem else None,
                   "network": m["network"], "claim_kind": m["kind"], "claimed_count": m["claimed_count"], "theorem": m["theorem"],
                   "candidate_id": m["candidate_id"], "digests": digests, "seconds": 1.0, "isolation": "none",
                   "steps": [{"step": "protected", "module": f"Protected.{short}", "cached": False}],
                   "receipt_path": str(work / "receipts" / f"{stem}.json")}
        if not problem and m["kind"] == "auxiliary":
            receipt["statement"] = "∀ ws, Candidate.Col.D ws = 10"
        elif not problem:
            receipt["certified_count"] = m["claimed_count"]
            if "scored" in m:
                bill = m["scored"]["claimed_bill"]
                receipt["scoring"] = {"status": "scored", "bill": bill, "extract": 448, "read": 0, "length": bill + 448, "description_size": 900}
        (work / "receipts" / f"{stem}.json").write_text(json.dumps(receipt))
        return receipt

    return service


def test_a_whole_run_with_lean_reading_what_was_compiled(tmp_path, monkeypatch):
    """The pilot's three parts with the real lock: a scripted agent, a service that keeps the acceptance
    service's layout and compiles with Lean, and nothing standing in for Lean's account. Round 1 submits a
    proof whose checker imports its helpers over two lines. The lock is read from the compiled modules, so
    the helpers are locked. In the seed check the locked text is compiled against the second network's
    protected module, its name replaced, and Lean finds the locked checker there; a submission that brings
    a second declaration of the checker does not count. The scaling session's lemma is about the locked
    checker, which the report says."""
    from core import loop
    from core.open_lane import stages
    from core.open_lane.session import Session

    from tests import test_stages as stand_ins

    A, B, call = stand_ins.A, stand_ins.B, stand_ins.call
    pa, pb = "N_max2_ladder_n2v24d8_s0_c576", "N_max2_ladder_n2v24d8_s3_c570"
    col, run_a = COL.replace(PA, pa), RUN.replace(PA, pa)
    run_b = RUN.replace(PA, pb).replace("ColRun", "ColRunB")
    scored = {**SCORED, "claimed_bill": 20000}
    scored_b = {**scored, "instance": "Candidate.ColRunB.D_instance"}
    round_1 = {"calls": [
        call("lean_check", path="Candidate/Helpers.lean", source=HELPERS, network=A, claimed_count=576),
        call("lean_check", path="Candidate/Col.lean", source=col, network=A, claimed_count=576),
        call("lean_check", path="Candidate/ColRun.lean", source=run_a, network=A, claimed_count=576),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.ColRun.performance",
             modules=["Candidate/ColRun.lean", "Candidate/Col.lean", "Candidate/Helpers.lean"], scored=scored),
    ], "response": "CLAIM: a proof.\nWHY IT HELPS: -\nNOTES: none."}
    again = "namespace Candidate.Col\ndef D (ws : List Nat) : Nat := 0\nend Candidate.Col\n"
    seed_check = {"calls": [
        # a helper the checker uses: locked, though its import is written over two lines
        call("lean_check", path="Candidate/Helpers.lean", source=HELPERS.replace("n + n", "n + n + 0"), network=B, claimed_count=570),
        call("lean_check", path="Candidate/ColRunB.lean", source=run_b, network=B, claimed_count=570),
        call("lean_check", path="Candidate/Again.lean", source=again, network=B, claimed_count=570),
        call("submit_candidate", network=B, claimed_count=570, theorem="Candidate.ColRunB.performance",
             modules=["Candidate/ColRunB.lean", "Candidate/Again.lean"], scored=scored_b),
        call("submit_candidate", network=B, claimed_count=570, theorem="Candidate.ColRunB.performance",
             modules=["Candidate/ColRunB.lean"], scored=scored_b),
    ], "response": "CLAIM: 570.\nWHY IT HELPS: -\nNOTES: none."}
    growth = "import Candidate.Col\nnamespace Candidate.Growth\ntheorem same_everywhere : ∀ ws, Candidate.Col.D ws = 10 := Candidate.Col.D_sound\nend Candidate.Growth\n"
    scaling = {"calls": [
        call("lean_check", path="Candidate/Growth.lean", source=growth, network=A, claimed_count=576),
        call("submit_candidate", network=A, claimed_count=576, theorem="Candidate.Growth.same_everywhere", modules=["Candidate/Growth.lean"], kind="auxiliary"),
    ], "response": "CLAIM: constant.\nWHY IT HELPS: -\nNOTES: none."}
    path = stand_ins.pilot_run(tmp_path, monkeypatch, [round_1, seed_check, scaling])
    monkeypatch.setattr(Session, "_service", lean_service({}))
    monkeypatch.setattr(loop, "check_inspection", the_real_check)  # the preflight too, with the Lean of these tests
    lines = []
    ctx = loop.start(path, log=lines.append)
    loop.drive(ctx)
    run = ctx.run
    assert run.done_rounds() == [0, 1, 2, 3], lines[-6:]
    state = stages.read_state(run)
    locked = state["locked"]
    assert locked["modules"] == ["Candidate/Col.lean", "Candidate/Helpers.lean"] and locked["free"] == ["Candidate/ColRun.lean"]
    assert locked["protected"] == pa and set(locked["fingerprints"]) == {"checker", "sound_statement", "context"}
    # the seed check: the helper the session tried to change went to the service as it was locked
    sub = run.round_path(2) / "attempt_0" / "open_lane" / "submissions"
    tools = [json.loads(l) for l in (run.round_path(2) / "attempt_0" / "open_lane" / "tools.jsonl").read_text().splitlines()]
    assert "Candidate/Helpers.lean is locked" in tools[0]["outcome"]["error"]
    assert (sub / "001" / "Candidate" / "Helpers.lean").read_text() == HELPERS
    assert (sub / "001" / "Candidate" / "Col.lean").read_text() == col.replace(pa, pb)
    check = [r for r in run.read_archive() if r.get("stage") == "seed_check"]
    assert [(r["status"], r["lock"]["intact"], r["lock"]["verified"]) for r in check] == [("ok", True, False), ("ok", True, True)]
    assert "Candidate.Col.D is declared by more than one module" in check[0]["lock"]["why"]
    assert check[1]["lock"]["fingerprints"] == locked["fingerprints"]
    assert [t["outcome"].get("locked_checker") for t in tools[3:]] == [False, True]
    result = state["stages"]["seed_check"]["result"]
    assert (result["outcome"], result["certified"], result["lock_verified"], result["record_id"]) == ("certified", 570, True, check[1]["record_id"])
    # the scaling question: Lean finds the locked checker in the lemma's submission
    lemma = state["stages"]["scaling"]["result"]["lemmas"]
    assert [(l["theorem"], l["locked_checker"]) for l in lemma] == [("Candidate.Growth.same_everywhere", True)]
    report = "\n".join(stages.report_lines(run))
    assert "The same checker on both: Lean reads the locked checker's kernel terms" in report
    assert "- `Candidate.Growth.same_everywhere`: ∀ ws, Candidate.Col.D ws = 10 (the locked checker)" in report
