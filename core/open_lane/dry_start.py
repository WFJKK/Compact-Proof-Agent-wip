"""A dry start: what a run's first proof round would begin with, checked before the run, with no agent and no
API call.

    python3 -m core.open_lane.dry_start --config <run config> [--check] [--keep] [--set KEY=VALUE ...]

For an open-lane run, with the same code a run uses:

1. The Lean service: built, at the commit lean-checker.lock names, and what it says it is (its policy); the
   seed check's network and Lean's answers about compiled modules, when the run has sessions after its proof
   rounds (as a run checks them when it starts).
2. In a run that continues an earlier one (open_lane.continue_from): that run can be continued, and a copy of it
   is made as the run would make it, in a folder of its own (<runs_dir>/_dry_start/<run_id>), never in the run's.
3. The first round's session is made there: the carried modules are put into its workspace (those the config
   replaces, open_lane.carried_replace, as their replacements) and compiled by the service, one by one. The
   report says which compiled, how long each took, and the first errors of those that did not. A carried module
   that does not compile leaves the agent to mend it and to compile again everything that imports it, on the
   round's time and its lean_check budget: better seen here. What counts is the best scored proof among the
   carried ones (the one that certifies most): the run is ready when the modules of its submission compile.
   Other carried modules (of an earlier proof, written for another claimed count and so for another protected
   module than the newer versions of what they import) usually do not compile any more; they are named, and
   the agent is told the same.
4. With --check, the best scored proof among the carried ones is submitted again from that workspace, as the
   agent would submit it: whether the service as it is now accepts and scores it, its description size against
   the budget, and how long the check takes on this machine. That is the time every later submission of the
   run takes at least.
5. With --check, in a run with sessions after its proof rounds (a seed check): the lock. If no proof of the run
   scores better than the carried one, that one is locked, as the earlier run's service compiled it, and what
   the seed check's session submits is compiled by the service as it is now. So the lock is read both ways,
   from the earlier submission and from the one just made, and the two must name the same checker: the same
   digests of its kernel terms, of the soundness statement and of the graph and task they reach. If the
   earlier one cannot be read (the service's work folder of that run is gone) or the digests differ, a seed
   check on the carried proof would halt or come out unverified: said here, before the run.

6. The modules a fresh run is given to start from (open_lane.start_drafts): each is compiled in that workspace
   as the agent would compile it. For one the config names a checker of (its `scored`: checker, sound,
   certificate, plan; a run whose checker the service runs compiled), the report gives the run the service
   makes of it (count, bill, length, the last-bits test), and with --check it is submitted: accepted and scored
   or not, and how long the check takes.

In a run whose checker the service runs compiled (open_lane.instance compiled), a carried proof is submitted
again as such a run submits: its checker's modules with the checker, the soundness theorem, the certificate
and the plan, and no instance. For a proof an earlier kernel run carried in, those are the modules its lock
holds. The session is made as one of the formalization phase, whatever the run's first round is: a discovery
session takes no proof.

Nothing here is scored or recorded in a run, and the folder is removed afterwards (--keep leaves it). Exit
status 0 when the modules of the best carried proof compiled (and, with --check, it was accepted and scored), 1
otherwise; with start drafts, when they compiled too (and, with --check, the named checker was accepted and
scored).
"""

from __future__ import annotations

import argparse
import json
import sys
import time
from pathlib import Path

from .. import loop
from ..loop import LoopError, select_networks
from ..model_folder import load_model_folder
from ..run_config import RunConfigError, load_run_config, parse_overrides, resolve
from . import continuation
from .session import Session, ToolError, carried_modules
from .stages import planned

FOLDER = "_dry_start"


def best_scored(carried: list[dict]) -> dict | None:
    """The carried scored proof that certifies most (the shorter one of two that certify the same): the entry
    of one of its modules."""
    scored = [m for m in carried if m.get("scored") and m.get("kind") == "performance" and not m.get("beyond_offered")]
    return max(scored, key=lambda m: (m.get("certified") or 0, -(m.get("length") or 0)), default=None)


def missing_import(m: dict) -> bool:
    """The module did not compile because a module it imports did not, or was compiled against another protected
    module (Lean finds no object file for an import)."""
    return any("object file" in e and "does not exist" in e for e in m.get("errors") or [])


def proof_of(best: dict | None) -> tuple[dict, set[str]]:
    """The manifest of the submission a carried entry comes from, and the paths of its modules."""
    if best is None:
        return {}, set()
    manifest = json.loads((Path(best["source"][: -len(best["path"])]) / "manifest.json").read_text())
    return manifest, {rel for rel in manifest.get("modules") or [] if isinstance(rel, str)}


def carried_report(carried: list[dict], best: dict | None, paths: set[str], log) -> tuple[int, int, int]:
    """The totals, then the carried modules that were replaced or did not compile: those of the best scored proof
    (`paths`, its submission's modules; all of them when no scored proof is carried) one by one, with the ones
    that only import one of them named together, then those of earlier proofs alone. Returns (how many of the
    best proof did not compile of themselves, how many of it did not compile, how many others did not compile)."""
    of_best = [m for m in carried if best is None or m["path"] in paths]
    bad = [m for m in of_best if not m.get("compiled")]
    own = [m for m in bad if not missing_import(m)]
    other = [m for m in carried if best is not None and m["path"] not in paths and not m.get("compiled")]
    total = sum(m.get("seconds") or 0 for m in carried)
    slow = sorted(carried, key=lambda m: -(m.get("seconds") or 0))[:5]
    short = lambda ms: ", ".join(m["path"][len("Candidate/"):-len(".lean")] for m in ms)
    log(f"carried modules: {len(carried)}, compiled {sum(1 for m in carried if m.get('compiled'))}, {total:.0f} s in all"
        + ("; slowest: " + ", ".join(f"{m['path'][len('Candidate/'):-len('.lean')]} {m.get('seconds') or 0:.0f} s" for m in slow) if carried else ""))
    if best is not None:
        log(f"the best carried scored proof: {best.get('theorem')} ({best.get('certified')} inputs, length {best.get('length'):,}; round {best['round']}"
            + (f" of {best['from_run']}" if best.get("from_run") else "") + f", submission {best['submission']}): {len(of_best)} modules, "
            f"{len(of_best) - len(bad)} compiled")
    for m in carried:
        if isinstance(m.get("replaced"), dict):
            log(f"  replaced: {m['path']} (open_lane.carried_replace)")
    for m in own:
        log(f"  did not compile: {m['path']}: {' | '.join(m.get('errors') or [])[:400]}")
    if len(bad) > len(own):
        log(f"  and {len(bad) - len(own)} that import a module that did not compile: {short(m for m in bad if missing_import(m))}")
    if other:
        log(f"  not of that proof, {len(other)} do not compile (the agent is told): {short(other)}")
    return len(own), len(bad), len(other)


def run(cfg: dict, check: bool, keep: bool, log=print) -> int:
    ol = cfg.get("open_lane") or {}
    if not ol.get("enabled"):
        raise LoopError("a dry start is for an open-lane run (open_lane.enabled)")
    folder = load_model_folder(resolve(cfg["model"]))
    entries = select_networks(folder, cfg)
    project = resolve(ol["lean_project"])
    if not (project / ".lake" / "build" / "bin" / "acceptcheck").is_file():
        raise LoopError(f"the Lean project at {project} has no built acceptcheck (lake build acceptcheck there first)")
    loop.check_lean_lock(project)  # at the commit lean-checker.lock names, with no uncommitted change
    loop.seed_check_entry(cfg, folder, entries)  # a seed check on the wrong network fails here, as at a run's start
    if planned(cfg):  # the sessions after the proof rounds lock a checker: Lean must answer about compiled modules
        loop.check_inspection(project)
    ident = loop.lean_identity(project, knowledge=ol.get("knowledge", "minimal"))
    log(f"Lean service: {project} at {str(ident.get('commit'))[:12]} (the lock's commit), policy {ident.get('policy')}")

    tmp = resolve(cfg["runs_dir"]) / FOLDER / cfg["run_id"]
    continuation.remove_tree(tmp)
    tmp.mkdir(parents=True)
    status = 0
    try:
        if continuation.setting(cfg):
            errors = continuation.check_parent(cfg, resolve(cfg["runs_dir"]) / cfg["run_id"])
            if errors:
                raise LoopError("; ".join(errors))
            continuation.inherit(tmp, cfg, log)
        t0 = time.monotonic()
        # as a session that takes proofs: in a python_then_lean run, one of the formalization phase
        session = Session.create(tmp / "round_001" / "attempt_0" / "open_lane",
                                 {**cfg, "open_lane": {**ol, "work_dir": str(tmp / "open_lane_work"), "discovery_rounds": 0}},
                                 cfg["model"], entries, tmp, log=log)
        carried = session.state.get("carried") or []
        given = [d for d in session.state.get("drafts") or [] if isinstance(d, dict) and d.get("given")]
        if not carried:
            log("nothing is carried into the first round: the run starts from "
                + (f"the {len(given)} module(s) it is given (open_lane.start_drafts)" if given else "an empty workspace"))
        best = best_scored(carried_modules(tmp, 1))  # with the file each entry comes from
        manifest, paths = proof_of(best)
        own, bad, _ = carried_report(carried, best, paths, log)
        log(f"the session's start took {time.monotonic() - t0:.0f} s; drafts placed: {len(session.state.get('drafts') or [])}, "
            f"Python files: {len(session.state.get('py_files') or {})}")
        if bad:
            status = 1
            log(f"NOT READY: {own} carried module(s) of the proof to go on from do not compile with the Lean service as it is now"
                + (f", and {bad - own} more import them" if bad > own else "") + ". The agent would have to mend them and "
                "compile again what imports them, on the round's time and lean_check budget. open_lane.carried_replace "
                "takes an adapted version of a module (config/defaults.yaml).")
        if check and bad:
            log("not submitted again: its modules do not all compile")
        elif check:
            status = max(status, check_best(session, best, manifest, log, lock=bool(planned(cfg)), project=project))
        submitted = False
        if given:
            start, submitted = start_report(session, cfg, entries[0]["id"], check, log)
            status = max(status, start)
        if status == 0:
            log("READY: the proof to go on from compiles in the first round's workspace" + (", and is accepted and scored" if check else "")
                if carried else
                "READY: the modules the run is given to start from compile in the first round's workspace"
                + (", and the checker among them is accepted and scored" if submitted else "")
                if given else "READY: nothing is carried, and the service answers")
    finally:
        if keep:
            log(f"kept: {tmp}")
        else:
            continuation.remove_tree(tmp)
            parent = tmp.parent
            if parent.is_dir() and not any(parent.iterdir()):
                parent.rmdir()
    return status


def scored_line(receipt: dict, log) -> bool:
    """What the service said of a submission that should be accepted and scored; True when it was."""
    scoring = receipt.get("scoring") or {}
    if receipt.get("status") != "accepted":
        log(f"NOT READY: the service as it is now does not accept it: {str(receipt.get('reason') or receipt.get('error'))[:600]}")
        return False
    size = f"description size {scoring.get('description_size')} of {scoring.get('size_budget')}"
    if scoring.get("plan_bits") is not None:
        size += f", plan {scoring.get('plan_bits')} bits of {scoring.get('plan_bits_budget')}"
    if scoring.get("status") != "scored":
        log(f"NOT READY: accepted, not scored: {scoring.get('reason')} ({size}; measured length {scoring.get('measured_length')})")
        return False
    how = {"compiled": "; the run made by the service with compiled code", "kernel": "; the run checked by the kernel"}
    log(f"accepted and scored: {receipt.get('certified_count')} inputs, length {scoring.get('length'):,}; {size}"
        + how.get(receipt.get("run"), ""))
    last = scoring.get("last_bits") or {}
    if last.get("runs"):  # the service's last-bits test (its policy v14)
        fewest = min(r["count"] for r in last["runs"] if r["level"] in last["levels"])
        log(f"  the last-bits test: at least {fewest:,} inputs on every copy of the network at 2^-{last['levels'][0]} and "
            f"2^-{last['levels'][-1]}" + (f"; the count holds down to 2^-{last['holds_to']}" if last.get("holds_to") else ""))
    return True


def steps_text(receipt: dict) -> str:
    steps = ", ".join(f"{s.get('step')} {s.get('seconds'):.0f} s" for s in receipt.get("steps") or []
                      if isinstance(s.get("seconds"), (int, float)) and s["seconds"] >= 1)
    return f" ({steps})" if steps else ""


def start_report(session: Session, cfg: dict, network: str, check: bool, log) -> tuple[int, bool]:
    """The modules the run is given to start from (open_lane.start_drafts), in the config's order: each compiled
    in the first round's workspace as the agent would compile it, with the run the service makes of a checker the
    config names for it; with `check`, that checker is submitted. Returns (0 when every module compiled and every
    submission was accepted and scored, whether one was submitted)."""
    status, submitted = 0, False
    for r in (cfg.get("open_lane") or {}).get("start_drafts") or []:
        block = r.get("scored") if isinstance(r.get("scored"), dict) else None
        try:
            out = session.lean_check(r["path"], edits=[], network=network, claimed_count=0,
                                     certificate=(block or {}).get("certificate"), checker=(block or {}).get("checker"),
                                     plan=(block or {}).get("plan"))  # within a compile's limit, as the agent's call
        except ToolError as exc:
            log(f"NOT READY: the start draft {r['path']} could not be compiled: {exc}")
            return 1, submitted
        if not out.get("ok"):
            status = 1
            log(f"NOT READY: the start draft {r['path']} does not compile with the Lean service as it is now "
                f"({out.get('seconds')} s of a limit of {out.get('limit_s')} s): {out.get('messages', '')[:600]}")
            continue
        line = f"the start draft {r['path']} compiles ({out.get('seconds')} s)"
        preview = out.get("scoring_preview") or {}
        ran, last = preview.get("run") or {}, preview.get("last_bits") or {}
        if ran:
            line += (f"; its checker's run: {ran.get('count'):,} inputs, bill {ran.get('bill'):,}, length {ran.get('length'):,}"
                     f"; description size {preview.get('description_size')} of {preview.get('size_budget')}"
                     + ("; the last-bits test passes" if last.get("passes") is True else
                        f"; the last-bits test: {str(last.get('reason') or 'does not pass')[:300]}"))
        elif block:
            line += f"; no run of its checker: {str(last.get('reason') or preview.get('reason') or preview.get('error') or preview)[:400]}"
        log(line)
        if not (check and block):
            continue
        if not session.compiled:
            log(f"not submitted: a start draft's checker is submitted by a run whose checker the service runs "
                "(open_lane.instance compiled)")
            continue
        t0 = time.monotonic()
        try:
            receipt = session.submit_candidate(network, modules=[r["path"]],
                                               scored={k: block[k] for k in Session.SCORED_COMPILED if k in block})
        except ToolError as exc:
            log(f"NOT READY: the submission of {r['path']} was refused before the service saw it: {exc}")
            return 1, submitted
        submitted = True
        full = session.receipts()[-1]
        log(f"submitting {block.get('checker')}, as the agent would: the check took {time.monotonic() - t0:.0f} s{steps_text(full)}")
        if not scored_line(full, log):
            status = 1
    return status, submitted


def check_lock(earlier: Path, now: Path, project: Path, log) -> int:
    """The lock of the carried proof, read from the submission of the earlier run (as that run's service compiled
    it) and from the submission just made (as the service compiles it now). 0 when both can be read and name the
    same checker."""
    from .lock import LockError, LockUnread, read_lock

    locks = {}
    for what, folder in (("the earlier run's submission", earlier), ("the submission just made", now)):
        try:
            locks[what] = read_lock(folder, project)
        except LockUnread as exc:
            log(f"NOT READY for the seed check: {what} ({folder}) cannot be read for the lock: {exc}. If no proof of the run "
                "scores better than the carried one, the run halts when its proof rounds are over.")
            return 1
        except LockError as exc:
            log(f"NOT READY for the seed check: the carried proof cannot be locked ({what}): {exc}")
            return 1
    was, new = locks.values()
    differ = [key for key in ("checker", "sound_statement", "context") if was["fingerprints"][key] != new["fingerprints"][key]]
    if differ:
        log("NOT READY for the seed check: the carried proof's checker, as the earlier run's service compiled it, is not "
            f"the checker the service compiles from the same modules now (differs in: {', '.join(differ)}). A seed check "
            "that locks the carried proof would come out unverified. A proof scored in this run is locked as this "
            "run's service compiled it, and does not have this problem.")
        return 1
    log(f"the lock: the carried proof can be locked ({len(was['modules'])} locked modules, {len(was['free'])} free), and its "
        "checker is the same compiled then and now")
    return 0


def check_best(session: Session, best: dict | None, manifest: dict, log, lock: bool = False, project: Path | None = None) -> int:
    """Submit the best carried scored proof again, from the session's workspace. 0 when it is accepted and scored
    (and, with `lock`, when the lock read from it is the one read from the earlier run's submission). A run
    whose checker the service runs compiled submits it without its instance: the checker's modules alone."""
    if best is None:
        log("no scored proof is carried: nothing to submit again")
        return 0
    scored = manifest.get("scored") or {}
    earlier = Path(best["source"][: -len(best["path"])])
    log(f"submitting it again: {manifest.get('theorem') or scored.get('sound')}, as the agent would")
    t0 = time.monotonic()
    try:
        if session.compiled:
            modules = list(manifest["modules"])
            if scored.get("run") != "compiled":  # proved with an instance: its checker's modules are what its lock holds
                from .lock import LockError, LockUnread, read_lock

                try:
                    modules = sorted(read_lock(earlier, project or session.lean_project)["modules"])
                except LockUnread as exc:
                    log("NOT READY: the carried proof was proved with an instance theorem. Which of its modules hold the "
                        "checker is read from what the earlier run's service compiled, and that cannot be read here "
                        f"({exc})")
                    return 1
                except LockError as exc:
                    log(f"NOT READY: the carried proof was proved with an instance theorem, and its checker's modules cannot "
                        f"be told from the instance's ({exc}): it cannot be submitted again without the instance")
                    return 1
                log(f"  without its instance: the {len(modules)} modules of its checker and soundness proof")
            session.submit_candidate(manifest["network"], modules=modules,
                                     scored={k: scored[k] for k in Session.SCORED_COMPILED if k in scored})
        elif scored.get("run") == "compiled":
            log("NOT READY: the carried proof has no instance theorem (the service ran its checker); a run with "
                "open_lane.instance kernel cannot submit it again")
            return 1
        else:
            session.submit_candidate(manifest["network"], int(manifest["claimed_count"]), manifest["theorem"],
                                     list(manifest["modules"]), manifest.get("scored"), manifest.get("kind", "performance"))
    except ToolError as exc:
        log(f"NOT READY: the submission was refused before the service saw it: {exc}")
        return 1
    receipt = session.receipts()[-1]  # the receipt as the service wrote it, with its steps
    log(f"the check took {time.monotonic() - t0:.0f} s{steps_text(receipt)}")
    if not scored_line(receipt, log):
        return 1
    length = (receipt.get("scoring") or {}).get("length")
    if best.get("length") and length != best["length"]:
        log(f"  note: the earlier receipt's length was {best['length']:,}")
    if lock and project is not None:
        return check_lock(earlier, session.path / "submissions" / f"{int(receipt.get('submission') or 0):03d}", project, log)
    return 0


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(prog="python3 -m core.open_lane.dry_start", description=__doc__.split("\n\n")[0])
    ap.add_argument("--config", required=True)
    ap.add_argument("--check", action="store_true", help="submit the best carried scored proof again and time the check")
    ap.add_argument("--keep", action="store_true", help="leave the dry start's folder (<runs_dir>/_dry_start/<run_id>)")
    ap.add_argument("--set", action="append", default=[], metavar="KEY=VALUE", help="a setting of the run config, as core.loop run takes it")
    ap.add_argument("--sandbox", help="the run's sandbox (as core.loop run --sandbox)")
    args = ap.parse_args(argv)
    try:
        overrides = parse_overrides(args.set)
        if args.sandbox:
            overrides["sandbox"] = args.sandbox
        cfg = load_run_config(args.config, overrides=overrides or None)
        return run(cfg, args.check, args.keep)
    except (LoopError, RunConfigError, continuation.ContinuationError, ToolError) as exc:
        print(f"NOT READY: {exc}")
        return 1


if __name__ == "__main__":
    sys.exit(main())
