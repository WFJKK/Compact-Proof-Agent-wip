"""One round: responses in, checked result records out.

A round folder holds one attempt per response:

    round_007/
        prompt.md                  the prompt sent (from Step 7 on)
        attempt_0/
            response.md            the raw response, saved before parsing
            response_meta.json     backend, tokens, cost
            parsed.json            claim, why, prediction, knob, notes, warnings; or the parse error
            recipe.py
            proofs/<network>__k<knob>.json.gz   (or __b<budget> when scoring at fixed budgets)
            results.json           one record per network and knob, written last
        meta.json                  versions, timings, totals
        DONE                       written last

An attempt whose results.json exists is complete and is never redone. A round
without DONE is finished on resume, reusing any response it already saved, so
no response is ever asked for twice.

For each attempt: parse the response, run the recipe in the sandbox once per
development network and knob value (or fixed budget), check every proof file, and write one
record each. With screening on, the recipe runs on one network per size
setting first, and on the rest only if it certified something there.
"""

from __future__ import annotations

import gzip
import json
import math
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed
from dataclasses import dataclass, field
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable

from .agent.parse import ParseError, parse_response
from .archive import RunDir, knob_label, record_id
from .check.worker import CheckerError, CheckerProcess
from .model_folder import ModelFolder
from .runner import Execution, Limits, run_recipe
from .sandbox import Sandbox
from .scoring import budget_grid, budget_position, default_budget_ratio
from .util import REPO_ROOT, git_state, sha256_bytes
from .versions import changed
from .zoo import load_weights


class RoundError(RuntimeError):
    pass


@dataclass
class Context:
    cfg: dict
    folder: ModelFolder
    run: RunDir
    entries: list[dict]
    versions: dict
    limits: Limits
    sandbox: Sandbox = field(default_factory=lambda: Sandbox("process"))
    log: Callable = print
    since: float = field(default_factory=time.time)
    held_out: bool = False  # True only in core.final's evaluation on held-out networks
    _weights: dict = field(default_factory=dict, repr=False)
    _lock: threading.Lock = field(default_factory=threading.Lock, repr=False)

    @property
    def rule_set(self) -> tuple:
        return tuple(self.cfg["rule_set"])

    def weights(self, network_id: str) -> dict:
        with self._lock:
            if network_id not in self._weights:
                self._weights[network_id] = load_weights(self.folder, network_id, allow_held_out=self.held_out)
            return self._weights[network_id]

    def info(self, entry: dict, budget: int | None = None) -> dict:
        info = {"sizes": self.folder.sizes(entry["setting"]), "input_space": self.folder.input_space(entry["setting"])}
        if budget is not None:  # scoring at fixed budgets: the recipe is told its budget, E and B
            info.update(budget=int(budget), E=int(entry["E"]), B=int(entry["B"]))
        return info

    def jobs(self, entries: list[dict]) -> list[tuple[dict, float, int | None]]:
        """What to run a recipe at: (network, knob, budget) for every network and knob value, or fixed budget."""
        if self.cfg["metric"] == "Q_grid":
            out = []
            for e in entries:
                for b in budget_grid(e["E"], e["B"], self.cfg.get("budget_ratio") or default_budget_ratio()):
                    out.append((e, budget_position(b, e["E"], e["B"]), b))
            return out
        return [(e, float(kn), None) for e in entries for kn in self.cfg["knob_values"]]

    def verify_trusted(self) -> None:
        bad = changed(self.versions, self.folder)
        if bad:
            raise RoundError(f"trusted files changed during the run ({', '.join(bad)}); the run halts")
        planted = compiled_files_since([REPO_ROOT / "core", REPO_ROOT / "rules", self.folder.path], self.since)
        if planted:
            raise RoundError(f"compiled files appeared in trusted folders during the run ({', '.join(planted[:3])}); the run halts")


def compiled_files_since(roots, since: float) -> list[str]:
    """Bytecode files under roots, written after since, that this interpreter could load.

    The pipeline writes none (core/__init__.py turns bytecode writing off). In a
    __pycache__ folder an interpreter only ever loads files with its own cache tag
    (cpython-313, say), so a file another Python version wrote there, for example
    a second run started from a different interpreter, cannot change this run and
    is ignored. Files with this interpreter's tag, and bytecode outside __pycache__,
    always count.
    """
    tag = sys.implementation.cache_tag
    out = []
    for root in roots:
        for p in Path(root).rglob("*"):
            if p.suffix not in (".pyc", ".pyo") or not p.is_file():
                continue
            if tag is not None and p.parent.name == "__pycache__" and f".{tag}." not in p.name:
                continue  # another interpreter's cache
            try:
                if p.stat().st_mtime >= since:
                    out.append(str(p))
            except OSError:
                pass
    return sorted(out)


def now() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def screen_entries(entries: list[dict]) -> list[dict]:
    """The first development network of each size setting."""
    seen, out = set(), []
    for e in entries:
        if e["setting"] not in seen:
            seen.add(e["setting"])
            out.append(e)
    return out


def promising(records: list[dict]) -> bool:
    return any(r["status"] == "ok" and (r.get("certified") or 0) > 0 for r in records)


# records ---------------------------------------------------------------------------
def _base(ctx: Context, k: int, j: int, source: str) -> dict:
    return {"run_id": ctx.run.run_id, "round": k, "attempt": j, "source": source, "model": ctx.folder.name}


def _empty_result_fields() -> dict:
    return {
        "uncertified_by_group": None,
        "uncertified_summary": None,
        "rejected_summary": None,
        "certified": None,
        "certified_accuracy": None,
        "certified_accuracy_float": None,
        "length": None,
        "length_by_rule": None,
        "leaves": None,
        "pieces_accepted": None,
        "rejected": [],
        "checked_by": None,
        "check_s": None,
        "proof_sha256": None,
        "proof_bytes": None,
    }


def parse_record(ctx: Context, k: int, j: int, source: str, error: str) -> dict:
    return {
        **_base(ctx, k, j, source),
        "record_id": record_id(ctx.run.run_id, k, j),
        "network": None,
        "setting": None,
        "knob": None,
        "status": "parse",
        "error": error,
        "runtime_s": 0.0,
        "peak_rss_mb": None,
        "sandbox": None,
        **_empty_result_fields(),
        "versions": ctx.versions,
    }


def _check(ctx: Context, checker: CheckerProcess, entry: dict, proof_path: Path, sha: str, cache: dict):
    """Check a proof once per network and proof content, in the checker process; returns (result, diagnosis, seconds)."""
    key = (entry["id"], sha)
    if key not in cache:
        ctx.verify_trusted()
        t = time.monotonic()
        try:
            result, diag = checker.check(entry["id"], proof_path, ctx.rule_set)
        except CheckerError as exc:
            raise RoundError(f"the checker failed on {entry['id']}: {exc}") from exc
        cache[key] = (result, diag, round(time.monotonic() - t, 3))
    return cache[key]


def _divisor(B: float, budget: float, ratio: float) -> float:
    """The budget as a nominal fraction of B: ratio, ratio squared, ... (budgets are rounded down, so B/budget is not exact)."""
    return float(ratio ** round(math.log(B / budget) / math.log(ratio)))


def execution_record(
    ctx: Context, k: int, j: int, source: str, entry: dict, knob, ex: Execution, cache: dict, checker: CheckerProcess, budget=None
) -> dict:
    nid = entry["id"]
    rec = {
        **_base(ctx, k, j, source),
        "record_id": record_id(ctx.run.run_id, k, j, nid, knob, budget),
        "network": nid,
        "setting": entry["setting"],
        "knob": float(knob),
        "budget": None if budget is None else int(budget),
        "budget_divisor": None if budget is None else _divisor(entry["B"], budget, ctx.cfg.get("budget_ratio") or default_budget_ratio()),
        "status": ex.status,
        "error": ex.error,
        "runtime_s": ex.runtime_s,
        "peak_rss_mb": ex.peak_rss_mb,
        "sandbox": ex.mode,
        **_empty_result_fields(),
        "n_inputs": entry["n_inputs"],
        "real_correct": entry.get("real_correct"),
        "real_accuracy": entry.get("real_accuracy"),
        "E": entry.get("E"),
        "B": entry.get("B"),
        "versions": ctx.versions,
    }
    rec["proof_bytes"] = ex.proof_bytes
    if ex.status != "ok":
        return rec

    proof = ex.proof
    if "network" not in proof:
        proof["network"] = nid  # the recipe never learns its network; a proof naming another one is rejected
    data = json.dumps(proof, separators=(",", ":"), ensure_ascii=False).encode()
    sha = sha256_bytes(data)
    path = ctx.run.write(k, f"attempt_{j}/proofs/{nid}__{knob_label(knob, budget)}.json.gz", gzip.compress(data, mtime=0))
    result, diag, seconds = _check(ctx, checker, entry, path, sha, cache)
    rec.update(proof_sha256=sha, checked_by="python", check_s=seconds)
    if result["status"] != "ok":
        rec.update(status="bad_output", error=f"the checker rejected the proof: {result['reason']}")
        return rec
    # A sound checker never certifies an input the network gets wrong. This is the one invariant a proof
    # cannot fake, so a violation halts the run instead of becoming a record. The reference is the checker's
    # own exact count when the zoo has it (core.check.exact_counts), else the float count.
    reference = entry.get("checked_correct") if entry.get("checked_correct") is not None else entry.get("real_correct")
    if reference is not None and result["certified"] > reference:
        raise RoundError(
            f"{nid}: the checker certified {result['certified']} inputs but the network gets only {reference} right "
            f"(proof {path}); the checker or the zoo is unsound, so the run halts"
        )
    rec.update(
        certified=result["certified"],
        certified_accuracy=result["certified_accuracy"],
        certified_accuracy_float=result["certified_accuracy_float"],
        length=result["length"],
        length_by_rule=result["length_by_rule"],
        leaves=result["leaves"],
        pieces_accepted=result["leaves"]["accepted"],
        rejected=result["rejected_pieces"],
        symmetry=result.get("symmetry", False),
        **diag,
    )
    return rec


# attempts --------------------------------------------------------------------------
def _execute(ctx: Context, k: int, j: int, source: str, recipe: str, jobs: list, cache: dict, checker: CheckerProcess) -> list[dict]:
    records = []
    if not jobs:
        return records

    def one(entry, knob, budget):
        return run_recipe(
            recipe,
            ctx.folder.source(),
            ctx.weights(entry["id"]),
            ctx.info(entry, budget),
            knob,
            ctx.limits,
            ctx.cfg["sandbox_dir"],
            sandbox=ctx.sandbox,
        )

    with ThreadPoolExecutor(max_workers=ctx.cfg["workers"]) as pool:
        futures = {pool.submit(one, entry, knob, budget): (entry, knob, budget) for entry, knob, budget in jobs}
        for fut in as_completed(futures):
            entry, knob, budget = futures[fut]
            rec = execution_record(ctx, k, j, source, entry, knob, fut.result(), cache, checker, budget)
            records.append(rec)
            ctx.log(_line(rec))
    return records


def _line(rec: dict) -> str:
    head = f"    {rec['network']} {knob_label(rec['knob'], rec.get('budget'))}: {rec['status']}"
    if rec["status"] == "ok":
        return f"{head}, certified {rec['certified']}/{rec['n_inputs']}, length {rec['length']:,}"
    return f"{head}: {(rec['error'] or '').splitlines()[-1][:120] if rec['error'] else ''}"


def _open_line(rec: dict) -> str:
    head = f"    {rec.get('network') or '-'} submission {rec.get('submission', '-')}: {rec['status']}"
    if rec["status"] == "ok":
        return f"{head}, certified {rec['certified']}/{rec['n_inputs']}, length {rec['length']:,}"
    if rec["status"] == "verified":
        return f"{head}, certified {rec['certified']}/{rec['n_inputs']}; {(rec.get('error') or '')[:120]}"
    return f"{head}: {(rec.get('error') or '').splitlines()[-1][:120] if rec.get('error') else ''}"


def run_attempt(ctx: Context, k: int, j: int, source: str, text: str) -> list[dict]:
    """Parse one response, run and check its recipe, and write the attempt's results. Idempotent.

    In an open-lane agent round the response is notes and the records come from the session's receipts
    (core.open_lane.records); nothing is parsed or run."""
    rel = f"attempt_{j}"
    done = ctx.run.read(k, f"{rel}/results.json")
    if done is not None:
        return done
    if k > 0 and ctx.cfg.get("open_lane", {}).get("enabled"):
        from .open_lane.records import open_lane_records

        try:
            records = open_lane_records(ctx, k, j, source)
        except RuntimeError as exc:
            raise RoundError(str(exc)) from exc
        for r in records:
            ctx.log(_open_line(r))
        ctx.run.write(k, f"{rel}/results.json", records)
        return records
    try:
        parsed = parse_response(text)
    except ParseError as exc:
        ctx.log(f"  attempt {j}: parse error: {exc}")
        ctx.run.write(k, f"{rel}/parsed.json", {"error": str(exc)})
        records = [parse_record(ctx, k, j, source, str(exc))]
        ctx.run.write(k, f"{rel}/results.json", records)
        return records
    ctx.run.write(k, f"{rel}/parsed.json", parsed.summary())
    ctx.run.write(k, f"{rel}/recipe.py", parsed.recipe)

    cache: dict = {}
    if ctx.cfg["screen"]:
        first = screen_entries(ctx.entries)
        rest = [e for e in ctx.entries if e not in first]
    else:
        first, rest = ctx.entries, []
    ctx.verify_trusted()
    try:
        checker = CheckerProcess(
            ctx.folder.path, ctx.versions, held_out=ctx.held_out, timeout_s=ctx.cfg["check_timeout_s"]
        )
    except CheckerError as exc:
        raise RoundError(f"the checker could not start: {exc}") from exc
    with checker:
        records = _execute(ctx, k, j, source, parsed.recipe, ctx.jobs(first), cache, checker)
        if rest:
            if promising(records):
                records += _execute(ctx, k, j, source, parsed.recipe, ctx.jobs(rest), cache, checker)
            else:
                ctx.log(f"  attempt {j}: certified nothing on the screening networks; not run on the rest")
    order = {e["id"]: i for i, e in enumerate(ctx.entries)}
    records.sort(key=lambda r: (order[r["network"]], r["knob"]))
    ctx.run.write(k, f"{rel}/results.json", records)
    return records


def attempt_summary(records: list[dict], response_meta: dict | None) -> dict:
    statuses: dict[str, int] = {}
    for r in records:
        statuses[r["status"]] = statuses.get(r["status"], 0) + 1
    return {
        "source": (response_meta or {}).get("source"),
        "statuses": statuses,
        "executions": sum(1 for r in records if r["network"] is not None),
        "recipe_seconds": round(sum(r.get("runtime_s") or 0 for r in records), 2),
        "check_seconds": round(sum(r.get("check_s") or 0 for r in records), 2),
    }


# rounds ----------------------------------------------------------------------------
def run_round(ctx: Context, k: int, backend, first_index: int, n_attempts: int, source: str, prompt=None) -> dict:
    """Run round k with up to n_attempts responses from backend, numbered from first_index; then mark it done.

    prompt is a core.agent.build_prompt.Prompt; the round keeps the first one it was given, so a resumed
    round sends exactly the prompt it saved.
    """
    if ctx.run.round_done(k):
        return ctx.run.read(k, "meta.json")
    started, t0 = now(), time.monotonic()
    ctx.log(f"round {k} ({source})")
    if prompt is not None and ctx.run.read(k, "prompt.json") is None:
        ctx.run.write(k, "prompt.md", prompt.text)
        ctx.run.write(k, "prompt.json", prompt.as_json())
    attempts, tokens_in, tokens_out, cost = [], 0, 0, 0.0
    for j in range(n_attempts):
        rel = f"attempt_{j}"
        text = ctx.run.read(k, f"{rel}/response.md")
        if text is None:
            if not backend.available(first_index + j):
                break
            where = ctx.run.round_path(k) / rel
            where.mkdir(parents=True, exist_ok=True)
            resp = backend.respond(prompt, first_index + j, where)
            ctx.run.write(k, f"{rel}/response.md", resp.text)  # first, so a paid response is never lost
            ctx.run.write(k, f"{rel}/response_meta.json", resp.meta)
            text = resp.text
        meta = ctx.run.read(k, f"{rel}/response_meta.json") or {}
        ctx.log(f"  attempt {j}: {meta.get('source') or meta.get('backend', '')}")
        ctx.verify_trusted()
        records = run_attempt(ctx, k, j, source, text)
        ctx.run.append_archive(records)
        attempts.append(attempt_summary(records, meta))
        tokens_in += int(meta.get("input_tokens") or 0)
        tokens_out += int(meta.get("output_tokens") or 0)
        cost += float(meta.get("cost_usd") or 0.0)
    round_meta = {
        "round": k,
        "source": source,
        "backend": getattr(backend, "name", None),
        "attempts": attempts,
        "versions": ctx.versions,
        "git": git_state(),
        "sandbox": ctx.sandbox.describe(),
        "limits": {"time_s": ctx.limits.time_s, "memory_mb": ctx.limits.memory_mb, "max_proof_bytes": ctx.limits.max_proof_bytes},
        "prompt": (ctx.run.read(k, "prompt.json") or {}).get("stats"),
        "tokens": {"input": tokens_in, "output": tokens_out},
        "cost_usd": round(cost, 4),
        "started": started,
        "finished": now(),
        "seconds": round(time.monotonic() - t0, 1),
    }
    ctx.run.write(k, "meta.json", round_meta)
    ctx.run.mark_done(k)
    return round_meta
