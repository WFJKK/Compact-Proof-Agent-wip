"""Lean spot checks: when a recipe enters the frontier, check a proof file or two in Lean as well.

A model folder opts in with `lean_check` in its config.yaml: the command that
checks one proof file, as a list of strings in which {proof} stands for a JSON
proof file and {weights} for the network's .npz weights. It runs in the model
folder's lean/ folder (or the model folder), and its last line of output is a
JSON object with "certified": how many inputs the Lean checker certifies, and,
when the checker rejects the proof, "status": "rejected" and a "reason". A
rejection is not a count of zero: it is recorded as such, and halts the run as
a disagreement does. If Lean and the Python checker disagree, the run halts
and says where.

Every spot check is appended to the run's lean.jsonl. No model folder names
a Lean checker yet, so every result is still labelled Python-checked. The
Lean checker itself (CompactCheck, a separate repository) checks linear and
attention proofs; its open lane, for proofs that are not proof files, has its
own service (scripts/accept.py there).
"""

from __future__ import annotations

import gzip
import json
import subprocess
import tempfile
from pathlib import Path

from .archive import knob_label
from .zoo import network_entry, weights_path

SPOT_CHECKS = 2
TIMEOUT_S = 3600


class LeanError(RuntimeError):
    pass


def lean_command(folder) -> list[str] | None:
    cmd = folder.config.get("lean_check")
    return [str(c) for c in cmd] if cmd else None


def run_lean(folder, network_id: str, proof_path: Path) -> int:
    """The Lean checker's certified count; a rejected proof is a LeanError, never a count of zero."""
    r = run_lean_full(folder, network_id, proof_path)
    if r["status"] != "ok":
        raise LeanError(f"the Lean checker rejected the proof: {r['reason']}")
    return r["certified"]


def run_lean_full(folder, network_id: str, proof_path: Path) -> dict:
    """{"status": "ok" | "rejected", "certified": n or None, "reason": str or None}."""
    cmd = lean_command(folder)
    if cmd is None:
        raise LeanError(f"{folder.name} has no Lean checker")
    weights = weights_path(folder, network_entry(folder, network_id))
    args = [c.replace("{proof}", str(proof_path)).replace("{weights}", str(weights)) for c in cmd]
    cwd = folder.path / "lean" if (folder.path / "lean").is_dir() else folder.path
    try:
        r = subprocess.run(args, cwd=cwd, capture_output=True, text=True, timeout=TIMEOUT_S)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise LeanError(f"the Lean checker did not run: {exc}") from exc
    if r.returncode != 0:
        raise LeanError(f"the Lean checker failed (exit code {r.returncode}): {r.stderr[-1000:]}")
    try:
        out = json.loads(r.stdout.strip().splitlines()[-1])
        if not isinstance(out, dict):
            raise TypeError("not an object")
        if out.get("status") not in (None, "ok"):
            return {"status": str(out["status"]), "certified": None, "reason": str(out.get("reason", ""))}
        n = out["certified"]
        if isinstance(n, bool) or not isinstance(n, int) or n < 0:
            raise TypeError(f"certified is {n!r}")
        return {"status": "ok", "certified": n, "reason": None}
    except (IndexError, KeyError, TypeError, ValueError) as exc:
        raise LeanError(f"the Lean checker's output has no certified count: {r.stdout[-300:]!r} ({exc})") from exc


def spot_check(ctx, k: int, records: list[dict], limit: int | None = SPOT_CHECKS) -> list[dict]:
    """Check up to `limit` of these records in Lean (all with None); halt on any disagreement."""
    results = []
    for rec in records if limit is None else records[:limit]:
        gz = ctx.run.round_path(k) / f"attempt_{rec['attempt']}" / "proofs" / f"{rec['network']}__{knob_label(rec['knob'])}.json.gz"
        with tempfile.TemporaryDirectory() as tmp:
            path = Path(tmp) / "proof.json"
            path.write_bytes(gzip.decompress(gz.read_bytes()))
            lean = run_lean_full(ctx.folder, rec["network"], path)
        results.append({"record_id": rec["record_id"], "python": rec["certified"], "lean": lean["certified"],
                        "lean_status": lean["status"], "lean_reason": lean["reason"],
                        "agree": lean["status"] == "ok" and lean["certified"] == rec["certified"]})
    if results:
        with open(ctx.run.path / "lean.jsonl", "a") as f:
            for r in results:
                f.write(json.dumps(r) + "\n")
        ctx.log(f"  Lean spot check: {sum(r['agree'] for r in results)} of {len(results)} agree")
    bad = [r for r in results if not r["agree"]]
    if bad:
        raise LeanError(
            "Lean and the Python checker disagree, so the run halts: "
            + "; ".join(f"{r['record_id']}: Python {r['python']}, Lean "
                        + (f"rejected ({r['lean_reason']})" if r["lean_status"] != "ok" else str(r["lean"])) for r in bad)
        )
    return results
