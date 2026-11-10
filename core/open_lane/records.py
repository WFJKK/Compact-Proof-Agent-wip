"""Archive records of an open-lane attempt, from the acceptance service's receipts.

One record per submission. Its status is `ok` when the submission was verified and scored: it then has a
certified count and a length in cost-v3 units, and enters the frontier as a proof file's record does.
`verified` means accepted without a length (no scoring, or scoring refused): the count is recorded, the
frontier does not see it. `lemma` is an accepted auxiliary submission (a statement, no count). The other
statuses are the receipt's (rejected, unsupported, timeout, error). An attempt that submitted nothing gets
one record of status `no_submission`, so the round is never empty.

A count above the exact reference count of the zoo (`checked_correct` with `checked_semantics` exact, from
`python -m core.check.exact_counts`) halts the run; above the float count alone it is flagged, since the
float count only approximates the real-semantics count.
"""

from __future__ import annotations

from ..archive import record_id
from .session import Session


def _fields() -> dict:
    return {"uncertified_by_group": None, "uncertified_summary": None, "rejected_summary": None, "certified": None,
            "certified_accuracy": None, "certified_accuracy_float": None, "length": None, "length_by_rule": None,
            "leaves": None, "pieces_accepted": None, "rejected": [], "checked_by": None, "check_s": None,
            "proof_sha256": None, "proof_bytes": None}


IDENTITY_KEYS = ("commit", "toolchain", "lean_project", "policy", "acceptcheck")


def check_receipt_identity(receipt: dict, expected: dict | None) -> None:
    """A receipt is evidence only from the service the run started with. An accepted receipt must carry the
    whole identity (the five digests of `accept.py identity`, the binary included) and every field must
    match; a receipt the service rejected before it was complete is checked on the fields it has. A
    mismatch or a missing field halts the run: the service changed under it, or the receipt is not one
    the pipeline can vouch for."""
    if not expected:
        raise RuntimeError(f"{receipt.get('receipt_path')}: the run recorded no Lean checker identity to check this receipt against; the run halts")
    digests = receipt.get("digests") or {}
    where = receipt.get("receipt_path")
    if receipt.get("status") == "accepted":
        missing = [k for k in IDENTITY_KEYS if not digests.get(k)]
        if missing:
            raise RuntimeError(f"{where}: an accepted receipt without the service's {', '.join(missing)}; the run halts")
    off = [k for k in IDENTITY_KEYS if digests.get(k) and digests[k] != expected.get(k)]
    if off:
        raise RuntimeError(
            f"{where}: the receipt's {', '.join(off)} differ from the Lean checker this run started with; "
            "the service changed under the run, so the run halts"
        )


def open_lane_records(ctx, k: int, j: int, source: str) -> list[dict]:
    """The records of attempt j of round k, from its session's receipts (none if there is no session)."""
    path = ctx.run.round_path(k) / f"attempt_{j}" / "open_lane"
    if not (path / "session.json").is_file():
        return []
    session = Session(path)
    base = {"run_id": ctx.run.run_id, "round": k, "attempt": j, "source": source, "model": ctx.folder.name, "lane": "open"}
    by_id = {e["id"]: e for e in ctx.entries}
    out = []
    for receipt in session.receipts():
        n = receipt.get("submission", len(out))
        nid = receipt.get("network")
        entry = by_id.get(nid)
        rec = {
            **base,
            "record_id": f"{ctx.run.run_id}/r{k:03d}/a{j}/{nid or 'none'}/open{n:03d}",
            "network": nid if entry else None,
            "setting": entry["setting"] if entry else None,
            "knob": None,
            "budget": None,
            "budget_divisor": None,
            "submission": n,
            "candidate_id": receipt.get("candidate_id"),
            "theorem": receipt.get("theorem"),
            "claimed_count": receipt.get("claimed_count"),
            "status": None,
            "error": None,
            "runtime_s": receipt.get("seconds") or 0.0,
            "peak_rss_mb": None,
            "sandbox": receipt.get("isolation"),
            **_fields(),
            "axioms": receipt.get("axioms"),
            "receipt": {k_: receipt.get(k_) for k_ in ("status", "reason", "scoring", "digests", "receipt_path")},
            "versions": ctx.versions,
        }
        if entry:
            rec.update(n_inputs=entry["n_inputs"], real_correct=entry.get("real_correct"), real_accuracy=entry.get("real_accuracy"),
                       E=entry.get("E"), B=entry.get("B"))
        check_receipt_identity(receipt, (ctx.versions or {}).get("lean_checker"))
        status = receipt.get("status")
        if status != "accepted" or not entry:
            rec.update(status=status if status in ("rejected", "unsupported", "timeout", "error") else "error",
                       error=receipt.get("reason") or ("the receipt names no network of this run" if not entry else "no reason given"))
            out.append(rec)
            continue
        if receipt.get("claim_kind") == "auxiliary":
            rec.update(status="lemma", statement=receipt.get("statement"), error=None)
            out.append(rec)
            continue
        certified = int(receipt["certified_count"])
        if certified > entry["n_inputs"]:
            raise RuntimeError(f"{nid}: the Lean service certified {certified} inputs of {entry['n_inputs']} ({receipt.get('receipt_path')}); the run halts")
        checked, semantics = entry.get("checked_correct"), entry.get("checked_semantics")
        real = entry.get("real_correct")
        if checked is not None and semantics == "exact" and certified > checked:
            # both counts are exact over the rationals, so this is unsoundness somewhere: the run halts
            raise RuntimeError(
                f"{nid}: the Lean service certified {certified} inputs but the exact count is {checked} "
                f"({receipt.get('receipt_path')}); the checker or the zoo is unsound, so the run halts"
            )
        if real is not None and certified > real:
            # the float count is an approximation of the real-semantics count (python -m core.check.exact_counts
            # audits it); a Lean count above it is recorded and flagged, not treated as a disproof
            rec["reference_warning"] = f"certified {certified} is above the float count {real}; the reference count is inexact"
        rec.update(certified=certified, certified_accuracy=f"{certified}/{entry['n_inputs']}",
                   certified_accuracy_float=certified / entry["n_inputs"], checked_by="lean", check_s=receipt.get("seconds"))
        scoring = receipt.get("scoring") or {}
        if scoring.get("status") == "scored":
            rec.update(status="ok", length=int(scoring["length"]),
                       length_by_rule={"bill": scoring.get("bill"), "extract": scoring.get("extract"), "read": scoring.get("read")},
                       description_size=scoring.get("description_size"))
        else:
            rec.update(status="verified", error=("not scored: " + (scoring.get("reason") or "no scored block in the manifest")))
        out.append(rec)
    if not out:
        out.append({**base, "record_id": record_id(ctx.run.run_id, k, j), "network": None, "setting": None, "knob": None,
                    "budget": None, "status": "no_submission", "error": "the session submitted no candidate", "runtime_s": 0.0,
                    "peak_rss_mb": None, "sandbox": None, **_fields(), "versions": ctx.versions})
    return out
