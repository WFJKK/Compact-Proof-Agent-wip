"""Diagnostics for the agent: where a proof loses accuracy, and where its length goes.

Computed from the checker's detailed result (every leaf's outcome and the
certified mask), the network's float margins and the model's task.group.
Nothing here ever scores; the float margins only help the agent see how far a
failed bound is from the truth.

Every input is decided by one leaf: the leaf holding it, or with the symmetry
rule the leaf holding its sorted version. An uncertified input that the
network classifies correctly was lost by its deciding leaf, for that leaf's
reason: skipped, label not constant, or a margin (bound) that was not
positive, short by some amount. Wrong inputs can never be certified.
"""

from __future__ import annotations

import statistics
from collections import Counter

import numpy as np

from . import inputs
from .model_folder import ModelFolder
from .zoo import load_module, network_entry

MAX_GROUPS = 12
MAX_EXAMPLES = 3
CHUNK = 1 << 13
RULE_ORDER = ("extract", "read", "tree", "contract", "approximate", "single", "interval", "tables", "token_interval", "symmetry")


def rule_order() -> tuple:
    """RULE_ORDER, then the categories of adopted rules (core/check/plugins.py)."""
    from .check.cost import EXTRA_CATEGORIES

    return RULE_ORDER + tuple(sorted(EXTRA_CATEGORIES - set(RULE_ORDER)))


def float_margins(folder: ModelFolder, network_id: str, allow_held_out: bool = False) -> np.ndarray:
    """Per input, in float: the label's output minus the largest other output (not positive when wrong)."""
    import torch

    entry = network_entry(folder, network_id)
    setting = entry["setting"]
    module = load_module(folder, network_id, allow_held_out=allow_held_out)
    toks = inputs.all_inputs(folder.input_space(setting))
    labels = np.asarray(folder.task.label(toks, folder.sizes(setting)), dtype=np.int64)
    out = np.empty(len(toks))
    for i in range(0, len(toks), CHUNK):
        with torch.no_grad():
            x = folder.encode(toks[i : i + CHUNK], setting).to(next(module.parameters()).dtype)
            logits = module(x).double().numpy()
        lab = labels[i : i + CHUNK]
        rows = np.arange(len(lab))
        own = logits[rows, lab].copy()
        logits[rows, lab] = -np.inf
        out[i : i + CHUNK] = own - logits.max(axis=1)
    return out


def _stats(values) -> dict | None:
    values = [float(v) for v in values]
    if not values:
        return None
    return {"min": min(values), "median": statistics.median(values), "max": max(values)}


def diagnose(folder: ModelFolder, entry: dict, result: dict, margins: np.ndarray, correct: np.ndarray) -> dict:
    """The diagnostic fields of one result record, from a checker result made with detail=True."""
    setting = entry["setting"]
    space = folder.input_space(setting)
    toks = inputs.all_inputs(space)
    groups = np.asarray(folder.task.group(toks, folder.sizes(setting)))
    certified = np.asarray(result["mask"], dtype=bool)
    correct = np.asarray(correct, dtype=bool)
    outcomes = result["outcomes"]

    leaf_of = np.full(tuple(space), len(outcomes), dtype=np.int64)  # len(outcomes): no leaf (cannot happen)
    for i, o in enumerate(outcomes):
        leaf_of[tuple(slice(lo, hi + 1) for lo, hi in o["ranges"])] = i
    leaf_of = leaf_of.reshape(-1)
    decider = leaf_of[inputs.input_index(np.sort(toks, axis=1), space)] if result.get("symmetry") else leaf_of
    accepted = np.array([o["accepted"] for o in outcomes] + [False])
    if not np.array_equal(accepted[decider], certified):
        raise RuntimeError("internal error: leaf outcomes and the certified mask disagree")
    reason = np.array([o["reason"] or "" for o in outcomes] + ["no leaf"], dtype=object)
    bound = np.array([o["margin"] if o["margin"] is not None else np.nan for o in outcomes] + [np.nan])

    lost = ~certified & correct
    wrong = ~correct
    per_group = {}
    for g in np.unique(groups[~certified]):
        sel = groups == g
        lost_g = np.flatnonzero(lost & sel)
        wrong_g = np.flatnonzero(wrong & sel)
        d = {
            "inputs": int(sel.sum()),
            "certified": int((certified & sel).sum()),
            "uncertified_correct": int(len(lost_g)),
            "wrong": int(len(wrong_g)),
        }
        if len(lost_g):
            d["why"] = dict(Counter(str(r) for r in reason[decider[lost_g]]))
            short = -bound[decider[lost_g]]
            short = short[~np.isnan(short)]
            if len(short):
                d["worst_shortfall"] = float(short.max())
            d["float_min_margin"] = float(margins[lost_g].min())
            d["examples"] = toks[lost_g[:MAX_EXAMPLES]].tolist()
        if len(wrong_g):
            d["wrong_examples"] = toks[wrong_g[:MAX_EXAMPLES]].tolist()
        per_group[str(g.item() if hasattr(g, "item") else g)] = d
    keep = sorted(per_group, key=lambda k: (-per_group[k]["uncertified_correct"], -per_group[k]["wrong"], k))

    rejected = [o for o in outcomes if not o["accepted"] and o["reason"] != "skipped"]
    shortfalls = [-o["margin"] for o in rejected if o["margin"] is not None]
    return {
        "uncertified_by_group": {k: per_group[k] for k in keep[:MAX_GROUPS]},
        "uncertified_summary": {
            "groups": len(per_group),
            "groups_shown": min(len(per_group), MAX_GROUPS),
            "uncertified_correct": int(lost.sum()),
            "wrong": int(wrong.sum()),
            "certified_but_float_wrong": int((certified & ~correct).sum()),
        },
        "rejected_summary": {
            "count": len(rejected),
            "skipped_leaves": sum(1 for o in outcomes if o["reason"] == "skipped"),
            "by_reason": dict(Counter(o["reason"] for o in rejected)),
            "shortfall": _stats(shortfalls),
        },
    }


# rendering for the prompt -----------------------------------------------------------
def _pct(x: float) -> str:
    return f"{100 * x:.3f}%"


def share(v: float, total: float) -> str:
    x = 100 * v / total if total else 0.0
    return f"{x:.1f}%" if x >= 0.05 else "<0.1%"


def _last_line(text: str | None) -> str:
    lines = [ln for ln in (text or "").splitlines() if ln.strip()]
    return lines[-1][:160] if lines else ""


def _knob(k) -> str:
    return f"{float(k):g}"


def at_label(r: dict) -> str:
    """How one execution is labelled: its fixed budget as B/x when the run scores at budgets, else its knob."""
    if r.get("budget") is not None:
        div = r.get("budget_divisor") or (r["B"] / r["budget"] if r.get("B") else None)
        return f"budget B/{div:g} ({r['budget']:,})" if div else f"budget {r['budget']:,}"
    return f"knob {_knob(r['knob'])}"


_at = at_label


def _median(values):
    values = [v for v in values if v is not None]
    return statistics.median(values) if values else None


def knob_lines(ok: list[dict]) -> tuple[list[str], float]:
    """One line per knob value (identical neighbours merged), and the knob with the best median result."""
    rows, best_knob, best_key = [], None, None
    for k in dict.fromkeys(r["knob"] for r in ok):
        kr = [r for r in ok if r["knob"] == k]
        acc = _median(r["certified"] / r["n_inputs"] for r in kr)
        real = _median(r.get("real_accuracy") for r in kr)
        length = _median(r["length"] for r in kr)
        ratio = _median(r["B"] / r["length"] for r in kr if r.get("B"))
        text = f"certified {_pct(acc)}" + (f" (real {_pct(real)})" if real is not None else "")
        text += f", length {int(length):,}" + (f" (B/{ratio:.1f})" if ratio else "") + f", median of {len(kr)}"
        if rows and rows[-1][2] == text:
            rows[-1][1] = k
        else:
            rows.append([k, k, text])
        if best_key is None or (acc, -length) > best_key:
            best_knob, best_key = k, (acc, -length)
    lines = []
    by_knob = {r["knob"]: r for r in ok}
    for first, last, text in rows:
        if first == last:
            label = _at(by_knob[first])
        elif by_knob[first].get("budget") is not None:
            label = f"budgets B/{by_knob[first]['budget_divisor']:g} to B/{by_knob[last]['budget_divisor']:g}"
        else:
            label = f"knobs {_knob(first)} to {_knob(last)}"
        lines.append(f"  {label}: {text}")
    return lines, best_knob


def render_attempt(records: list[dict], grouping: str = "group") -> str:
    """A few lines per size setting: statuses, the knob curve, and where accuracy and length go."""
    if len(records) == 1 and records[0]["status"] == "parse":
        return f"status parse: {records[0]['error']}"
    lines = []
    for s in dict.fromkeys(r["setting"] for r in records):
        rs = [r for r in records if r["setting"] == s]
        nets = sorted({r["network"] for r in rs})
        status = Counter(r["status"] for r in rs)
        lines.append(
            f"{s} ({len(nets)} network{'s' if len(nets) != 1 else ''}, {len(rs)} runs): "
            + ", ".join(f"{k} {v}" for k, v in sorted(status.items()))
        )
        for st in ("crash", "timeout", "bad_output"):
            for e, n in Counter(_last_line(r["error"]) for r in rs if r["status"] == st).most_common(2):
                lines.append(f"  {st} x{n}: {e}")
        ok = [r for r in rs if r["status"] == "ok"]
        if not ok:
            continue
        knob_lines_, best = knob_lines(ok)
        lines += knob_lines_
        kr = [r for r in ok if r["knob"] == best]
        at = f" at {_at(kr[0])}" if len(knob_lines_) > 1 else ""

        mid = sorted(kr, key=lambda r: r["length"])[len(kr) // 2]
        parts = [(c, mid["length_by_rule"].get(c, 0)) for c in rule_order() if mid["length_by_rule"].get(c)]
        lines.append(
            f"  length by rule{at} ({mid['network']}): "
            + ", ".join(f"{c} {share(v, mid['length'])}" for c, v in parts)
        )

        rej = [r.get("rejected_summary") or {} for r in kr]
        counts = [x.get("count", 0) for x in rej]
        if any(counts):
            reasons: Counter = Counter()
            for x in rej:
                reasons.update(x.get("by_reason") or {})
            shorts = [x["shortfall"] for x in rej if x.get("shortfall")]
            text = f"  rejected pieces{at}: {statistics.median(counts):g} per network (median); over all networks: "
            text += ", ".join(f"{k} {v}" for k, v in reasons.most_common())
            if shorts:
                text += f"; bounds short by {min(x['min'] for x in shorts):.3g} to {max(x['max'] for x in shorts):.3g}"
            lines.append(text)

        lost: dict[str, dict] = {}
        wrong: dict[str, Counter] = {}
        for r in kr:
            for g, d in (r.get("uncertified_by_group") or {}).items():
                if d["uncertified_correct"]:
                    e = lost.setdefault(g, {"n": 0, "nets": 0, "why": Counter(), "short": 0.0, "margin": None, "ex": None})
                    e["n"] += d["uncertified_correct"]
                    e["nets"] += 1
                    e["why"].update(d.get("why") or {})
                    e["short"] = max(e["short"], d.get("worst_shortfall") or 0.0)
                    m = d.get("float_min_margin")
                    if m is not None and (e["margin"] is None or m < e["margin"]):
                        e["margin"] = m
                    e["ex"] = e["ex"] or d.get("examples")
                for ex in d.get("wrong_examples") or []:
                    wrong.setdefault(g, Counter())[tuple(ex)] += 1
        if lost:
            top = sorted(lost.items(), key=lambda kv: -kv[1]["n"])[:4]
            descr = []
            for g, e in top:
                bits = f"{grouping} {g}: {e['n']} on {e['nets']} network{'s' if e['nets'] != 1 else ''} ("
                bits += ", ".join(w for w, _ in e["why"].most_common(2))
                if e["short"]:
                    bits += f", short by up to {e['short']:.3g}"
                if e["margin"] is not None:
                    bits += f"; true float margin at least {e['margin']:.3g}"
                bits += f"; e.g. {list(e['ex'][0])})" if e["ex"] else ")"
                descr.append(bits)
            more = len(lost) - len(top)
            lines.append(
                f"  correct but uncertified{at}: "
                + "; ".join(descr)
                + (f"; and {more} more groups" if more > 0 else "")
            )
        if wrong:
            items = sorted(wrong.items(), key=lambda kv: (-sum(kv[1].values()), kv[0]))
            shown = []
            for g, c in items[:5]:
                pairs = ", ".join(f"{list(ex)} on {n}" for ex, n in c.most_common(3))
                shown.append(f"{grouping} {g}: {pairs}")
            lines.append(
                "  wrong inputs, never certifiable (examples, with the number of networks): "
                + "; ".join(shown)
                + (" ..." if len(items) > 5 else "")
            )
    return "\n".join(lines)
