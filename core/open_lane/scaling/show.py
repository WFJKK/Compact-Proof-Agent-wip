"""What the status and the report show of a run's scaling proofs (read from stages.json, `scaling_proofs`)."""

from __future__ import annotations

from ...archive import RunDir
from .. import stages
from . import links, plan, prompt
from . import sizes as network_sizes


def step_line(step: dict, proofs: list[dict]) -> str:
    res = step.get("result")
    head = f"{plan.name(step)} (round {step['round']})"
    if res is None:
        return head + ": not done yet"
    n = len(res["lemmas"])
    said = sum(1 for l in res["lemmas"] if links.about(l, proofs))
    return (f"{head}: {n} lemma(s) accepted, {said} with a submitted proof's checker in its statement"
            + (f"; ${res['cost_usd']:.2f}" if isinstance(res.get("cost_usd"), (int, float)) and res["cost_usd"] else ""))


def links_status(sp: dict, sizes: list[dict]) -> list[str]:
    """Per size, which links an accepted theorem holds, by the sessions' own account."""
    table = links.table(sp["steps"])
    if not table:
        return []
    lines = [f"theorems per size ({', '.join(links.LINKS)}), by the sessions' own account of what each says:"]
    for size in sizes:
        row = table.get(size["symbol"]) or {}
        have = [k for k in links.LINKS if links.held(row.get(k))]
        lines.append(f"  {size['symbol']}: " + (", ".join(have) if have else "none") +
                     ("" if len(have) == len(links.LINKS) else "; missing: " + ", ".join(k for k in links.LINKS if k not in have)))
    return lines


def _read(run: RunDir) -> tuple[dict | None, list[dict]]:
    sp = (stages.read_state(run) or {}).get("scaling_proofs")
    return (sp, network_sizes.stored(sp, run.config())) if sp else (None, [])


def status_lines(run: RunDir) -> list[str]:
    sp, sizes = _read(run)
    if not sp:
        return []
    return (["scaling proofs (after the run, never scored):"] + ["  " + step_line(s, sp["proofs"]) for s in sp["steps"]]
            + ["  " + line for line in links_status(sp, sizes)])


def report_lines(run: RunDir) -> list[str]:
    sp, sizes = _read(run)
    if not sp:
        return []
    lines = ["## The scaling proofs", "",
             "Started after the run by a person. They ask, as theorems of Lean, how the proofs' cost grows with each size "
             "of the network against brute force's; on this network " + ", ".join(network_sizes.text(s) for s in sizes)
             + ". Never scored. A lemma's statement is the agent's own: read it before relying on it. Under each lemma: the "
             "proofs whose checker Lean finds, term for term, in the modules the service compiled for it, and whether its "
             "statement names one of them. A lemma whose statement names no submitted checker says nothing about the proofs "
             "by itself (it may compare two formulas of the agent's own).", "",
             "The proofs:", ""]
    lines += [f"- `{p['record_id']}`: checker `{p['checker']}`, {p['certified']:,} certified at length {p['length']:,}"
              + (" (locked)" if p["locked"] else "" if p["offered"] else f"; not offered: {p['why']}") for p in sp["proofs"]]
    lines.append("")
    table = links.table(sp["steps"])
    if table:
        lines += ["### What is a theorem, per size", "",
                  "The result for a size is four links: `general`, a checker with the size as a parameter that is the submitted "
                  "checker at this network's value; `cost`, its exact bill at every value; `formula`, that bill in closed form or "
                  "between bounds; `brute`, brute force's cost and the comparison. Below, the theorem each session's answer names "
                  "for a link, where it is the named theorem of a submission the service accepted. That it says what the link "
                  "asks is the agent's account: the statements are under the sessions.", "",
                  "| size | " + " | ".join(links.LINKS) + " |", "| --- |" + " --- |" * len(links.LINKS)]
        lines += [f"| {s['symbol']} | " + " | ".join(links.cell_text((table.get(s["symbol"]) or {}).get(k), code=True) for k in links.LINKS) + " |"
                  for s in sizes]
        lines.append("")
    for s in sp["steps"]:
        res = s.get("result")
        what = plan.GENERAL_WORDS if plan.is_general(s) else next(
            (size["words"] for size in sizes if size["symbol"] == s["parameter"]), network_sizes.OWN_WORDS)
        lines += [f"### {s['parameter']}: {what}" + (", a further session" if s.get("again") else "")
                  + f" (round {s['round']}, {s['minutes']:g} minutes, at most ${float(s['usd']):.2f})", ""]
        if res is None:
            lines += ["Not done yet.", ""]
            continue
        if not prompt.asked_for_links(s):
            lines += ["Asked for formulas, with as much proved as the session could; not for the links.", ""]
        for name in ("CLAIM", "THEOREMS", "SCALING"):
            if res["answer"].get(name):
                lines += [f"**{name.title()}** (the agent's):", "", res["answer"][name], ""]
        lines += [f"The whole answer is `round_{s['round']:03d}/attempt_0/response.md`. Lemmas accepted: {len(res['lemmas'])}.", ""]
        ran = s.get("pipeline") or {}
        if ran.get("commit"):
            changed = ran.get("changed_since_run") or []
            lines += [f"Ran with pipeline {ran['commit'][:7]}" + (
                f"; changed since the run started: {', '.join(changed)} (its networks, task and architecture are the run's)"
                if changed else "") + ".", ""]
        for l in res["lemmas"]:
            found = [rid for rid, c in l["checkers"].items() if c["verified"]]
            unknown = [rid for rid, c in l["checkers"].items() if c["verified"] is None]
            said = links.about(l, sp["proofs"])
            lines.append(f"- `{l['theorem']}`: " + (f"its modules hold the checker of {', '.join(f'`{r}`' for r in found)}" if found else
                                                    "its modules hold no submitted proof's checker, by Lean's account")
                         + (f"; not known for {', '.join(f'`{r}`' for r in unknown)}" if unknown else "")
                         + ("; its statement names the checker of " + ", ".join(f"`{r}`" for r in said) if said else
                            "; its statement names no submitted checker")
                         + ("; it uses what the run does not offer of the Lean project's library" if l.get("beyond_offered") else ""))
            lines += ["", "  ```", "  " + (l.get("statement") or "(no statement in the receipt)"), "  ```", ""]
    return lines
