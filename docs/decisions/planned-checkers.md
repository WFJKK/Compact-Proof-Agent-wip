# Planned checkers and a scoring preview (13 November 2026)

Decided with the user on 13 November 2026, after run attn-min2-ptl-1 and an outside review of the first proposal.

## What happened

Round 3 of attn-min2-ptl-1 submitted a scored partial proof (672 of 4,096 inputs). After two service fixes it is
verified, but scoring refused it: its checker's description size was 14,043 against a budget of 13,376. The
agent learnt of this, and of an earlier allowlist refusal, only from its one submission, after the round's
budget was spent. A preview of the same checker shows where the size went: the shape checks (`pre`) 5,486 and a
table of where each row's far pairs start (`d0`) 610.

## Two decisions

1. **A scoring preview during development.** `lean_check` takes `checker`, the name of the agent's checker; a
   successful compile then reports the counted-language closure and the description size against the budget,
   measured by the same functions as the score step (`accept.py compile --checker`, `acceptcheck closure`). It
   is a preview: the soundness and instance theorems and the general layer's kernel time are still checked
   only on submission.
2. **A plan input (policy v9).** Data computed offline that says where to look (which inputs go into which
   group, where a loop stops) is a plan, not numerical evidence. The fixed rules lane keeps plans free and
   bounds them (cost-v4, `docs/decisions/same-proof-same-cost.md`); in the open lane a plan could only live in
   the checker's code, where it counts toward the description size, and the certificate cannot carry it (it
   yields abstract numbers, not indices). A scored block may now give `"plan": [natural numbers]`; the checker
   is then `D : List Nat → Checker`.

## Why a plan is safe

- Not trusted: the soundness theorem must hold for every plan, and the general layer may not mention the
  protected module's `plan`, so only the instance runs the checker on it. A plan can steer which checks run,
  never stand in for one.
- Free, as in the fixed rules lane; turning an entry into a number for arithmetic goes through `I.lit`,
  charged 1, as a certificate number is.
- Bounded as that lane bounds its tree: at most 4 entries per input plus 10,000, each below 2^32.

The identity trick that the description size guards against (a copy of the weights in the code, so that the
proof can do the brute force where nothing is counted) needs a fixed reference the proof can rely on; a plan,
quantified over in the soundness theorem, is not one.

## Corrections from the review

The first proposal said to move the tables into the certificate and that frozen transfer would make the size
cap unnecessary. Both were wrong: the certificate cannot hold indices and charges what the fixed rules lane
keeps free, and the cap stays (frozen transfer measures transferable verified efficiency, not understanding;
`docs/decisions/frozen-transfer.md`).

## Where it lives

Lean project: `accept.py` (`--checker`, `--plan`, `plan_problem`, policy v9), `make_protected.py` (the `plan`
constant and `_p<hash>` in the module name; unplanned modules are unchanged), `AcceptMain.lean` (`closure`
reports the size; `score-planned`), `examples/open_lane/max2_tiny_planned`, `docs/COUNTED.md`. Pipeline:
`lean_check(checker, plan)`, the scored block's `plan`, the prompts `open_lane_v6` and
`open_lane_formalization_v1`.

## Not decided here

Frozen transfer for the open lane (the next step): a frozen recipe would produce each network's certificate and
plan.
