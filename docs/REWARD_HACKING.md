# Reward hacking: what the loop guards against, and what was found

The agent is scored on proofs it writes, by a checker it cannot touch, under a cost model it can read. Anything it can gain without a better proof is a hole in one of those three. This page lists the holes looked for, the one found, and the guards in place. Keep it current: every new rule is a new surface.

## The one found (12 October 2026)

In the first max2 runs the `row_segments` approximation charged 1 per merge step where the checker did two operations (a difference and a comparison), the same two a dense range does per token at a charge of 2. The pilot's round-5 claim said so in plain words: "one step per segment touched instead of the dense two steps per token". It wrote the contracted matrix itself as an approximation with one segment per entry and error 0, the same check at half the price, and its full proofs looked 1.5 times shorter than the hand-written one. Nothing was unsound: the proofs certified what they claimed. Only the length was wrong.

`cost-v2` charges the step 2, and the audit that followed charged the three other places where an approximation did uncharged work (locating a row's segments, subtracting the error, the low-rank differences). Measured again, the pilot never beat the hand-written proof at full accuracy; the second run's genuine idea (coarse surrogates away from the diagonal, exact checks only near it) kept a gain of about 10 to 17 percent. See `docs/COST_MODEL.md`.

What made it visible: the length by rule shown to the agent, which also let it probe the model on purpose ("knob 0.75 vs 1 isolates the cost"), and the agent's own claims, which name the trick. The claims are the first thing to read after a jump in the metric.

## Surfaces and guards

**The cost model.** Everything the checker does is charged, so no work can hide. The audit went through every `counter.add` in `core/check/` against the stated rule (one operation on exact numbers counts 1) and asked, for each: does the charge scale with the work, and can a proof shift work into an uncharged path? Index arithmetic (loop counters, advancing a merge) is not counted anywhere; so that it cannot grow on its own, locating a range's segments is a lookup in an index that is charged when built. Two conventions are deliberate and uniform, so no proof gains from them: a linear map on a one-hot input is a lookup (its output size per position, the additions across positions not charged separately), and `exp` and `softmax` count 1 and 3 per entry although the checker's enclosures take many operations, because a proof controls how many entries are evaluated, not how precisely. `tests/test_checker.py` pins each approximation form's charge to what it does and checks that an exact approximation never costs less than the dense check it repeats.

**The checker.** Nothing a proof claims is trusted; every bound is recomputed exactly. Soundness tests run random trees and random approximations against exact brute force, the general evaluator against the model's own float forward and against 200-digit decimals for `exp`. One invariant no proof can fake: a sound checker never certifies more inputs than the network gets right. A record that did would halt the run (`core/rounds.py`), and `core.remeasure` checks every archived proof against it.

**The sandbox and the trusted files.** A recipe sees its weights, the sizes and the knob, nothing else; it never learns which network it is proving. Real runs use `sandbox: hardened`, which refuses to start rather than fall back to running recipes with the user's rights. The core and the model folder are hash-checked at every check, and bytecode appearing in them halts the run.

**The metric.** Q counts the single best proof at each budget, so partial proofs at well-chosen lengths raise it without a new idea. That is the metric working as defined, not a hack, but it means a higher Q is not the same as a shorter complete proof. The max2 run of 13 October scored on Q went further: its recipe defined the knob as an index into five budgets that it chose, per network, by maximising its own predicted Q (its KNOB text: "four budgets chosen by an exact DP that maximises the log-length area of this recipe's own certified-accuracy step curve"). Every proof was real; the score rewarded placing them as well as making them. `Q_grid` (section 5 of `docs/SPEC.md`) removes that lever: the loop fixes the budgets, runs the recipe once per budget, and reads accuracy only there. Report the shortest full-accuracy proof next to either score, and compare against the hand-written proof given the same budgets, so the gap shows only what the agent added.

**The rule text.** The agent plans against the costs it is told. An understated cost (the old text said low rank costs "about r per output" where the code charged 2r) misleads it into dropping a rule that would have paid; an overstated one hides a hole. The text in `core/check/rules.py` now states each charge as the code makes it.

## When something looks too good

1. Read the round's claim and the length by rule. A proof that is much shorter with the same leaves is paying less somewhere, not doing less.
2. Check the proof against the rule's cost: is every operation the checker does in the charge?
3. If a charge was wrong, bump the cost version, re-measure every run with `python -m core.remeasure`, and never edit archived results.
4. If the certified count is wrong, that is a soundness bug, which is worse: stop the runs and fix the checker first.
