# Reviews

## Review 1: SOUND (manual backend, model not recorded)

Summary. I found no soundness or trust problem in 2.2. The rule change has two parts:
- a flag, structured (rule.py 315), set only where a QVal is created (475) or a new Soft is created (625);
- check_leaf (1369-1389), which records the first pass's evaluator through a factory and runs the second pass only when that evaluator made structure.
Both passes are the evaluations I reviewed before. The skip removes only a pass that would repeat the first exactly. The core fix (concretize) is correct and preserves values.

The cases above are passing regression sequences, not counterexamples:
- leaves certified through a completed query-by-query pass with two pair groups;
- leaves that only the second pass certifies, on the four-head stub_query;
- single-input leaves whose second pass reaches the fixed concretize.
The stub_query networks carry explicit weights (see item 4). Through the route's audit (--only-counterexamples) they give 14 leaves plus the 83 fixed regressions: 0 violations, 37 certified, 18,086 exact single checks.

Items from my 2.1 review

A. RESOLVED. The DESCRIPTION (rule.py 104-113), SOUNDNESS.md section 8 and the core's descriptions (core/check/rules.py line 50, docs/RULES.md line 80) now promise, with at most one varying position, only that the leaf is certified whenever token_interval certifies it, and that an uncertified leaf gets at least token_interval's bound, which is its smallest margin wherever token_interval keeps every value per input.

I checked this on 1,500 leaves with one varying position (trained and random networks). On the seven folders where token_interval keeps every value per input, every uncertified leaf got its exact smallest margin, and no leaf with all inputs correct was left uncertified. On xorformer-majority, 33 of 210 uncertified leaves are inexact and 7 leaves with all inputs correct are uncertified, exactly as with token_interval and as the new text says.

One precision: the list "concatenating, stacking or expanding values" is not exhaustive. var_op (core/check/tokens.py, 521) has no per-input rule for nn.Linear, transpose or .T either, so those also box a per-input value. No current folder applies them to one. The text should say "such as", in the rule and in the core.

B. RESOLVED in the wording. Sentence 3 of the DESCRIPTION (rule.py 73) now names the 2**-64 floor, and SOUNDNESS.md section 3 explains GUARD_BITS. My 2.1 case (the token-independent attn-max4 network, now in regressions.json) behaves as stated: token_interval certifies the leaf with three varying positions, the rule returns 0, and the one-varying leaf is certified through the second pass.

Minor: exp's 2**-120 rounding is also part of "the rounding of its bounds". It is relative to the weights, hence scaled by the rows' magnitude, and it can exceed 2**-64 of the rows' unit. Both are far below trained margins, so the parenthetical understates the rounding but does not mislead.

C. RESOLVED. The xorformer leaf from my 2.1 review (random:4:4.0, one varying position) now costs 4,561, token_interval's charge, instead of 9,122.

The skip logic is sound, and it answers both of the coordinator's questions:
- Where per_input is read: only in qval (429) and intercept (602).
- Where structured is set: exactly where a QVal (475) or a new Soft (625) is created. Every other Soft, PScores or PProd construction (518, 663, 674, 1318, 1322) needs an existing Soft or QVal.
- A first pass that made no structure therefore took PerInputEvaluator's path node by node, with the same values read from the same memo. On 150 xorformer leaves its bound and output equal PerInputEvaluator's.
- A first pass that made a Soft or QVal and then turned it into plain values (a discarded branch) still has structured True, so the second pass runs. That can only cost more; it never loses a bound.
- A first pass that made none but differs from the second pass is impossible, since the two evaluators differ only in declining those two constructions.

Minor wording: sentence 19 (rule.py 108) says "not repeated when the first pass kept no softmax or query structure". The code tests whether the first pass made structure, not whether it kept it.

4. RESOLVED. I instrumented the four-head stub_query. It reaches:
- two pair groups in one decision, next to a per-token group and a box group;
- a PScores leaving the token rules (query_var and collapse_query of a PScores);
- pair_margin's singles and others classes (residual[:, 0] @ F, with one token or several at position 0).

One gap remains. On random weights, by_query never completed in my sample (44 of 44 stopped), and the route's audit samples random weights. I found leaves that certify through a completed query-by-query pass with two pair groups and give them in the first two cases.

Note also that changing stub_query's parameters changed what every "random:<seed>:<scale>" case on it draws. My three 2.1 stub_query sequences in regressions.json now run on different networks: the leaves that were certified through a completed query-by-query pass are no longer certified, and by_query now stops early or is never reached (8 of 8 re-run). They are still valid soundness checks but no longer test what they were added for. Regressions on synthetic folders should carry explicit weights; a changed folder then makes the case malformed, visibly, instead of silently different.

The core fix (commit 7dfd8b1, core/check/tokens.py, concretize). It is correct and preserves values:
- The old code read rows.lo[0][None], which indexes a Python int when the rows are scalars (TypeError, so the whole proof is rejected).
- The new rows.lo[0:1] gives the same (1, *rest) array whenever the old code worked.

Confirmed:
- On the core test's stub_query leaves, the old code raised TypeError in token_interval and in token_convex's second pass; the new code gives the exact margins.
- On 60 single-input attn-max4 leaves, old and new give identical bounds.
- 67 single-input stub_query leaves reach the fixed path inside token_convex's second pass; three are in the last case.
- The pattern occurs nowhere else in the core or the rule.

Every agent-facing claim in the DESCRIPTION, once more
- Sentence 3 (certifies every leaf token_interval certifies, up to rounding): true; see B. No leaf with several varying positions lost certification: 1,404 tested, 170 certified by token_interval.
- Levels 0 to 3, A, B and query by query: implemented as described. I checked every intermediate level below.
- Sentence 18 (rule.py 104), "the first query token that leaves an output not positive ends the search, and the leaf is not certified": with one varying position the second pass can still certify the leaf. On the GUARD_BITS network in regressions.json, leaf [[15,15],[0,0],[0,0],[0,14]] label 15: by_query stops, the first pass returns 0, and check_leaf certifies with 7.31e-26 through the second pass. This can happen only at the rounding edge on current folders. Say "the levels leave the leaf not certified".
- Sentence 19: see C ("kept" against "made").
- Sentence 20: true; see A for the list.
- Charges: one small mismatch with the code. "level 0: 1 per position (a table read; else 3 per token)", but a position with one token costs 2 (min_difference_all, rule.py 798).

What held up (2.2 loaded with use_candidate on its own path; byte-code writing disabled throughout):
- Exact oracle (the single rule's interval for every input, no tolerance): 16,450 leaves, 10,875 of them on the four-head stub_query at scales 0.25 to 512. No bound above the exact minimum, no crash; worst relative slack about 5e-47.
- Every intermediate bound on the four-head stub_query: level A, level B per output, fixed_levels per query token and output, and levels 0 to 3 per output for the non-pair decision. 936 pair decisions (two pair groups) and 469 non-pair decisions, no excess.
- Differential memo test of check_leaf: each leaf with a fresh memo against long shared sequences (repeats, token_interval interleaved), 10,064 leaves on all eight folders. Bounds and outputs identical.
- Float64 brute force: all 9,261 boxes with a random second label on a four-head stub_query network (11,535 leaves), token_interval interleaved.
- With one varying position: 1,050 leaves compared with PerInputEvaluator and token_interval (first passes without structure identical; nothing token_interval certifies left uncertified), and 1,500 leaves for exactness (item A).
- Static guard passes. The files match the hashes in checks.json, and the prompt's rule.py is identical to the candidate's.
