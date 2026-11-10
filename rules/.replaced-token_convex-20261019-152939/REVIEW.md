# Reviews

## Review 1: SOUND (manual backend, model not recorded)

Summary. I found no soundness or trust problem in 2.1. The code change is small and sound by construction:
- check_leaf (rule.py 1362-1373) keeps the larger of two lower bounds.
- PerInputEvaluator (1355-1359) differs from ConvexEvaluator only in declining qval (424) and intercept (596) in leaves with at most one varying position.
- Each pass is an evaluation already reviewed (version 2, and version 1's per-input path).

Nothing I tried makes either pass exceed a margin, including on the paths stub_query reaches for the first time. The cases above are passing regression sequences, not counterexamples. Through the route's audit (--only-counterexamples) they give 21 leaves plus the 62 fixed regressions: 0 violations, 37 certified, 18,324 exact single checks.

The verdict covers soundness and trust only. The new agent-facing claim about leaves with at most one varying position is false on xorformer-majority (item A), and the "(up to exp's rounding)" qualifier is inexact (item B). Since the agent reads the DESCRIPTION, the wording should be corrected before adoption.

Earlier points

1. RESOLVED. The second pass restores version 1's per-input evaluation in leaves with at most one varying position, and the bound is the maximum of the two passes. On 504 such leaves over all eight folders (random and trained), the second pass's bound equals token_interval's bound exactly, every time. So 2.1 never certifies less than token_interval there. Every v2 example from my last review now certifies with the exact margin:
- stub_twopaths random:4:16.0 [[0,3],[4,4],[3,3]] label 4 now gives 9886.91;
- stub_twopaths random:2:4.0 [[1,1],[1,1],[0,1]] label 1 now gives 2.01749;
- stub_general random:2:4.0 [[3,3],[1,1],[2,3]] label 3 now gives 0.117765.
On every folder except xorformer-majority (item A), aligned leaves are certified exactly when all inputs are correct, and an uncertified leaf gets its smallest margin (504 leaves, 0 exceptions outside xorformer).

2. RESOLVED. Uncertified query-varying leaves now get the exact margin. For example, attn-max4 random:5:4.0 gives -22.2033 for [[10,10],[15,15],[9,9],[6,11]] label 15 and -51.2736 for [[14,14],[10,10],[14,14],[1,5]] label 14, both equal to the true minimum. The exactness test now runs on random networks too, which would have caught the gap. It still leaves out xorformer-majority (item A).

3. RESOLVED in the text. PROPOSAL.md line 39 now promises "Lose anything token_interval or version 1 certifies", and a new section lists what version 2 changed. The QVal docstring and SOUNDNESS.md section 8 are corrected. The new promise holds except at the GUARD_BITS edge of item B, where token_interval certifies and 2.1 does not.

4. MOSTLY RESOLVED. I instrumented stub_query. It reaches:
- two-term, keyed QVals;
- pair_margin with three groups side by side (pair, per-token rows, box);
- the query-position term at weight -0.5, so level A's negative branch (1132) and pessimised with w < 0;
- query_view and fixed_levels with non-pair groups next to a pair group;
- query_var and collapse_query for a QVal and a PProd.

Still unreached on every folder:
- a PScores leaving the token rules, i.e. the PScores branches of query_var (535-541) and collapse_query (555-557);
- two pair groups in one decision;
- pair_margin's singles and others classes (1094 and 1098), which are always empty.

On random stub_query weights, by_query almost always stops early: 27 of 27 decisions in one sample. So certification through the completed query-by-query pass with three groups is rare. I found such leaves and put them in the cases above (random:4:0.5, random:16:0.5, with bounds as tight as 0.003614 against a true minimum of 0.003663). I read the unreached branches and found them correct, but no audit exercises them.

5. DOCUMENTED, NOT CHANGED. SOUNDNESS.md section 6 now says the pair box and its interval softmax are computed when the Soft is made and charged only if used (rule.py 608-614). When the levels decide, this work is still done and not charged. That is acceptable as a stated convention, but computing them lazily would make charge and work match.

New findings

A. With at most one varying position, the new exactness claims are false on xorformer-majority. The claims are:
- DESCRIPTION, rule.py 105-109: "So such a leaf is certified exactly when all its inputs are correct (up to exp's rounding), a leaf that is not certified gets its smallest margin".
- SOUNDNESS.md section 8 (line 135): PerInputEvaluator "keeps every value one per input in such a leaf ... The second pass's bound is token_interval's, exact per input up to the rounding of exp and of the softmax's division".

The bound is token_interval's, but token_interval is not exact here. Its per-input evaluation boxes values at operations var_op does not cover (core/check/tokens.py, var_op: no cat, stack or expand). In xorformer-majority, positions = torch.cat([bits, query.expand(...)]). I traced it in both passes: node cat receives the bits' per-token CSep and an IT, var_op declines cat, the per-input value is collapsed, and cat returns the box over the leaf. stack and expand behave the same way. Everything after that is interval arithmetic over the box.

Leaves where every input is correct but the leaf is not certified (token_interval gives the same bound):
- random:4:4.0 [[1,1],[1,1],[1,1],[0,0],[0,0],[0,1],[1,1],[0,0],[0,0],[0,0],[0,0],[1,1]] label 0: bound -172.874, true +6.665.
- random:1:4.0 [[0,1],[1,1] eleven times] label 1: -899.157 vs +18.232.
- perturbed:xorformer-majority-n12h1d8-s2:1:2.0 [[0,0],[0,0],[0,0],[0,0],[1,1],[0,0],[1,1],[0,1],[1,1],[1,1],[1,1],[0,0]] label 0: -721.386 vs +22.884.

An uncertified leaf whose bound is not its smallest margin: random:4:4.0 [[1,1],[0,1],[1,1],[0,0],[0,0],[0,0],[0,0],[1,1],[1,1],[1,1],[1,1],[1,1]] label 1: -199.371 vs -6.665.

Correct-but-uncertified leaves per 40 one-varying-bit leaves: random:4:4.0 21, random:3:1.0 22, perturbed s2:1:2.0 22, random:2:16.0 6, perturbed s0:0:0.5 5. On the six trained networks and three perturbed by 0.1 to 0.2, all of about 10,400 sampled one-varying-bit leaves were correct and certified, so the effect on the scored networks is small; the claim is still false as stated.

The core makes the same overclaim: core/check/rules.py lines 49-50 (token_interval's description) and docs/RULES.md (the Var paragraph, line 80). 2.1 inherits it. The 2.1 exactness test does not run on xorformer-majority, which would have caught this.

Fix: qualify the claim, for example "exact when token_interval keeps every value per input; values are boxed at operations its per-input evaluation does not cover, such as torch.cat, torch.stack and expand". Alternatively, teach the core's var_op those operations. Either way, add xorformer-majority to the exactness test.

B. "It certifies every leaf token_interval certifies (up to exp's rounding)" (rule.py 72-73) is inexact with several varying positions. In both decisions, each group's bound is rounded down at 2**e0, with e0 at most a group's row exponent minus GUARD_BITS = 64 (rule.py 69, 849, 1101). That is 2**-64 of the rows' unit. token_interval sums at 2**-120.

The last case above is a constructed, token-independent attn-max4 v16 network where logit 15 = a_0 - a_1, about 7.3e-26 for every input. On the leaf [[15,15],[0,14],[0,14],[0,14]] label 15 (three varying positions), token_interval certifies with bound 7.311e-26, which is the exact margin, and the single rule certifies every input. 2.1 returns 0. The one-varying leaf [[15,15],[0,0],[0,0],[0,14]] is certified through the second pass. Float64 shows a margin of 0 here; only the exact recheck sees it.

No trained network comes near this: it needs a margin below 2**-64 of the rows' unit. So only the wording matters. Either say "up to rounding at 2**-64 of a group's row unit, and exp's", or keep the larger of the levels' bound and token_interval's term-wise bound in leaves with several varying positions too.

C. Charges. Both passes are charged. The second pass charges what token_interval charges, except that context rows are kept for the proof (tables) and matched per leaf, as the DESCRIPTION says. For example, attn-max2 random:7:16.0 [[57,57],[46,46]]: pass 2 costs 94 less per leaf and 126 more in tables than token_interval. That is the 126 score entries kept, minus the 32 numbers paid to match the query.

When the first pass makes no Soft and no QVal (every xorformer leaf, for example), the second pass repeats it exactly. random:4:4.0's leaf in item A costs 4,561 per pass, 9,122 in all, for the same bound. This is honest but wasteful; check_leaf could skip the second pass in that case.

What held up (2.1 loaded with use_candidate on its own path):
- The two-pass logic. Both bounds are lower bounds, ok follows the kept bound, and the condition at 1369 matches the evaluator's own test for at most one varying position. The passes share memo keys only for identical computations (pure rows, tables, top2). The second pass's context rows use version 1's keys, which the first pass never writes.
- Differential memo test of check_leaf. Each leaf with a fresh memo against long shared sequences (repeats, token_interval interleaved), 24,140 leaves on all eight folders: identical bounds and outputs.
- Exact oracle: the single rule's interval for every input, no tolerance. 32,475 leaves: 15,000 on stub_query with random weights at scales 0.25 to 512; 4,000 with crafted stub_query weights (small integers with exact ties, exponents 2**-40 to 2**40, mixed per entry, sparse, duplicate rows, s = 0 and s < 0); the rest on all folders. No bound above the exact minimum, no crash.
- Every intermediate bound on stub_query: level A, level B per output, fixed_levels per query token and output, and levels 0 to 3 per output for the non-pair decision. 656 pair and 370 non-pair decisions, no excess.
- Float64 brute force: all 9,261 boxes with a random second label on two stub_query networks, 23,070 leaves, token_interval interleaved.
- Never weaker than token_interval: 3,882 leaves with several varying positions on all folders. token_interval certified 530 of them, and 2.1 certified every one.
