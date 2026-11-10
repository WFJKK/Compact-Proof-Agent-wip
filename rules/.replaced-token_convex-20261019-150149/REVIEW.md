# Reviews

## Review 1: SOUND (manual backend, model not recorded)

Summary. I found no soundness or trust problem in version 2. No bound I could produce exceeds the leaf's true smallest margin. I checked against float64 brute force and, much more sharply, against the exact single-rule interval of every input. The cases above are passing regression sequences on the version 2 paths, not counterexamples: shared memo with token_interval interleaved, pair path with tight bounds, query-only aligned leaves, the incomplete-group path, the aligned levels, prefix and suffix tables, and 128 query tokens. Through the route's audit (--only-counterexamples) they give 56 leaves plus the 6 fixed regressions, 0 violations, 21 certified and 18,019 exact single checks; the smallest slack is -5.5e-12 at magnitude 1e4 (float rounding). What I did find are claims in SOUNDNESS.md, the DESCRIPTION, the PROPOSAL and one test that the code does not implement (items 1 to 3). All are about precision, not soundness.

1. Leaves with at most one varying position. These are no longer decided as token_interval decides them, and the claim that they are certified exactly is false.

rule.py 591-592 (intercept) now builds a Soft in aligned leaves whenever the scores are a Sep with exact 1-d rows or a PScores. rule.py 820 hands a GMix to token_interval's decision only when no complete group reaches the output. The argument misses two consequences:
(a) If the group is not complete (stub_twopaths: head @ A + head @ B, then h + h @ W), the terms keep the Soft's plain weights. These are softmax(box) over the whole leaf, not one weight per input. Version 1 and token_interval had per-input weights there.
(b) If a term outside the group sits at the varying position (stub_general: h[:, n-1], weight 1, one row per token), lines 841 and 852 bound it by its range over the tokens. That bound is decoupled from the group's term at the same position and from the scores.

Examples where every input is correct, token_interval and version 1 give the exact margin and certify, and version 2 does not:
- stub_twopaths random:4:16.0, [[0,3],[4,4],[3,3]] label 4: bound -137868, true +9886.9.
- stub_twopaths random:4:16.0, [[5,5],[1,1],[1,2]] label 5: -177059 vs +19798.
- stub_twopaths random:4:16.0, [[5,5],[5,5],[4,5]] label 5: -82495 vs +30474.
- stub_twopaths random:2:4.0, [[1,1],[1,1],[0,1]] label 1: -91.03 vs +2.017.
- stub_general random:2:4.0, [[3,3],[1,1],[2,3]] label 3: -3.933 vs +0.1178.

On random aligned leaves (about 125 per network), version 2's bound is below token_interval's on 11 to 47 leaves per stub_general network and 74 to 124 per stub_twopaths network. So the following claims are false:
- SOUNDNESS.md section 8 (line 133): "Every other value stays one per input" and "so the rule certifies exactly the leaves whose inputs are all correct".
- The DESCRIPTION, rule.py 101-105: "these levels decide: they certify exactly the leaves whose inputs are all correct ... every other value is kept per input, as by token_interval".
- The DESCRIPTION, rule.py 71: "It does everything token_interval does".

On the four attention folders exact certification does hold, because the only term outside the group is a single or a query term. The test that would catch this, test_rule.py 122-133 ("never weaker than token_interval"), runs only on FOLDERS (line 38), which are the attention folders.

Proposed fix: in an aligned leaf, either take the larger of the levels' bound and token_interval's per-input bound, or keep version 1's per-input evaluation unless the group is complete and every other term is a single or a query term. Then state that in the DESCRIPTION and run the "never weaker" test on the stub folders too.

2. The test test_exact_decision_when_one_position_varies (test_rule.py 137-160) asserts at line 160 that an uncertified leaf with one varying position gets its exact smallest margin. SOUNDNESS.md section 5 (line 99) lists this as checked. It is false when the varying position is the query. by_query stops at the first query token that leaves an output not positive (rule.py 1279-1280), and pair_margin then keeps level B's value (1147).

I ran the test's own loop on audit-reproducible networks. The assertion fails on:
- 12 of 60 leaves on attn-max4 v16 random:5:4.0;
- 13 of 60 on attn-max4 v16 random:1:1.0;
- 19 of 60 on attn-min2 v64 random:2:4.0.
All failures have the query varying. Examples on attn-max4 random:5:4.0: [[10,10],[15,15],[9,9],[6,11]] label 15 gives bound -28.79 against exact -22.20; [[14,14],[10,10],[14,14],[1,5]] label 14 gives -51.395 against -51.274. The test passes only because its trained network rarely produces such a leaf. The bound is still sound, and certification is still exact for these leaves on the attention folders: a token that leaves an output not positive at level 3 has an input whose margin is at most 0, up to exp's rounding. Only the test and section 5 overclaim.

3. PROPOSAL.md line 39 says: "What it must not do. Change anything for leaves without such scores (the query fixed, or at most one position varying): the bounds and the charges stay token_convex's." The code and SOUNDNESS.md section 8 contradict this. Two examples on zoo:attn-max4-v16-s1:
- The single-input leaf [[3,3],[4,4],[5,5],[6,6]] label 6 gets 7.6971 (exact) from version 1 and 3.2186 from version 2.
- The fixed-query leaf [[15,15],[0,15],[0,15],[3,3]] label 15, with the same bound 10.17 from both, is charged tables 14202 and token_convex 815 by version 1, and 13398 and 780 by version 2.
Either the proposal or the code should change.

Minor wording: SOUNDNESS.md section 8 says "a QVal in such a leaf means qpos is the varying position". QVals are also made when the query position holds one token. The code handles that correctly (query_var broadcasts); only the text is wrong. The QVal docstring (rule.py 151, "where several tokens are allowed") has the same slip.

4. Version 2 paths that no current model folder reaches. I instrumented every decision on all seven folders:
- Every QVal has one term, and a key.
- Every pair_margin call has exactly one pair group, no other group, and one query term of weight exactly 1.
- query_var and collapse_query (a QVal, PProd or PScores leaving the token rules) are never called.

So the following paths are covered by neither the tests nor the audit, and no counterexample can be written for them today: the multi-term QVal; level A's branch for negative query weights (rule.py 1118, 1127) and pessimised's w < 0 case (1183); several groups in pair_margin; non-pair groups next to a pair group in query_view; and query_var and collapse_query.

I read each of them and found them correct: query_var's three cases, collapse_query's interval product for a PProd, the largest difference for w < 0, and the per-group sums in levels A and B and in fixed_levels. A future folder with a two-term query, a scaled residual or two heads would reach them. The audit should get a synthetic folder that does.

5. Charges. Reuse is charged once, and nothing used as free is computed more than once:
- A repeated leaf charges 0 to tables and the same token_convex amount.
- Bounds and charges are identical whether a leaf runs alone, after others, in reverse order, or after token_interval leaves.

One small item of work done but not charged: intercept (rule.py 603-609) computes pscores_box (2 per pair) and softmax(box) for every pair Soft, but charges them (via _box_cost, 613) only if the weights are used. When the complete group reaches the output, which is the usual case, that O(pairs) work is done and never charged. The DESCRIPTION says so, and version 1 did the same for the weights; computing the box lazily would remove it.

query_view recomputes col_extremes for every query token and charges it again. That over-charges and is harmless. Some leaves cost more than brute force: attn-max2 random:7:16.0 [[59,59],[0,55]] costs 517,115 for 56 inputs, mostly level 3 per output per query token. That charge is honest.

What held up (candidate loaded in-process, scratch files only):

Reading:
- Every new memo key determines its value. QVal: term keys plus the weight and constant values. Pair: Sep key, QVal key and token pair. pcol: pair key, query token, end. Also minmaxdiff and top2. The qpos diagonal entries follow the same formula as the off-diagonal ones, so even a shared key would stay consistent.
- Tables rescale exactly. col_extremes' read at a finer exponent is exact, because the extremes are entries of the leaf's own column.
- The id()-keyed caches hold their objects, and nothing mutates a term, a stored row or a returned table array.
- Every rescaling rounds down (_floor_ratio, _shift). Exp enclosures are outward, with every argument at most 0 (box_ends, exact_setup, and pair_ends with K = max(0, ghi) at line 1248).
- Lemma C's relative box contains every input's relative scores for each query token, the reference position and the query position's own entry included.
- Level A's query term at w times its smallest difference over tokens and outputs; level B via pessimised; by_query's exact per-token constants; query_view's restriction of the qpos term and of a per-token Soft's qpos row; and top_two with ties are all correct.

Float64 brute force, with token_interval leaves interleaved on one program:
- All 9,261 boxes with a random second label on 11 stub_twopaths networks (scales 0.1 to 1000): about 127,000 leaves.
- About 300 attention networks (trained, perturbed 0.01 to 2, random 0.25 to 1000, every setting including v24, v64 and v128), each a 40-leaf sequence with random labels.
- 100 crafted networks: small integers with exact ties, per-tensor exponents from 2^-40 to 2^40, mixed per-entry exponents, sparse, rank one, duplicated rows.
- 50 networks with leaves up to 20,000 inputs.
- Whole-proof replays of test_rule.py's label-set trees on 5 attn-max4 networks: 892 rule leaves, every certified leaf correct.

Exact oracle (the single rule's interval for every input, no tolerance): about 7,400 leaves, including very sharp weights (scale 300 to 3000), all-zero tensors, denormals, and 1e-30/1e30 mixed weights. The worst relative slack is about 2e-37, and no bound exceeds the exact minimum.

Every intermediate bound, not only the returned one: I recomputed with the evaluator's own methods level A, level B per output, fixed_levels per query token and output, and levels 0 to 3 per output for the non-pair decision. Each was compared with brute force restricted to that query token. About 3,200 pair and 4,000 non-pair decisions, no excess.

Differential memo test: each leaf's bound with a fresh memo (run_token_leaf's memo argument) against its bound inside 40-leaf shared sequences with repeats and token_interval interleaved. About 16,000 leaves on all seven folders, identical everywhere.

Trust: the static guard passes. There are no model-specific constants, no globals, no nondeterminism (id() is used only as a cache key) and no I/O. The file hashes match checks.json.
