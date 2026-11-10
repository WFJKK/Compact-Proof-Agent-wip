# Proposal: token_convex

Version 1 is the first section; version 2 extends it to leaves where the query varies (last section).

**Source.** Written by Claude in the session of 19 October 2026, from the comparison of the agent's four-token proofs with Gross et al.'s cubic proof (results/gross-cubic-2026-10-16). The agent's own NEW RULE IDEA answers from the four-token runs were on the user's machine and not available here; `python -m core.rules_route proposals <run folder>` lists them, to be compared with this one.

**Implemented by.** Claude, in the same session, acting as the route's separate implementer for this first rule (the agent being scored did not write it). The route's audit and an independent adversarial review then checked it (status.json).

## NEW RULE IDEA

With token_interval, a leaf where several positions vary is bounded term by term: each softmax weight gets its own interval, and the bound lets every non-maximal position take its largest weight at the same time. Those weights can add up to far more than one, so the bound fails unless at most one position varies, and a proof needs about one leaf per input of the other positions. That is why the four-token proofs stay at B/23 to B/124 while the cubic proof reaches B/223 and B/705.

The cubic proof's central idea is a convexity argument: the attention output is a softmax-weighted average, so its worst case over many inputs is found by pessimising the attention once and then using that the weights sum to one. A generic rule can do this without knowing the model:

1. Keep a softmax's scores when its input is a box (and per token, when the scores are exact per token, as they are with the query fixed).
2. When its weights multiply exact rows and are summed over the positions, bound the sum by the exact minimum of the softmax-weighted average of the per-position label-minus-output differences: over the box of scores (a ratio of linear functions, minimised at the ends of the score ranges), or over every choice of one token per position, each with its own score and difference (Dinkelbach's method, one pass over the tokens per step).
3. Pessimise over the wrong outputs first, as the cubic proof does, and fall back to per-output bounds only where that fails.
4. Reuse: running minima of token-only rows over ranges that start at the first token or end at the last, and rows that depend on a value fixed in the leaf (the attention scores for a fixed query) kept per value.

With this, one leaf per (query, largest token, first position holding it) should certify every input in it, about (n - 1) V leaves per query instead of V^(n - 1) inputs, and a full proof should cost about as much as the cubic proof while certifying every correct input.

## Version 2: leaves where the query varies (19 October 2026)

**Source.** The comparison of 19 October 2026 (`results/convex-rule-2026-10-19/README.md`): with token_convex, a proof of max (or min) of four tokens fixes the query in every leaf and pays a softmax bound per query, so its partial proofs certify about 11% of the inputs at B/1,700 (v16), while Gross et al.'s sub-cubic proofs certify about 62% at B/1,500 by bounding the attention for every query at once. Their idea, in the form a model-agnostic checker can use, is the subject of this proposal. Written by Claude in the session of 19 October 2026, as the route's implementer again (no LLM API calls while building).

**Problem.** In a leaf where the query position varies, token_convex boxes the query before it meets the keys, so every attention score becomes an interval over the whole leaf. The scores of all positions then move independently, although they share one query: the scores of the position holding the largest token and of the others rise and fall together with the query, while their differences stay large. A softmax depends only on those differences, so the box loses almost everything.

**Idea.** Keep the query apart from the keys:

1. A value that depends only on the query position's token (the query vector, a Mix whose terms all sit at that position) is kept exactly per token of that position.
2. Its product with the keys (a Sep) followed by the sum over the head dimension is kept per pair: position p's score for every token at p and every token at the query position (for the query position itself, the diagonal). These are dot products of exact rows, kept for the whole proof like the other token rows.
3. A softmax over such scores keeps them. The decision then has two new levels, tried before the query-by-query ones:
   - **Level A, every output at once, over all queries.** Pick a reference position r (one with the fewest tokens, not the query position). For every input, the softmax weights are exp(s_p - s_r) normalised, and s_p - s_r = S_p[t_p, q] - S_r[t_r, q]. Its smallest and largest value over the leaf come from each query token's column of the pair table (running minima and maxima over the position's token range), so position p's relative weight lies in a box, and r's is exactly 1. Lemma A (the existing box minimum) then bounds the weighted sum, as in level 0, with the query position's own terms at their smallest over its tokens.
   - **Level B**, the same per other output.
   - **Then query by query**: for each token q at the query position, the leaf restricted to it is a leaf with a fixed query, whose scores are exact per token (a column of the pair table), and levels 0 to 3 apply unchanged, for the outputs levels A and B left unsettled. The leaf's bound for an output is the larger of level B's and the smallest over the query tokens.

**Why it should pay.** A float prototype on attn-max4 v16 (seed 1), with leaves "the positions in S hold M, the others 0..M-1" (one leaf per M and set S), found levels A and B certifying 65% of the inputs and the query-by-query levels another 32%, with the leaves of the first half costing about 5,600 in total. Gross et al.'s sub-cubic proofs reach 62%; their bound is level A with a low-rank approximation of the score table in place of the exact table, which at these sizes costs little either way (the pair table is (n - 1) V^2 dot products, about 11,500 at v16, against B = 65 million).

**What it must not do.** Lose anything token_interval or version 1 certifies. Nothing model-specific: the rule recognises a value depending on one position's token and a dot product of it with a Sep, not an attention layer by name.

## Version 2.1: the review's points (19 October 2026)

The adversarial review of version 2 (verdict SOUND) found that version 2 changes more than the paragraph above promised, and that one change loses precision. A fixed query's scores are read from the pair table (the same numbers, kept once for the whole proof; charges differ slightly). With at most one varying position the softmax structure is used too; there, a group that does not reach the output complete keeps interval weights for the whole leaf, and a term outside the groups at the varying position is bounded apart from the group, so on the synthetic folders tests/stub_general and tests/stub_twopaths version 2 failed to certify leaves that token_interval and version 1 certify. Version 2.1 keeps the structure as a first pass in such leaves and, when it does not certify, evaluates the leaf again with every value per input, as version 1 does, keeping the larger bound. A new synthetic folder, tests/stub_query, reaches the paths no other folder did (a two-term scaled query, three kinds of softmax together, a negative query-position weight, query values that leave the token rules), and the tests now check, on random networks of the synthetic folders, that the rule never certifies less than token_interval and decides exactly with one varying position.
