# Proposal: token_convex

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
