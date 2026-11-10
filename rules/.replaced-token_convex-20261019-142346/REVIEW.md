# Reviews

## Review 1: SOUND (manual, None)

Independent adversarial review by a separate Claude agent that had not seen the implementation, in two rounds (19 October 2026). It was given only the rule's files, the core code and the audit tool.

Round 1 (on the first version) confirmed two soundness bugs that token_convex shared with token_interval, neither reachable on the five model folders of the day:
1. Term rows memoized under (node, origin, position) are not unique: in h @ A + h @ B, or h + h @ W, followed by another product, two terms of one Mix share origin and position, and the second read the first's rows. Leaves were certified with bound 1.0 (twomaps) and 2.0 (reslin) where the float64 and exact single-rule margin was -9.
2. An nn.Linear's product and its bias step were memoized under one key, so the bias was dropped (bound 2.0 against -18).
It also found a crash with a single output (an empty minimum in min_difference_all), and said SOUNDNESS.md section 4 was false as written and that the context-key argument rested on an unstated invariant.

Fixes: term rows are kept under (node, origin, position, chain), bias rows under a key tagged "+" (core commits 587d440 and 02304ec, with regression tests and the synthetic folders tests/stub_general and tests/stub_twopaths that the audit now samples); one output returns (1, -1); SOUNDNESS.md section 4 rewritten.

Round 2 (on commit 592466a, the files under review here) found no counterexample:
- The old reproductions now give the exact margin under token_convex and token_interval (twomaps -9, reslin -9, biaslin -18).
- About 25,000 fuzzed leaves, 0 violations: the five model folders with crafted and random weights, arbitrary boxes and labels, one shared program per network with token_interval leaves interleaved, peel sequences and long fixed-query runs; stub_general and stub_twopaths; and six further scratch architectures (two softmaxes sharing one value Sep then h + h @ W; a positional bias added to the scores; values that depend on the query; scores that are not per position; a scaled and negated copy of the head; nn.Linear with a bias at every stage and one Linear called twice). Smallest slack -1.5e-11 (float rounding).
- The official audit at --level small (252 leaves) and --level full --seed 5 (1,960 leaves over 7 folders, 936 certified, 11,876 single checks) both pass.
- No other memo key can collide: only linear memoizes twice at one node, and "+" separates the two; in one leaf an origin creates at most one term per position and each matrix of a kept term's chain is fixed by its node, so equal term keys mean equal rows; the key families differ in length and type; range tables carry the right keys plus label and direction.
- The context-key invariant holds for the current operations: a node whose value can be a Sep is never an exact non-Sep value (with several varying positions it is a Sep, a WSep or a non-exact box; otherwise a Sep, a WSep or a Var), so the exact constant appended to a context always comes from the other argument, and a node's Sep argument is the same in every leaf.
- A copy of the rule with the old term key fails the two regression sequences below (bound 2.0 against -9.0 and 1.0); the current rule passes them. The audit's sequence mode catches a cross-leaf table bug that single cases miss.

Remaining critique, none of it a soundness problem:
1. SOUNDNESS.md section 4 states the Sep-argument invariant without its reason; the reason is the one given above.
2. A crash path: IT.__mul__ on 0-d operands goes through np.where with Python ints and raises OverflowError past 2**63 (scaling a head built from softmax weights, in token_interval too). The checker then rejects the whole proof, and the audit stops instead of recording it.
3. Add the two regression sequences to the audit's fixed cases.
