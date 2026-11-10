# Soundness of token_convex

**Claim.** If `check_leaf` returns a positive bound for a leaf with constant label l, every input in the leaf is classified correctly: for every input x in the leaf and every other output j, the network's output at l exceeds its output at j by at least the bound.

The rule is token_interval (docs/RULES.md, section token_interval) with three changes: a softmax over the positions keeps its scores, the decision uses them, and some work is reused. Version 2 (sections 6 to 9) extends this to leaves where the query position varies (values that depend on that position's token, scores per pair of tokens, and decision levels that use them), and uses the softmax's structure in leaves with at most one varying position as well, first; version 2.1 evaluates such a leaf again as token_interval does when that first pass does not certify it (section 8). This file argues each change. Everything not mentioned here is token_interval's code, unchanged, and its argument applies.

## 1. The values

token_interval's values keep, for every input x of the leaf, a set that contains x's true value (a Sep holds every allowed token's exact row; a Mix holds a constant interval plus terms w_k R_k[t]; a Var holds one interval per input). token_convex adds one kind and two annotations (version 2 adds three more kinds, section 6).

**Soft.** A softmax node over axis 1 of a (1, n) input becomes a Soft in a leaf where several positions vary, and in any leaf when its input is a Sep with exact one-dimensional rows or a PScores (section 6); otherwise token_interval's evaluation applies (with at most one varying position, its values are one per input). The input is first turned into an interval tensor S exactly as token_interval would (a Sep becomes the entrywise box of its rows per position; a PScores the box of its entries per position). The rule keeps:

- the box S, so for every input x, x's score s_p(x) lies in [L_p, H_p];
- if the input was a Sep with exact one-dimensional rows, those rows: for every input x, s_p(x) is the row entry of x's token at p (the Sep invariant);
- if the input was a PScores whose query position has one token, the scores per token: its single column (section 6), which is exactly what such a Sep's rows would be;
- if the input was a PScores whose query position has several tokens, its entries (section 6);
- the interval softmax of S (core/check/interval.py), the value every operation sees that does not use the structure.

**Grouped terms.** The only operation that uses a Soft as such is the product with a Sep whose shape is (1, n, ...) when the Soft's shape is exactly (1, n, 1, ..., 1) with the softmax axis at 1, followed directly by a sum over axis 1. The result is the Mix with terms a_p R_p[t_p], where a_p is the softmax weight of position p and R_p the Sep's rows at p. This is token_interval's own construction (a WSep summed over the positions); the term keeps its weight interval and, in addition, the label (softmax id, p). Products with constant matrices act on the rows (linearity), and adding values joins the term lists; both keep the labels, because they leave every weight as it was. Scaling a Mix removes the labels (the weights change). Any other operation sees the plain interval weights.

**Kept rows.** See section 4. They change what is charged, never a value.

So for every input x, the true network output at the logits equals c + sum over terms of w_k R_k[t_k(x)] with c in the constant interval and each w_k in its interval, as for token_interval, and in addition: for every softmax id g whose labelled terms cover positions 0..n-1 once each, the weights of those terms are exactly softmax(s(x)) for a score vector s(x) in g's box (and equal to its per-token or per-pair scores when kept).

## 2. The decision

Fix an other output j. The margin of input x is

    m_j(x) = (c_l - c_j) + T_j(x) + G_j(x)

where T_j collects the terms outside complete groups and G_j(x) = sum over groups of the group's contribution. For one group with positions p = 0..n-1, with d_p(t) = R_p[t, l] - R_p[t, j]:

    G(x) = sum_p a_p d_p(t_p),   a = softmax(s(x))

Write u_p = exp(s_p - K) for any constant K. Then a_p = u_p / sum_q u_q, so G(x) = sum_p u_p d_p / sum_p u_p, a ratio of two linear functions of u.

The constant part and T_j are bounded exactly as in token_interval (a term with one row and an exact weight is a constant; any other term by the corners of its weight interval times the range of its differences; a weight with one entry per input, possible with at most one varying position, by its smallest and largest entry). Every level below bounds G from below; the leaf's bound is the smallest, over j, of the sum of the three lower bounds.

**Lemma A (box).** Let c_1..c_n be numbers and 0 <= lo_p <= hi_p with some hi_p > 0. The minimum of f(u) = sum u_p c_p / sum u_p over the box lo <= u <= hi (where the denominator is positive) is attained at a u with u_p = hi_p for c_p below the minimum and u_p = lo_p for c_p above it.

*Proof.* df/du_p = (c_p - f(u)) / sum u. At a minimiser, raising u_p lowers f if c_p < f and lowering it does if c_p > f, so each u_p sits at the end shown (entries with c_p = f can be moved to either end without changing f). If every lo_p is 0, f near u = 0 takes only values that it takes at u_p = hi_p e_p (f is unchanged by scaling u), and these are among the candidates below. ∎

Sorting the positions by c_p, the minimiser is one of the n + 1 vectors that put the first k positions at hi and the rest at lo. The rule evaluates all of them (skipping a zero denominator) and takes the smallest, with integer cross-multiplication, so the result is exactly the minimum over the box.

**Lemma B (token choices).** Let each position p choose one of finitely many options i, each with a number c_{p,i} and an interval [lo_{p,i}, hi_{p,i}] of weights, hi > 0. Let lam* be the minimum of sum w_p c_p / sum w_p over all choices and all weights in their intervals. For a ratio lam = N/D (D > 0) of one such choice, let F = sum_p min over i and w of w (D c_{p,i} - N). Then F <= 0, and F = 0 exactly when lam = lam*; if F < 0, the choice attaining F has a ratio below lam.

*Proof.* For any choice, sum w (D c - N) = D (sum w c) - N (sum w), which has the sign of its ratio minus lam. The choice that gave lam makes it 0, so F <= 0. F = 0 means every choice has ratio at least lam, so lam = lam*. If F < 0 the minimising choice has ratio below lam. ∎

The minimum over w of w (D c - N) is at lo if D c - N >= 0 and at hi otherwise, and the minimum over i and w decomposes by position, so F costs one pass over the tokens. Starting from an actual choice, each step goes to a choice with a strictly lower ratio, so the search ends (finitely many choices, and weights only at their ends); the rule stops after 64 steps without a result and then uses nothing from this level.

**The levels.** Let K be the largest score upper bound in the leaf, and for each position (level 0, 2) or token (level 1, 3) let lo and hi be the outward enclosures of exp at the lower and upper ends of its score minus K (core/check/interval.py exp_bounds: lo <= exp(x) <= hi, at 2^-120). For every input, u_p = exp(s_p(x) - K) lies in the enclosure of its position's box (and of its own token's score, which is exact when kept).

- Level 2, output j: c_p = the smallest d_p(t) over p's tokens. For every input, G(x) = sum u_p d_p(t_p) / sum u_p >= sum u_p c_p / sum u_p (u_p >= 0), which is at least Lemma A's minimum over the box of enclosures.
- Level 3, output j: options are p's tokens, each with its own difference d_p(t) and its own enclosure. Every input is one choice with weights inside the enclosures, so G(x) >= lam* (Lemma B).
- Levels 0 and 1: the same with d_p(t) replaced by the smallest over every other output j of d_p(t) for that j. That number is at most d_p(t) for each j, so the bound is below G for every j at once; adding the smallest over j of the rest of the margin gives a number below every m_j(x).

The smallest difference over every other output (levels 0 and 1) is R_p[t, l] minus the largest entry of R_p[t] at an output other than l (version 2): with a the output of the row's largest entry and b the output of the largest among the others, that entry is R_p[t, a] if a != l and R_p[t, b] if a = l, so the difference is the same number token_interval would compute from all outputs.

Each result N/D is turned into an integer at a fixed exponent by rounding down, so it stays a lower bound. A level is used only if its total is positive; otherwise the next one runs. Levels 2 and 3 replace a level-2 value by the level-3 value only when it is larger, and both are lower bounds, so the larger one is too. Groups whose labelled terms do not cover every position once are not used; their terms are bounded as token_interval bounds them.

## 3. Rounding

Only exp rounds, outwards. Every other quantity is an exact integer at a power-of-two exponent: differences of exact rows, the cross-multiplied comparisons, dot products of exact rows (version 2), and the final divisions and rescalings to a coarser exponent, which round down.

## 4. Reuse

Every reused value must be a deterministic exact function of the key it is kept under. The keys, and why each
determines its value:

- **Sep rows** are kept under (node, origin, position), plus a tag "+" for the bias step of a linear node (an
  nn.Linear multiplies and adds its bias at one node, so the two steps need different keys), plus the context.
  A node's Sep argument is the same graph value in every leaf, and every operation that makes a Sep (the
  lookup, adding or multiplying by a constant, a sum over a row dimension, a product with a constant matrix)
  computes its rows from that argument's rows and, at most, one constant. If the constant is the same in every
  leaf (it does not depend on the input), the rows depend on the token alone, or on the argument's own context.
  If it depends on the input but is exact in this leaf, its exact value (exponent and integers) is appended to
  the context. If it is not exact, or a product's matrix depends on the input, the rows are not kept at all,
  and nor is anything computed from them. So by induction over the graph, a Sep row's value is a function of
  its node, position, token and context, which is what it is kept under. (token_interval keeps token-only
  rows under the same keys; the two compute them identically.)
- **Term rows** are kept under (node, origin, position, chain), where origin is the node where the term began
  (selecting a position of a Sep, or a sum over the positions) and chain the constant matrix products applied
  to it since, in order. Two terms of one Mix can share their origin and position and still differ, as in
  h @ A + h @ B or h + h @ W; their chains tell them apart. A term's first rows are the rows of its origin's
  Sep argument at its position, and each product in the chain is fixed by its node, so (origin, position,
  chain) determines the rows. Only terms whose rows depend on the token alone are kept.
- **Range tables** hold running minima (and maxima) of rows kept as above, over tokens 0..k or k..V-1,
  extended with the same rows the leaf would have used; the per-token minima over the other outputs are plain
  functions of kept rows and the label.

Version 2 adds keys of its own (section 9). So reuse changes the count, never a bound. Two keying errors of this
kind were found while the rule went through the route (19 October 2026), both shared with token_interval and
neither reachable on the model folders of that day: the bias step of an nn.Linear read back the product's rows,
and two terms with one origin read each other's rows at the next product. Both are fixed, with regression tests
and synthetic model folders the audit now samples (tests/stub_general, tests/stub_twopaths).

## 5. Checks

- The rule's tests (test_rule.py): Lemma A and Lemma B against brute force on random small instances in exact arithmetic; the leaf bound never above the smallest float64 margin of the leaf's inputs, on all four attention folders; never certifying less than token_interval, on the attention folders' trained networks and on random-weight networks of the three synthetic folders; with one varying position (the query's or another's), certifying exactly the leaves the network classifies correctly and giving a leaf it does not certify its smallest margin, on trained and random networks of two attention folders and the synthetic folders; reuse charged once; linear networks refused. Version 2: the relative-weight box (section 7) against brute force on random score tables; the largest-other-output shortcut against brute force; leaves where the query varies, on trained, sharp random and perturbed networks of the four attention folders, never above the float64 margin; such a leaf certifying whenever all its fixed-query parts do; its reuse charged once; a whole proof of such leaves certifying every correct input. tests/stub_query (version 2.1) reaches the paths the attention folders do not: a query with two terms and a learned scale, three kinds of softmax next to each other, a query-position term with a negative weight, and values computed from the query that leave the token rules.
- The route's audit (core/rules_route/audit.py): the same comparison against brute force on trained, random-weight and perturbed networks of every model folder beyond linear maps, synthetic ones included, with leaves of token_interval interleaved on one program so the memo is shared, and every input of every certified leaf rechecked with the single rule.
- In every run that uses the rule, the checker worker compares each accepted leaf's bound with the float margins of its inputs and halts the run on any excess (core/check/plugins.py, runtime_audit).

## 6. Values that depend on the query position's token (version 2)

**QVal.** At an unsqueeze of a Mix m whose terms all sit at one position q0, each with an exact scalar weight and exact rows, and whose constant is exact, the rule makes a QVal. By the Mix invariant, for every input x, m's value is const + sum_k w_k R_k[t] with t the token at q0 (each term's row for x's token there; the weights are exact numbers). So vals[i] = const + sum_k w_k R_k[i], computed exactly, is m's value for every input whose token at q0 is the i-th, and the QVal holds it unsqueezed. (With one token at q0 this is the exact value token_interval would compute; version 1 computed it per leaf.) q0 becomes the leaf's query position qpos; a Mix at another position later in the leaf is not made a QVal (it is evaluated as before).

**PProd.** The product of a Sep of shape (1, n, d) with exact rows and a QVal of shape (1, 1, d) at qpos. For every input x, entry (p, k) of the true product is sep.rows[p][t_p(x), k] * vals[i(x)][k], with i(x) the index of x's token at qpos. It is not computed; if anything but a sum over its last axis uses it, it becomes the interval product of the Sep's box and the QVal's box (each contains its factor's value for every input), or, in a leaf where only qpos varies, one exact value per input.

**PScores.** The sum of a PProd over its last axis. For p != qpos, ent[p][a, i] = sum_k sep.rows[p][a, k] * vals[i][k]; for p = qpos, ent[p][i] = sum_k sep.rows[qpos][i, k] * vals[i][k] (the Sep's tokens at qpos are the leaf's tokens there, the same list as the QVal's; both factors read x's token at qpos). So for every input x the true score at p is ent[p][t_p(x), i(x)], or ent[qpos][i(x)]. All entries are exact integers at one exponent (each dot product is exact; rescaling to the smallest exponent multiplies by powers of two).

A PScores that is not the input of a softmax becomes the box of its entries per position (contains every input's scores), or, in a leaf with at most one varying position, one exact value per input: either qpos is the varying position and every other position has one token, or qpos has one token and the entries of the varying position's tokens are its per-input values; either way the per-input values are entries, broadcast where a position has one entry. A QVal and a PProd in such a leaf become per-input values the same way.

**Softmax of a PScores.** With one query token, the scores are exact per token: position p's are column 0 of ent[p] (the query position's, ent[qpos][0]); the Soft keeps them as per-token rows, with the box of each column (section 1), and everything of sections 1 and 2 applies as for a Sep's rows. With several query tokens, the Soft keeps the PScores; its box (each position's smallest and largest entry) contains every input's scores. The box and the interval softmax of it are computed when the Soft is made, so that any later use can read them, and charged (2 per pair score, 6 per entry) the first time something uses them; the levels never do, as version 1's weights.

## 7. The decision with scores per pair of tokens (version 2)

The decision of section 2 changes only when some complete group's Soft has pair scores. Terms outside the groups are of four kinds: the constant; terms with one row and an exact scalar weight (constants); the query position's terms with an exact scalar weight and a row for each of its tokens ("query terms": for every input whose token at qpos is the i-th, the term's value is w R[i]); and the rest, bounded as token_interval does, which holds for every input.

**Lemma C (relative box).** Fix a position r. For every input x and position p, a_p(x) = exp(s_p - s_r) / sum_k exp(s_k - s_r). If for every input g_p(x) = s_p(x) - s_r(x) lies in [glo_p, ghi_p] (g_r = 0), then for any K, u_p = exp(g_p - K) lies in [exp(glo_p - K), exp(ghi_p - K)], u_r = exp(-K), and a = u / sum u. So G(x) = sum u_p d_p / sum u_p with u in a box, and Lemma A's minimum over that box (with c_p at most every d_p(t) the position allows) is a lower bound of G(x) for every input. ∎

**The ranges.** r is a position other than qpos with the fewest tokens (the lowest such; qpos itself if it is the only position), so the scores of r and p share x's query token. For a query token index i, let colmin_p(i) and colmax_p(i) be the smallest and largest of ent[p][a, i] over p's tokens a (one entry if p has one token). For every input with query index i: s_p - s_r = ent[p][t_p, i] - ent[r][t_r, i] lies in [colmin_p(i) - colmax_r(i), colmax_p(i) - colmin_r(i)]; for p = qpos, s_qpos - s_r = ent[qpos][i] - ent[r][t_r, i] lies in [ent[qpos][i] - colmax_r(i), ent[qpos][i] - colmin_r(i)]; if r = qpos, s_p - s_r = ent[p][t_p, i] - ent[qpos][i]. glo_p and ghi_p are the smallest and largest of these ends over i, so the hypothesis of Lemma C holds for every input. K is the largest ghi_p, or 0 if that is negative, so every argument of exp is at most 0; the ends are enclosed outwards (exp_bounds), r's exp(-K) too.

**Level A.** c_p is the smallest difference over p's tokens and every other output (for qpos, over its tokens: the term at qpos has a row for each). By Lemma C and the argument of level 0, the group's bound is below G(x) for every input and every other output. The rest: the constant, constants and other terms as in section 2, and each query term with weight w >= 0 at w times its smallest difference over its tokens and every other output, which is at most its value for every input and every output. So min over j of the rest without query terms, plus these, plus the groups' bounds, is below every m_j(x). If some query term has a negative weight, the rest is computed per output (w times the largest difference) and its smallest over j is used.

**Level B.** For each other output j: the same with c_p the smallest d_p over p's tokens for that j, and each query term at w times its smallest difference for that j (or its largest if w < 0). Below m_j(x) for every input.

**Query by query.** For a query token index i, consider the inputs whose token at qpos is the i-th. For them a group with pair scores is a group with scores exact per token: position p != qpos has score ent[p][t_p, i] for its token t_p, qpos has the single score ent[qpos][i], and every score lies in the box [colmin_p(i), colmax_p(i)]. A group with per-token scores keeps them, with qpos restricted to its i-th token; a group with only a box keeps it (it holds for every input). Each group's term at qpos keeps its i-th row. Query terms are constants w R[i]; the rest is bounded as before. This is the situation of section 2 with a fixed query, so levels 0 to 3 give, for each output j still unsettled after level B, a lower bound Q_j(i) of m_j(x) over these inputs.

**Combination.** If every query token gives a positive bound for every unsettled output, then for each such j, min_i Q_j(i) is below m_j(x) for every input, and so is level B's value; the rule keeps the larger. As soon as one token leaves an output not positive the leaf cannot be certified, the rule stops, and keeps level B's values (lower bounds for every input). The leaf's bound is the smallest over j.

## 8. Leaves with at most one varying position (version 2)

Version 1 left such leaves to token_interval's evaluation, one value per input. Version 2 makes a softmax a Soft there too when its scores are exact per token (a Sep) or per pair (a PScores), and uses the decision of sections 2 and 7 when a complete group reaches the output. Nothing in Lemmas A to C or the levels needs several varying positions, and terms with a weight per input are bounded by that weight's smallest and largest entry (section 2). A QVal, PProd or PScores that leaves the token rules becomes one exact value per input: either qpos is the varying position and every other position has one token, or qpos has one token and its values are the same for every input (section 6). So this first pass is sound. It can be weaker than token_interval: a group that does not reach the output complete keeps the softmax's interval weights for the whole leaf where token_interval had one weight per input, and a term outside the groups at the varying position is bounded over its tokens apart from the group's term there (the review of 19 October 2026 found both on tests/stub_general and tests/stub_twopaths).

**The second pass (version 2.1).** If the first pass does not certify the leaf, `check_leaf` evaluates it again with PerInputEvaluator, which keeps every value one per input in such a leaf (it makes neither Softs nor QVals there), exactly as version 1 and token_interval do, with the reuse of section 4. Both passes give lower bounds of every input's margin, so the larger is one too; both are charged. The second pass's bound is token_interval's, exact per input up to the rounding of exp and of the softmax's division. So such a leaf is certified exactly when all its inputs are correct (up to that rounding), a leaf that is not certified gets its smallest margin (up to that rounding), and a certified leaf's bound may be below its smallest margin, since the first pass stops at the first positive bound.

## 9. Reuse added in version 2

- **QVal values** are kept per token under ("token_convex:qval", ((term key, weight value), ...), constant value), only when every term's rows are kept. A term key determines the term's rows (section 4; term keys exist only for rows that depend on the token alone), and the weights and the constant are exact values written into the key, so the values are a function of the key and the token.
- **Pair entries** are kept per (token at p, token at qpos) under ("token_convex:pair", the Sep's key at p, the QVal's key), only when both keys exist. The entry is the dot product of the Sep's row kept under its key (section 4) and the QVal's value kept under its key, with its exponent stored alongside, so it is a function of the key and the two tokens.
- **Column tables** under ("token_convex:pcol", pair key, query token, end) hold running minima and maxima, over tokens from one end of the range, of entries kept under the pair key for that query token, extended with the entries the leaf would have used. An extreme read at a finer exponent than the leaf's is used only if it converts exactly; otherwise the leaf computes it from its own entries.
- **Difference tables** under ("token_convex:minmaxdiff", term key, label, end) hold running minima and maxima of the label-minus-output differences of rows kept under the term key.
- **Largest outputs** under ("token_convex:top2", term key), per token: the outputs of the largest and the second largest entry of the row kept under that key, a function of the row. A query token's view of a term at qpos (section 7) carries the term's key and holds only that token's row, which is the row kept under the key for that token, so its reads agree.
- **Within a leaf**, minima computed from a term and the box of a QVal, PProd or PScores are kept for the rest of the leaf by the object's identity; the cache holds the object, so no other object can take its identity during the leaf, and nothing in it outlives the leaf.

Each of these changes what is charged, never a value.
