# Soundness of token_convex

**Claim.** If `check_leaf` returns a positive bound for a leaf with constant label l, every input in the leaf is classified correctly: for every input x in the leaf and every other output j, the network's output at l exceeds its output at j by at least the bound.

The rule is token_interval (docs/RULES.md, section token_interval) with three changes: a softmax over the positions keeps its scores, the decision uses them, and some work is reused. This file argues each change. Everything not mentioned here is token_interval's code, unchanged, and its argument applies.

## 1. The values

token_interval's values keep, for every input x of the leaf, a set that contains x's true value (a Sep holds every allowed token's exact row; a Mix holds a constant interval plus terms w_k R_k[t]; a Var holds one interval per input). token_convex adds one kind and two annotations.

**Soft.** In a leaf where several positions vary, the softmax node's input is first turned into an interval tensor S exactly as token_interval would (a Sep becomes the entrywise box of its rows per position). The rule then requires S to have shape (1, n) and the softmax to run over axis 1. It keeps:

- the box S, so for every input x, x's score s_p(x) lies in [L_p, H_p];
- if the input was a Sep with exact one-dimensional rows, those rows: for every input x, s_p(x) is the row entry of x's token at p (the Sep invariant);
- the interval softmax of S (core/check/interval.py), the value every operation sees that does not use the structure.

**Grouped terms.** The only operation that uses a Soft as such is the product with a Sep whose shape is (1, n, ...) when the Soft's shape is exactly (1, n, 1, ..., 1) with the softmax axis at 1, followed directly by a sum over axis 1. The result is the Mix with terms a_p R_p[t_p], where a_p is the softmax weight of position p and R_p the Sep's rows at p. This is token_interval's own construction (a WSep summed over the positions); the term keeps its weight interval and, in addition, the label (softmax id, p). Products with constant matrices act on the rows (linearity), and adding values joins the term lists; both keep the labels, because they leave every weight as it was. Scaling a Mix removes the labels (the weights change). Any other operation sees the plain interval weights.

**Kept rows.** See section 4. They change what is charged, never a value.

So for every input x, the true network output at the logits equals c + sum over terms of w_k R_k[t_k(x)] with c in the constant interval and each w_k in its interval, as for token_interval, and in addition: for every softmax id g whose labelled terms cover positions 0..n-1 once each, the weights of those terms are exactly softmax(s(x)) for a score vector s(x) in g's box (and equal to its per-token scores when kept).

## 2. The decision

Fix an other output j. The margin of input x is

    m_j(x) = (c_l - c_j) + T_j(x) + G_j(x)

where T_j collects the terms outside complete groups and G_j(x) = sum over groups of the group's contribution. For one group with positions p = 0..n-1, with d_p(t) = R_p[t, l] - R_p[t, j]:

    G(x) = sum_p a_p d_p(t_p),   a = softmax(s(x))

Write u_p = exp(s_p - K) for any constant K. Then a_p = u_p / sum_q u_q, so G(x) = sum_p u_p d_p / sum_p u_p, a ratio of two linear functions of u.

The constant part and T_j are bounded exactly as in token_interval (a term with one row and an exact weight is a constant; any other term by the corners of its weight interval times the range of its differences). Every level below bounds G from below; the leaf's bound is the smallest, over j, of the sum of the three lower bounds.

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

Each result N/D is turned into an integer at a fixed exponent by rounding down, so it stays a lower bound. A level is used only if its total is positive; otherwise the next one runs. Levels 2 and 3 replace a level-2 value by the level-3 value only when it is larger, and both are lower bounds, so the larger one is too. Groups whose labelled terms do not cover every position once are not used; their terms are bounded as token_interval bounds them.

## 3. Rounding

Only exp rounds, outwards. Every other quantity is an exact integer at a power-of-two exponent: differences of exact rows, the cross-multiplied comparisons, and the final divisions, which round down.

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

So reuse changes the count, never a bound. Two keying errors of this kind were found while the rule went
through the route (19 October 2026), both shared with token_interval and neither reachable on the model folders
of that day: the bias step of an nn.Linear read back the product's rows, and two terms with one origin read
each other's rows at the next product. Both are fixed, with regression tests and synthetic model folders the
audit now samples (tests/stub_general, tests/stub_twopaths).

## 5. Checks

- The rule's tests (test_rule.py): Lemma A and Lemma B against brute force on random small instances in exact arithmetic; the leaf bound never above the smallest float64 margin of the leaf's inputs, on all four attention folders; never certifying less than token_interval; exact when one position varies; reuse charged once; linear networks refused.
- The route's audit (core/rules_route/audit.py): the same comparison against brute force on trained, random-weight and perturbed networks of every model folder beyond linear maps, synthetic ones included, with leaves of token_interval interleaved on one program so the memo is shared, and every input of every certified leaf rechecked with the single rule.
- In every run that uses the rule, the checker worker compares each accepted leaf's bound with the float margins of its inputs and halts the run on any excess (core/check/plugins.py, runtime_audit).
