# Soundness of the generic rules

Every rule here is generic: it works for any model folder whose `model.py` uses the supported operations (linear maps, sums over one dimension, additions) and whose inputs are one-hot tokens. The rules' short descriptions, shown to the agent, are in `core/check/rules.py`. Networks with other operations, such as softmax attention, are covered by the last section. None of these arguments has a Lean proof yet, so every result is labelled Python-checked.

**What is certified.** The checker certifies the network as a function over the rationals, defined by its float32 weights converted exactly. A float32 forward pass can disagree only on inputs whose margin is within rounding error. On all 20 max2 networks, exact brute force and float32 agree on every input.

**Arithmetic.** Float32 weights are dyadic rationals and convert to integers times a power of two with no rounding (`Exact.from_float`). Every later operation is an integer operation on those. Numbers supplied by a proof file must be dyadic too (denominator a power of two), with a bounded numerator and exponent (`parse_number`); exponent notation and other denominators are refused, and refused before the value is built, so a short string cannot name a huge number. This keeps every intermediate fraction small, so no proof can make the exact arithmetic slow while every operation still counts as 1. Nothing is ever rounded.

**Robustness.** The checker rejects a malformed or hostile proof as a whole rather than failing: any error from proof-supplied data, including arithmetic that runs out of range or memory, becomes a rejection, while the checker's own internal invariants stay fatal. A proof that is merely expensive to check is cut off by a per-proof time limit and rejected. So no single proof can halt or hang a run.

## Split tree

A split divides the current range [lo, hi] of one position at strictly increasing cuts inside (lo, hi]. The pieces [lo, c1−1], ..., [ck, hi] are disjoint and cover [lo, hi], and the number of children must equal the number of pieces. By induction from the root, which covers every input, the leaves partition the input space. So summing leaf sizes never counts an input twice. The walk is iterative, with node and size limits, so a hostile tree cannot exhaust the stack.

## single

The leaf must hold exactly one input. The checker evaluates the network exactly and certifies the input if the label's logit is strictly larger than every other logit. Ties are never certified.

## interval

The task's `constant_label` must confirm that every input in the leaf has the same label l.

- **One-hot sets.** For position p with tokens in [lo, hi], a linear map W applied to the one-hot vector gives a column W[:, t] for some t in the range. For each coordinate, min over t and max over t bound that column. Summed over positions, the centre and radius of those bounds give a box containing the summed vector for every input in the leaf.
- **Boxes through linear maps.** If x lies in the box with centre c and radius r, then W x + b lies in the box with centre W c + b and radius |W| r. This is standard interval arithmetic, computed exactly. Sums and additions of boxes add centres and radii.
- **Margins at a linear output.** The margin for output j is (W_l − W_j)·x + (b_l − b_j), which is at least (W_l − W_j)·c − |W_l − W_j|·r + (b_l − b_j) for x in the box.
- **Margins when the output map sees one-hot sets directly**, as after a full contraction. The margin is the sum over positions of W[l, t_p] − W[j, t_p], plus the bias difference. It is therefore at least the sum over positions of min over t in the range of W[l, t] − W[j, t]. This is exact when all but one position is a single token.
- **Without a linear output map**, the margin is at least (c_l − r_l) − (c_j + r_j).

The leaf is certified only if every lower bound for j ≠ l is positive. So every input in it has a positive margin, and the network classifies it correctly.

## contract

Matrix multiplication is associative, so replacing consecutive linear maps x ↦ W_k(⋯(W_1 x + b_1)⋯) + b_k by the single map with weight W_k⋯W_1 and bias W_k⋯W_2 b_1 + ⋯ + b_k computes the same function. The chain must be consecutive, and every intermediate result must feed only the next map, so nothing else in the graph reads the values that disappear. The product is computed exactly.

## symmetry

Two conditions are checked, and both must hold.

- **The network ignores order.** The traced graph shows that the input is used only by a sum over the positions dimension. Then the output is g of the sum of the per-position vectors, for some g, so it is the same for every reordering of the positions.
- **The label ignores order.** The task declares `LABEL_SYMMETRIC = True`. The model-folder loader tests the declaration on random inputs, and the declaration itself is trusted model code.

Then an input is correct exactly when its sorted version is. Under symmetry, a leaf counts only its inputs with tokens in non-decreasing order, each weighted by its number of distinct reorderings. Every sorted input lies in exactly one leaf, because the leaves partition the inputs. Every input is a reordering of exactly one sorted input. So no input is counted twice, and the total never exceeds the number of inputs. A test compares the weighted count with enumeration for 1, 2 and 3 positions. The certified mask checks it again on every proof.

## approximate

For a linear map with weight W, the proof supplies P. The checker computes eps = max over all entries of |W − P|, exactly. Then W[l, t] − W[j, t] ≥ P[l, t] − P[j, t] − 2 eps for every t, so for any range the minimum over t of the left side is at least the minimum of P[l, t] − P[j, t], minus 2 eps. The forms differ only in how that minimum is bounded.

- **dense:** computed directly.
- **row_segments:** rows l and j are constant on known pieces, so the minimum over a range is the minimum over the overlapping pieces. It is computed by merging the two rows' segments, exactly.
- **low_rank** (P = F G): P[l, t] − P[j, t] = Σ_k c_k G[k, t] with c = F_l − F_j. For every t this is at least Σ_k c_k · (G_min[k] if c_k ≥ 0 else G_max[k]), where G_min and G_max are taken over the range.

All three are tested against exact brute force on random leaves and random approximations, including poor ones.

## skip

It certifies nothing.

## Networks beyond linear maps

A network whose model.py uses operations other than nn.Linear, sums and additions (the xorformer model's softmax attention, for example) is traced with torch.fx and evaluated by `core/check/general.py`. Only a fixed list of operations is accepted: parameters, indexing and reshaping (getitem, unsqueeze, expand, transpose, cat, stack, zeros_like), sums, differences, products, matrix products, sums over a dimension, exp and softmax. Anything else stops the check with its name. `contract`, `approximate` and `symmetry` are refused for such networks.

**Interval tensors.** Every value is a pair of integer arrays lo and hi with one shared power-of-two exponent, standing for the intervals [lo·2^e, hi·2^e]. The weights are exact (lo = hi), converted from floats without rounding. Sums, differences and products of intervals are computed exactly from the endpoints: a sum adds lower ends and upper ends; a product takes the smallest and largest of the four endpoint products (two when one side is exact); a matrix product splits the exact side into its positive and negative entries. So if every input of an operation lies in its interval, so does the output. Nothing in these operations is rounded.

**exp.** For x = X·2^e, write y = |x|/2^m with m chosen so that y ≤ 2^-8. The series of exp(y) has positive terms, each at most y times the one before, so the terms after the k-th sum to at most twice the k-th. The terms are computed as integers at 2^-W, the lower sum rounding every step down and the upper sum rounding up and adding twice the last term. For x < 0, exp(x) = 1/exp(|x|), with the division rounded outwards. Then exp(x) is the m-th repeated square of exp(±y); each squaring of [L, H] with L ≥ 0 gives [L², H²], again rounded outwards. The final bounds are multiples of 2^-120. Arguments of absolute value 4096 or more are refused. Because exp is increasing, the exp of an interval [a, b] lies in [lower(exp a), upper(exp b)]. A test compares these bounds with correctly rounded values at 200 digits.

**softmax.** softmax(z) = softmax(z − c) for any c, so each row is first shifted by the largest upper end, an exact subtraction. The weight of entry j, e_j / (e_j + Σ_{k≠j} e_k), grows with e_j and shrinks with every other e_k. It is therefore at least lower(e_j) / (lower(e_j) + Σ_{k≠j} upper(e_k)) and at most upper(e_j) / (upper(e_j) + Σ_{k≠j} lower(e_k)); both divisions round outwards to 2^-120, and the weights are kept within [0, 1].

**The input.** For a single leaf the input is the exact one-hot tensor. For an interval leaf the input may only be multiplied by a weight matrix W, a lookup of W's rows: at a position whose tokens are lo..hi the result is one of the rows lo..hi, so it lies in the box of their entrywise minimum and maximum. Any other use of the input in an interval leaf stops the check.

**Deciding.** A leaf is certified if the lower end of the label's output is strictly larger than the upper end of every other output, for every input in the leaf (the task confirms a constant label, as for linear networks). Since every true value lies in its interval, every input in a certified leaf is classified correctly. The interval bounds treat different entries as independent, which is sound but loses precision on wide boxes; a proof can split them.

**Input-free parts.** Nodes that do not depend on the input (the xorformer query vector, say) are evaluated once per proof by the same interval arithmetic and charged to extract.

## token_interval

For networks beyond linear maps (`core/check/tokens.py`). The task must confirm a constant label l, as for interval. The leaf allows a set T_p of tokens at each position p. The checker never forms a coordinate box at the input; it keeps four kinds of values, each standing for a set of exact (or enclosed) tensors, one per input of the leaf.

- **Sep** (one row per position and token). The lookup x @ W gives, at position p, the row W[t] for the token t there, so holding W[t] for every t in T_p holds the true row of every input. Adding an exact tensor C gives W[t] + C[p], a product with an exact matrix gives row @ M, an elementwise product with an exact tensor and a sum over a non-position dimension act row by row: each is the same exact operation the single rule performs, applied to each possible row. So for every input, its true value at p is among the stored rows at p.
- **Mix** (a sum of weighted rows). Selecting position p of a Sep gives the term 1 · R[t_p]. Multiplying a Sep by a tensor that is one scalar w_p per position and summing over the positions gives the sum of terms w_p · R_p[t_p]; the true weights lie in the stored w_p (an interval, or one interval per input, see Var). For an exact matrix M, (c + Σ w_k R_k[t]) @ M = c @ M + Σ w_k (R_k[t] @ M) by linearity, so the rows stay exact through later constant maps. Adding values adds constants and joins the term lists. Scaling by a scalar scales the constant and every weight.
- **Var** (a value per input). If at most one position p* allows more than one token, every input of the leaf is fixed by its token at p*. A Sep then lines up its rows along p*'s tokens (the other positions have one row), a Mix evaluates c + Σ w_k R_k[t] per token, and every later operation (products, sums, exp, softmax) is the interval operation of the general evaluator applied to each input's own value. So each input keeps an interval containing its true value, and softmax weights per input are as tight as for a single check. Operations with no per-input rule (such as concatenating, stacking or expanding values, as xorformer's model does) box their arguments over the leaf (below), so from there on the bound is sound but no longer per input.
- **Leaving the domain.** An operation the rules above do not cover first turns a Mix whose terms each have one row and an exact weight into its exact value; otherwise, with one varying position, into a Var; otherwise into an interval tensor: a Sep into the entrywise minimum and maximum of its rows per position, a Mix into c plus Σ w_k times the box of R_k's rows (interval products). These contain every input's value, so the general evaluator's argument applies from there on.

**Deciding.** For an interval tensor output, as for interval. For a Var output, the label's lower bound minus every other output's upper bound per input, and the smallest over the inputs. For a Mix output, for each other output j: margin_j = (c_l − c_j) + Σ_k w_k (R_k[t, l] − R_k[t, j]). With one varying position, each term's weight and row belong to the input in question, so the bound per input is c_l.lo − c_j.hi plus Σ_k min(w_k.lo · Δ_k, w_k.hi · Δ_k), with Δ_k that input's exact difference, and the leaf's bound is the smallest over its inputs. With several varying positions, each term's contribution is at least the smallest of the four products of the ends of w_k's interval and of the range of Δ_k over the term's tokens (a product is bilinear, so its minimum over a box is at a corner), whatever the other terms do. Either way every true margin is at least its bound, so a leaf whose bounds are all positive classifies every input correctly.

**Reused rows.** A row that depends on its token alone (made only from a lookup and constants that do not depend on the input) is the same in every leaf, so the checker computes it once per proof and keeps it under (node, the node where its term began, position, token). Rows that depend on anything else (the query, for example) are recomputed in every leaf. This changes what is charged, never what is certified.

**Tests.** `tests/test_token_interval.py` compares the bound with the float network's smallest margin on random leaves of all four attention folders: never above it, and within 10^-3 of it when one position varies. It also checks that reused rows are charged once and that linear networks refuse the rule.

## Adopted rules

Rules that come through the rule route (docs/RULE_ROUTE.md) live in `rules/<name>/`, each with its own soundness argument in `SOUNDNESS.md`, its tests, the proposal it implements and a `status.json` recording the checks it passed. The checker uses one only while its files match the hashes recorded at adoption. The first is `token_convex` (`rules/token_convex/SOUNDNESS.md`): token_interval plus the softmax's structure, so that a leaf where several positions vary is bounded by the exact minimum of the attention-weighted average, not weight by weight. Its version 2 also takes leaves where the query position varies: the query is kept exact per token and the attention scores per pair of tokens, and the softmax is bounded for every query at once against a reference position (its `SOUNDNESS.md`, section 7), then query token by query token. With at most one varying position it tries this first and, if that does not certify the leaf, evaluates it again as token_interval does.
