# Cost model `cost-v4`

A proof's length is the work the checker does on numbers to check it, counted in exact operations. The definition lives in `core/check/cost.py`, whose docstring is shown to the agent; this page adds the reasoning and the numbers for max2.

## What counts

Each operation on exact numbers counts 1: a multiply-add, an addition or subtraction, or a comparison.

| Category | Charged for | Cost |
| --- | --- | --- |
| `extract` | converting the weights exactly | 1 per parameter (this is E) |
| `read` | reading the numbers a proof supplies | 1 per number of an approximation's form: each value (`dense`), each entry of the two factors (`low_rank`), each segment's start, end and value (`row_segments`) |
| `contract` | multiplying a×b by b×c matrices | a·b·c, in the cheapest order; biases cost one matrix-vector product each |
| `approximate` | checking an approximation | 2 per entry, plus a·r·c to multiply out low-rank factors; `row_segments` also 1 per entry and 2 per segment for the column index that locates a range's segments. A range bounded through an approximation is charged to `interval`: `dense` 2 per token per output; `low_rank` 2r per token plus 3r per output; `row_segments` 2 per merge step of the two rows' segments plus 2 per output to locate them; then 1 per output to subtract the error |
| `single` | one exact forward pass | linear on a one-hot input: output size per position; linear on a vector: in·out; bias, sum or add: its size; final comparison: outputs − 1 |
| `interval` | bounds over a set of inputs | linear on a token set: 2·out per token; linear on a box: 2·in·out; output linear on token sets: 2·outputs per token (or what the approximation's form needs); output linear on a box: 3·in·outputs |
| `tables` | rows of `token_interval` leaves that depend on their token alone, computed once per proof | lookup: output size per token; product with a constant matrix: in·out per row; adding or multiplying by a constant: the row's size; sum: (size − 1) per result entry |
| `token_interval` | everything else in `token_interval` leaves | the same counts per row, or per input where a value is kept per input, doubled for interval values; boxing rows: 2 per entry; decision per term and other output: 3 per input (exact weight) or 5 (interval weight), or 3 per token plus 8 with several varying positions; then 1 per input and other output, and outputs − 1 for the constant part |

The plan costs nothing: the split tree (its positions, cuts and leaf rules), the contraction chains, the symmetry flag, names and notes.

Rules adopted through the rule route (docs/RULE_ROUTE.md) add a category of their own for their per-leaf work and use `tables` for work they share across leaves; each rule's description, shown to the agent, lists its charges (for `token_convex`, see `rules/token_convex/rule.py`). Adopting a rule changes the length of no proof without its leaves.

## Why these choices

- **Every operation on numbers is charged.** That includes converting the weights and reading the numbers a proof supplies, so no work on numbers can hide in a large proof file or in a hint the checker trusts. The checker trusts nothing a proof claims. For this charge to be fair, every operation must be on a small number: proof numbers are required to be dyadic and bounded (see `docs/RULES.md`), so a proof cannot make one operation secretly expensive. A proof that is still slow to check, for any reason, is cut off by a per-proof time limit (`check_timeout_s`) and rejected.
- **The plan is free.** Where to split and which rule to run on which box is bookkeeping with whole numbers, as is counting what an accepted leaf certifies (under symmetry too). In Gross et al. a proof's length is the cost of running its computational part on the model, and the code of that part is not counted. The open lane follows this (a checker's code is capped by a description budget, not charged), and so does the fixed rules lane since `cost-v4`, so the same proof costs the same in both lanes. The proof file's size is capped instead (its numbers and strings, and its tree's nodes, in proportion to the number of inputs). A large plan buys nothing by itself: every rule's work is charged where it runs, and a skip leaf certifies nothing.
- **Searching is free.** A recipe may spend any amount of floating-point work finding a proof. Only checking it counts, as in Gross et al.
- **One-hot inputs are lookups.** A linear map applied to a one-hot token costs its output size, the cost of reading one column, not a full matrix-vector product. Brute force is charged the same way, so this choice does not favour any proof.
- **Bounds cost double.** An interval operation works on a centre and a radius.

## Change from `cost-v3`

`cost-v4` (9 November 2026) stops charging the plan: the tree (1 per node), the symmetry count (1 per accepted leaf) and the proof file's plan entries in `read` (its schema and network strings, split positions and cuts, rule names, flags and names). `read` keeps the numbers of the approximations, which `cost-v3` counted the same way, and nothing else changes. Under `cost-v3` the same proof had two lengths, one per lane: brute force on the tiny max-of-2 network cost 4,323 as a proof file (80 for the weights, 64 forward passes at 63, 73 tree nodes and 138 numbers and strings) and 4,112 in the open lane, which charges a checker's code nothing. Now it is 4,112 in both. The reasons are in `docs/decisions/same-proof-same-cost.md`.

Every proof is shorter by its plan; no count changes. E is unchanged and B, now E plus one forward pass per input, is shorter by the brute-force tree (table below). Results measured under `cost-v3` stay as they are; the ones in this repository are re-measured into new files in `results/cost-v4-2026-11-09/`, and a run elsewhere is re-measured next to itself with `python -m core.remeasure --run <run folder>`.

## Change from `cost-v2`

`cost-v3` (16 October 2026) adds the `token_interval` rule and its two categories. Nothing else changes: every proof without `token_interval` leaves has the same length as under `cost-v2`, and E and B are unchanged (the manifests were refilled only to record the version). Rows reused across leaves are charged once because the checker computes them once; that sharing is the compression Gross et al. get from precomputing EQKE, EVOU and EU. A brute-force check of one input is still the full single rule, so B is unchanged and stays comparable.

## Change from `cost-v1`

`cost-v2` changes the approximate rule's charges and nothing else. Bounding a token range through a `row_segments` approximation walks the segments of two rows together, and each step takes a difference and a comparison, exactly what a dense range does per token. `cost-v1` charged such a step 1 instead of 2. In the first max2 runs the agent noticed (its round-5 claim: "one step per segment touched instead of the dense two steps per token") and wrote the contracted matrix as an "approximation" with one segment per entry and error 0: the matrix itself, checked by the same work at half the charge. That made full proofs look 1.5 times shorter than the hand-written one without any new idea. Under `cost-v2` the same proof is longer than the hand-written one, and segments pay only where they are long, which is the actual saving the rule was meant to reward.

The audit that followed found three smaller places where the checker did work the approximate rule did not charge, all of them favouring approximations over the exact check: locating a row's segments in a range (`cost-v1` used a binary search it did not count; now a column index, built when the approximation is read and charged, makes it two lookups, charged), subtracting the error from every output, and the differences of the low-rank factors. None of them could be exploited for a gain, but they are charged now so that the rule costs exactly what it does. E and B do not change, since brute force uses no approximation; results measured under `cost-v1` are re-measured from their saved proofs with `python -m core.remeasure`.

## E and B for max2

E is the extract cost, the least any proof pays. B is the length of the brute-force proof, which checks every input with `single` and nothing else: E plus one forward pass per input. `core/check/costs.py` computes both without running brute force, and a test checks that B equals the length the checker reports for the brute-force proof. That holds on all 20 max2 networks.

| Size setting | Inputs | E | B | B/E | B under `cost-v3` |
| --- | --- | --- | --- | --- | --- |
| v64 (d_vocab 64, d_model 8) | 4,096 | 1,088 | 2,683,968 | 2,467 | 2,696,387 |
| v128 (d_vocab 128, d_model 16) | 16,384 | 4,352 | 40,358,144 | 9,273 | 40,407,555 |

Baselines on `max2-v128-s0` (certified accuracy 16383/16384 for each):

| Proof | Length | B / length | Length under `cost-v3` |
| --- | --- | --- | --- |
| Brute force | 40,358,144 | 1.0 | 40,407,555 |
| Symmetry | 20,338,880 | 2.0 | 20,372,796 |
| Contraction with interval leaves by larger token | 2,444,929 | 16.5 | 2,446,083 |
