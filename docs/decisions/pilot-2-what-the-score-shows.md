# Pilot 2: where the Q_grid gain comes from, and what it does not show (22 October 2026)

A note on reading the open-lane pilot's numbers. Run `open-lane-pilot-tiny-3`, tiny max2 network (8 tokens, 64 inputs, 80 weights), budgets 135, 270, 540, 1,080, 2,161.

## Correction (23 October 2026): round 4 is a real algorithmic gain

This note was written after round 3 and reads every gain as accounting. That holds for rounds 1 to 3 (the Q_grid jump), not for round 4. Its full proof (Full64, length 719) rests on a new sufficient test. With `mx_c` the largest off-diagonal entry of column c of M, `top_c` the column's largest entry and `dm_c = M[c,c] - mx_c` its diagonal margin, the pair (a, m) with a < m is certified by

    top_a - M[m,a] < dm_m

Sound for every weight (proved in the agent's general layer): for each wrong output j, the margin (M[m,a] - M[j,a]) + (M[m,m] - M[j,m]) is at least (M[m,a] - top_a) + dm_m. It decouples the two columns, so once each column's summaries are known a pair costs 2 operations instead of a comparison against every wrong output; pairs it cannot certify fall back to a refined test (6 operations) or the exact one (16).

The matched comparison is the same cubic method written as a counted checker (1,152), not the proof file (1,227): Full64 is 38% shorter (Q 0.510 against 0.332 matched and 0.347 for the proof file; cost of finishing 6.01 against 3.75 and 3.52). Offline estimates put the gain at 2.4 to 2.7 times at v64 and 3.3 to 3.6 times at v128 against the matched method: it grows with the vocabulary, but it is not shown to lower the exponent. Whether the frozen method transfers is what the frozen-transfer evaluation tests.

## The numbers

| proof | 135 | 270 | 540 | 1080 | 2161 | Q_grid | full proof |
|---|---|---|---|---|---|---|---|
| brute force | 0 | 0 | 0 | 0 | 0 | 0.000 | 4,323 |
| cubic (contract + interval, with budget) | 0 | 0 | 0 | 51/64 | 64/64 | 0.359 | 1,227 |
| agent, after 3 rounds | 0 | 6/64 | 38/64 | 64/64 | 64/64 | 0.538 | 1,031 |

Q_grid is the mean over the five budgets of the best certified fraction within each budget.

## Same mathematics, different accounting

Both the cubic proof and the agent's rest on the same fact: the network is linear in the summed one-hot, so the logits of (a, b) are column a plus column b of M = U L E. The agent found this on its own in its first minute, but it is not a new idea. The gain comes from three accounting differences:

1. Fixed cost. The cubic proof computes all of M (contract 384) before certifying anything: 80 + 384 = 464 before the first input, which is why it has nothing under 540. The agent pays 80 + 63 (one guard forward pass) and then buys columns at 48 each as its plan needs them.
2. Price per input. One interval leaf costs about 86 and certifies a group; the agent's exact checks from columns cost 16 per pair of inputs, 7 per diagonal, 4 per pair under a sufficient test that reuses column maxima. On a network this small the leaf is overpriced for the job.
3. Structure. The cubic proof's file pays tree 23 and read 44; the open lane charges a checker's description nothing and only bounds it (size budget 8,192 + 4E).

The honest size of the gain is the full-proof comparison, 1,031 against 1,227 (16%), where fixed costs no longer matter. The Q_grid jump from 0.36 to 0.54 is almost entirely item 1 read through the budget grid.

## What the metric rewards that is not understanding

- Input selection: a partial proof certifies the cheapest inputs the budget allows (the agent picks them by exhaustive search in Python; the hand baseline 4 does the same, largest groups first). A certified 38 of 64 says nothing about the other 26.
- Budget boundaries: proofs are tuned to land just under a budget (536 under 540, 269 under 270); nothing between budgets counts, so the agent left a 1,031 to 840 improvement of the full proof unmade because it would not move the score.
- The price list: constant-factor gains against cost-v3's prices look the same on the scoreboard as structural gains.

## What would be gaming, and is open only on this network

On the tiny network the size budget cannot separate a checker from the weights (80 weights fit in 8,512 units with room): a checker carrying a copy of the weights, verifying it with 80 comparisons and 80 gates, and counting by concrete computation would certify 64 of 64 for about 320, under the 540 budget, with no understanding. Documented in docs/COUNTED.md; the agent has not done it. The sign would be full coverage at a few hundred with a description size near the budget. On v64 and up the budget forbids it.

## How to tell insight from accounting

On one network only the measure can be checked: use the full-proof length rather than partial points; re-score under other reasonable price lists (the receipts carry what is needed: bill, extract, read, description size) and see whether the ranking holds; read the general layer (a lemma about the weights, proved for all weights, versus a list of inputs). None of this stops gaming; it detects it and feeds the cost model.

What stops the one-network kind is a method rather than a proof: one general layer, parametric in the sizes, applied unchanged to networks the agent did not tune on (other seeds, larger vocabularies), with per-network data only through the charged certificate. Then a weight copy and a hard-coded plan have nowhere to live and input selection must be a rule the checker applies. What that establishes is that the frozen method generalises; it does not establish understanding (accounting gains transfer too), and the growth of length with the vocabulary is evidence about scaling, not insight. Understanding is a separate claim: the relationship found, why it explains the computation, what it predicts. That is the ticket's frozen transfer and knowledge conditions, and the v64 pilot.

## Cost-model changes worth considering before v64

- Charge description size at a rate calibrated so that the brute-force checker's description costs what its proof-file tree costs in the fixed rules lane, making the two lanes consistent and making proof-specific information cost something.
- Price a numeral by its bits rather than a flat 1.
- Record the bill per category in every receipt, so any proof can be re-priced offline.
