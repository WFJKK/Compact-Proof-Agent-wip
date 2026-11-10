# The same proof costs the same in both lanes (cost-v4, 9 November 2026)

## The problem

Under cost-v3 the two lanes gave the same proof different lengths. Brute force on the tiny max-of-2 network
(V = 8, two positions, 64 inputs) cost 4,112 in the open lane and 4,323 in the fixed rules lane. Both do the same
work on numbers: read the 80 weights (E = 80) and run one exact forward pass per input (63 each, so 4,032).
The difference of 211 was the fixed rules lane charging its plan:

- tree: 1 per node of the split tree (73 here);
- read: 1 per number, string or boolean of the proof file (138 here: the schema and network strings, 9 split
  positions, 63 cuts and 64 rule names);
- symmetry: 1 per leaf certified under the symmetry rule (none here).

The open lane charges none of these. A checker's code is not charged (its size is capped by the description
budget), and read is the certificate only, the numbers the proof passes to its checker. Everything else was
already priced the same in both lanes: E, and every operation on numbers, by the same functions (the open
lane's `single` charges the fixed rules lane's `singleCost`; the attention rules are compared with Python in tests).

## The decision

The plan is free in the fixed rules lane too. Cost-v4 drops the tree charge, the symmetry charge and every plan
entry from read. Read keeps the numbers a proof supplies for the checker to compute with, which in a proof
file are the entries of its approximations (every value of a dense form, every entry of a low-rank form's two
factors, the start, end and value of every segment), at 1 each as before. Nothing else changes. The Lean
mirror of the fixed rules lane's bill (`CountedCheck.lean` of the checker) bills the same, and its reproduction test
against the Python checker stays the gate. The open lane does not change.

## Why this direction

The 22 October plan (frozen-transfer.md) went the other way: charge the open lane for the size of its
checker's description, calibrated so that the brute-force checker would cost what its proof file's tree costs.
We drop that plan for this one:

- In Gross et al. a proof's length is the cost of running its computational part on the model. The code of
  that part is not counted. A plan (where to split, which rule to run on which box) is the code of the
  fixed rules lane's proof, and walking it is bookkeeping with whole numbers, not work on the network's numbers.
- A description charge needs a rate, and none is natural: against the brute-force proof file alone it comes
  out above 0.5 per node, which would price the agent's full proof of pilot 2 above its bill (review brief,
  23 October).
- Both lanes bound the plan instead of charging it: the fixed rules lane caps the proof file (numbers and strings,
  and tree nodes, in proportion to the number of inputs), the open lane caps the description.

Nothing can hide in a free plan: the plan only says which rule runs where, every rule's work on numbers is
charged where it runs, and a skip leaf certifies nothing. Counting what an accepted leaf certifies, under
symmetry too, is arithmetic on the box's bounds.

## Consequences

- E is unchanged. B is E plus one forward pass per input, so it drops by the brute-force tree: 4,323 to
  4,112 on the tiny max-of-2 network, 12,571 to 12,360 on the tiny attention network, 2,696,387 to 2,683,968
  on max2 v64 and 40,407,555 to 40,358,144 on max2 v128. The zoo manifests are refilled.
- Every length in the fixed rules lane drops by its plan; no length grows, and no count changes. Results measured under
  cost-v3 stay as they are. The ones in this repository are re-measured into new files
  (`results/cost-v4-2026-11-09/`), and a run outside it is re-measured next to itself with
  `python -m core.remeasure --run <run folder>`. Scores under the two versions are comparable only after that.
- The agent's prompt shows the cost model's docstring, so it now reads that the plan costs nothing.
