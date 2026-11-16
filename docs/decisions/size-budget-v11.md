# The description-size budget follows the network (16 November 2026)

Decided with the user on 16 November 2026, after run attn-min2-ptl-3. The Lean service's policy v11
(Compact-Proof-Checker, scripts/accept.py; the reasons in its docs/COUNTED.md, "The size budget").

## What happened

The checker of run attn-min2-ptl-3 measured 11,156 against a budget of 13,376 (8192 + 4E on attn-min2
v64d8-s1) and certified half of the inputs. The other half needs code of about the size of the first half's own
(its row checks 1,544, a threshold table 561, the shared checks it reuses), so a full checker would land near or
over the budget. The 672-input proof of attn-min2-ptl-1 was refused scoring at 14,043 against the same budget.
The user asked to raise the budget and whether it could follow the network instead of a fixed formula.

## The rule

What the budget blocks is a checker that holds a copy of the weights in its code, checks the copy against the
weights at about one charged operation per weight, and then computes on it in free arithmetic. So the budget is
set from the least a copy holds, `weight_bits`: each weight's sign and its significant bits, from its highest to
its lowest nonzero bit. On the zoo these bits do not compress (lzma, bz2 and zlib save under 1%) and the signs are
balanced; a float32 weight has about 24 of them.

    budget = max(8192 + 4 E, min(weight_bits / 2, 16384))

- Where half of `weight_bits` decides, a checker holds at most half of what the weights are, and a copy measures
  at least twice the budget. Half because, in the zoo's attention networks, the embedding and the unembedding,
  which every logit needs, hold 47 to 79% of the bits: at half, a copy of both leaves under 700 units for code
  (v24) or does not fit (v64d8).
- `8192 + 4 E` decides on small networks (attention at v16), where an honest checker is about as large as the
  weights; the budget there is v10's.
- The cap keeps large networks where they were: from E = 2,048 on, `8192 + 4 E` is over any honest checker so far.
- No budget goes down. attn-min2 v64d8-s1: 13,376 becomes 15,563 (room beside the round-2 checker: 2,220
  becomes 4,407). max2 v64-s0: 12,544 becomes 13,010.

## What was considered and not done

- A fixed raise (8 per parameter, or a larger base): either too little on v64d8 or a budget at the size of a copy
  on v16, whose weights hold 13,052 bits.
- Charging description size over the budget instead of refusing: a partial copy can save about a hundred
  operations per unit of code it holds, so the price per unit that stops it would make honest code costly.
- Counting each distinct piece of code once: it would make the agent's checker smaller, but a table can then be
  written as a list of choices among a few hundred shared pieces, each new node carrying several bits, so a
  copy would measure a fraction of its size. Sharing is sound only with each reference charged its length in
  bits.

## Open

- The plan (policy v9) is bounded in entries, not in information. Whether a plan can carry a copy that the
  checker checks against the weights at run time is open (see the project's notes of 16 November).
- On the v16 networks a copy of the embedding and the unembedding fits beside about 4,000 units of code, as it
  did under v10.
