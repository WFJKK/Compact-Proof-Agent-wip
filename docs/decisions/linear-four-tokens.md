# The linear network on four tokens: max of 4 and min of 4 (18 November 2026)

Prepared at the user's word on 18 November 2026 ("prepare max 4 linear and min 4 linear"), after the first
compiled-mode run on the linear max-of-2 network (linear-max2-ptl-2).

## Why these networks

On max of 2 the agent's proof (length 100,309, brute force over 26.8) certifies every correct input, and
asking for fewer inputs would shorten it little: every method found there computes the 64 by 64 table
M = U L E (36,864 operations), and the rest is spread evenly over the inputs. That network has no short
proof of most inputs, so it cannot show what a score does with one.

With more than two tokens the same architecture has one. The logits are a sum over the tokens,

    logits(t) = M[:, t1] + M[:, t2] + M[:, t3] + M[:, t4]

so the gap between the right output and any other is linear in the input, and the inputs on which a given
output wins form a convex set. An input with label m and other tokens a, b, c is the average of the pure
inputs (a,a,a,m), (b,b,b,m) and (c,c,c,m). If those are right, and (m,m,m,m) is, the input is right. There
are about V^2 / 2 pure inputs, each tested against V outputs: a proof of length about V^3 whatever the number
of tokens, against V^4 forward passes for brute force. It is partial: an input is lost when one of its pure
inputs is wrong, also where the network is right on the input itself.

That is the shape of the paper's cubic proof on the attention network (short, most inputs, not all), on an
architecture where the Lean service already runs everything.

## The model folders

`models/max4` and `models/min4`: the max2 model's module (`models/max2/model.py`, copied) on four positions;
the label is the largest or the smallest token. Two sizes each:

| Size | Tokens, width | Inputs | Weights (E) | Brute force (B) |
| --- | --- | --- | --- | --- |
| v16 | 16, 4 | 65,536 | 144 | 7,274,640 |
| v64 | 64, 8 | 16,777,216 | 1,088 | 11,257,513,024 |

- v64 is the max2 model's v64 with four positions: the same 1,088 weights, the same description budget of the
  Lean service to within its rounding (13,069) and a plan budget of 6,534 bits. A forward pass costs 671
  (655 on two tokens). Brute force is never run there; B comes from the shapes.
- v16 is small enough for brute force to be run, by the Python checker and by the Lean service.
- Training: max2's optimizer, learning rate and batch size, 80,000 steps instead of 4,000. Measured before
  the zoo was trained (seed 0, 200,000 sampled inputs): at v64 97.5% after 4,000 steps, 99.1% after 10,000,
  99.8% after 80,000, where it has levelled off. At v16 above 99.99%.
- Ten seeds a size, four held out, with the max2 model's split seed: at v64 the same seeds are held out
  (2, 6, 7, 9), so s0 and s1 are development networks; at v16 seeds 0, 1, 2 and 6 are held out.
- The zoo (trained on the cloud machine, about three minutes a network at v64): at v64 the networks are
  right on 99.78 to 99.84% of their inputs (max4) and 99.74 to 99.84% (min4), so each is wrong on 27,000 to
  43,000 inputs. At v16 they are right on every input or on all but one.

## What the Lean service does at this size (cloud machine, 18 November)

- The network is exported and its protected module built in about 20 s (the exporter enumerates the
  16,777,216 inputs once, to name the task).
- A probe checker (the single-input rule on the 64 inputs whose first three tokens are 0, with its soundness
  proof) compiles in 2 s, runs on the network and its eight copies in 2 s (bill 42,944 = 64 forward passes of
  671) and is accepted and scored in 7 s.
- A compiled checker that mentions `allInputs task.space` builds the list of all 16,777,216 inputs before it
  does anything else: the same 64 forward passes took 32 s. The agent is told this (the model folders'
  `open_lane.compiled.notes`); it is a fact about the tools at this size.
- At v16 the service ran brute force (65,536 forward passes of 111, a bill of 7,274,496) on the network
  and on its eight copies, and the submission took 103 s. So a check runs about 0.7 million charged
  operations a second here, nine runs to a check: a bill of 10 million takes about two minutes, one of 200
  million about 40. A development compile gives the nine runs 120 s.

## The runs that are prepared

- `config/pilot/linear-max4.yaml`, `config/pilot/linear-min4.yaml`: the pilot's base on `<model>-v64-s0`,
  the seed check on `<model>-v64-s1`, no baselines replayed, 4 GB for a run_python call.
- `config/pilot/linear-<model>-ptl-1.yaml`: the first run. python_then_lean, the checker's run made by the
  service, one discovery round and four formalization rounds of 60 minutes from an empty workspace, then the
  reading of the best checker. No seed check and no scaling question. Caps: $30 a session, $180 the run.
- `config/pilot/linear-<model>-dry.yaml`: the same run given the probe module, for the dry start alone:

      python3 -m core.open_lane.dry_start --config config/pilot/linear-max4-dry.yaml --sandbox seatbelt --check

The agent is told the task and the sizes, as always, and nothing about convexity, pure inputs or any proof.
The worked example is brute force on the tiny two-token network, as for max2.

## Reference numbers (estimates in Python, from the zoo's masks; not Lean, not checked by the service)

Counts are exact (from the stored masks of right inputs); lengths are a simple count of operations.
`python3 scripts/linear4_reference.py models/max4 max4-v64-s0` prints them (about 2 GB and a minute).
At v16, where the networks are right on every input, the pure inputs certify every input.

On `max4-v64-s0` (16,743,886 of 16,777,216 inputs right):

| Proof | Length | B over length | Right inputs certified | Cost of finishing (the score today) |
| --- | --- | --- | --- | --- |
| Brute force | 11,257,513,024 | 1 | all | 1 |
| Pure inputs (a,a,a,m) | about 423,000 | 26,600 | 71.0% | 3.5 |
| Doubled inputs (a,a,b,m) | about 11.4 million | 980 | 98.0% | 47 |
| Doubled inputs, then the multisets left over | about 16 million | 690 | all | 690 |
| Every multiset, with M | about 193 million | 58 | all | 58 |

The other networks looked at give the same picture:

| Network | Right | Pure inputs certify | Doubled inputs certify |
| --- | --- | --- | --- |
| max4-v64-s0 | 99.80% | 71.0% of the right inputs | 98.0% |
| max4-v64-s1 | 99.80% | 69.4% | 97.9% |
| min4-v64-s0 | 99.81% | 71.0% | 98.0% |
| min4-v64-s1 | 99.84% | 72.1% | 98.2% |

No input is certified wrongly by either argument on any of the four (checked against the masks).

- "Pure inputs" is the cubic proof above. "Doubled inputs": (a,b,c,m) is also the average of (a,a,b,m),
  (b,b,c,m) and (c,c,a,m), about V^3 / 3 inputs to test, a proof of length about V^4.
- "Multisets": the output depends only on the multiset of tokens; every multiset tested with M. The row
  "then the multisets left over" names the 19,016 multisets the doubled inputs leave, which a plan could not
  do within its budget (6,534 bits): it is what free hints would allow, not a proof under the rules.
- Under cost of finishing, as the pilot scores today, the short proofs look poor and the complete one best:
  each right input left out is charged a forward pass (671), and 29% of 16.7 million inputs is 3.3 thousand
  million. A score that asked for a share of the inputs would rank them the other way. Not built; the
  user's open question of 18 November.

## Not done

- No reference proof has been written in Lean for these networks. The library's linear proof (its entries 1
  and 5) has not been put through today's service.
- Scoring by targets (a share of the inputs asked for) is not built.
- No run has been made.
