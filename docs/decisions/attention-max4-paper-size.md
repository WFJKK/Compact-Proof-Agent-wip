# The attention max-of-4 network at the paper's size, prepared for a first run (23 November 2026)

Prepared at the user's word on 23 November 2026, while the first linear max-of-4 run went on the Mac ("we will
implement attention in the meantime"). It is the network on which the paper this work follows defines its
cubic proof, so that proof is the reference.

## The network

`models/attn-max4` at v64, the paper's own size: one layer, one head, attention only, no biases, learned
positional embeddings, read at the last position; vocabulary size 64, width 32, four positions.

| | |
| --- | --- |
| Inputs | 16,777,216 |
| Weights (E) | 8,320 |
| A forward pass | 13,159 operations |
| Brute force (B) | 220,771,393,664, from the shapes, never run |
| attn-max4-v64-s0 | 16,775,920 inputs right (99.992%) |

The zoo is the one trained on 19 October (ten seeds; s0, s2, s3, s4, s7 and s8 are development networks).
Nothing was trained or changed for this.

## What the Lean service does at this size (cloud machine, 23 November)

- The first compile against the network also builds its module: 113 s, once per work folder.
- A probe checker (the general single rule `I.gsingle` on the 64 inputs whose first three tokens are 0, with
  its soundness proof): the nine runs (the network and its eight copies) in 8 s, a bill of 842,176 (64 forward
  passes); accepted and scored in 14 s. 58 of the 64 inputs certified.
- So the service runs about one million charged operations a second here, nine runs to a check. A bill of 5.6
  million (the library's version of the paper's cubic proof at this size, by its bill formula) takes about 50
  s; a lean_check preview's 120 s holds bills up to about 13 million. The Mac has been 2.6 to 3 times faster.
- Budgets the service sets for this network: description size 24,576 units (the cap), plan 49,927 bits (a
  quarter of the weights' 199,710 bits).

## The runs that are prepared

- `config/pilot/attn-max4.yaml`: the pilot's base on `attn-max4-v64-s0`, the seed check on `attn-max4-v64-s2`
  (s1 is held out), no baselines replayed, 4 GB for a run_python call.
- `config/pilot/attn-max4-ptl-1.yaml`: the first run, from an empty workspace: python_then_lean, the
  checker's run made by the service, one discovery round and four formalization rounds of 90 minutes (the
  attention pilots' length), then the reading. Caps $40 a session, $200 the run. Score: cost of finishing.
- `config/pilot/attn-max4-dry.yaml`: the same run given the probe module
  (`config/pilot/start/attn-max4-probe/Probe.lean`), for the dry start alone:

      python3 -m core.open_lane.dry_start --config config/pilot/attn-max4-dry.yaml --sandbox seatbelt --check

- `models/attn-max4/config.yaml` has the open-lane blocks for both modes. The worked examples are brute force
  on the tiny two-token attention network (`attn_max2_tiny_scored`, `attn_max2_tiny_run`), as for attn-min2.
  The notes say how the tools behave at this size and nothing about any proof.

## Checked on the cloud machine

- The dry start: READY.
- A rehearsal of the run (its dry-start config, the fake backend playing three scripted sessions, the real
  Lean service at eab37d3; no API call): round 0 replays nothing; in round 1 the agent's Python runs the
  network on all 16,777,216 inputs in numpy in 29 s and counts 16,775,920 right, the zoo's number; in round 2
  lean_check shows the service's run and the submission is accepted and scored; the proof is locked, the
  reading opens `py/locked_proof.json`, and the report is written.
- Tests: `tests/test_attn_max4_open_lane.py`.

## Found on the way: one metric took 40 s a call at this size

`core/scoring.py`'s `q_above` cut the brute-force line at every one of its steps, one per input, in a Python
loop: about 40 s a call at 16,777,216 inputs. Every round's prompt and every report call it per network, so
it added minutes to each round of the four-token runs (the rehearsals' reports took about 200 s). Above
100,000 steps it now sums the same pieces with numpy: 4 s, the same value to 1e-12 (a test compares the two;
40 random cases agreed to 8e-14). Lines of fewer steps take the old loop unchanged.

## References (not checked by today's service)

| Proof on attn-max4-v64 | Length | Right inputs certified | Where from |
| --- | --- | --- | --- |
| Brute force | 220,771,393,664 | all | the shapes |
| The paper's cubic proof | B/12,283 | 97.5% | 19 October: their code on our network, length in the fixed rules lane's units |
| The same, the library's Lean version (entry 7) | about 5.6 million, B/39,000 | | its bill formula at this size, not run here |
| token_convex version 2 (hand-built, fixed rules lane) | B/14,836 | all | 19 October |

Under cost of finishing the cubic proof scores about 40: the 2.5% it leaves are charged a forward pass each.

## Not done

- The paper's proofs have not been put through the service on this network.
- Scoring by targets (a share of the inputs asked for) is not built: the score is cost of finishing.
- No run has been made.
