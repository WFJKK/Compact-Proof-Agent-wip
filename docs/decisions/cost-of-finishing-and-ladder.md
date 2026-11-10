# Cost of finishing as the score, on a ladder of sizes (10 November 2026)

## What happened

Every score the pilots were driven by so far could be raised without a better proof:

- Q_grid: proofs tuned to land just under a budget (536 under 540, 269 under 270). When cost-v4 moved B,
  pilot 2's Q_grid fell from 0.5375 to 0.4188 with the proofs unchanged
  (results/cost-v4-2026-11-09/README.md).
- Q_exact and Q_above: the agent chooses where its proofs sit on the length axis, and a partial proof
  certifies the cheapest inputs the agent can find. The area rewards the placement.
- All of them, on one network: a proof made for one set of weights scores like an account of the mechanism.

Cost of finishing moved from 6.0 to 5.7 under the same change of B, which is B's own change and nothing else.

## The decision

1. The score of a network is its cost of finishing:

       B / min over checked proofs of (length + u * c)

   with u the correct inputs the proof leaves uncertified and c what brute force charges for one input (the
   single rule's exact charge, from the run's round-0 brute-force record). It answers one question: how many
   times shorter than brute force is the cheapest complete proof built on the agent's work.
2. A network counts at least 1. Brute force alone always finishes at B, so a network without a proof, or with
   proofs that finish above B, is at 1 and never below (`core.scoring.finishing_ratio`).
3. The score of a run is the geometric mean over all its networks, every size setting together
   (`core.scoring.run_cost_of_finishing`; per size setting `cost_of_finishing_geomean` in the summary).
   Ratios average on the log scale: a factor of 2 counts the same on every network, and one network at 20
   with five at 1 gives 1.65, not 4.2.
4. The agent is shown this score and nothing else (`core/open_lane/prompt.py`, `finishing_scoreboard`): the
   run's score, each size setting's, and per network the cheapest way to finish (the proof used, the inputs
   left, what they cost). A receipt's line says what finishing from that proof costs against B. No Q, no
   budgets, no brute-force line.
5. Patience: under this metric a scored proof is progress only if it raised the score of its size setting,
   as under Q_above (`core.loop.GAIN_METRICS`). Lemmas and verified proofs count as before.
6. The pilot runs on a ladder of sizes with two development seeds each (below), so that one run asks for
   the mechanism of an architecture and task, not for a proof about one set of weights.
7. No complexity proof is required of a submission. The ladder makes scaling visible in the scores per
   size; a statement of how the length grows, and its proof, are asked for afterwards, for the method that
   won. A good proof is never refused because its author could not prove a formula for its cost.

## What this stops, and what it does not

Stopped by construction:

- Budget boundaries: there are no budgets.
- Point placement: one number per network, a minimum over proofs. A second proof helps only if it finishes
  cheaper.
- Brute force on a subset: under cost-v4, B = E + n * c exactly, so k inputs by brute force finish at B
  and score 1.000. Round 0's brute force scores 1.000 on each of the ladder's six development networks (a
  run with the fake backend), and the tests check that a subset by brute force is no progress.
- Picking inputs: a partial proof earns exactly what it saves on the inputs it certifies, against c each.
- One network: a proof that serves a single network moves the run's score by the sixth root of its factor.

Not stopped:

- A constant factor against the price list counts like a structural gain on one size. The ladder is what
  tells them apart: a constant factor is about the same at every size, a better method gains more where
  there are more inputs (n3v4d4 and n4v4d4 differ in the context length alone).
- A separate proof per network still earns on each network. Six of them, each made for one set of weights,
  would score like one method.
- The weight copy (pilot-2-what-the-score-shows.md): the description budget is 8,192 + 4E and these networks
  have 108 to 136 weights, so a checker that carries a copy of one network's weights may fit, as the
  earlier note worked out for the linear tiny network (not measured on these; no agent has done it). The sign is a description size near the budget and a
  different general layer per network; the receipts carry the description size.

What closes the last two is the held-out half of the ladder: the general layer frozen, a new instance
theorem per held-out network, nothing else changed. That evaluation is not automated yet (`core.final`
still refuses an open-lane run), so after the pilot it is done by hand. Until then two things show it: the
agent's answer says which networks its checker covers (WHY IT HELPS), and the archived submissions show
whether the networks' proofs import one general layer or one each.

## The ladder

`tests/attn_maxn_tiny`: Gross et al.'s one-layer, one-head, attention-only transformer on the largest
token, at three sizes, four seeds each, all at full accuracy.

| Size | Positions | Tokens | Inputs | E | c | B | Development | Held out |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| n2v8d4 | 2 | 8 | 64 | 136 | 191 | 12,360 | seeds 1, 2 | seeds 0, 3 |
| n3v4d4 | 3 | 4 | 64 | 108 | 229 | 14,764 | seeds 0, 2 | seeds 1, 3 |
| n4v4d4 | 4 | 4 | 256 | 112 | 287 | 73,584 | seeds 0, 2 | seeds 1, 3 |

Training depends only on the sizes, the seed and the training settings, so seeds 0 and 1 of n2v8d4 and
n4v4d4 are the networks of `tests/attn_max2_tiny` and `tests/attn_max4_tiny`, the same weights bit for bit.
The split is named in the folder's config (`split.held_out_seeds`, new) instead of drawn: the networks
earlier pilots developed on stay development networks, the ones those folders held out stay held out, and
of the new seeds 2 is for development and 3 held out, fixed before they were trained.

Reference points from the hand proofs under cost-v4 (results/cost-v4-2026-11-09/attn-tiny-reference.json;
fixed rules lane proofs, the same lengths in both lanes):

- n2v8d4 seed 1: peeling 7,217, a ratio of 1.71; Gross et al.'s cubic proof 12,436, above B, so 1.
- n4v4d4 seed 0: peeling 7,183, a ratio of 10.2; the cubic proof 5,486, a ratio of 13.4.

A method at those lengths on both seeds of n2v8d4 and n4v4d4, and at 1 on n3v4d4, would score about 2.8.

## Prompt template v4

`core/agent/prompts/open_lane_v4.md`, for runs over several networks scored on cost of finishing. Against
v3: the goal names the mechanism shared by seeds and sizes; the score comes before the rules; the rules of
scoring are lists (what a checker may use, the limits on the general layer, getting the instance through
the kernel); there is advice on how to work (study the weights first, get one scored proof through early,
write the checker for every size by reading the sizes with `I.weightShape`); and WHY IT HELPS asks for the
mechanism, the checker step that relies on it, what would make the proof fail on a network, and which
networks it covers. The Lean sources are pasted as before.

An option, off: `open_lane.second_example` names a second worked example in the Lean project, a scored
proof that is not brute force. The prompt points to it and `read_file` may read its folder; the source is
not pasted. It is more knowledge than the earlier pilots had, so a run with it is another condition and
says so.

## Not changed

Q, Q_grid, Q_exact and Q_above are computed and reported as before (reports, `core.rescore`), and the
median cost of finishing stays in the summary next to the geometric mean. Templates v1 to v3 and the
earlier configs are untouched, and under the other metrics the open-lane prompt is what it was. The Lean
service, the lock and the proof-file schema are untouched, and no result was rewritten. One change reaches
old configs: a new run with `metric: cost_of_finishing` is now driven by the geometric mean over a size
setting's networks instead of the median.

## The pilot

`config/open-lane-pilot-attn-maxn-tiny.yaml`: the six development networks, minimal knowledge, template v4,
the brute-force worked example, 7 rounds, 8 submissions and three hours per session.
