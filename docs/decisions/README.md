# Decisions

Design decisions of the open lane and its evaluation, copied here from the project's notes so that a reviewer
working from the repositories can read them. Each is dated; later decisions supersede earlier ones.

- [pilot-2-what-the-score-shows.md](pilot-2-what-the-score-shows.md) (22 October 2026): where pilot 2's
  Q_grid gain came from (fixed cost, input selection, the price list), what the metric rewards that is not
  understanding, the one loophole open on the tiny network, and how to read partial coverage; with a
  correction (23 October): round 4's full proof rests on a real algorithmic gain, a decoupled sufficient test.
- [frozen-transfer.md](frozen-transfer.md) (22 October 2026): the next evaluation. A submission is a method
  (size-parametric general layer plus a certificate recipe), scored by Q_exact on a fixed dense schedule of
  budgets, on held-out networks, with the frontier as the record and cost of finishing (exact fallback
  costs) as the tie-breaker; what is frozen; how held-out is enforced; what the claim is (the frozen method
  generalises) and is not (understanding); the cost model to freeze first (policy v4, then the matched
  baseline remeasured).
- [q-above.md](q-above.md) (26 October 2026): the score counts only what beats brute force. Brute force on
  any subset of the inputs is a proof the agent can always write, and Q_exact rewarded it (the first attention
  pilot scored 0.15 with no compression); Q_above is the frontier's log-area above the brute-force line over
  the room above it, with the review's corrections (an achievable line from the run's own baseline, the
  positive part over exact breakpoints, patience by gain, what the number means, versions kept with
  re-scored runs).
- [same-proof-same-cost.md](same-proof-same-cost.md) (9 November 2026): cost-v4. The fixed rules lane stops
  charging its plan (tree nodes, the proof file's plan entries, the symmetry count), as the open lane never
  charged a checker's code, so the same proof costs the same in both lanes (brute force on the tiny max-of-2
  network: 4,112 in both; 4,323 in the fixed rules lane under cost-v3). Replaces the description charge planned in
  frozen-transfer.md.
- [one-network-pilot.md](one-network-pilot.md) (10 November 2026): the pilot is about one network and has
  three parts. The proof rounds are driven by cost of finishing, the one score the agent is shown: no budgets
  to land under, no points to place, brute force on any subset 1. Then the seed check: the best proof's
  checker, locked by module, runs unchanged on a second seed of the same sizes, and the agent writes only
  that network's instance. Then the scaling question: how the checker's cost grows with the sizes, against
  brute force's, with what can be proved of it as lemmas. A pilot's size must rule out a copy of the weights
  in a checker (the first: the linear max-of-2 network at 64 tokens, width 8). The pilot is one config and the
  model a few lines of it; what differs between architectures is stated by the model folder. Runs over
  several sizes are parked.
