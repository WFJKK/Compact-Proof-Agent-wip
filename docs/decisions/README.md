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
- [agent-told-nothing.md](agent-told-nothing.md) (10 November 2026): the agent is told the specification,
  what a proof is and what it costs, and nothing about what works on a network. From 20 October its tools
  reached the Lean project's docs, README and the fixed rules' sources, so no open-lane run since shows
  unaided discovery (counts and lengths stand). What a run shows is now a surface per knowledge condition,
  with excerpts that are parts of the Lean project's files; a run does not start if anything shown matches a
  forbidden expression; and a proof that mentions a constant of the Lean library which the run does not
  show is recorded without a length, by Lean's account of the compiled modules. Not closed: the agent can
  ask Lean about the library, and an unconfined machine lets its code read files. Both are named, with what
  the Lean project has to change.
- [size-budget-v11.md](size-budget-v11.md) (16 November 2026): the Lean service's description-size budget
  follows the network: 8192 + 4E, or half of the least a copy of the weights holds (each weight's sign and
  significant bits) where that is more, at most 16,384 (policy v11). attn-min2 v64d8-s1: 13,376 becomes 15,563.
  Why half, why the cap, and what was considered and not done.
- [no-wasted-runs-v12.md](no-wasted-runs-v12.md) (17 November 2026): what guards a run against a copy and
  against lost work. The size budget cannot hold a copy out on a network of attn-min2 v64d8's size (32,768
  random bits measure 11,536 when written with an alphabet of variables); the seed check with the plan bounded
  in information does (policy v12). A dry start before a run, replaced carried modules, and the measured
  length of a proof refused scoring.
- [run-by-compiled-code-v15.md](run-by-compiled-code-v15.md) (18 November 2026): a result is soundness
  (mathematics, kernel-checked) and the run on the network (arithmetic). With `open_lane.instance: compiled`
  the agent proves soundness alone and the Lean service runs the compiled checker for the count and the bill
  (its policy v15): the linear proof's check goes from 82 minutes to 21 s, and the proof from ten modules to
  one. The kernel mode stays, the default stays kernel, and every result says which it was. With it: start
  drafts, for work that no run folder can hand on.
- [linear-four-tokens.md](linear-four-tokens.md) (18 November 2026): the linear network on four tokens, max
  of 4 and min of 4 (`models/max4`, `models/min4`), prepared for a first run each. With more than two tokens
  the architecture has a short proof of most inputs by convexity (pure inputs: about V^3 operations, 71% of
  the right inputs at 64 tokens, brute force over 26,600), which max of 2 has not. The sizes, the training,
  what the Lean service does at 16,777,216 inputs, the run and dry-start configs, and reference numbers.
- [attention-max4-paper-size.md](attention-max4-paper-size.md) (23 November 2026): the attention max-of-4
  network at the paper's size (`models/attn-max4` at v64) prepared for a first run: what the Lean service does
  there, the run and dry-start configs, a rehearsal, references, and `q_above` summed with numpy on lines of
  many steps (it took about 40 s a call at 16,777,216 inputs).
- [scaling-proofs.md](scaling-proofs.md) (23 and 24 November 2026): the scaling proofs after a run, `python3 -m
  core.loop scale --run <run>`: how the cost of every scored proof on the run's frontier grows with each size,
  as theorems. Four links per size (a general checker, its exact cost, the formula, brute force), a first
  session for the general checker and one per size, further sessions with `--again`; each lemma checked by
  Lean against the proofs' checkers, printed in full, and marked when its statement names none. A package of
  its own (`core/open_lane/scaling`) that reads the sizes from the network's size setting, so that it can
  follow any open-lane run on one network: no model folder declares anything for it.

