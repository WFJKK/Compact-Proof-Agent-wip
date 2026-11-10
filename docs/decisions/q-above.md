# Q_above: the score counts only what beats brute force (26 October 2026)

## What happened

The first open-lane pilot on an attention network (`open-lane-pilot-attn-max2-tiny`, minimal knowledge,
64 inputs, brute force 12,571) scored 0.15 under Q_exact after three rounds with no compression at all:
four of its nine submissions were brute force on subsets of the inputs (10, 20, 32 and 48 inputs, at exactly
191 per input plus 136), which Q_exact rewards because the baseline holds only the full brute-force proof
and gives nothing below it. The line of all such subsets scores 0.206 under Q_exact, against 0.250 for the
hand proof (token_convex peeling, 7,384). The same gap existed in every earlier run and went unused, because
proofs that beat brute force were found at once (the linear pilot's cheapest points were real compression:
6 inputs for 269 against 458 by brute force).

## The decision

The brute-force line is part of the baseline, and the score is the improvement over it, normalised by the
room above it:

    b(L) = min(coverage, floor((L - E) / c)) / n
    Q_above = integral of (a(L) - b(L))+ over log L / integral of (a_max - b(L)) over log L

over [max(E, B/1000), B], with c the single rule's charge per input and coverage the inputs brute force
certifies, both from the run's round-0 brute-force record; E the extract the open lane charges (the zoo's E);
a_max the share of inputs the network gets right. A proof earns credit only where it certifies more inputs
than brute force of the same length.

Corrections from the review of the proposal, adopted:

1. The line must be achievable: its coverage and cost come from the established baseline (the round-0
   record), not from assuming every input certifiable at one price; without a record the line is an estimate
   and the metrics say so. The open lane's accounting is the same (its single and gsingle charge c per input,
   its extract is E), checked on the tiny networks.
2. The positive part, integrated exactly over the merged breakpoints, not a difference of raw Q_exacts: the
   hand proof ties the line at its first point (8 inputs for 1,664) and wins after, so the raw difference
   gives 0.055 and the positive part 0.078.
3. Patience: a scored proof counts as progress only if it raised Q_above; a duplicate or a worse proof does
   not; a new accepted lemma still does.
4. What the number means: a score of 0.05 is 5% of the remaining log-area headroom, not 5% of the operations
   saved and not a statement about understanding.
5. Re-scoring old runs does not make them comparable by itself: `core.rescore` writes the versions the
   numbers depend on (cost model, checker, the Lean service's identity and knowledge condition) next to them.

## Numbers under Q_above

- The tiny attention max2 network: the line 0.206 (Q_exact), the hand proof 0.078, the pilot's subsets 0.
- The tiny attention max4 and min4 networks: the hand proof 0.36.
- The linear pilot (`open-lane-pilot-tiny-3`): 0.252 after round 1, 0.363 after round 4 (Q_exact 0.413, 0.510).

## Not changed

Q, Q_grid, Q_exact and cost of finishing stay available and are reported; archives keep every verified
submission, scored or not; the Lean service is untouched.
