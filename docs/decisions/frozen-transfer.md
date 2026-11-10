# Frozen transfer: evaluating methods, not proofs (decisions, 22 October 2026)

Why: pilot 2 showed that on one network the budget-grid score cannot separate a better understanding of the network from better spending of a budget (docs/decisions/pilot-2-what-the-score-shows.md). The next evaluation judges a method on networks the agent did not tune on. What that establishes, stated carefully: whether the frozen method generalises beyond the networks it was developed on. It does not by itself establish understanding (a bookkeeping gain transfers too, and a real discovery can be specific to one checkpoint); understanding needs the relationship found, why it explains the computation and what it predicts, with the accounting secured independently. Discussed with the reviewer on 22 October; its amendments and corrections are included.

## The submission is a method

A method is: the Lean general layer (checker `D`, soundness theorem, dependencies), parametric in the sizes, which it reads through `weightShape`, proved for every size and every weight; a recipe (Python, run in the recipe sandbox) that produces the certificate from a network's weights; the method's hyperparameters, budget handling and input-selection rules, which live in the recipe. The service checks the general layer once (replay, soundness at the fixed statement, closure, size budget) and then, per network of a family, runs the recipe, evaluates the instance and writes a receipt. On small networks the instance is kernel-checked; on large ones the compiled checker evaluates it and the receipt says so (`execution_assurance`). Certificate-generation resources (recipe time, memory) are recorded separately from verification cost and never enter the length.

## Feedback and score

- The score is Q_exact: the log-area of the verified certified-accuracy frontier over [max(E, B/1000), B], normalised by log(B / L0), computed from the actual lengths of the proofs the method produces when the evaluator requests one at each budget of a fixed dense schedule (about twelve per decade, frozen before the experiment, the same for method and baseline). The frontier is the record; cost of finishing is the tie-breaker and is always reported separately, using the exact fallback cost of every uncovered input, never an average. Over-budget or invalid proofs score zero at that budget.
- Feedback, every round: Q_exact on each development network, one row per network across the sizes, plus the mean, measured on the same schedule (so development submissions are a method and its plans, not loose proofs; otherwise the agent chooses where its points sit, the 13 October effect). The agent may study those weights and tune.
- Score, once, at the end: the same on held-out networks, from the frozen method, with the improvement over the matched baseline on the same network reported per row, and the failures reported with the successes. Averaged equally across seeds within a size, then across sizes. Four seeds per size is evidence of limited precision; the report says so.
- The dev-to-held-out gap measures generalisation across checkpoints, not "how much was tuning": tuning can find structure that transfers, and checkpoint difficulty and sampling noise move the gap too. Report rows, not only the gap.
- Size extrapolation is a separate condition: develop on v64 only, score on v128 as well. Harsher, and it tells more; not the default, because the agent cannot debug its method at a size it never sees. Parameterising the code is the precondition, not the result: whether the mathematics and the proof construction hold at larger sizes is what the runs measure. The zoo's v64 (width 8) and v128 (width 16) change vocabulary and width together; conclusions about scaling in V need settings that vary V with d fixed, which are new zoo entries.

## What is frozen

Everything the final evaluation runs: the Lean code and its dependencies, the recipe, hyperparameters, budget handling and selection rules, the checker version (the lock), the cost model and the scoring protocol. The frozen recipe may read a held-out network's weights to generate its certificate; the research agent receives nothing from the final evaluation. A run records the frozen method's digests, as it records the checker's identity today.

## Held out, enforceably

- During development the held-out checkpoints, their proofs and their results must be unreachable, not merely labelled. On Linux the recipe sandbox (Landlock or container) and the open-lane session's `run_python` enforce this; on a Mac the process sandbox does not (the probe reads other weights), so a development run on a Mac must not have the held-out files on the machine at all, and the final evaluation runs where the agent never ran.
- A final set that is inspected and then followed by revisions becomes development data. Keep a genuinely untouched final set with fresh seeds, trained only when the evaluation happens (the zoo's training is deterministic in the seed, so this is a manifest entry, not a new procedure), and use the existing held-out seeds for the iterations before it.

## Scope of the claim

A high held-out score shows transferable verified efficiency: the frozen method generalises to networks it was not tuned on. It does not show understanding or mechanistic novelty: an accounting loophole or a standard optimisation transfers too, so the matched cost model and evaluator-controlled budgets stay necessary, and the growth of length with the vocabulary is evidence about the method's scaling, not a proof of insight. Understanding is claimed separately, from the relationship found, why it explains the computation and what it predicts. A discovery specific to one checkpoint is reported on its own even if it transfers badly.

## The cost model to freeze first (cost-v4)

(Note of 9 November 2026: the name cost-v4 went to a different change, the fixed rules lane no longer charging its plan, and that change replaces the calibrated description charge below; see same-proof-same-cost.md.)

Before any held-out number: a free tensor-size read (the pilot's guard did two jobs, well-formedness and certifying one input with its mirror, so the saving is 63 minus whatever certifies those inputs instead; rebuild the proof and measure, never subtract); the audited match-compiler constants and the graph constructors allowed; numerals priced by bits; a calibrated charge for the checker's description, versioned; bills tallied by the operation the service executed, with the candidate's label secondary. Then remeasure the agent's proofs and the cubic baseline ported to the counted language on the same accounting; the adversarial regression tests keep running against every change.

## Implementation scope

One new component (the final evaluation of a frozen method on a family), but with three real requirements: a real freeze (digests recorded and checked), access isolation (sandbox on Linux, physical separation on a Mac, fresh seeds for the final set), and reproducible automatic execution (the recipe and the instance evaluation with no agent in the loop). The knowledge conditions of the ticket (what library the agent may read) are set up in the same change, since both are about what the agent can see.
