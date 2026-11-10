# The pilot: one network, cost of finishing, a second seed, then scaling (10 November 2026)

## What happened

Every score the pilots were driven by so far could be raised without a better proof:

- Q_grid: proofs tuned to land just under a budget (536 under 540, 269 under 270). When cost-v4 moved B,
  pilot 2's Q_grid fell from 0.5375 to 0.4188 with the proofs unchanged
  (results/cost-v4-2026-11-09/README.md).
- Q_exact and Q_above: the agent chooses where its proofs sit on the length axis, and a partial proof
  certifies the cheapest inputs the agent can find. The area rewards the placement.
- On one network, a proof made for one set of weights scores like an account of the mechanism.

Cost of finishing moved from 6.0 to 5.7 under the same change of B, which is B's own change and nothing else.

## The decision

A run is about one network, and has three parts.

1. The proof rounds. The agent proves the network's accuracy, and the score is the cost of finishing:

       B / min over checked proofs of (length + u * c)

   with u the correct inputs a proof leaves uncertified and c what brute force charges for one input (the
   single rule's exact charge, from the run's round-0 brute-force record). It answers one question: how many
   times shorter than brute force is the cheapest complete proof built on the agent's work. The agent is
   shown this number and nothing else (no Q, no budgets, no brute-force line), and a scored proof keeps the
   loop's patience alive only if it raised it.
2. The seed check. When the rounds are over, the checker of the best scored proof is locked and run,
   unchanged, on a second network: the same model and sizes, another seed. The agent writes that network's
   instance and nothing else. What comes out is how much a checker written for one network certifies on
   one it was not written for.
3. The scaling question. Last, the agent states how the locked checker's cost grows with the sizes of the
   network, compares it with brute force's growth, and proves what it can of that as lemmas. Never scored,
   and a proof is never refused because its author could not prove a formula for its cost.

The agent is not shown networks of other sizes. Which model a pilot runs on is one choice (linear or
attention; max or min of 2 or 4), made in a file of a few lines. The first pilot is the linear max-of-2
network at 64 tokens and hidden width 8.

A pilot's size must be one at which a copy of the weights does not fit a checker (below).

## What the score stops, and what it does not

Stopped by construction:

- Budget boundaries: there are no budgets.
- Point placement: one number, a minimum over proofs. A second proof helps only if it finishes cheaper.
- Brute force on a subset: under cost-v4, B = E + n * c exactly, so k inputs by brute force finish at B.
  On a network with m misclassified inputs, brute force on the correct ones alone finishes at B - m * c,
  a ratio of 1.0002 on the pilot's network.
- Picking inputs: a partial proof earns exactly what it saves on the inputs it certifies, against c each.

Not stopped by the score, and what answers each:

- A proof made for one set of weights (a plan for its inputs, numbers read off its matrices and written
  into the checker). The seed check: such a checker certifies little or nothing on the second seed.
- The weight copy (pilot-2-what-the-score-shows.md): a checker that carries the weights and compares.
  The size. The Lean service refuses a checker whose description is over 8,192 + 4E, and a copy measures
  at least one unit per bit of the weights as the exporter writes them. The pilot's network needs at
  least 34,044 against a budget of 12,544. On the tiny networks of the earlier pilots a copy fits (1,241 to
  3,772 against budgets of 8,384 to 8,736), where it would have finished the linear max-of-2 one at about
  320 against 719 for the best proof an agent found. The seed check would expose a copy too: it certifies
  nothing there.
- A constant factor against the price list counts like a structural gain. The scaling question: a
  constant factor leaves the growth rate where it was.

## The seed check, and what the lock rests on

A scored proof has a general part (the checker `D`, its soundness theorem and what they use, all proved
for every weight) and an instance (the kernel's run of `D` on one network's weights). The lock tells them
apart by module (`core/open_lane/lock.py`):

- The locked modules are the ones that declare the checker and the soundness theorem, and every submitted
  module they import. A constant is taken to be declared in the module it is named after
  (`Candidate.Col.D` in `Candidate/Col.lean`).
- A proof can be locked when its instance theorem is declared outside them. A proof kept in one module
  cannot. Template v5 says so from the first round, each round's receipts say of every scored proof
  whether it is ready, and the aim says so when the proof the score rests on is not.
- When the rounds end, the best scored proof that can be locked is locked (the one that finishes the
  network cheapest). A better proof passed over is recorded with the reason.

In the seed check's session the locked modules cannot be saved over, and before every compile and every
submission they are written into the workspace again from the lock. One change is made: a locked module
may import the protected module of the network it was written for (the checker reads its `graph` and
`task`), and that name is replaced by the second network's. Two networks of the same sizes have the same
graph and task, so a checker and a soundness proof that never look at the weights compile as they are.
The submission must name the locked checker and soundness theorem, and the locked modules always go along.
The receipt carries a hash of every module the service compiled, and the record says whether those hashes
are the locked text's (`lock.in_receipt`).

What it rests on:

- The naming convention above. A proof that does not follow it is not locked, never wrongly locked.
- The service refusing a submission that declares a constant twice (its kernel replay does). The locked
  modules are in every submission of the session, so the name the manifest gives for the checker can only
  be the locked declaration.
- The second network being unseen until then. It is a development network of the model that is not the
  run's, never named in the proof rounds' prompts, and `run_python` is given the run's network only. On a
  Mac the sandbox does not stop a program from reading other files (frozen-transfer.md), so there the
  second seed is unseen by instruction, not by enforcement.

The check uses a development seed, so the model's held-out seeds stay untouched for a final evaluation.

Its result is reported next to the run's score, never folded into it: per network, the count certified
of the count correct, the length, and the cost of finishing.

## The scaling question

A checker cannot branch on a truth value, so its bill depends on the sizes and on its code, never on the
values of the weights. That makes the growth of its cost a statement a theorem can settle. The session
asks for the claim in words (the checker's bill and brute force's cost as formulas in the sizes, and a
verdict: a smaller exponent, the same exponent with a smaller constant, or no gain) and for as much of it
as can be proved, as lemmas, in order of strength: the bill is the same for every weight of this shape;
the bill as a formula for every size; the comparison. The formula for every size needs a checker that
makes sense at every size, which a checker that fixes its sizes does not. The agent may then write a
version that reads them and prove it equal to the locked one at this size.

A lemma's statement is the agent's own, and the service checks only that it is proved. A person reads the
statement before relying on it.

## The first pilot

`config/pilot/linear-max2.yaml`, on `models/max2` at 64 tokens and hidden width 8:

| | Network | Correct inputs | E | c | B |
| --- | --- | --- | --- | --- | --- |
| Proof rounds | max2-v64-s0 | 4,095 of 4,096 | 1,088 | 655 | 2,683,968 |
| Seed check | max2-v64-s1 | 4,092 of 4,096 | 1,088 | 655 | 2,683,968 |

Minimal knowledge, template v5, the brute-force worked example of the tiny linear network (not one of
these networks), 7 proof rounds at most, 4 submissions and three hours per session. A reference point: the
proof library's first entry (an exact test per group of inputs, written for every size) is accepted by the
service on the first network at length 308,097, a ratio of 8.7, with a description size of 4,303 against
the budget of 12,544, in about 15 minutes.

What is known about this size in Lean's kernel, and stated in the prompt: no instance has fitted one
theorem (one `decide +kernel` over a whole run ran out of memory at 6 GB), so an instance is built from
small decided facts; and the 15 minutes above, so that a session of three hours plans its compiles.

## One pilot, any model

The pilot is written once, `config/pilot/base.yaml` (the score, the template, the rounds, the sessions'
budgets, the scaling question), and a run is a file next to it that extends it (`extends`, new in run
configs) and names a model, one network and the second seed. What differs between architectures is stated
by the model folder, in its `config.yaml` under `open_lane`: the worked example and the further Lean
sources (paths in the Lean project) and notes for the agent about the architecture in Lean's kernel. A run
config may still set any of them. The templates hold nothing about an architecture. A pilot on another
model needs a model folder with a size at which no copy fits, and a config of a few lines; no change to
`core/`.

For attention networks that size is an open question: the tiny ones, where every forward pass is a fact
the kernel can check, are far below it, and at the sizes where a copy does not fit a proof that falls back
on single inputs cannot be run through the kernel.

## Parked: runs over several sizes

Built on the same day and set aside: `tests/max2_ladder` (the linear network at 24, 32 and 48 tokens, sizes
at which a copy does not fit: at least 13,115 to 27,233 against budgets of 9,984 to 11,520; at 16 tokens a
copy is at the budget) and `tests/attn_maxn_tiny` (the attention network at
context lengths 2, 3, 4, where a copy fits), with `config/open-lane-ladder-base.yaml`, the two configs that
extend it and prompt template v4. A run on several networks is scored by the geometric mean of their costs
of finishing, a network counting at least 1. Nothing in the pilot setup uses them; the tests use the
linear folder as a small model with two development seeds of one size.

## Not changed

Q, Q_grid, Q_exact and Q_above are computed and reported as before, and the median cost of finishing stays
in the summary next to the geometric mean. Templates v1 to v3 and the earlier configs are untouched. The
Lean service, the lock file and the proof-file schema are untouched, and no result was rewritten. One
change reaches old configs: a new run with `metric: cost_of_finishing` on several networks is driven by
the geometric mean over a size setting's networks instead of the median.

Not built: the seed check without an agent (the service running the locked checker itself, from a
certificate recipe), and any check that a scaling lemma says what its author claims.
