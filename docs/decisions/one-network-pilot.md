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
   instance and nothing else, with a new certificate if the checker reads one. What comes out is how much a
   checker written for one network certifies on one it was not written for. It does not by itself show
   understanding or its absence: another seed can compute differently, or with smaller margins.
3. The scaling question. Last, the agent states how the locked checker's cost grows with the sizes of the
   network, compares it with brute force's growth, and proves what it can of that as lemmas. Never scored,
   and a proof is never refused because its author could not prove a formula for its cost.

The agent is not shown networks of other sizes. Which model a pilot runs on is one choice (linear or
attention; max or min of 2 or 4), made in a file of a few lines. The first pilot is the linear max-of-2
network at vocabulary size 64 and hidden width 8.

A pilot's size must be one at which the weights cannot be written out in a checker (below).

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
  nothing there. What the budget rules out is the weights written out, in any encoding of their bits. It
  does not show that no compressed information about one checkpoint can sit in a checker; that is the
  seed check's to catch.
- A constant factor against the price list counts like a structural gain. The scaling question: a
  constant factor leaves the growth rate where it was.

## The seed check, and what the lock rests on

A scored proof has a general part (the checker `D`, its soundness theorem and what they use, all proved
for every weight) and an instance (the kernel's run of `D` on one network's weights). The lock tells them
apart by module (`core/open_lane/lock.py`), and what a module declares and imports is asked of Lean:

- The locked modules are the ones that declare the checker and the soundness theorem, and every submitted
  module they import. Both facts are read by a Lean program (`core/open_lane/inspect_oleans.lean`, run
  with the service's own Lean) from the `.olean` files the acceptance service compiled for the accepted
  proof. Nothing is read off the source: Lean lets `Candidate.Check.D` be declared in any file, by a macro
  as well as by a `def`, a string can look like a declaration, and an import can span lines.
- A proof can be locked when its instance theorem is declared outside them. A proof kept in one module
  cannot. Template v5 says so from the first round, each round's receipts say of every scored proof
  whether it is ready, and the aim says so when the proof the score rests on is not.
- When the rounds end, the best scored proof that can be locked is locked (the one that finishes the
  network cheapest). A better proof passed over is recorded with the reason.

The lock holds two things: the locked modules' text, and the checker's fingerprints.

The text keeps a session from editing the checker. In the seed check's session the locked modules cannot
be saved over, and before every compile and every submission they are written into the workspace again
from the lock. One change is made: a locked module may import the protected module of the network it was
written for (the checker reads its `graph` and `task`), and that name is replaced by the second
network's. The submission must name the locked checker and soundness theorem, and the locked modules
always go along. The receipt carries a hash of every module the service compiled, and the record says
whether those hashes are the locked text's (`lock.in_receipt`).

The fingerprints establish, afterwards, that the checker a proof was accepted with is the locked one.
They are three digests of kernel terms, as Lean reads them from the compiled modules, with the protected
module's name left out:

- `checker`: the checker and every constant of the candidate's it depends on, definitions with their
  values and theorems with their statements (a proof changes nothing a definition computes);
- `sound_statement`: the soundness theorem's statement, with every constant of the candidate's it is
  written in;
- `context`: the constants of the protected module those reach, which are the network's graph and task.
  Two networks of one size setting have the same graph and task (the pilot's two protected modules define
  them word for word alike), so the context is the same when only the seed differs.

When the service accepts a scored proof in the seed check, Lean is asked about the modules it has just
compiled, and the three digests are compared with the lock's (`lock.same_checker`). Equal digests mean
the same checker term for term, on the same graph and task, with the same soundness statement, whatever
any source text looks like. The session is told at once whether its proof counts, and the record carries
`lock.verified` with the reason when not, naming the constants that differ.

What it rests on:

- The inspection program is the pipeline's, not the acceptance service's, and it trusts the service's
  work folder to hold what the service compiled. It checks that the folder's copy of the modules' sources
  is the submitted one, and no more than that. A receipt does not carry the fingerprints. Putting them
  into the receipt needs a change to the Lean project and a new lock commit, and is not done.
- A name saying which constant is meant. A submission in which two modules declare one constant, or one
  is named under the marker that stands for the protected module (`Protected._`), is refused. The service
  refuses a candidate that declares a constant twice, so this does not happen to a proof it accepted.
- The compiled module showing what a definition is. A file written in Lean's module system (it begins with
  `module`) keeps the bodies of its definitions out of the `.olean`, and an axiom has none: a checker that
  depends on either cannot be locked.
- Lean compiling the same text to the same terms on both networks. On small modules with structures,
  recursion and proofs inside definitions it does (`tests/test_lock_lean.py`). If it did not somewhere,
  the result would be reported as unverified, not as a transfer.
- The second network being unseen until then. It is a development network of the model that is not the
  run's, never named in the proof rounds' prompts, and `run_python` is given the run's network only. On a
  Mac the sandbox does not stop a program from reading or writing other files (frozen-transfer.md), so
  there the second seed is unseen, and the work folder untouched, by instruction and not by enforcement.

Two reviews on 10 November are why it is built this way. The first lock guessed a constant's module from
its name: it froze an empty file named like the checker while the file with the real definition stayed
editable. The second read declarations and imports from source text: an import written over two lines
escaped it, text in a string was taken for declarations, and it compared the checker's description size,
which does not establish identity and only raised a warning. Each case is a test now, on modules compiled
by Lean.

The check uses a development seed, so the model's held-out seeds stay untouched for a final evaluation.

Its result is reported next to the run's score, never folded into it: per network, the count certified
of the count correct, the length, and the cost of finishing. There are three outcomes and they are kept
apart:

- `certified`: a scored proof was accepted and Lean finds the locked checker in it. Its count is a result,
  a claim of 0 included: that is a checked statement that the checker certifies nothing there.
- `unverified`: a scored proof was accepted, but its checker is not the locked one, or its declarations do
  not single one out. It is listed with the reason and is not a measurement of how the checker transfers.
- `no_result`: the session ended without an accepted scored proof (out of time, nothing compiled,
  submissions rejected). It is reported with what happened, never as zero coverage.

Lean not answering is none of the three. If Lean cannot be run, or the compiled modules are not where the
service keeps them, nothing is known about the proof: the run halts and a resume asks again. This holds
when the lock is read (no proof is passed over for it) and when an accepted proof is compared (it is not
recorded as unverified). A run with a seed check also checks before it starts that the inspection program
runs with the Lean project's Lean.

## The scaling question

A checker cannot branch on a truth value, so its bill depends on the sizes and on its code, never on the
values of the weights. That makes the growth of its cost a statement a theorem can settle. The session
asks for the claim in words (the checker's bill and brute force's cost as formulas in the sizes, and a
verdict: a smaller exponent, the same exponent with a smaller constant, or no gain) and for as much of it
as can be proved, as lemmas, in order of strength: the bill is the same for every weight of this shape
on which the run succeeds; the bill as a formula for every size; the comparison. The formula for every
size needs a checker that makes sense at every size, which a checker that fixes its sizes does not. The
agent may then write a version that reads them and prove it equal to the locked one at this size.

After a review of the prompt (10 November), the claim must also say: which sizes vary and which are held
fixed; the family of networks the checker is sound for; the total length part by part (E, the
certificate, the bill), since a certificate can grow; the conditions the formula holds under, since a run
can fail on some values; and what the checker certifies at other sizes, established, assumed or unknown.
A version that is the locked checker at this size and certifies nothing elsewhere would be cheap at every
size and say nothing, so cheap checking and a useful accuracy bound are asked for as separate claims.

A lemma's statement is the agent's own, and the service checks only that it is proved. A person reads the
statement before relying on it. One thing is checked for the reader: for each accepted lemma Lean is asked,
as in the seed check, whether the modules the service compiled hold the locked checker term for term. The
report says so per lemma, so that the checker's name in a statement can be read as the locked checker.

## The first pilot

`config/pilot/linear-max2.yaml`, on `models/max2` at vocabulary size 64 and hidden width 8:

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
small decided facts; and the 15 minutes above, so that a session of three hours plans its compiles. The
prompt says both ways of proving an instance (one theorem for a short run, parts and glue for a long one)
and where the second is shown: the Lean project's docs and a brute-force example on a small attention
network (`open_lane.split_example`), which `read_file` may read.

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
certificate recipe), the checker's fingerprints computed by the acceptance service and carried in its
receipt (a change to the Lean project), and any check that a scaling lemma says what its author claims.
