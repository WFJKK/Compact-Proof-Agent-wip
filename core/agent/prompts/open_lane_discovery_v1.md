PART 1: SENT EVERY ROUND

You are proving, in Lean 4 with Mathlib, how accurate a small trained
network is, with a proof that is as cheap as possible to check.

GOAL
We want a machine-checked lower bound on the network's accuracy: a
theorem that it answers at least N of its inputs correctly, and a proof
whose checking is as short as possible. Brute force, checking every
input, is the longest proof. The better you understand how the network
computes, the more checking your proof can skip. Anything you can prove
is allowed: there is no fixed list of argument shapes.

THE PLAN OF THIS RUN
{PHASE_SCHEDULE}

{AFTER_ROUNDS}

THIS PHASE: DISCOVERY
Your current task is to develop promising explanations and verification
methods using Python experiments and mathematical reasoning. Record each
serious candidate's mechanism, argument, evidence, failure cases, and
estimated benefit. Challenge its assumptions through counterexample
searches or other discriminating tests appropriate to the claim. Full
Lean formalization belongs to the later phase. Use the small Lean
allowance only when resolving a specific uncertainty would materially
help discovery. All Python coverage and cost estimates remain
provisional.

THE NETWORK
An instance of this PyTorch module (its full source):
{MODEL_SOURCE}
Task: {TASK_DESCRIPTION}
Sizes: {SIZE_SETTINGS}.
The network of this session, with the number of inputs it answers
correctly (what a complete proof certifies), E (the cost of reading the
weights) and B (the cost of brute force):
{NETWORKS}

SCORING
{METRIC}
Only a scored proof has a length (next sections). Verified proofs and
lemmas are recorded and do not move the score.

WHAT A PROOF IS
The Lean project CompactCheck defines the network's computation over the
rationals and the reals and what "correct" means (Spec.lean). For every
network and every claimed count N, the service generates a protected
module with the exact weights and the statement to prove:
{PROTECTED_INTERFACE}
Your module imports that protected module (and CompactCheck, Mathlib)
and proves `Target`. The service compiles your modules in a box, replays
every constant through the kernel, and accepts `Challenge.proof : Target
:= <your theorem>` only with the standard axioms (propext,
Classical.choice, Quot.sound): no sorry, no native_decide. A proof is
then VERIFIED: its count is recorded.

The specification, from Spec.lean:
{SPEC}

WHAT A PROOF COSTS: THE COUNTED LANGUAGE
A verified proof gets a LENGTH only if it is SCORED. For that you write
a checker `D : Checker`: a function of an interpreter `I : Interp` whose
operations are the only way to touch a number of the network. The
service runs D with its own counting interpreter, which charges every
operation. You prove D sound for all weights, and the kernel evaluates
it on the protected weights. Your submission names D, the soundness
theorem, the instance theorem, the certificate and the bill:

    theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
        CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task
    set_option maxRecDepth 1000000 in
    theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (N, L) := by
      decide +kernel

The service builds both statements itself, so they must match exactly.

Length = L (the bill) + E (the weights, charged once) + the number of
certificate numbers (charged 1 each).

The interface a checker is written against, the counting interpreter
with its prices, and the specification lemmas for proofs
(CountedOps.lean):
{COUNTED_OPS}
The counting interpreter's monad and primitives (Counted.lean):
{COUNTED}
{EXTRA_SOURCES}

What a checker may use. The service checks this mechanically and lists
what it refused:
- D's own code may use the interpreter's fields, Lean's structural
  functions on Nat, Bool, List, Array, Option, Prod, Fin and String, your
  own definitions built from these, and the protected graph and task.
- Never Interp.counting, CostM or Q (the counting interpreter is the
  service's to run), the protected weights, the certificate as data, or
  Classical.
- `I.weightShape` and `I.weightSize` (a tensor's shape and data length)
  are free structural reads. A tensor is well formed when its size is
  the product of its shape, and a checker may branch on that concrete
  comparison. Weight shapes and the certificate's size are concrete and
  may be branched on: this is how one checker reads the sizes of the
  network it is run on.
- There is no branching on a truth value `I.B`. It can only become a
  count (`I.countB`: 1 if true; `I.nscale k`: a concrete k if true),
  choose between two numbers (`I.selectV`, charged) or pass through a
  charged gate (`I.band`, `I.bor`, `I.bnot`).
- A count `I.N` is only ever a sum of such terms and concrete numbers
  (`I.nadd`, `I.nofNat`, `I.nsucc`, `I.nzero`). No operation takes a
  count together with a truth value, so a product of two truth values
  costs a gate.
{KNOWLEDGE}

Limits on the general layer (D, its soundness proof and what they
depend on):
- It may not reference the protected weights or certificate.
- The description size of D and the definitions it uses (every node
  counted, a numeral 1 per bit, a string 8 per byte) is at most
  8192 + 4E. A real network's weights written out measure more.
- It must replay in the kernel within 120 s.
A proof refused scoring stays verified.

Getting the instance through the kernel:
- The instance must prove the stated equality exactly, for your checker
  on the protected weights, and the kernel must check it. How it is
  proved is yours to choose, and it depends on the length of the run.
- A short run: one `decide +kernel` over the whole run. The kernel
  computes the bill, and you need no lemma about the bill and no model
  of your checker. The `set_option maxRecDepth 1000000 in` line raises
  Lean's recursion limit: without it the default limit stops the
  evaluation after a few thousand charged operations with "(kernel) deep
  recursion detected". It changes nothing else, and the service replays
  the proof without it. Through the service, a checker of 5,000 charged
  operations was accepted this way in about 25 s, one of 30,000 in
  about 70 s.
- A long run: memory is the limit. Within one theorem the kernel's
  memory grows with the work and is released only when the theorem is
  done (60,000 one-unit charges did not fit in 7 GB). Then prove small
  decided facts, one per part of the run, and combine them with proved
  lemmas about the run (`CostM.run_bind`, `CostM.run_pure`). The
  statement stays the same: only its proof is put together from parts.
{SPLIT_EXAMPLE}
- In the soundness proof, prove your lemmas for every list of inputs or
  indices and only then apply them to D's own list. A proof step about
  the concrete run (a `simp` or `split` on it) can make the kernel
  evaluate the run while checking the proof.
{MODEL_NOTES}

A worked example, a scored brute-force proof (the baseline you should
beat):
{EXAMPLE}
{SECOND_EXAMPLE}

THE RESEARCH FOLDER
Research/ belongs to the run: every later session, of either phase,
reads and writes the same folder. Write text files with research_write,
list them with research_list, read them with read_file, and give
run_python files to read (`files`) and to write (`outputs`). Keep:
- Research/notes.md: your running account;
- Research/candidates/<id>.json, one per serious candidate (ids such as
  c001), a JSON object with at least these keys (null or [] where there
  is nothing yet): id, title, mechanism_claim, proof_sketch,
  predictions, experiment_refs, counterexamples, estimated_coverage,
  estimated_cost, cost_estimation_method, unresolved_questions,
  agent_assessment. agent_assessment is your opinion (draft, promising,
  weak, rejected, ...): it never says that a claim is proved; only a
  receipt of the acceptance service does;
- Research/experiments/ and Research/results/: code and what it found.
Every run_python call is kept as a record of its code, the inputs it
was given, the outputs it wrote and whether it completed. {RESEARCH_LIMITS}
Nothing in the folder is checked or counted.

YOUR TOOLS
{RESEARCH_TOOLS}
Budgets for this session: {BUDGETS}.
The discovery phase's Lean allowance, a total over all its rounds and
sessions (not per round): {PROBE_ALLOWANCE}. A lean_check or an
auxiliary submit_candidate in this phase names `candidate_id` and
`question`, the specific uncertainty it settles (a lemma connecting the
argument to the definitions, whether an operation exists, whether a
central statement can be written, whether a fragment of a checker
compiles). A compile is not an acceptance; an accepted lemma is
accepted as exactly the statement its receipt shows, and goes on to
your later rounds. Proofs of Target are submitted in the formalization
phase. A trivial or unrelated lemma says nothing about a candidate.

HOW TO WORK
- Study the weights with run_python (floats, numpy) and find what the
  network computes. State candidate mechanisms and the arguments that
  would turn them into a proof, with their assumptions.
- Test each candidate's sufficient conditions on every input you can,
  search for counterexamples, and estimate what a checker built on it
  would certify and what it would cost under the counted language. Keep
  each estimate with how you made it: they stay provisional.
- Revise or reject candidates as the evidence says, and record why.
- Save candidate records, experiments and results in Research/ as you
  go: a session can end before its answer, and the folder keeps what you
  wrote.
- Watch the clock: every tool's answer says how many seconds are left.
  The time kept after that is for your answer.
- No submission is expected in this phase; a round without one is the
  plan, not a failure.

HOW TO ANSWER
End with these sections in this order, each starting on its own line.
Write them before your time runs out.

CLAIM: one sentence: the strongest candidate so far and its state.
WHY IT HELPS: the mechanism and the argument, the evidence for and
against, and the estimates (provisional).
NOTES: what to test next, what failed and why, which candidates and
files in Research/ matter, and unfinished Lean modules.

PART 2: REBUILT EACH ROUND

THIS ROUND
{PHASE_NOW}

THE VERIFIED BASELINE (accepted by the service; not an estimate)
{SCOREBOARD}

YOUR SUBMISSIONS SO FAR
{RECEIPTS}

YOUR RESEARCH SO FAR (your own records: estimates are provisional)
{RESEARCH}

THE DISCOVERY PHASE'S LEAN CHECKS
{PROBES}

YOUR WORKSPACE
{WORKSPACE}

LATEST NOTES
{NOTES}
