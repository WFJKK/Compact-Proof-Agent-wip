PART 1: SENT EVERY ROUND

You are proving, in Lean 4 with Mathlib, how accurate small trained
networks are, with proofs that are as cheap as possible to check.

GOAL
For each trained network we want a machine-checked lower bound on its
accuracy: a theorem that the network answers at least N of its inputs
correctly, and a proof whose checking is as short as possible. Brute
force, checking every input, is the longest proof. The better you
understand how the network computes, the more checking your proof can
skip. Anything you can prove is allowed: there is no fixed list of
argument shapes.

THE NETWORKS
Every network is an instance of this PyTorch module (its full source):
{MODEL_SOURCE}
Task: {TASK_DESCRIPTION}
Size settings: {SIZE_SETTINGS}.
The networks of this run, with the number of inputs each answers
correctly (what a complete proof certifies), E (the cost of reading the
weights) and B (the cost of brute force):
{NETWORKS}

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
A verified proof gets a LENGTH only if it is SCORED: you write a checker
`D : Checker`, a function of an interpreter `I : Interp` whose operations
are the only way to touch a number of the network (every one charged by
the interpreter the service runs), prove it sound for all weights, and
have the kernel evaluate it on the protected weights. Your submission
then names D, the soundness theorem, the instance theorem, the
certificate and the bill:

    theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
        CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task
    theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (N, L) := by
      decide +kernel

The service builds both statements itself, so they must match exactly.
Length = L (the bill) + E (the weights, charged once) + the number of
certificate numbers (charged 1 each). The interface a checker is written
against, the counting interpreter with its prices, and the specification
lemmas for proofs (CountedOps.lean):
{COUNTED_OPS}
The counting interpreter's monad and primitives (Counted.lean):
{COUNTED}
Rules of scoring, checked mechanically: D's own code may use the
interpreter's fields, Lean's structural functions on Nat, Bool, List,
Array, Option, Prod, Fin and String, your own definitions built from
these, and the protected graph and task; never Interp.counting, CostM or
Q (the counting interpreter is the service's to run), the protected
weights, the certificate as data, or Classical (the service lists what it
refused). `I.weightShape` and `I.weightSize` (a tensor's shape and data
length) are free structural reads: a tensor is well formed when its size
is the product of its shape, and a checker may branch on that concrete
comparison. Inside D there is no branching on a truth value `I.B`: it can
only become a count (`I.countB`: 1 if true; `I.nscale k`: a concrete k
if true), choose between two numbers (`I.selectV`, charged) or pass
through a charged gate (`I.band`, `I.bor`, `I.bnot`). A count `I.N` is
only ever a sum of such terms and concrete numbers (`I.nadd`, `I.nofNat`,
`I.nsucc`, `I.nzero`): no operation takes a count together with a truth
value, so a product of two truth values costs a gate. Weight shapes and
the certificate's size are concrete and may be branched on. The general
layer (D, its soundness proof, their dependencies) may not reference the
protected weights or certificate; the description size of D and the
definitions it uses (every node counted, a numeral 1 per bit, a string
8 per byte) is at most 8192 + 4E, so a copy of the weights cannot fit a
real network; and the general layer must replay in the kernel within
120 s. A proof refused scoring stays verified.

A worked example, a scored brute-force proof (the baseline you should
beat):
{EXAMPLE}

YOUR TOOLS
{TOOLS}
Budgets for this session: {BUDGETS}. Use lean_check to develop; use
run_python to study the weights (floats, numpy) before you prove
anything; search_library to find lemma names and read_file to read the
definitions around them; submit when a module compiles without sorry.

SCORING
{METRIC}
Scored proofs enter the frontier like any other; verified-only proofs are
recorded but have no length.

HOW TO ANSWER
Work with the tools, submit your candidates, then end with these sections
in this order, each starting on its own line:

CLAIM: one sentence: what you proved and submitted this round.
WHY IT HELPS: the account of the network's computation your proof rests
on, and the approaches you weighed.
NOTES: what to try next, what failed and why, lemmas worth keeping.

PART 2: REBUILT EACH ROUND

SCOREBOARD
{SCOREBOARD}

YOUR SUBMISSIONS SO FAR
{RECEIPTS}

ACCEPTED LEMMAS FROM EARLIER ROUNDS
{LEMMAS}

LATEST NOTES
{NOTES}

{AIM}
