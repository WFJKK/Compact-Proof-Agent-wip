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

THIS PHASE: FORMALIZATION
Your current task is to turn the strongest saved candidates into
accepted Lean results. Inspect the recorded argument and experimental
evidence, identify missing assumptions, develop the checker and its
soundness proof, and submit them: the acceptance service checks the
proof and runs the checker. Use Python when needed for diagnosis,
counterexample searches, or certificate generation. If a candidate
fails, record the reason and revise it or try another. Report only
evaluator-accepted results as verified.

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
network the service generates a protected module with the network:
{PROTECTED_INTERFACE}
Your modules import it (and CompactCheck, Mathlib) for `graph` and
`task`, and never mention the weights: what you prove holds for every
weight.

A result has two parts, and you write the first.
1. Soundness, which is mathematics. You write a checker `D` (next
   section) and prove that, whatever the weights, it never counts more
   inputs than the network answers correctly. The service compiles your
   modules in a box, replays every constant through the kernel, and
   accepts the soundness theorem only with the standard axioms (propext,
   Classical.choice, Quot.sound): no sorry, no native_decide.
2. The run, which is arithmetic. The service runs your compiled checker
   on the network's weights, with your certificate and plan, and takes
   the count and the bill from that run. You prove nothing about the
   run and claim no count: in this run there is no instance theorem and
   no theorem of `Target`.
By your soundness theorem the count the run returns is a proved lower
bound on the number of inputs the network answers correctly. A proof
whose soundness theorem the kernel accepts and whose checker runs is
VERIFIED: its count is recorded.

The specification, from Spec.lean:
{SPEC}

WHAT A PROOF COSTS: THE COUNTED LANGUAGE
A verified proof gets a LENGTH only if it is SCORED. For that you write
a checker `D : Checker`: a function of an interpreter `I : Interp` whose
operations are the only way to touch a number of the network. The
service runs D with its own counting interpreter, which charges every
operation. You prove D sound for all weights. Your submission names D,
the soundness theorem and the certificate:

    theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
        CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task

The service builds this statement itself, so yours must match exactly.
The run it then makes is `CostM.billed (D Interp.counting) ⟨weights,
cert⟩` on the network's weights and your certificate. If that is
`some (N, L)`, N is the count and L the bill. If it is `none` (the
checker fails), there is no count and the submission is rejected.

Length = L (the bill) + E (the weights, charged once) + the number of
certificate numbers (charged 1 each).

A PLAN steers a checker for free. If your checker needs data you
computed offline that says WHERE to look (which inputs go into which
group, where a loop stops), give it as a plan: natural numbers in the
scored block ("plan": [...]), below 2^32, at most 4 per input plus
10,000, and small: a plan says where to look and holds no copy of the
weights. Its length in a prefix code (an entry v costs
2 x bitlength(v + 1) - 1 bits: 0 costs 1, 63 costs 13) is at most a
quarter of the bits of the network's weights; lean_check with `checker`
and the plan shows both numbers. The checker is then
`D : List Nat → Checker` and reads the plan
as ordinary Lean data, with no charge; turning an entry into a number
for arithmetic goes through `I.lit`, charged 1. A plan is not trusted:
the soundness theorem must hold for every plan,

    theorem D_sound : ∀ (p : List Nat) (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
        CostM.exec (D p Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task

and the service runs `D` on the plan you submit (lean_check takes the
same plan). Data written into D's code counts toward its description
size; data in a plan does not.

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
- It is all you submit, and it may not reference the protected weights.
- The description size of D and the definitions it uses (every node
  counted, a numeral 1 per bit, a string 8 per byte) is at most the
  network's size budget: 8192 + 4E, or half the bits of its weights
  (each weight's sign and significant bits) where that is more, at
  most 16,384; and never above 24,576, however large the network.
  A copy of the weights measures more.
- lean_check with `checker` (D's name) shows, before you submit, whether
  D stays in the counted language and its description size against
  the budget, with its largest definitions.
- It must replay in the kernel within 120 s.
- Its count must not go with the last bits of the weights. With the
  run on the network the service runs D, with the same certificate and
  plan, on copies of the network in which every
  weight is moved by about 2^-20 or 2^-16 of itself. On each copy D
  must certify at least 9/10 of what it certifies on the network. A
  checker that computes on the weights it is given does; one that
  compares the weights with numbers of this network held in its code
  certifies nothing there. So leave room in what you compare: a
  threshold or a certificate number a little inside what the weights
  give, not exactly on it. A copy moves a sum of products of weights
  by up to about 2^-16 of the sizes of its terms; several times that
  is room enough.
- D is run as compiled code, so it must be its own compiled code:
  nothing `noncomputable` in D or what it uses, and no
  `implemented_by`, `extern`, `export`, `csimp` or `initialize` in
  your modules. A checker that cannot be run has no count.
A proof refused scoring stays verified, with its count.

The run, and what is left to the kernel:
- lean_check with `checker` (D's name), and with the certificate and
  the plan you mean to submit, makes the run before you submit. `run`
  in its answer is the count, the bill and the length a submission of
  that checker gets, and `last_bits` what it certifies on the copies.
  It costs a compile and seconds: use it whenever the checker changes.
- The run on the network and the eight runs on copies get an hour
  together, and each must run from start to end: Lean stops compiled
  code that recurses a few million calls deep (a million runs). A
  lean_check preview gives the nine runs two minutes; when they do not
  fit, it shows the run on the network alone, if that one was made.
- The kernel checks your soundness proof and nothing about the run.
  Keep it so: prove your lemmas for every list of inputs or indices and
  only then apply them to D's own list. A proof step about the concrete
  run (a `simp` or `split` on it, a `decide`) makes the kernel evaluate
  the run while checking the proof, which is slow and can exhaust
  memory, and which this run has no need of.
- Where the soundness proof does have the kernel compute (a decided
  fact about the graph, say): for the kernel an Array is a list.
  Building one entry by entry (`Array.ofFn`, `Array.range`,
  `Array.map`, `push`) walks the list for every entry: 512 entries cost
  seconds and a gigabyte. Write the data of a tensor of your own as
  `((List.range n).map f).toArray`. To have the kernel evaluate the
  specification's `semOps` or `semGraph`, rewrite with `semOps_eqK` or
  `semGraph_eqK` first (CompactCheck/SemanticsKernel.lean): the same
  tensors, built from lists and read through a tree.
{MODEL_NOTES}

A worked example, a scored brute-force proof (the baseline you should
beat): its checker and its soundness theorem are all of it.
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

HOW TO WORK
- Start from the shortlist below: read the candidates' records and the
  experiments they cite, and find what the argument still assumes.
- Write the checker in Lean (the worked example is a place to start
  from) and have lean_check run it (`checker`) before you prove
  anything about it: what it certifies, its bill and its length. That
  is the run a submission gets, so the numbers are the real ones once
  the soundness proof is accepted.
- Prove the central lemma of a soundness proof early, in a module of
  its own, and submit it as a lemma (kind auxiliary): an accepted lemma
  is carried into your later rounds.
- Read the sizes with `I.weightShape` where you can, rather than writing
  this network's numbers into the checker, and prove it sound for every
  weight.
- Use Python for diagnosis, counterexample searches and certificates.
  When a candidate fails, record why in its record and in
  Research/notes.md, and revise it or take the next one.
- Name the candidate a proof comes from (candidate_id) when you submit.
- Use lean_check to develop; send `edits` to change part of a saved
  module. Submit when a module compiles without sorry.
- Watch the clock: every tool's answer says how many seconds are left.
- Modules accepted in earlier rounds are in your workspace (below).
  Import them rather than writing them again. Your unfinished modules
  are there too, listed apart: they are drafts, not accepted, until a
  submission of them is.

HOW TO ANSWER
Work with the tools, submit your candidates, then end with these sections
in this order, each starting on its own line. Write them before your
time runs out: a session that runs out of time leaves no notes.

CLAIM: one sentence: what you proved and submitted this round, as the
receipts say.
WHY IT HELPS: the mechanism your proof rests on, which step of the
checker relies on it, and what would have to be different about another
network's weights for the checker to certify less there.
NOTES: what to try next, what failed and why, the provisional counts and
bills you measured, and which unfinished modules to go on with.

PART 2: REBUILT EACH ROUND

THIS ROUND
{PHASE_NOW}

THE SHORTLIST FROM DISCOVERY
{SHORTLIST}

SCOREBOARD
{SCOREBOARD}

YOUR SUBMISSIONS SO FAR
{RECEIPTS}

YOUR RESEARCH (your own records: estimates are provisional)
{RESEARCH}

YOUR WORKSPACE
{WORKSPACE}

LATEST NOTES
{NOTES}

{AIM}
