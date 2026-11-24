THIS SESSION: THE CHECKER WITH ITS SIZES AS PARAMETERS
The proof rounds of this run are over, and a person has looked at its
proofs. {STEP_LINE}

These sessions ask how the cost of the run's scored proofs grows with
each size of the network, against brute force, and they ask for the
answer as theorems of Lean. A theorem about the cost at other sizes
needs a checker that runs at other sizes, and its exact cost there.
This session is for those two, for all three sizes at once. What the
first part of this message says about raising a score is background
here: nothing in this session is scored, and nothing in it can undo
what was accepted.

THE PROOFS
The scored proofs of {NETWORK} that no shorter proof matched in inputs
certified:
{PROOFS}

LOCKED
{LOCKED}
These modules are in your workspace and cannot be saved over; new
modules may import them.{RENAME}{OTHERS}
The certificate and the plan of each proof above, with the count and
the bill of its receipt, are in your Python workspace as
py/handed_in_proofs.json (the locked one also as py/locked_proof.json).
{WORKSPACE}

{EARLIER}

THE SIZES
On this network: {SIZES}. Brute force is one forward pass on every
input: on this network {N} inputs at {PER_INPUT} each plus E, which is
B = {B}.

WHAT COUNTS
A result of these sessions is a theorem the service accepted
(submit_candidate with kind auxiliary: a lemma has any statement and
is never scored). A formula worked out by hand, a Python model, a Lean
function evaluated at a few sizes: these find a formula and test it.
They do not prove it, and they are not results.

For each size S of V, n and d, the result is four links, and each is
a theorem or it is missing:
- general: a checker with S as a parameter, proved to be the
  submitted checker at this network's value of S;
- cost: the exact bill of that checker's run at every value of S, as
  a function defined in Lean;
- formula: that function in closed form in S, or between proved
  bounds;
- brute: brute force's cost as a function of S, and the comparison.
This session is for the first two links, for V, n and d together. The
sessions after it take one size each for the other two.

THE GENERAL CHECKER
1. Find what each submitted checker does at another value of each
   size. It is general in a size when, for every value of it, there
   are weights of matching shapes that get past its tests of shapes.
   It is not when a number of this network is written into it (a loop
   bound, an index, a stride, a test of a shape), nor when it tests a
   size against the network's own graph or task: those are this
   network's and hold its sizes, so the checker refuses every other
   value and certifies nothing there. A lemma that has such a test
   among its hypotheses holds at this network's value only, whatever
   it quantifies over.
2. Where a checker is not general, write the general one: the same
   code with the size as a parameter in each such place. One checker
   with all the sizes it needs as parameters is best. Prove that at
   this network's values it is the submitted checker: by `rfl` when
   the two unfold to the same term, by a proved equality otherwise.
   It must be the same method at every value: nothing in it may
   depend on a size being this network's. Proofs that share their
   code share a general checker with what separates them as its
   parameters.
3. Prove its cost: for every value of the sizes, every weight
   assignment of the shapes the general checker accepts there, every
   certificate and every plan, if its run succeeds then its bill is a
   function you define in Lean of the sizes and of what the plan and
   the certificate contribute. A checker cannot branch on a truth
   value, so on a run that succeeds the bill does not depend on the
   values of the weights; a run can still fail on some values, and
   that is a condition of the theorem. The earlier sessions' lemmas
   about the bill, where there are any, may do this at this network's
   sizes: their proofs are where to start, with the numbers made
   parameters.
Only the cost of the general checker is asked. Its soundness at other
values is not: do not generalise a soundness proof.

WHAT TO HAND IN
One theorem where you can: the conjunction of the equality with the
submitted checker and the cost theorem, so that its statement alone
says what is proved and names the submitted checker ({CHECKERS}). A
lemma whose statement names no submitted checker says nothing about
the proofs by itself, and the report says so beside it. Where one
theorem is out of reach, the links as separate lemmas. If the three
sizes do not all fit, take them in the order V, n, d, the locked proof
first, and say exactly what is left.
For each accepted lemma, Lean is asked which of the proofs' checkers
the modules the service compiled hold, term for term: only then is
that checker's name in your statement the checker that was submitted.
For the locked one the answer to submit_candidate says so
(`locked_checker`); for the others it is asked when this session ends,
so keep their modules as they are. Checkers are not submitted for a
count in this session.

TIME
{CLOCK}
The links are the work: a session that stops with tool time left and
a link missing has wasted it. Prove sums and bounds by induction and
by lemmas about lists and ranges; a `decide` or a kernel evaluation of
a large sum runs out of time. Before the tool time ends, submit what
is proved (part of a conjunction is a result) and leave the rest
saved in your workspace: the next session starts with your accepted
lemmas, with the modules you leave without submitting them, and with
your Python files.

HOW TO ANSWER
End with these sections in this order, each starting on its own line:

CLAIM: for each proof (or group of proofs), in a sentence each: in
which sizes its checker was general as submitted, for which a general
checker now exists, and for which its exact cost is a theorem.
THEOREMS: one line for each size and each of the links general and
cost, in exactly this form: `V general: Candidate.Module.theorem`,
with the full name of the accepted theorem whose statement holds that
link (one theorem may hold several links); `V general: as submitted`
where the submitted checker is general in that size as it is;
`V cost: none` where the link is missing. A theorem counts only if the
service accepted it as the named theorem of a submission.
SCALING: one line per proof: the proof (its record), its general
checker, the cost function and what its arguments are.
WHY IT HELPS: the conditions the theorems hold under; what is argued
but not proved.
NOTES: what stopped you where you stopped, and what the next session
can build on.
