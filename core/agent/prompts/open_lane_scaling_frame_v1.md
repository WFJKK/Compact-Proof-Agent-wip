THIS SESSION: {TITLE}
The proof rounds of this run are over, and a person has looked at its
proofs. {STEP_LINE}

These sessions ask how the cost of the run's scored proofs grows with
each size of the network, against brute force, and they ask for the
answer as theorems of Lean. {AIM}
What the first part of this message says about raising a score is
background here: nothing in this session is scored, and nothing in it
can undo what was accepted.

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
On this network: {SIZES}. {VARIED}
Brute force is one forward pass on every input: on this network {N}
inputs at {PER_INPUT} each plus E, which is B = {B}. How that grows
with the sizes follows from the model's source and the single rule's
prices.

WHAT COUNTS
A result of these sessions is a theorem the service accepted
(submit_candidate with kind auxiliary: a lemma has any statement and
is never scored). A formula worked out by hand, a Python model, a Lean
function evaluated at a few sizes: these find a formula and test it.
They do not prove it, and they are not results.

{LINKS}

{TASK}

WHAT TO HAND IN
{HAND_IN}
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

{ANSWER}
WHY IT HELPS: the arguments and the conditions the theorems hold
under; what is argued but not proved.
NOTES: what stopped you where you stopped, and what the next session
can build on.
