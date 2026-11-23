THIS SESSION: HOW THE COST GROWS WITH {SYMBOL}
The proof rounds of this run are over, and a person has looked at its
proofs. {STEP_LINE}

This session asks one question about the run's scored proofs: how does
what each costs grow with {PARAMETER}, while {HELD} stay as they are on
this network, and does it grow more slowly than brute force? What the
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

{EARLIER}

THE SIZES
On this network: {SIZES}. This session varies {SYMBOL} and holds the
other two at these values. Brute force is one forward pass on every
input: on this network {N} inputs at {PER_INPUT} each plus E, which is
B = {B}. How that grows with the sizes follows from the model's source
and the single rule's prices.

Why a theorem can answer it: a checker cannot branch on a truth value,
so on a run that succeeds its bill depends on the sizes (the tensors'
shapes, the length of the certificate and of the plan) and on its own
code, not on the values of the weights. A run can still fail on some
values, and a certificate or a plan can be longer on another network.
So a formula for the cost holds under conditions, and they are part of
the claim. Where the cost depends on something other than the sizes,
such as how many pieces a plan makes, that is a parameter of the
formula of its own: say what it is and what it was on this network.

WHAT TO HAND IN
For each proof, or one formula for proofs that share a checker or a
method, with what separates them as its parameters:
1. In your answer:
   - the total length as a formula in {SYMBOL}, part by part: E, the
     certificate's length, the bill;
   - brute force's cost as a formula in {SYMBOL};
   - the verdict: a smaller exponent, the same exponent with a smaller
     constant, or no gain;
   - what the proof certifies at other values of {SYMBOL}: shown,
     assumed or unknown. A cheap check and a useful accuracy bound are
     separate claims: a checker that certifies nothing at other sizes
     is cheap at every size and says nothing there.
2. As much of it as you can prove in Lean, submitted as lemmas
   (submit_candidate with kind auxiliary: a lemma has any statement
   and is never scored). In order of strength:
   a. for every weight assignment of this network's shapes (and every
      certificate and plan as long as the proof's), if the checker's
      run succeeds then its bill is the bill in the proof's receipt;
   b. the bill as an exact formula in {SYMBOL}, for every value of it,
      the other sizes as on this network. If a checker fixes {SYMBOL},
      you may write a version that reads it and prove the formula for
      that version. It must be the same method at every value: prove
      that it is the submitted checker at this network's value, and say
      what it does at the others;
   c. the formula's leading order against brute force's.
Checkers are not submitted for a count in this session. For each
accepted lemma, Lean is asked which of the proofs' checkers the modules
the service compiled hold, term for term: only then is that checker's
name in your statement the checker that was submitted. For the locked
one the answer to submit_candidate says so (`locked_checker`); for the
others it is asked when this session ends, so keep their modules as
they are.

HOW TO ANSWER
End with these sections in this order, each starting on its own line:

CLAIM: for each proof (or group of proofs), its growth in {SYMBOL},
brute force's, and the verdict, a sentence each.
SCALING: one line per proof: the proof (its record), the formula, its
leading order, and which accepted lemma proves which of a, b, c.
WHY IT HELPS: the arguments and the conditions the formulas hold
under; what is argued but not proved.
NOTES: what stopped you where you stopped, and what the next session
can build on.
