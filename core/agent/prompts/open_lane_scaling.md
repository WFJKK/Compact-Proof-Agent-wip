THIS SESSION: HOW THE COST GROWS
The proof rounds of this run are over. The best of your scored proofs
that could be locked was of {FROM_NETWORK}: {FROM_RESULT}
{SEED_CHECK_RESULT}

This last session asks one question about that proof's checker, which is
locked: how does what it costs grow with the sizes of the network, and
does it grow more slowly than brute force? What the first part of this
message says about raising a score is background here: nothing in this
session is scored, and nothing in it can undo what was accepted.

Why a theorem can answer it: a checker cannot branch on a truth value,
so on a run that succeeds its bill depends on the sizes (the tensors'
shapes, the certificate's length) and on its own code, not on the values
of the weights. A run can still fail on some values (an operation given
something outside what it handles returns nothing), and a certificate
can be longer on another network. So a formula for the cost holds under
conditions, and they are part of the claim. Brute force is one forward
pass on every input: on this network, {N} inputs at {PER_INPUT} each
plus E, which is B = {B}. How that grows with the sizes follows from the
model's source and the single rule's prices.

LOCKED
{LOCKED}
These modules are in your workspace and cannot be saved over; new
modules may import them.{RENAME}

WHAT TO HAND IN
1. The claim, in your answer:
   - the sizes you let vary and the ones you hold fixed, and why;
   - the family of networks and tasks for which the checker (or the
     version of it you generalize to, below) is sound;
   - its total length as a formula in those sizes, part by part: E, the
     certificate's length, the bill;
   - brute force's cost as a formula in the same sizes;
   - the verdict: a smaller exponent, the same exponent with a smaller
     constant, or no gain;
   - what the checker certifies at other sizes: established, assumed or
     unknown. A cheap check and a useful accuracy bound are separate
     claims. A checker that certifies nothing away from this size is
     cheap at every size and says nothing there.
2. As much of the claim as you can prove in Lean, submitted as lemmas
   (submit_candidate with kind auxiliary: a lemma has any statement and
   is never scored). In order of strength:
   a. for every weight assignment of this network's shapes and every
      certificate as long as yours, if the locked checker's run succeeds
      then its bill is the number in your instance. Or prove as well
      that the run always succeeds;
   b. the bill as a formula in the sizes, for every size. This needs a
      checker that makes sense at every size. If yours fixes the sizes,
      you may write a version that reads them and prove the formula for
      that version. It must be the same method at every size, not the
      locked checker at this size and something else elsewhere: prove
      that it is the locked checker at this network's sizes, and say
      what it does at the others;
   c. the comparison with brute force's formula.
Proofs of `Target` are not accepted in this session. For each accepted
lemma, Lean is asked whether the modules the service compiled hold the
locked checker, term for term, and the answer to submit_candidate says
so (`locked_checker`): only then is {CHECKER} in your statement the
checker that was locked.

HOW TO ANSWER
End with these sections in this order, each starting on its own line:

CLAIM: the two growth rates and the verdict, in one or two sentences.
WHY IT HELPS: the formulas, the conditions they hold under and the
argument. For each accepted lemma, its name and exactly which of a, b, c
it proves. Then what is argued but not proved.
NOTES: what stopped you where you stopped.
