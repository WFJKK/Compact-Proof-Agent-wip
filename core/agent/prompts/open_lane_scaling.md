THIS SESSION: HOW THE COST GROWS
The proof rounds of this run are over. Your best scored proof was of
{FROM_NETWORK}: {FROM_RESULT}
{SEED_CHECK_RESULT}

This last session asks one question about that proof's checker, which is
locked: how does what it costs grow with the sizes of the network, and
does it grow more slowly than brute force? What the first part of this
message says about raising a score is background here: nothing in this
session is scored, and nothing in it can undo what was accepted.

Why a theorem can answer it: a checker cannot branch on a truth value,
so its bill does not depend on the values of the weights, only on the
sizes (the tensors' shapes, the certificate's length) and on its own
code. Brute force is one forward pass on every input: on this network,
{N} inputs at {PER_INPUT} each plus E, which is B = {B}. How that grows
with the sizes follows from the model's source and the single rule's
prices.

LOCKED
{LOCKED}
These modules are in your workspace and cannot be saved over; new
modules may import them.{RENAME}

WHAT TO HAND IN
1. The claim, in your answer: your checker's bill as a formula in the
   sizes (say which sizes), brute force's cost as a formula in the same
   sizes, and the verdict: a smaller exponent, the same exponent with a
   smaller constant, or no gain.
2. As much of the claim as you can prove in Lean, submitted as lemmas
   (submit_candidate with kind auxiliary: a lemma has any statement and
   is never scored). In order of strength:
   a. for every weight assignment of this network's shapes, the bill of
      the locked checker is the number in your instance: the bill does
      not depend on the weights;
   b. the bill as a formula in the sizes, for every size. This needs a
      checker that makes sense at every size. If yours fixes the sizes,
      you may write a version that reads them, prove that it is the
      locked checker at this network's sizes, and prove the formula for
      that version;
   c. the comparison with brute force's formula.
Proofs of `Target` are not accepted in this session.

HOW TO ANSWER
End with these sections in this order, each starting on its own line:

CLAIM: the two growth rates and the verdict, in one or two sentences.
WHY IT HELPS: the formulas and the argument. For each accepted lemma,
its name and exactly which of a, b, c it proves. Then what is argued but
not proved.
NOTES: what stopped you where you stopped.
