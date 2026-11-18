THIS SESSION: THE SEED CHECK
The proof rounds of this run are over. The best of your scored proofs
that could be locked was of {FROM_NETWORK}: {FROM_RESULT}

Its checker is now locked, and this session runs it on the second
network named above, {NETWORK}: the same architecture and sizes, trained
from another seed. Nothing about the checker may change. The question is
what a checker written for the first network certifies on one it was not
written for. What the first part of this message says about raising a
score is background here: this session has one job.

LOCKED
{LOCKED}
These modules are in your workspace and cannot be saved over. Whatever
the workspace holds, the service receives them as they were accepted:
before every lean_check and every submission they are written again from
the lock.{RENAME}

YOURS TO GIVE
- The certificate and the plan for {NETWORK}, if the checker reads any,
  computed from this network's weights (run_python has them). They are
  all that changes. The service runs the locked checker on this network
  itself: there is nothing to prove here and no count to claim. The
  ones the proof was accepted with on {FROM_NETWORK} are in your Python
  workspace as py/locked_proof.json, to see their form: they were made
  for that network's weights.
- lean_check shows the run before you submit: compile the checker's
  module as it is (its path, with `edits: []`), with `checker`
  {CHECKER}, the certificate and the plan. `run` in the answer is the
  count, the bill and the length a submission of them gets.
- The checker may certify fewer inputs here than the network answers
  correctly: that is a result, not a failure. If it certifies nothing
  here, submit that too: a count of 0 is a checked result. If its run
  fails on this network (it returns nothing), the service rejects the
  submission: say so in your answer, and why it fails. A session that
  ends with no accepted submission is recorded as no result, which is
  a different thing.
Submit with submit_candidate: the checker's module, with scored.checker
{CHECKER} and scored.sound {SOUND} (anything else is refused), the
certificate and the plan.
An accepted proof counts as this session's result only if Lean finds
the locked checker in it: the modules the service compiled are read,
and the checker's kernel terms, with those of everything it depends on,
must be the ones that were locked. The answer to submit_candidate says
whether it counts (`locked_checker`). A module of yours that declares
one of the checker's constants again makes the proof not count.

HOW TO ANSWER
End with these sections in this order, each starting on its own line:

CLAIM: what the locked checker certified on {NETWORK}: the count and the
length.
WHY IT HELPS: where the two networks differ for your proof: which inputs
it certified on the first network and not here, and what about this
network's weights the checker's test fails on. If nothing differs, say
what the proof relies on that both networks share.
NOTES: how you made the certificate and the plan for this network, and
what you would change in the checker if it were not locked.
