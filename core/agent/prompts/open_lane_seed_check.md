THIS SESSION: THE SEED CHECK
The proof rounds of this run are over. Your best scored proof was of
{FROM_NETWORK}: {FROM_RESULT}

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

YOURS TO WRITE
- The instance for {NETWORK}: `D_instance` for its weights, the facts it
  is built from and the theorem proving `Target`, in a module that is
  not locked.{FREE}
- The certificate, if the checker reads one, computed from this
  network's weights (run_python has them).
- The count. Claim what the locked checker certifies on this network. It
  may be fewer inputs than the network answers correctly: that is a
  result, not a failure. If it certifies nothing here, submit nothing
  and say so.
Submit with submit_candidate: kind performance, with scored.checker
{CHECKER} and scored.sound {SOUND} (anything else is refused), your
instance theorem, the certificate and the bill.

HOW TO ANSWER
End with these sections in this order, each starting on its own line:

CLAIM: what the locked checker certified on {NETWORK}: the count and the
length.
WHY IT HELPS: where the two networks differ for your proof: which inputs
it certified on the first network and not here, and what about this
network's weights the checker's test fails on. If nothing differs, say
what the proof relies on that both networks share.
NOTES: what had to be redone for this network, and what you would change
in the checker if it were not locked.
