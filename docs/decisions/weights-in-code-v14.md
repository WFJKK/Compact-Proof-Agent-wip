# Numbers of the network in a checker's code: what stands against it (17 November 2026)

Decided with the user on 17 November 2026, starting from the question left open that day: does a score count
only with its seed check? The Lean service's policy v14 (Compact-Proof-Checker, docs/COUNTED.md) and the
reading stage of this pipeline.

## The danger

A checker pays for every operation on the weights it is given. What its own code holds, and what that code
computes on it, is free. A checker that held the network's weights, exact or rounded, could compare the real
ones with them at a few charged operations each and do everything else for free on its copy. Run
attn-min2-ptl-3's proof pays 190,761; the same count would then cost a few thousand, with nothing understood.

Why it cannot simply be forbidden: code can hold numbers in its structure, and a size limit separates a
checker from a copy only where the weights are much larger than a checker. On attn-min2 v64d8 a real checker
measures 11,156 units and a copy of the weights about 11,000.

## What a second seed can and cannot say

The seed check runs the locked checker on a network of the same sizes trained from another seed. The user's
objection to making its number the result: a compact proof may rest on a circuit that only the first network
has. From outside that looks like numbers written into the code: good on the first network, poor on the
second. So a second seed says something only when the checker does well there (nothing was written in, and
the circuit is shared). When it does poorly the cause is open.

Decided: the first network's score is the result. The seed check stays what it was, a measurement of whether
the checker carries over, reported beside the score and never a condition for it.

## What was considered and dropped

- The same network in another basis. Permuting and rescaling the coordinates of an internal space gives a
  network that computes exactly the same function with other weights: a real proof would pass on it, a
  checker holding the old weights would certify nothing. Dropped at the user's word: which changes of basis
  leave the function alone depends on the architecture, and the method has to hold for any network.
- A judge that decides. A language model reading the code can be wrong either way.

## What was built

All three work from the network file or the code alone, for any network.

1. The size budget is capped at 24,576 units (the service's policy v14). It grew by 4 units per parameter,
   which left room for a copy rounded to 11 bits per weight at any size. The cap is 1.75 times the largest
   real checker measured (14,043) and above the budget of every network that has a proof. Beside 3,000 units
   of other code it leaves room for 14 bits per weight at 4,352 parameters, 7 at 8,256 and 5 at 12,352 (13
   at both before). An exact copy (24 bits per weight) did not fit from 4,352 parameters on before either:
   what the cap changes is how finely a rounded copy can be held, and that the room shrinks as the network
   grows. A rounded copy still fits at every size the zoo has. A size limit is a wall only where the weights
   are many times a checker: about one bit per weight is left at 50,000 parameters.
2. The last-bits test (policy v14). After the kernel has scored a proof, the service runs the same checker,
   compiled, with the proof's certificate and plan, on copies of the network in which every nonzero parameter
   is moved by about 2^-20 or 2^-16 of itself. The checker must certify at least 9/10 of its count on each
   copy, or the proof is refused scoring. Measured: the brute-force example keeps 64 of 64; attn-min2-ptl-3's
   proof keeps 1,889 of 1,889 on every copy down to 2^-12 (and breaks at 2^-8, where its 61 thresholds stop
   fitting); a checker that asks one weight to be exactly a stored number certifies 0. It takes 11 s on that
   proof. The run is of compiled code, so the first run is on the network itself and must give what the
   kernel established, and a candidate module with `implemented_by`, `extern`, `export`, `csimp` or
   `initialize` is not run and not scored. Nor is a checker the test cannot run: one that is
   `noncomputable`, or whose own code does not run to the end. What the service itself could not do is an
   error, never a refusal. lean_check with `checker` makes the same runs on a development compile and shows
   them in its preview (`last_bits`), so a count that hangs on the last bits costs a compile to see and not
   a submission.
3. The reading (`open_lane.code_review`). After the proof rounds a session reads the locked checker and says
   whether its count comes from what it computes on the weights or from numbers of the network in its code,
   with what it found. It is told what the two checks above said of the proof and what they cannot see. Its
   verdict is in the status and the report as a language model's reading: an alarm for a person. It decides
   nothing.

## What is not covered

A copy that is rounded and compared with a tolerance. The last-bits test passes it at every level finer than
its tolerance; the size budget leaves it room at every size the zoo has. On those networks it is left to the
reading and to a person. The pilots at width 8 are to be reported as that: passed the last-bits test, and
read.

The last-bits test also has a case where it would be wrong: a network whose weights have exact structure
that a proof rightly uses (whole numbers written by hand, two tensors stored apart that are equal entry for
entry). The copies break such structure. Zeros and the exporter's constants are kept, and trained weights
have no other; for a network built by hand it is a limit to state.

## For the agent

The prompts state the cap and the last-bits rule with the scoring conditions, and name the reading among
what follows the rounds. Nothing in them says what the network computes.
