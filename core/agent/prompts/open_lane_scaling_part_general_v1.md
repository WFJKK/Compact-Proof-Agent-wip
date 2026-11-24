== TITLE ==
THE CHECKER WITH ITS SIZES AS PARAMETERS

== AIM ==
A theorem about the cost at other sizes
needs a checker that runs at other sizes, and its exact cost there.
This session is for those two, for every size at once.

== VARIED ==
This session takes them together.

== LINKS ==
For each size S of the network ({SYMBOLS}), the result is four links,
and each is a theorem or it is missing:
- general: a checker with S as a parameter, proved to be the
  submitted checker at this network's value of S;
- cost: the exact bill of that checker's run at every value of S, as
  a function defined in Lean;
- formula: that function in closed form in S, or between proved
  bounds;
- brute: brute force's cost as a function of S, and the comparison.
This session is for the first two links, for every size together. A
session on one size is for the other two.

== TASK ==
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

== HAND_IN ==
One theorem where you can: the conjunction of the equality with the
submitted checker and the cost theorem, so that its statement alone
says what is proved and names the submitted checker ({CHECKERS}). A
lemma whose statement names no submitted checker says nothing about
the proofs by itself, and the report says so beside it. Where one
theorem is out of reach, the links as separate lemmas. If the sizes
do not all fit, take them in this order: {ORDER}, the locked proof
first, and say exactly what is left.

== ANSWER ==
CLAIM: for each proof (or group of proofs), in a sentence each: in
which sizes its checker was general as submitted, for which a general
checker now exists, and for which its exact cost is a theorem.
THEOREMS: one line for each size and each of the links general and
cost, in exactly this form: `{FIRST} general: Candidate.Module.theorem`,
with the full name of the accepted theorem whose statement holds that
link (one theorem may hold several links); `{FIRST} general: as submitted`
where the submitted checker is general in that size as it is;
`{FIRST} cost: none` where the link is missing. A theorem counts only if
the service accepted it as the named theorem of a submission.
SCALING: one line per proof: the proof (its record), its general
checker, the cost function and what its arguments are.
