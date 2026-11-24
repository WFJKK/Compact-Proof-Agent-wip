== TITLE ==
THE COST AS A THEOREM IN {SYMBOL}

== AIM ==
This session takes one size:
{PARAMETER}{HELD}.

== VARIED ==
This session varies {SYMBOL}{HOLDS}.

== LINKS ==
The result in {SYMBOL} is four links, and each is a theorem or it is
missing:
- general: a checker with {SYMBOL} as a parameter, proved to be the
  submitted checker at {SYMBOL} = {VALUE};
- cost: the exact bill of that checker's run at every value of
  {SYMBOL}, as a function defined in Lean;
- formula: that function in closed form in {SYMBOL}, or between
  proved bounds;
- brute: brute force's cost as a function of {SYMBOL}, and the
  comparison.

== TASK ==
THIS SESSION'S WORK
Start from what the earlier sessions had accepted: THE LINKS SO FAR
above, where there are any, says which links they named a theorem for.
Read a theorem's statement before you build on it: what it fixes,
what it leaves free, and what it assumes.
1. general and cost, where they are missing for {SYMBOL}. A submitted
   checker is general in {SYMBOL} when, for every value of it, there
   are weights of matching shapes that get past its tests of shapes.
   It is not when this network's {VALUE} is written into it (a loop
   bound, an index, a stride, a test of a shape), nor when it tests
   {SYMBOL} against the network's own graph or task, which are this
   network's: then it refuses every other value, and a lemma with
   that test among its hypotheses holds at {VALUE} only, whatever it
   quantifies over. Where it is not general, write the general
   checker: the same code with {SYMBOL} as a parameter in each such
   place, and prove that at {VALUE} it is the submitted checker (by
   `rfl` when the two unfold to the same term). Then its cost: for
   every value of {SYMBOL}, every weight assignment of the shapes it
   accepts there, every certificate and every plan, if its run
   succeeds then its bill is a function you define in Lean. Only the
   cost of the general checker is asked, not its soundness at other
   values.
2. formula. The cost function in closed form in {SYMBOL}, for every
   value of it from a stated one on, and for every plan and
   certificate of a stated family (for instance: every entry of the
   plan at most K, with what K was on this network). Proved from the
   definition of the cost function, by induction on its sums: not a
   second formula that is only evaluated against the first. Exact
   where you can. Where the exact form is out of reach, an upper
   bound with explicit constants is a result too; add the lower bound
   if you claim the exponent is exact. Where the cost depends on
   something other than the sizes, such as how many pieces a plan
   makes, that is a parameter of the formula of its own.
3. brute. Brute force's cost as a Lean function of {SYMBOL}: one
   forward pass at the single rule's prices times the number of
   inputs, plus E, proved equal to {B} at {SYMBOL} = {VALUE}. Then the
   comparison as a theorem, for every value of {SYMBOL} from a stated
   one on: the proof's cost times a power of {SYMBOL} at most a
   constant times brute force's, or whichever inequality says how
   the two grow apart.
4. The verdict follows from 2 and 3: a smaller exponent, the same
   exponent with a smaller constant, or no gain. A link you cannot
   prove stays missing: say so, and say what is argued in its place.
If all four links are theorems already, check that their statements
say what the links ask, say so, and end: only then is a short session
the right one.
In words, not as a theorem: what each proof certifies at other values
of {SYMBOL}: shown, assumed or unknown. A cheap check and a useful
accuracy bound are separate claims.

== HAND_IN ==
One theorem where you can, the conjunction of the links you have for
{SYMBOL}, so that its statement alone says what is proved and names
the submitted checker ({CHECKERS}). A lemma whose statement names no
submitted checker says nothing about the proofs by itself (it may
compare two formulas of your own), and the report says so beside it.
Where one theorem is out of reach, the links as separate lemmas. The
locked proof first; proofs that share a checker or a method share
their theorems, with what separates them as parameters.

== ANSWER ==
CLAIM: for each proof (or group of proofs), its growth in {SYMBOL},
brute force's, and the verdict, a sentence each, and for each of the
three whether it is a theorem.
THEOREMS: one line for each of the four links, in exactly this form:
`{SYMBOL} formula: Candidate.Module.theorem`, with the full name of
the accepted theorem whose statement holds that link (one theorem may
hold several links); `{SYMBOL} general: as submitted` where the
submitted checker is general in {SYMBOL} as it is;
`{SYMBOL} brute: none` where the link is missing. A theorem counts
only if the service accepted it as the named theorem of a submission.
SCALING: one line per proof: the proof (its record), the formula, its
leading order, brute force's, and what is a theorem of it.
