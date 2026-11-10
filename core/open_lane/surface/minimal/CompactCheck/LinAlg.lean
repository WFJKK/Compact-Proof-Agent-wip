-- [excerpt] CompactCheck/LinAlg.lean as this run offers it: vectors, and the test that one entry is strictly the largest.
-- [excerpt] Lines marked like this one are notes. Every other line is a line of the Lean project's file,
-- [excerpt] in its order. The file holds more than is shown here.

namespace CompactCheck

/-- A vector: a list of exact rational numbers. -/
abbrev Vec := List Rat

/-- Entry `i` of `v`, or 0 if `i` is out of range. -/
def vecGet (v : Vec) (i : Nat) : Rat :=
  v.getD i 0

/-- The margin of entry `l` over each entry: `v[l] - v[j]` for every `j`.
    The entry for `j = l` is 0. -/
def marginsAt (v : Vec) (l : Nat) : Vec :=
  let vl := vecGet v l
  v.map (fun a => vl - a)

-- [excerpt] Every entry except entry `l` is strictly positive.
def allPosExcept (v : Vec) (l : Nat) : Bool :=
  ((List.range v.length).zip v).all fun (j, a) => j == l || 0 < a

/-- Entry `l` exists and is strictly larger than every other entry.
    Ties are never accepted. -/
def strictMaxAt (v : Vec) (l : Nat) : Bool :=
  l < v.length && allPosExcept (marginsAt v l) l

end CompactCheck
