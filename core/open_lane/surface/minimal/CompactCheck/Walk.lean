-- [excerpt] CompactCheck/Walk.lean as this run offers it: inputs.
-- [excerpt] Lines marked like this one are notes. Every other line is a line of the Lean project's file,
-- [excerpt] in its order. The file holds more than is shown here.

namespace CompactCheck

/-- An input: one token per position. -/
abbrev Input := List Nat

/-- Every input of a space, for testing on small spaces. -/
def allInputs : List Nat → List Input
  | [] => [[]]
  | v :: vs => (List.range v).flatMap fun t => (allInputs vs).map (t :: ·)

end CompactCheck
