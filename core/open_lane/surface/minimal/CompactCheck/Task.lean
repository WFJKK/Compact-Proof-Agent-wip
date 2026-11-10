-- [excerpt] CompactCheck/Task.lean as this run offers it: the task, as far as it is part of the specification.
-- [excerpt] Lines marked like this one are notes. Every other line is a line of the Lean project's file,
-- [excerpt] in its order. The file holds more than is shown here.

namespace CompactCheck

-- [excerpt] A task: the input space (position `p` takes the tokens `0, ..., space[p] - 1`) and the correct
-- [excerpt] output for every input.
structure Task where
  name : String
  space : List Nat
  label : Input → Nat
-- [excerpt] (The structure has further fields, which are not part of the specification. This run does not
-- [excerpt] offer them.)

/-- The largest of `positions` tokens, each in `0, ..., values - 1`
    (max2, attn-max2, attn-max4). -/
def maxTask (positions values : Nat) : Task where
  name := "max"
  space := List.replicate positions values
  label x := x.foldl max 0
-- [excerpt] (and the further fields)

/-- The smallest of `positions` tokens, each in `0, ..., values - 1`
    (attn-min2, attn-min4). Every token is at most `values - 1`, so that is
    a safe starting value. -/
def minTask (positions values : Nat) : Task where
  name := "min"
  space := List.replicate positions values
  label x := x.foldl min (values - 1)
-- [excerpt] (and the further fields)

/-- The label of majority: 1 if the tokens add up to more than half of
    `positions`, that is to at least `positions / 2 + 1`, else 0. -/
def majorityLabel (positions : Nat) (x : Input) : Nat :=
  if positions / 2 + 1 ≤ x.foldl (· + ·) 0 then 1 else 0

/-- Majority on `positions` bits, the tokens 0 and 1 (xorformer-majority):
    1 exactly when more than half of the bits are 1. With 12 bits, at least
    7 of them. -/
def majorityTask (positions : Nat) : Task where
  name := "majority"
  space := List.replicate positions 2
  label := majorityLabel positions
-- [excerpt] (and the further fields)

/-- The task with this name, for this input shape. -/
def taskByName (name : String) (positions values : Nat) : Option Task :=
  match name with
  | "max" => some (maxTask positions values)
  | "min" => some (minTask positions values)
  | "majority" => if values = 2 then some (majorityTask positions) else none
  | _ => none

end CompactCheck
