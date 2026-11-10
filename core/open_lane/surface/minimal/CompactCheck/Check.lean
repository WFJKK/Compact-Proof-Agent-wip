-- [excerpt] CompactCheck/Check.lean as this run offers it: the exact test for one input.
-- [excerpt] Lines marked like this one are notes. Every other line is a line of the Lean project's file,
-- [excerpt] in its order. The file holds more than is shown here.

namespace CompactCheck

/-- The checker's test for one input: the network's output is a logit
    vector of shape `[1, n]` and the label's logit is strictly larger than
    every other logit. Exact, over the rationals. -/
def singleOk (g : Graph) (w : Weights Rat) (task : Task) (x : Input) : Bool :=
  match evalGraph g w x with
  | some out => out.shape == [1, out.data.size] && strictMaxAt out.data.toList (task.label x)
  | none => false

end CompactCheck
