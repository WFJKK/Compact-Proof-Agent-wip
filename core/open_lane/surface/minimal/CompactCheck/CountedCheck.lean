-- [excerpt] CompactCheck/CountedCheck.lean as this run offers it: what the single-input rule is charged on a linear network.
-- [excerpt] Lines marked like this one are notes. Every other line is a line of the Lean project's file,
-- [excerpt] in its order. The file holds more than is shown here.

namespace CompactCheck

/-- The parameters of the network: `extract`, E. -/
def paramCount (w : Weights Rat) : Nat :=
  (w.map fun p => p.2.data.size).sum

/-! ## One exact forward pass (`single`) -/

/-- What the Python evaluator knows about a value when it runs one input: the one-hot input, its sum
    over the positions, or an exact tensor of this shape. -/
inductive SKind where
  | oneHot
  | summed
  | dense (shape : List Nat)

-- [excerpt] The positions of the graph the output depends on (`op.args`: the operations an operation reads);
-- [excerpt] the others are left out of the bill.
def reachable (g : Graph) : List Nat :=
  go (g.nodes.length) [g.output] [g.output]
where
  go : Nat → List Nat → List Nat → List Nat
    | 0, _, seen => seen
    | fuel + 1, [], seen => let _ := fuel; seen
    | fuel + 1, i :: todo, seen =>
      let args := match g.nodes[i]? with
        | some op => op.args
        | none => []
      let new := args.filter (fun a => !seen.contains a)
      go fuel (todo ++ new) (seen ++ new)

/-- The `single` charge of one input, as `_run_concrete` charges it: a linear map on the one-hot input
    costs its output size per position (a lookup), on a vector `in * out` per leading index; a bias, a sum or
    an addition its output size; the final comparison `outputs - 1`. -/
def singleCost (g : Graph) (w : Weights Rat) : Option Nat := do
  let keep := reachable g
  let (cost, kinds) ← g.nodes.foldlM (init := (0, (#[] : Array SKind))) fun (cost, kinds) op => do
    let i := kinds.size
    let charged := keep.contains i
    match op with
    | .input => pure (cost, kinds.push .oneHot)
    | .sum a d =>
      match kinds[a]? with
      | some .oneHot => if normDim d 3 == some 1 then pure (cost, kinds.push .summed) else none
      | some .summed => none
      | some (.dense s) =>
        let dim ← normDim d s.length
        let n := s.getD dim 0
        let s' := s.eraseIdx dim
        let c := shapeSize s' * (n - 1)
        pure (if charged then cost + c else cost, kinds.push (.dense s'))
      | none => none
    | .linear a wn bn =>
      let W ← List.lookup wn w
      let out := W.shape.getD 0 0
      let inn := W.shape.getD 1 0
      let (c, s') ← match kinds[a]? with
        | some .oneHot => some (g.positions * out, [1, g.positions, out])
        | some .summed => some (g.positions * out, [1, out])
        | some (.dense s) => some (shapeSize s * out, s.dropLast ++ [out])
        | none => none
      let _ := inn
      let c := if bn.isSome then c + shapeSize s' else c
      pure (if charged then cost + c else cost, kinds.push (.dense s'))
    | .add a b =>
      match kinds[a]?, kinds[b]? with
      | some (.dense s), some (.dense _) => pure (if charged then cost + shapeSize s else cost, kinds.push (.dense s))
      | _, _ => none
    | _ => none
  match kinds[g.output]? with
  | some (.dense s) => some (cost + (s.getLast?.getD 0 - 1))
  | _ => none

end CompactCheck
