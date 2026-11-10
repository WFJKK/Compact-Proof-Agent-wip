-- [excerpt] CompactCheck/Soundness.lean as this run offers it: the exact evaluator computes what the specification computes, and an input the exact test accepts is answered correctly.
-- [excerpt] Lines marked like this one are notes. Every other line is a line of the Lean project's file,
-- [excerpt] in its order. The file holds more than is shown here.

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.BigOperators.Group.List
import CompactCheck.Spec

namespace CompactCheck

/-! ## 1. The checker's numbers are the spec's numbers -/

section cast

/-- Reading a rational as a real. -/
local notation "toR" => (fun q : ℚ => (q : ℝ))

@[simp] theorem Tensor.map_shape' {α β : Type} (f : α → β) (t : Tensor α) :
    (t.map f).shape = t.shape := rfl

@[simp] theorem Tensor.map_data_size {α β : Type} (f : α → β) (t : Tensor α) :
    (t.map f).data.size = t.data.size := by
  simp [Tensor.map]

@[simp] theorem Tensor.map_mk {α β : Type} (f : α → β) (s : List Nat) (d : Array α) :
    (Tensor.mk s d).map f = ⟨s, d.map f⟩ := rfl

theorem Tensor.get_map_cast (t : Tensor ℚ) (i : Nat) :
    (t.map toR).get i = ((t.get i : ℚ) : ℝ) := by
  simp only [Tensor.get, Tensor.map, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases t.data[i]? <;> simp

@[simp] theorem Tensor.get_mk_map_cast (s : List Nat) (d : Array ℚ) (i : Nat) :
    Tensor.get ⟨s, d.map toR⟩ i = ((Tensor.get ⟨s, d⟩ i : ℚ) : ℝ) :=
  Tensor.get_map_cast ⟨s, d⟩ i

theorem cast_list_sum (l : List ℚ) : ((l.sum : ℚ) : ℝ) = (l.map toR).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

theorem oneHotInput_cast (P V : Nat) (x : Input) :
    (oneHotInput P V x : Option (Tensor ℝ)) =
      (oneHotInput P V x : Option (Tensor ℚ)).map (Tensor.map toR) := by
  simp only [oneHotInput]
  split_ifs <;> simp [Array.map_map, Function.comp_def, apply_ite (fun q : ℚ => (q : ℝ))]

theorem linearOp_cast (W : Tensor ℚ) (b : Option (Tensor ℚ)) (t : Tensor ℚ) :
    linearOp (W.map toR) (b.map (Tensor.map toR)) (t.map toR) =
      (linearOp W b t).map (Tensor.map toR) := by
  cases b <;>
  · simp only [linearOp, Tensor.map, Option.map_none, Option.map_some, Array.size_map]
    split_ifs <;> simp [Array.map_map, Function.comp_def, cast_list_sum]

theorem sumOp_cast (dim : Int) (t : Tensor ℚ) :
    sumOp dim (t.map toR) = (sumOp dim t).map (Tensor.map toR) := by
  simp only [sumOp, Tensor.map, Array.size_map]
  cases normDim dim t.shape.length with
  | none => rfl
  | some d =>
    dsimp only
    split_ifs <;> simp [Array.map_map, Function.comp_def, cast_list_sum]

theorem addOp_cast (a b : Tensor ℚ) :
    addOp (a.map toR) (b.map toR) = (addOp a b).map (Tensor.map toR) := by
  simp only [addOp, Tensor.map, Array.size_map]
  split_ifs <;> simp [Array.map_map, Function.comp_def]

theorem lookup_realWeights (n : String) (w : Weights ℚ) :
    List.lookup n (realWeights w) = (List.lookup n w).map (Tensor.map toR) := by
  induction w with
  | nil => rfl
  | cons p w ih =>
    obtain ⟨m, t⟩ := p
    simp only [realWeights, List.map_cons, List.lookup] at *
    split <;> simp_all

theorem evalOp_cast (g : Graph) (w : Weights ℚ) (x : Input) (vals : Array (Tensor ℚ))
    (op : Op) :
    evalOp g (realWeights w) x (vals.map (Tensor.map toR)) op =
      (evalOp g w x vals op).map (Tensor.map toR) := by
  cases op with
  | input => simp only [evalOp, oneHotInput_cast]
  | linear a wn bn =>
    simp only [evalOp, Array.getElem?_map, lookup_realWeights]
    cases vals[a]? <;> cases List.lookup wn w <;> simp only [Option.map_none, Option.map_some]
    rename_i t W
    cases bn with
    | none => simpa using linearOp_cast W none t
    | some bn =>
      dsimp only
      cases List.lookup bn w with
      | none => rfl
      | some b => simpa using linearOp_cast W (some b) t
  | sum a d =>
    simp only [evalOp, Array.getElem?_map]
    cases vals[a]? <;> simp [sumOp_cast]
  | add a b =>
    simp only [evalOp, Array.getElem?_map]
    cases vals[a]? <;> cases vals[b]? <;> simp [addOp_cast]
  | _ => simp [evalOp]

theorem evalOps_cast (g : Graph) (w : Weights ℚ) (x : Input) (ops : List Op)
    (vals : Array (Tensor ℚ)) :
    evalOps g (realWeights w) x ops (vals.map (Tensor.map toR)) =
      (evalOps g w x ops vals).map (Array.map (Tensor.map toR)) := by
  induction ops generalizing vals with
  | nil => simp [evalOps]
  | cons op ops ih =>
    simp only [evalOps, evalOp_cast]
    cases evalOp g w x vals op with
    | none => rfl
    | some v => simp [← Array.map_push, ih]

/-- Over the reals, the exact evaluator's output is its output over the
    rationals, read as real numbers. -/
theorem evalGraph_cast (g : Graph) (w : Weights ℚ) (x : Input) :
    evalGraph g (realWeights w) x = (evalGraph g w x).map (Tensor.map toR) := by
  unfold evalGraph
  have h := evalOps_cast g w x g.nodes #[]
  simp only [Array.map_empty] at h
  rw [h]
  cases evalOps g w x g.nodes #[] <;> simp [Array.getElem?_map]

/-! ### The exact evaluator computes what the spec computes

`semOp` gives every operation of `evalOp` the value `evalOp` gives it; the
other operations are those `evalOp` does not run. -/

section bridge

variable {α : Type} [Zero α] [One α] [Add α] [Mul α] [Neg α] [ExpDiv α]

theorem semOp_of_evalOp {g : Graph} {w : Weights α} {x : Input} {vals : Array (Tensor α)}
    {op : Op} {v : Tensor α} (h : evalOp g w x vals op = some v) :
    semOp g w x vals op = some v := by
  cases op <;> first | exact h | simp [evalOp] at h

theorem semOps_of_evalOps {g : Graph} {w : Weights α} {x : Input} :
    ∀ {ops : List Op} {vals out : Array (Tensor α)},
      evalOps g w x ops vals = some out → semOps g w x ops vals = some out
  | [], vals, out, h => by simpa [evalOps, semOps] using h
  | op :: ops, vals, out, h => by
    simp only [evalOps] at h
    cases hv : evalOp g w x vals op with
    | none => simp [hv] at h
    | some v =>
      simp only [hv] at h
      simp only [semOps, semOp_of_evalOp hv]
      exact semOps_of_evalOps h

theorem semGraph_of_evalGraph {g : Graph} {w : Weights α} {x : Input} {out : Tensor α}
    (h : evalGraph g w x = some out) : semGraph g w x = some out := by
  unfold evalGraph at h
  unfold semGraph
  cases hv : evalOps g w x g.nodes #[] with
  | none => simp [hv] at h
  | some vals =>
    simp only [hv] at h
    rw [semOps_of_evalOps hv]
    exact h

end bridge

/-- When the exact evaluator runs the network, the real output is its exact
    output, read as real numbers. -/
theorem realOutput_of_evalGraph {g : Graph} {w : Weights ℚ} {x : Input} {out : Tensor ℚ}
    (h : evalGraph g w x = some out) : realOutput g w x = some (out.map toR) := by
  apply semGraph_of_evalGraph
  rw [evalGraph_cast, h]
  rfl

end cast

/-! ## 2. An accepted input is answered correctly -/

theorem strictMaxAt_spec (v : Vec) (l : Nat) (h : strictMaxAt v l = true) :
    l < v.length ∧ ∀ j < v.length, j ≠ l → vecGet v j < vecGet v l := by
  simp only [strictMaxAt, allPosExcept, marginsAt, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, List.length_map] at h
  obtain ⟨hl, hall⟩ := h
  refine ⟨hl, fun j hj hne => ?_⟩
  have hmem : (j, vecGet v l - v[j]) ∈
      (List.range v.length).zip (v.map fun a => vecGet v l - a) := by
    rw [List.mem_iff_getElem]
    refine ⟨j, by simp [hj], ?_⟩
    simp [List.getElem_zip, List.getElem_range, List.getElem_map]
  have hpos := hall _ hmem
  simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or, decide_eq_true_eq] at hpos
  have hj' : vecGet v j = v[j] := by
    simp [vecGet, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rw [hj']
  exact sub_pos.mp hpos

/-- `single_sound`: an input the checker accepts is answered correctly. -/
theorem singleOk_correct (g : Graph) (w : Weights ℚ) (task : Task) (x : Input)
    (h : singleOk g w task x = true) : Correct g w task x := by
  unfold singleOk at h
  split at h
  · rename_i out hout
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hshape, hmax⟩ := h
    obtain ⟨hl, hlt⟩ := strictMaxAt_spec _ _ hmax
    simp only [Array.length_toList] at hl hlt
    refine ⟨out.map (fun q : ℚ => (q : ℝ)), realOutput_of_evalGraph hout, ?_, ?_, ?_⟩
    · simpa [Tensor.map] using hshape
    · simpa using hl
    · intro j hj hne
      simp only [Tensor.map_data_size] at hj
      rw [Tensor.get_map_cast, Tensor.get_map_cast]
      have := hlt j hj hne
      rw [vecGet_toList, vecGet_toList] at this
      exact_mod_cast this
  · exact absurd h (by simp)

end CompactCheck
