import Candidate.Loops

/-!
# The free count loop over the input space equals a sum over `allInputs`, and a pointwise bound gives
`≤ countP`.
-/

namespace Candidate.Loops
open CompactCheck

/-- Σ over the inputs of a space, in the order of `allInputs` (free: counts only). -/
def sumInputs (I : Interp) : List Nat → (Input → I.N) → I.N
  | [], f => f []
  | v :: vs, f => (List.range v).foldl (fun n t => I.nadd n (sumInputs I vs (fun x => f (t :: x)))) I.nzero

theorem foldl_add_eq (h : Nat → Nat) : ∀ (l : List Nat) (a : Nat),
    l.foldl (fun n t => n + h t) a = a + (l.map h).sum
  | [], a => by simp
  | t :: l, a => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add_eq h l (a + h t)]
    omega

theorem sum_map_flatMap {α β : Type} (f : β → Nat) (g : α → List β) : ∀ (l : List α),
    ((l.flatMap g).map f).sum = (l.map fun t => ((g t).map f).sum).sum
  | [] => by simp
  | a :: l => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    rw [sum_map_flatMap f g l]

theorem sumInputs_eq : ∀ (vs : List Nat) (f : Input → Nat),
    sumInputs Interp.counting vs f = ((allInputs vs).map f).sum
  | [], f => by simp [sumInputs, allInputs]
  | v :: vs, f => by
    simp only [sumInputs, allInputs]
    rw [sum_map_flatMap]
    rw [show (fun n t => Nat.add n (sumInputs Interp.counting vs fun x => f (t :: x))) =
      (fun n t => n + (((allInputs vs).map fun x => f (t :: x)).sum)) from ?_]
    · rw [foldl_add_eq, Nat.zero_add]
      congr 1
      apply List.map_congr_left
      intro t _
      rw [List.map_map]
      rfl
    · funext n t
      rw [sumInputs_eq vs]
      rfl

theorem sum_le_countP {α : Type} (f : α → Nat) (p : α → Bool) (h : ∀ x, f x ≤ cond (p x) 1 0) :
    ∀ (l : List α), (l.map f).sum ≤ l.countP p
  | [] => by simp
  | a :: l => by
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    have h1 := h a
    have h2 := sum_le_countP f p h l
    rcases hpa : p a with _ | _ <;> simp [hpa] at h1 ⊢ <;> omega

end Candidate.Loops
