import Candidate.LinearSum

/-!
# (P3) the box bound and (P4, ordered form) counting product boxes in `allInputs`.
-/

namespace Candidate.Boxes

open CompactCheck Protected.N_max4_v64_s0 Candidate.Linear

/-- (P3) A per-position lower bound on `Mat[m,x_p] - Mat[j,x_p]` whose sum is positive
    gives the strict margin. -/
theorem logit_lt_of_lower (E L U : Tensor ℚ) (d P V : Nat) (x : Input) (hx : x.length = P)
    (hall : ∀ a ∈ x, a < V) (m j : Nat) (lo : Nat → ℚ)
    (hlo : ∀ p ∈ Finset.range P,
      lo p ≤ Mat E L U d V m (x.getD p 0) - Mat E L U d V j (x.getD p 0))
    (hsum : 0 < ∑ p ∈ Finset.range P, lo p) :
    logit E L U d P V x j < logit E L U d P V x m := by
  have h := margin_eq E L U d P V x hx hall m j
  have h2 := Finset.sum_le_sum hlo
  linarith

/-- A product box: one token interval `[lo, hi)` per position. -/
def inBox : List (Nat × Nat) → Input → Bool
  | [], [] => true
  | (lo, hi) :: bs, t :: x => (lo ≤ t && t < hi) && inBox bs x
  | _, _ => false

/-- The number of inputs of a product box (when every interval fits the space). -/
def boxSize : List (Nat × Nat) → Nat
  | [] => 1
  | (lo, hi) :: bs => (hi - lo) * boxSize bs

theorem countP_range_interval (v lo hi : Nat) :
    (List.range v).countP (fun t => lo ≤ t && t < hi) = min hi v - lo := by
  induction v with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp only [List.countP_cons, List.countP_nil, Bool.and_eq_true, decide_eq_true_eq]
    split <;> omega

theorem countP_and_const {α : Type} (q : Bool) (r : α → Bool) (ys : List α) :
    ys.countP (fun x => q && r x) = if q then ys.countP r else 0 := by
  cases q <;> simp

theorem sum_map_countP {α : Type} (l : List Nat) (q : Nat → Bool) (r : α → Bool) (ys : List α) :
    (l.map fun t => ys.countP (fun x => q t && r x)).sum = l.countP q * ys.countP r := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.countP_cons, countP_and_const]
    split
    · ring
    · simp

theorem countP_flatMap' {α β : Type} (p : β → Bool) (l : List α) (f : α → List β) :
    (l.flatMap f).countP p = (l.map fun a => (f a).countP p).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.countP_append, ih]

/-- (P4, ordered) The inputs of a product box within `allInputs space`. -/
theorem countP_inBox : ∀ (bs : List (Nat × Nat)) (space : List Nat),
    List.Forall₂ (fun (b : Nat × Nat) v => b.2 ≤ v) bs space →
    (allInputs space).countP (inBox bs) = boxSize bs
  | [], [], _ => by simp [allInputs, inBox, boxSize]
  | (lo, hi) :: bs, v :: vs, h => by
    cases h with
    | cons hb hrest =>
      have ih := countP_inBox bs vs hrest
      simp only [allInputs, boxSize]
      rw [countP_flatMap']
      simp only [List.countP_map]
      have : (fun t => (allInputs vs).countP (inBox ((lo, hi) :: bs) ∘ (t :: ·))) =
          fun t => (allInputs vs).countP (fun x => (lo ≤ t && t < hi) && inBox bs x) := by
        funext t
        rfl
      rw [this, sum_map_countP, countP_range_interval, ih]
      simp only at hb
      rw [Nat.min_eq_left hb]

end Candidate.Boxes
