import Candidate.LibCubicChecker
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Counting inputs

The facts about lists of tokens the count of entry 7 rests on, none about networks.

* `countP_prod`: the inputs of `n` positions of `V` tokens with a condition on each position's
  token, one condition per position, number the product of the numbers of tokens that pass.
* `prod_pat`: over the positions of a pattern, `Π_p (if p ∈ K then a else 1) = a^|K|`.
* `sum_thresholds`: `Σ_{i < λ} [i + 1 ≤ g] ((i + 1)^c - i^c) = g^c` for `g ≤ λ`, the count the
  checker assembles from comparisons.
* `sum_swap`, `countP_eq_sum`: sums over the inputs and over the classes commute.
-/

namespace GrossCubic

open CompactCheck Finset

/-- A constant summed over the elements of a list that pass a test. -/
theorem sum_map_ite {α : Type} (P : α → Prop) [DecidablePred P] (C : ℕ) :
    ∀ l : List α, (l.map fun t => if P t then C else 0).sum = C * l.countP fun t => decide (P t)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_map_ite P C l, List.countP_cons]
    by_cases h : P a
    · simp [h, Nat.mul_add]; ring
    · simp [h]

/-- The inputs of a product set: at each position `p < n` a condition `P p` on its token. -/
theorem countP_prod (V : ℕ) : ∀ (n : ℕ) (P : ℕ → ℕ → Prop) [∀ p, DecidablePred (P p)],
    (allInputs (List.replicate n V)).countP (fun x => decide (∀ p < n, P p (x.getD p 0))) =
      ∏ p ∈ range n, (List.range V).countP fun t => decide (P p t)
  | 0, P, _ => by simp [allInputs]
  | n + 1, P, _ => by
    have ih := countP_prod V n (fun p t => P (p + 1) t)
    have hstep : ∀ t, ((allInputs (List.replicate n V)).map (t :: ·)).countP
        (fun x => decide (∀ p < n + 1, P p (x.getD p 0))) =
        if P 0 t then ∏ p ∈ range n, (List.range V).countP (fun s => decide (P (p + 1) s))
        else 0 := by
      intro t
      rw [List.countP_map, ← ih]
      by_cases h0 : P 0 t
      · rw [ite_eq_left h0]
        refine List.countP_congr fun y _ => ?_
        simp only [Function.comp_apply, decide_eq_true_eq]
        constructor
        · intro h p hp
          simpa using h (p + 1) (by omega)
        · intro h p hp
          rcases p with _ | p
          · simpa using h0
          · simpa using h p (by omega)
      · rw [ite_eq_right h0]
        refine List.countP_eq_zero.mpr fun y _ => ?_
        simp only [Function.comp_apply, decide_eq_true_eq, not_forall]
        exact ⟨0, by omega, by simpa using h0⟩
    rw [Finset.prod_range_succ', List.replicate_succ, allInputs, List.countP_flatMap]
    simp only [Function.comp_def]
    rw [List.map_congr_left (fun t _ => hstep t), sum_map_ite]

/-- The positions of a pattern, one bit each. -/
theorem prod_pat (a : ℕ) : ∀ (L pat : ℕ),
    ∏ p ∈ range L, (if pat.testBit p then a else 1) = a ^ (inPat L pat).length
  | 0, _ => by simp [inPat]
  | L + 1, pat => by
    rw [Finset.prod_range_succ, prod_pat a L pat]
    unfold inPat
    rw [List.range_succ, List.filter_append]
    by_cases h : pat.testBit L <;> simp [h, pow_succ]

/-- The count from comparisons: for `g ≤ λ` and `c ≥ 1`, the thresholds `i + 1 ≤ g` with
    weights `(i + 1)^c - i^c` add up to `g^c`. -/
theorem sum_thresholds (c g : ℕ) (hc : 1 ≤ c) : ∀ (lam : ℕ), g ≤ lam →
    ((List.range lam).map fun i =>
      if i + 1 ≤ g then (i + 1) ^ c - i ^ c else 0).sum = g ^ c
  | 0, h => by
    have : g = 0 := by omega
    subst this
    rw [Nat.zero_pow (by omega)]
    simp
  | lam + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases hg : g ≤ lam
    · rw [sum_thresholds c g hc lam hg]
      simp [show ¬ (lam < g) by omega]
    · have hgl : g = lam + 1 := by omega
      subst hgl
      have hmono : lam ^ c ≤ (lam + 1) ^ c := Nat.pow_le_pow_left (by omega) c
      have hsum : ((List.range lam).map fun i =>
          if i + 1 ≤ lam + 1 then (i + 1) ^ c - i ^ c else 0).sum =
          ((List.range lam).map fun i => if i + 1 ≤ lam then (i + 1) ^ c - i ^ c else 0).sum := by
        congr 1
        refine List.map_congr_left fun i hi => ?_
        have := List.mem_range.mp hi
        simp [show i + 1 ≤ lam + 1 by omega, show i + 1 ≤ lam by omega]
      rw [hsum, sum_thresholds c lam hc lam le_rfl]
      simp only [le_refl, ↓reduceIte, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      omega

/-- A count as a sum of indicators. -/
theorem countP_eq_sum {α : Type} (l : List α) (P : α → Bool) :
    l.countP P = (l.map fun x => if P x then 1 else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases h : P a
    · simp [h, ih]; omega
    · simp [h, ih]

/-- Sums over two lists commute. -/
theorem sum_swap {α β : Type} (l : List α) (cs : List β) (f : β → α → ℕ) :
    (cs.map fun c => (l.map (f c)).sum).sum = (l.map fun x => (cs.map fun c => f c x).sum).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.map_cons, List.sum_cons, ih, ← List.sum_map_add]
    simp

end GrossCubic
