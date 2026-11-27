import Candidate.LibCommonBasic

import Mathlib.Order.Monotone.Basic

/-!
# Sorting the positional errors

The checker sorts each query's positional errors by insertion, a network of `min` and `max`
(`GrossSub.sortV`). Its value is a sorted permutation of its input (`sortVal_perm`,
`sortVal_sorted`). Then, for any `k` of the values, chosen anyhow (the positions of an input that
hold the largest token), the sum of a monotone function over them lies between its sums over the
`k` smallest and the `k` largest (`take_le_subperm`, `subperm_le_drop`): their sorting argument.
-/

namespace GrossSub

open CompactCheck

/-- The value of one insertion: compare-and-exchange along the list. -/
def insVal (x : Q) : List Q → List Q
  | [] => [x]
  | y :: ys => ⟨min x.val y.val⟩ :: insVal ⟨max x.val y.val⟩ ys

/-- The value of the sort. -/
def sortVal : List Q → List Q
  | [] => []
  | x :: xs => insVal x (sortVal xs)

theorem length_insVal (x : Q) : ∀ ys : List Q, (insVal x ys).length = ys.length + 1
  | [] => rfl
  | y :: ys => by simp [insVal, length_insVal _ ys]

theorem length_sortVal : ∀ xs : List Q, (sortVal xs).length = xs.length
  | [] => rfl
  | x :: xs => by simp [sortVal, length_insVal, length_sortVal xs]

theorem insVal_perm (x : Q) :
    ∀ ys : List Q, ((insVal x ys).map (·.val)).Perm (x.val :: ys.map (·.val))
  | [] => List.Perm.refl _
  | y :: ys => by
    simp only [insVal, List.map_cons]
    have ih := insVal_perm ⟨max x.val y.val⟩ ys
    refine (List.Perm.cons _ ih).trans ?_
    simp only
    rcases le_total x.val y.val with h | h
    · rw [min_eq_left h, max_eq_right h]
    · rw [min_eq_right h, max_eq_left h]
      exact List.Perm.swap _ _ _

theorem insVal_sorted (x : Q) : ∀ ys : List Q, (ys.map (·.val)).Pairwise (· ≤ ·) →
    ((insVal x ys).map (·.val)).Pairwise (· ≤ ·)
  | [], _ => List.pairwise_singleton _ _
  | y :: ys, hs => by
    simp only [insVal, List.map_cons] at hs ⊢
    rw [List.pairwise_cons] at hs ⊢
    refine ⟨fun b hb => ?_, insVal_sorted _ ys hs.2⟩
    have hb' := (insVal_perm ⟨max x.val y.val⟩ ys).subset hb
    rcases List.mem_cons.mp hb' with rfl | hb'
    · exact min_le_max
    · exact le_trans (min_le_right _ _) (hs.1 b hb')

theorem sortVal_perm : ∀ xs : List Q, ((sortVal xs).map (·.val)).Perm (xs.map (·.val))
  | [] => List.Perm.refl _
  | x :: xs => by
    simp only [sortVal, List.map_cons]
    exact (insVal_perm x _).trans (List.Perm.cons _ (sortVal_perm xs))

theorem sortVal_sorted : ∀ xs : List Q, ((sortVal xs).map (·.val)).Pairwise (· ≤ ·)
  | [] => List.Pairwise.nil
  | x :: xs => insVal_sorted x _ (sortVal_sorted xs)

/-! ## Sums over the smallest and the largest -/

/-- **The `k` smallest.** For a sorted list and any `k` of its entries (a subpermutation), the sum
    of a monotone function over the first `k` is at most its sum over those. -/
theorem take_le_subperm {f : ℚ → ℝ} (hf : Monotone f) :
    ∀ (w : List ℚ), w.Pairwise (· ≤ ·) → ∀ S : List ℚ, S.Subperm w →
      ((w.take S.length).map f).sum ≤ (S.map f).sum
  | [], _, S, hS => by
    rw [List.subperm_nil.mp hS]; simp
  | a :: w, hw, S, hS => by
    rw [List.pairwise_cons] at hw
    by_cases ha : a ∈ S
    · -- `a` is one of them: take it out on both sides
      have hp : S.Perm (a :: S.erase a) := List.perm_cons_erase ha
      have hS' : (S.erase a).Subperm w := by
        have := hS.erase a
        simpa using this
      have ih := take_le_subperm hf w hw.2 (S.erase a) hS'
      have hlen : S.length = (S.erase a).length + 1 := by
        rw [hp.length_eq]; simp
      rw [hlen, List.take_succ_cons, List.map_cons, List.sum_cons, hp.map f |>.sum_eq,
        List.map_cons, List.sum_cons]
      linarith
    · -- it is not: they are all in `w`, whose first `k` are no smaller than `a` and the first
      -- `k - 1` of `w`
      have hS' : S.Subperm w := by
        have := hS.erase a
        rwa [List.erase_of_not_mem ha, List.erase_cons_head] at this
      have ih := take_le_subperm hf w hw.2 S hS'
      have hk : S.length ≤ w.length := hS'.length_le
      rcases Nat.eq_zero_or_pos S.length with h0 | hpos
      · rw [h0]; simp [List.length_eq_zero_iff.mp h0]
      · obtain ⟨k, hk1⟩ : ∃ k, S.length = k + 1 := ⟨S.length - 1, by omega⟩
        rw [hk1] at ih hk ⊢
        rw [List.take_succ_cons, List.map_cons, List.sum_cons]
        have hkw : k < w.length := by omega
        rw [List.take_add_one, List.getElem?_eq_getElem hkw] at ih
        simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, add_zero] at ih
        have hle : f a ≤ f (w[k]) := hf (hw.1 _ (List.getElem_mem hkw))
        linarith

/-- The sum over all entries is the sum over the first `k` and the rest. -/
theorem sum_take_drop (f : ℚ → ℝ) (w : List ℚ) (k : ℕ) :
    ((w.take k).map f).sum + ((w.drop k).map f).sum = (w.map f).sum := by
  rw [← List.sum_append, ← List.map_append, List.take_append_drop]

/-- **The `k` largest.** For a sorted list and a partition of its entries into `S` and `C`
    (as multisets), the sum over `S` is at most the sum over the last `|S|`. -/
theorem subperm_le_drop {f : ℚ → ℝ} (hf : Monotone f) (w : List ℚ) (hw : w.Pairwise (· ≤ ·))
    (S C : List ℚ) (hSC : (S ++ C).Perm w) :
    (S.map f).sum ≤ ((w.drop (w.length - S.length)).map f).sum := by
  have hC : C.Subperm w := (List.sublist_append_right S C).subperm.trans hSC.subperm
  have h1 := take_le_subperm hf w hw C hC
  have hlen : w.length - S.length = C.length := by
    rw [← hSC.length_eq, List.length_append]; omega
  rw [hlen]
  have h2 := sum_take_drop f w C.length
  have h3 : (S.map f).sum + (C.map f).sum = (w.map f).sum := by
    rw [← List.sum_append, ← List.map_append, (hSC.map f).sum_eq]
  linarith

/-- The `k` smallest, for a partition. -/
theorem take_le_part {f : ℚ → ℝ} (hf : Monotone f) (w : List ℚ) (hw : w.Pairwise (· ≤ ·))
    (S C : List ℚ) (hSC : (S ++ C).Perm w) :
    ((w.take S.length).map f).sum ≤ (S.map f).sum :=
  take_le_subperm hf w hw S ((List.sublist_append_left S C).subperm.trans hSC.subperm)

end GrossSub
