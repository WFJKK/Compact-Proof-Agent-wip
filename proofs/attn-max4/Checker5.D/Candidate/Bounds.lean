import Candidate.Bridge

/-!
# Real-number bounds used by the group checker: interval product lower bound, far bound.
-/

namespace Candidate.Formula

/-- `min (lo*h) (hi*h) ≤ e*h` whenever `lo ≤ e ≤ hi`. -/
theorem lbProd_le {lo hi e h : ℝ} (h1 : lo ≤ e) (h2 : e ≤ hi) : min (lo * h) (hi * h) ≤ e * h := by
  rcases le_or_gt 0 h with hh | hh
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right h1 hh)
  · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right h2 hh.le)

/-- The far bound: `-E * max 0 N ≤ e * h` when `0 ≤ e ≤ E` and `-h ≤ N`. -/
theorem far_le {E e h N : ℝ} (he0 : 0 ≤ e) (heE : e ≤ E) (hN : -h ≤ N) : -E * max 0 N ≤ e * h := by
  have hE0 : 0 ≤ E := le_trans he0 heE
  rcases le_or_gt 0 h with hh | hh
  · have : 0 ≤ e * h := mul_nonneg he0 hh
    have : 0 ≤ E * max 0 N := mul_nonneg hE0 (le_max_left _ _)
    linarith
  · have hNh : -h ≤ max 0 N := le_trans hN (le_max_right _ _)
    have h3 : e * (-h) ≤ E * max 0 N :=
      mul_le_mul heE hNh (by linarith) hE0
    linarith

/-- Exponential monotonicity for the far bound: `exp (S - K) ≤ hi` when `S ≤ Smax` and `exp (Smax - K) ≤ hi`. -/
theorem exp_far_le {S Smax K hi : ℝ} (hS : S ≤ Smax) (hhi : Real.exp (Smax - K) ≤ hi) :
    Real.exp (S - K) ≤ hi :=
  le_trans (Real.exp_le_exp.mpr (by linarith)) hhi

/-- A sum of four terms, each bounded below. -/
theorem sum4_le {a b : Fin 4 → ℝ} (h : ∀ k, a k ≤ b k) : ∑ k, a k ≤ ∑ k, b k :=
  Finset.sum_le_sum fun k _ => h k

theorem sum_range4_le {a b : ℕ → ℝ} (h : ∀ k < 4, a k ≤ b k) :
    ∑ k ∈ Finset.range 4, a k ≤ ∑ k ∈ Finset.range 4, b k :=
  Finset.sum_le_sum fun k hk => h k (Finset.mem_range.mp hk)

theorem sum_range4_expand (a : ℕ → ℝ) : ∑ k ∈ Finset.range 4, a k = a 0 + a 1 + a 2 + a 3 := by
  simp [Finset.sum_range_succ]

end Candidate.Formula
