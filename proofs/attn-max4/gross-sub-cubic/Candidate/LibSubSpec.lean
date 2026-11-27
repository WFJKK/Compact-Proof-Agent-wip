import Candidate.LibCommonBasic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Steps 2 to 4 of entry 9, over the reals

The argument for one input, with the softmax's denominator cleared, as facts about real numbers;
none mentions networks or checkers.

* `logit_le`: the advantage of an output `j` over the label, weighted by the exponentials of the
  scores, is at most `X (F + R) + Y (F + W)`: `X`, `Y` the weights on the label's positions and on
  the others, `F` the direct and positional paths, `R` the label's path, `W` the worst other
  token's (their `compute_largest_wrong_logit_quadratic`, before the average).
* `ratio_lo`, `ratio_hi`: with the other tokens' score gaps between `a_lo` and `a_hi`, and the
  positions holding the label anywhere among the others, the weights compare with those of the
  arrangements of the sorted positional errors (their `compute_extreme_softmaxed_..._quadratic`):
  `X B_lo ≥ A_lo Y` and `X B_hi ≤ A_hi Y`.
* `endpoint_le`: the cleared test at an endpoint, with the average `avg` of the certificate,
  bounds `A (F + R) + B (F + W)` for every output (their average split, taken at `R_max` and
  `R_min`: sound for every `avg`).
* `combine_lo`, `combine_hi`: from an endpoint to the input, when the slope `R - W` has the right
  sign.
-/

namespace GrossSub

open Finset

/-! ## The logit bound -/

/-- **The bound on one output.** With `e_p > 0` the weights, `D ≤ Fd` the direct path's advantage,
    `P_p ≤ Pp` the positional path's, the label's positions adding `R` and the others at most `W`:
    `Σ_p e_p (D + P_p + Q_p) ≤ X (Fd + Pp + R) + Y (Fd + Pp + W)`. -/
theorem logit_le (n : ℕ) (e : ℕ → ℝ) (he : ∀ p < n, 0 < e p) (lab : ℕ → Prop) [DecidablePred lab]
    (D Fd Pp R W : ℝ) (P Q : ℕ → ℝ) (hD : D ≤ Fd) (hP : ∀ p < n, P p ≤ Pp)
    (hR : ∀ p < n, lab p → Q p = R) (hW : ∀ p < n, ¬ lab p → Q p ≤ W) :
    ∑ p ∈ range n, e p * (D + (P p + Q p)) ≤
      (∑ p ∈ range n, if lab p then e p else 0) * (Fd + Pp + R) +
      (∑ p ∈ range n, if lab p then 0 else e p) * (Fd + Pp + W) := by
  rw [Finset.sum_mul, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp' := mem_range.mp hp
  have hep := he p hp'
  by_cases hl : lab p
  · simp only [hl, ↓reduceIte, zero_mul, add_zero]
    rw [hR p hp' hl]
    have := hP p hp'
    nlinarith
  · simp only [hl, ↓reduceIte, zero_mul, zero_add]
    have := hP p hp'
    have := hW p hp' hl
    nlinarith

/-! ## The weights against the sorted arrangements -/

/-- **The lower endpoint.** `X = E (s + c1)` (the label's positions: `s` from the positions other
    than the query's, `c1` the query's), `Y ≤ E e^{-a} (T - s + c2)` (the others, each gap at least
    `a`), and `s* ≤ s` (the `k` smallest): then `X B* ≥ A* Y` with `A* = e^a (s* + c1)`,
    `B* = T - s* + c2`. -/
theorem ratio_lo {X Y E a s sS T c1 c2 : ℝ} (hE : 0 < E) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hsS : sS ≤ s) (hsT : s ≤ T) (hS0 : 0 ≤ sS) (hX : X = E * (s + c1))
    (hY : Y ≤ E * Real.exp (-a) * (T - s + c2)) :
    Real.exp a * (sS + c1) * Y ≤ X * (T - sS + c2) := by
  have ha : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 ≤ Real.exp a * (sS + c1) := by positivity
  calc Real.exp a * (sS + c1) * Y ≤ Real.exp a * (sS + c1) * (E * Real.exp (-a) * (T - s + c2)) :=
        mul_le_mul_of_nonneg_left hY hpos
    _ = E * ((sS + c1) * (T - s + c2)) := by
        rw [show Real.exp a * (sS + c1) * (E * Real.exp (-a) * (T - s + c2)) =
          (Real.exp a * Real.exp (-a)) * (E * ((sS + c1) * (T - s + c2))) by ring, ha, one_mul]
    _ ≤ E * ((s + c1) * (T - sS + c2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hE.le
        nlinarith
    _ = X * (T - sS + c2) := by rw [hX]; ring

/-- **The upper endpoint.** As `ratio_lo`, with each gap at most `a`, and `s ≤ s^` (the `k`
    largest): `X B^ ≤ A^ Y`. -/
theorem ratio_hi {X Y E a s sL T c1 c2 : ℝ} (hE : 0 < E) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (hsL : s ≤ sL) (hLT : sL ≤ T) (hs0 : 0 ≤ s) (hX : X = E * (s + c1))
    (hY : E * Real.exp (-a) * (T - s + c2) ≤ Y) :
    X * (T - sL + c2) ≤ Real.exp a * (sL + c1) * Y := by
  have ha : Real.exp a * Real.exp (-a) = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 ≤ Real.exp a * (sL + c1) := mul_nonneg (Real.exp_pos a).le (by linarith)
  calc X * (T - sL + c2) = E * ((s + c1) * (T - sL + c2)) := by rw [hX]; ring
    _ ≤ E * ((sL + c1) * (T - s + c2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hE.le
        nlinarith
    _ = Real.exp a * (sL + c1) * (E * Real.exp (-a) * (T - s + c2)) := by
        rw [show Real.exp a * (sL + c1) * (E * Real.exp (-a) * (T - s + c2)) =
          (Real.exp a * Real.exp (-a)) * (E * ((sL + c1) * (T - s + c2))) by ring, ha, one_mul]
    _ ≤ Real.exp a * (sL + c1) * Y := mul_le_mul_of_nonneg_left hY hpos

/-! ## The test at an endpoint -/

/-- `max (lo y) (hi y)` bounds `e y` for `lo ≤ e ≤ hi`. -/
theorem le_kup {lo hi e y : ℝ} (hlo : lo ≤ e) (hhi : e ≤ hi) : e * y ≤ max (lo * y) (hi * y) := by
  rcases le_or_gt 0 y with hy | hy
  · exact le_trans (mul_le_mul_of_nonneg_right hhi hy) (le_max_right _ _)
  · exact le_trans (mul_le_mul_of_nonpos_right hlo hy.le) (le_max_left _ _)

/-- **Their average split, made sound.** With `top ≥ L + avg R` and `g0 = top + (1 - avg) W`, for
    `A, B ≥ 0` and `R` between `Rmin` and `Rmax`: `A (F + R) + B (F + W)`, `F = L + s`, is at most
    the larger of the tests at `R* = Rmax` and `R* = Rmin`,
    `A (g0 + (1 - avg)(R* - W) + s) + B (g0 - avg (R* - W) + s)`. -/
theorem endpoint_le {A B L R W s avg top Rmax Rmin : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (htop : L + avg * R ≤ top) (hRmax : R ≤ Rmax) (hRmin : Rmin ≤ R) :
    A * (L + s + R) + B * (L + s + W) ≤
      max (A * (top + (1 - avg) * W + (1 - avg) * (Rmax - W) + s) +
          B * (top + (1 - avg) * W - avg * (Rmax - W) + s))
        (A * (top + (1 - avg) * W + (1 - avg) * (Rmin - W) + s) +
          B * (top + (1 - avg) * W - avg * (Rmin - W) + s)) := by
  -- each output is below the line in `R` through the two tests
  have h1 : A * (L + s + R) + B * (L + s + W) ≤
      A * (top + (1 - avg) * W + (1 - avg) * (R - W) + s) +
        B * (top + (1 - avg) * W - avg * (R - W) + s) := by
    have e1 : L + s + R ≤ top + (1 - avg) * W + (1 - avg) * (R - W) + s := by nlinarith
    have e2 : L + s + W ≤ top + (1 - avg) * W - avg * (R - W) + s := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left e1 hA, mul_le_mul_of_nonneg_left e2 hB]
  -- the line is affine in `R`: its value is at most the larger end
  set c := A * (1 - avg) - B * avg
  have e : ∀ x, A * (top + (1 - avg) * W + (1 - avg) * (x - W) + s) +
      B * (top + (1 - avg) * W - avg * (x - W) + s) =
      (A + B) * (top + (1 - avg) * W + s) + c * (x - W) := fun x => by ring
  rw [e R] at h1
  rw [e Rmax, e Rmin]
  rcases le_or_gt 0 c with hc | hc
  · exact le_trans h1 (le_trans (by nlinarith) (le_max_left _ _))
  · exact le_trans h1 (le_trans (by nlinarith) (le_max_right _ _))

/-- **From an endpoint to the input.** If `X B* ≥ A* Y`, the slope `R - W` is at most zero and the
    cleared test at the endpoint is negative, so is `X (F + R) + Y (F + W)`. -/
theorem combine_lo {X Y A B F R W : ℝ} (hXY : 0 < X + Y)
    (hAB : 0 < A + B) (hr : A * Y ≤ X * B) (hRW : R ≤ W) (hneg : A * (F + R) + B * (F + W) < 0) :
    X * (F + R) + Y * (F + W) < 0 := by
  have key : (A + B) * (X * (F + R) + Y * (F + W)) =
      (X + Y) * (A * (F + R) + B * (F + W)) + (B * X - A * Y) * (R - W) := by ring
  have h1 : (B * X - A * Y) * (R - W) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
  have h2 : (X + Y) * (A * (F + R) + B * (F + W)) < 0 := mul_neg_of_pos_of_neg hXY hneg
  have h3 : (A + B) * (X * (F + R) + Y * (F + W)) < 0 := by linarith
  by_contra hc
  push Not at hc
  have := mul_nonneg hAB.le hc
  linarith

/-- **The upper endpoint to the input.** If `X B^ ≤ A^ Y`, the slope `R - W` is at least zero and
    the cleared test at the endpoint is negative, so is `X (F + R) + Y (F + W)`. -/
theorem combine_hi {X Y A B F R W : ℝ} (hXY : 0 < X + Y)
    (hAB : 0 < A + B) (hr : X * B ≤ A * Y) (hRW : W ≤ R) (hneg : A * (F + R) + B * (F + W) < 0) :
    X * (F + R) + Y * (F + W) < 0 := by
  have key : (A + B) * (X * (F + R) + Y * (F + W)) =
      (X + Y) * (A * (F + R) + B * (F + W)) + (B * X - A * Y) * (R - W) := by ring
  have h1 : (B * X - A * Y) * (R - W) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have h2 : (X + Y) * (A * (F + R) + B * (F + W)) < 0 := mul_neg_of_pos_of_neg hXY hneg
  have h3 : (A + B) * (X * (F + R) + Y * (F + W)) < 0 := by linarith
  by_contra hc
  push Not at hc
  have := mul_nonneg hAB.le hc
  linarith

end GrossSub
