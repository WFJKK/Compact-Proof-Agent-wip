import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Linear algebra for entry 9

Facts about matrices written as functions `ℕ → ℕ → ℚ` with finite sums over `Finset.range`, none
about networks or checkers.

* `split_eq`: their `split_SVD` is an identity for any vectors `u`, `v`: `A B = Ê + Ar Br`.
* `bil_*`, `sub_eq`: their subproduct decomposition is an identity for any directions.
* `prod_diff_le`: their `max_row_diffs_per_dim_2` and its recursive use: a bound on the spread of
  a row of `A N` from bounds on the spreads of the rows of `N`, with any row `a` subtracted.
-/

namespace GrossSub

open Finset

/-! ## Spreads -/

/-- `|x| y ≤ |x| f` and `-(x y) ≤ |x| f` from `|y| ≤ f`: the product with a bounded factor. -/
theorem mul_le_abs_mul {x y f : ℚ} (h1 : y ≤ f) (h2 : -y ≤ f) : x * y ≤ |x| * f := by
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    exact mul_le_mul_of_nonneg_left h1 hx
  · rw [abs_of_neg hx]
    nlinarith

/-- **The bound of one row.** If `N[k][i] - N[k][j] ≤ f k` for every row `k` and columns `i`, `j`,
    then for every row `a` (their mean row, or zero) and columns `i`, `j` of `A N`:
    `(A N)[q][i] - (A N)[q][j] ≤ s + Σ_k |A[q][k] - a k| f k`, where `s` bounds the spread of
    `a N`. -/
theorem prod_diff_le (K : ℕ) (A : ℕ → ℚ) (N : ℕ → ℕ → ℚ) (a f : ℕ → ℚ) (s : ℚ) (i j : ℕ)
    (hN : ∀ k < K, N k i - N k j ≤ f k) (hN' : ∀ k < K, N k j - N k i ≤ f k)
    (hs : ∑ k ∈ range K, a k * N k i - ∑ k ∈ range K, a k * N k j ≤ s) :
    ∑ k ∈ range K, A k * N k i - ∑ k ∈ range K, A k * N k j ≤
      s + ∑ k ∈ range K, |A k - a k| * f k := by
  have e : ∑ k ∈ range K, A k * N k i - ∑ k ∈ range K, A k * N k j =
      (∑ k ∈ range K, a k * N k i - ∑ k ∈ range K, a k * N k j) +
        ∑ k ∈ range K, (A k - a k) * (N k i - N k j) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [e]
  have h2 : ∑ k ∈ range K, (A k - a k) * (N k i - N k j) ≤ ∑ k ∈ range K, |A k - a k| * f k :=
    Finset.sum_le_sum fun k hk => mul_le_abs_mul (hN k (mem_range.mp hk))
      (by have := hN' k (mem_range.mp hk); linarith)
  linarith

/-! ## Their `split_SVD`, for any vectors -/

/-- `A B = Ê + Ar Br` with `uA = uᵀ A`, `Ar = A - u uA`, `Bv = B v`, `Br = B - Bv vᵀ` and
    `Ê = u (uA B) + (Ar Bv) vᵀ`, for any `u`, `v`. -/
theorem split_eq (V r : ℕ) (A B : ℕ → ℕ → ℚ) (u v : ℕ → ℚ) (q t : ℕ) :
    ∑ k ∈ range r, A q k * B k t =
      (u q * ∑ k ∈ range r, (∑ s ∈ range V, u s * A s k) * B k t +
        (∑ k ∈ range r, (A q k - u q * ∑ s ∈ range V, u s * A s k) *
          ∑ t' ∈ range V, B k t' * v t') * v t) +
      ∑ k ∈ range r, (A q k - u q * ∑ s ∈ range V, u s * A s k) *
        (B k t - (∑ t' ∈ range V, B k t' * v t') * v t) := by
  set uA : ℕ → ℚ := fun k => ∑ s ∈ range V, u s * A s k
  set Bv : ℕ → ℚ := fun k => ∑ t' ∈ range V, B k t' * v t'
  have e1 : ∑ k ∈ range r, (A q k - u q * uA k) * Bv k =
      ∑ k ∈ range r, A q k * Bv k - u q * ∑ k ∈ range r, uA k * Bv k := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∑ k ∈ range r, (A q k - u q * uA k) * (B k t - Bv k * v t) =
      ∑ k ∈ range r, A q k * B k t - v t * ∑ k ∈ range r, A q k * Bv k -
        u q * ∑ k ∈ range r, uA k * B k t + u q * v t * ∑ k ∈ range r, uA k * Bv k := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  change _ = (u q * ∑ k ∈ range r, uA k * B k t +
      (∑ k ∈ range r, (A q k - u q * uA k) * Bv k) * v t) +
      ∑ k ∈ range r, (A q k - u q * uA k) * (B k t - Bv k * v t)
  rw [e1, e2]
  ring

/-! ## Their subproduct decomposition, for any directions -/

/-- The bilinear form `X M Yᵀ` of a row `X` and a row `Y` (`d` coordinates each). -/
def bil (d : ℕ) (M : ℕ → ℕ → ℚ) (X Y : ℕ → ℚ) : ℚ :=
  ∑ a ∈ range d, X a * ∑ b ∈ range d, M a b * Y b

theorem bil_add_left (d : ℕ) (M : ℕ → ℕ → ℚ) (X X' Y : ℕ → ℚ) :
    bil d M (fun a => X a + X' a) Y = bil d M X Y + bil d M X' Y := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem bil_add_right (d : ℕ) (M : ℕ → ℕ → ℚ) (X Y Y' : ℕ → ℚ) :
    bil d M X (fun b => Y b + Y' b) = bil d M X Y + bil d M X Y' := by
  unfold bil
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_congr rfl fun b _ => by ring

theorem bil_smul_left (d : ℕ) (M : ℕ → ℕ → ℚ) (c : ℚ) (X Y : ℕ → ℚ) :
    bil d M (fun a => c * X a) Y = c * bil d M X Y := by
  unfold bil
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring

theorem bil_smul_right (d : ℕ) (M : ℕ → ℕ → ℚ) (c : ℚ) (X Y : ℕ → ℚ) :
    bil d M X (fun b => c * Y b) = c * bil d M X Y := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `bil` against a row scaled from the right: `X M (c Y)ᵀ` read with `M`'s rows summed first. -/
theorem bil_swap (d : ℕ) (M : ℕ → ℕ → ℚ) (X Y : ℕ → ℚ) :
    bil d M X Y = ∑ b ∈ range d, Y b * ∑ a ∈ range d, X a * M a b := by
  unfold bil
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

/-- `M = Wq Wkᵀ`: the form of `M` splits along the head's coordinates. -/
theorem bil_prod (d h : ℕ) (Wq Wk : ℕ → ℕ → ℚ) (X Y : ℕ → ℚ) :
    bil d (fun a b => ∑ k ∈ range h, Wq a k * Wk b k) X Y =
      ∑ k ∈ range h, (∑ a ∈ range d, X a * Wq a k) * ∑ b ∈ range d, Wk b k * Y b := by
  unfold bil
  have lhs : ∀ a, X a * ∑ b ∈ range d, (∑ k ∈ range h, Wq a k * Wk b k) * Y b =
      ∑ b ∈ range d, ∑ k ∈ range h, X a * Wq a k * (Wk b k * Y b) := by
    intro a
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [Finset.sum_congr rfl fun a _ => lhs a]
  have rhs : ∀ k, (∑ a ∈ range d, X a * Wq a k) * ∑ b ∈ range d, Wk b k * Y b =
      ∑ a ∈ range d, ∑ b ∈ range d, X a * Wq a k * (Wk b k * Y b) := fun k => by
    rw [Finset.sum_mul_sum]
  rw [Finset.sum_congr rfl fun k _ => rhs k, Finset.sum_comm (s := range h)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]

/-- A row written as a rank-one part plus a remainder. -/
theorem fun_split (X : ℕ → ℚ) (c : ℚ) (x R : ℕ → ℚ) (hR : ∀ a, R a = X a - c * x a) :
    X = fun a => c * x a + R a :=
  funext fun a => by rw [hR]; ring

/-- **Their subproduct decomposition** (`decompose_EQKE_error_quadratic`), for any directions:
    `EQKE[q, t] = Eq_q M Ek_tᵀ` with `M = Wq Wkᵀ` is the six rank-one terms of `Ê` plus the
    remainder `(Qe2 Wqe)(Wkeᵀ Ke2ᵀ)`. The hypotheses are the definitions of the checker's tables;
    the rank-one parts `kd k1`, `qd q1`, ... may be any (theirs are projections). -/
theorem sub_eq (d h : ℕ) (Eq Ek Wq Wk : ℕ → ℕ → ℚ) (kd qd skd sqd qu ku : ℕ → ℚ)
    (k1 q1 k2 q2 wq1 wk1 z1 z2 z3 z4 z5 z6 x1 y2 x3 y4 x5 y5 y6 x6 : ℕ → ℚ)
    (Ke Qe Ke2 Qe2 Wqe Wke : ℕ → ℕ → ℚ) (q t : ℕ)
    (hKe : ∀ t b, Ke t b = Ek t b - kd t * k1 b)
    (hQe : ∀ q a, Qe q a = Eq q a - qd q * q1 a)
    (hKe2 : ∀ t b, Ke2 t b = Ke t b - skd t * k2 b)
    (hQe2 : ∀ q a, Qe2 q a = Qe q a - sqd q * q2 a)
    (hWqe : ∀ a k, Wqe a k = Wq a k - qu a * wq1 k)
    (hWke : ∀ b k, Wke b k = Wk b k - ku b * wk1 k)
    (hz1 : ∀ b, z1 b = ∑ a ∈ range d, q1 a * ∑ k ∈ range h, Wq a k * Wk b k)
    (hx1 : ∀ t, x1 t = ∑ b ∈ range d, Ek t b * z1 b)
    (hz2 : ∀ a, z2 a = ∑ b ∈ range d, (∑ k ∈ range h, Wq a k * Wk b k) * k1 b)
    (hy2 : ∀ q, y2 q = ∑ a ∈ range d, Qe q a * z2 a)
    (hz3 : ∀ b, z3 b = ∑ a ∈ range d, q2 a * ∑ k ∈ range h, Wq a k * Wk b k)
    (hx3 : ∀ t, x3 t = ∑ b ∈ range d, Ke t b * z3 b)
    (hz4 : ∀ a, z4 a = ∑ b ∈ range d, (∑ k ∈ range h, Wq a k * Wk b k) * k2 b)
    (hy4 : ∀ q, y4 q = ∑ a ∈ range d, Qe2 q a * z4 a)
    (hz5 : ∀ b, z5 b = ∑ k ∈ range h, Wk b k * wq1 k)
    (hx5 : ∀ t, x5 t = ∑ b ∈ range d, Ke2 t b * z5 b)
    (hy5 : ∀ q, y5 q = ∑ a ∈ range d, Qe2 q a * qu a)
    (hz6 : ∀ a, z6 a = ∑ k ∈ range h, Wqe a k * wk1 k)
    (hy6 : ∀ q, y6 q = ∑ a ∈ range d, Qe2 q a * z6 a)
    (hx6 : ∀ t, x6 t = ∑ b ∈ range d, Ke2 t b * ku b) :
    bil d (fun a b => ∑ k ∈ range h, Wq a k * Wk b k) (Eq q) (Ek t) =
      (qd q * x1 t + y2 q * kd t + sqd q * x3 t + y4 q * skd t + y5 q * x5 t + y6 q * x6 t) +
      ∑ k ∈ range h, (∑ a ∈ range d, Qe2 q a * Wqe a k) * ∑ b ∈ range d, Wke b k * Ke2 t b := by
  set M : ℕ → ℕ → ℚ := fun a b => ∑ k ∈ range h, Wq a k * Wk b k with hM
  -- the query side: Eq = qd q1 + Qe, Qe = sqd q2 + Qe2; the key side likewise
  have eEq : Eq q = fun a => qd q * q1 a + Qe q a := fun_split _ _ _ _ (hQe q)
  have eEk : Ek t = fun b => kd t * k1 b + Ke t b := fun_split _ _ _ _ (hKe t)
  have eQe : Qe q = fun a => sqd q * q2 a + Qe2 q a := fun_split _ _ _ _ (hQe2 q)
  have eKe : Ke t = fun b => skd t * k2 b + Ke2 t b := fun_split _ _ _ _ (hKe2 t)
  have s1 : bil d M (Eq q) (Ek t) =
      qd q * bil d M q1 (Ek t) + kd t * bil d M (Qe q) k1 + bil d M (Qe q) (Ke t) :=
    calc bil d M (Eq q) (Ek t) = bil d M (fun a => qd q * q1 a + Qe q a) (Ek t) := by rw [← eEq]
      _ = qd q * bil d M q1 (Ek t) + bil d M (Qe q) (Ek t) := by
        rw [bil_add_left, bil_smul_left]
      _ = qd q * bil d M q1 (Ek t) + bil d M (Qe q) (fun b => kd t * k1 b + Ke t b) := by
        rw [← eEk]
      _ = _ := by rw [bil_add_right, bil_smul_right]; ring
  have s2 : bil d M (Qe q) (Ke t) =
      sqd q * bil d M q2 (Ke t) + skd t * bil d M (Qe2 q) k2 + bil d M (Qe2 q) (Ke2 t) :=
    calc bil d M (Qe q) (Ke t) = bil d M (fun a => sqd q * q2 a + Qe2 q a) (Ke t) := by
          rw [← eQe]
      _ = sqd q * bil d M q2 (Ke t) + bil d M (Qe2 q) (Ke t) := by
        rw [bil_add_left, bil_smul_left]
      _ = sqd q * bil d M q2 (Ke t) + bil d M (Qe2 q) (fun b => skd t * k2 b + Ke2 t b) := by
        rw [← eKe]
      _ = _ := by rw [bil_add_right, bil_smul_right]; ring
  have t1 : bil d M q1 (Ek t) = x1 t := by
    rw [bil_swap, hx1]
    exact Finset.sum_congr rfl fun b _ => by rw [hz1]
  have t2 : bil d M (Qe q) k1 = y2 q := by
    rw [hy2]; unfold bil
    exact Finset.sum_congr rfl fun a _ => by rw [hz2]
  have t3 : bil d M q2 (Ke t) = x3 t := by
    rw [bil_swap, hx3]
    exact Finset.sum_congr rfl fun b _ => by rw [hz3]
  have t4 : bil d M (Qe2 q) k2 = y4 q := by
    rw [hy4]; unfold bil
    exact Finset.sum_congr rfl fun a _ => by rw [hz4]
  -- the remainder, through the head's coordinates
  have t5 : bil d M (Qe2 q) (Ke2 t) = y5 q * x5 t + y6 q * x6 t +
      ∑ k ∈ range h, (∑ a ∈ range d, Qe2 q a * Wqe a k) * ∑ b ∈ range d, Wke b k * Ke2 t b := by
    rw [hM, bil_prod]
    have eq1 : ∀ k, ∑ a ∈ range d, Qe2 q a * Wq a k =
        y5 q * wq1 k + ∑ a ∈ range d, Qe2 q a * Wqe a k := by
      intro k
      rw [hy5, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by rw [hWqe]; ring
    have eq2 : ∀ k, ∑ b ∈ range d, Wk b k * Ke2 t b =
        wk1 k * x6 t + ∑ b ∈ range d, Wke b k * Ke2 t b := by
      intro k
      rw [hx6, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [hWke]; ring
    have ex5 : ∑ k ∈ range h, wq1 k * ∑ b ∈ range d, Wk b k * Ke2 t b = x5 t := by
      rw [hx5]
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [hz5, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have ey6 : ∑ k ∈ range h, (∑ a ∈ range d, Qe2 q a * Wqe a k) * wk1 k = y6 q := by
      rw [hy6]
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hz6, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    have e : ∀ k, (∑ a ∈ range d, Qe2 q a * Wq a k) * ∑ b ∈ range d, Wk b k * Ke2 t b =
        y5 q * (wq1 k * ∑ b ∈ range d, Wk b k * Ke2 t b) +
        x6 t * ((∑ a ∈ range d, Qe2 q a * Wqe a k) * wk1 k) +
        (∑ a ∈ range d, Qe2 q a * Wqe a k) * ∑ b ∈ range d, Wke b k * Ke2 t b := by
      intro k
      rw [eq1 k]
      conv_lhs => rw [show (∑ b ∈ range d, Wk b k * Ke2 t b) = _ from rfl]
      rw [add_mul]
      conv_lhs => arg 2; rw [eq2 k]
      ring
    rw [Finset.sum_congr rfl fun k _ => e k, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ex5, ey6]
    ring
  rw [s1, s2, t1, t2, t3, t4, t5]
  ring

end GrossSub
