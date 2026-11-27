import Candidate.LibSubLin

/-!
# The `svd` bound of entry 9, certified

Gross et al. bound the spread of a row of the remainder `R = Ar Br` by `√2 σ₁(R)`, `σ₁` from an
SVD. The checker has no square roots; it reads `T`, `F₁`, `F₂` and `ε` from the certificate and
checks two matrices of size `r` (the inner dimension) positive semidefinite:

    X₁ = T Tᵀ - Arᵀ Ar,      X₂ = ε² I - 2 Tᵀ (Br Brᵀ) T

each as `F Fᵀ` plus a remainder whose diagonal dominates its row and column together
(`qf_nonneg`). Then every row of `R` spreads by at most `ε` (`spread_le_of_psd`): with
`b = Br (e_i - e_j)` and `w = Tᵀ b`,

    (R (e_i - e_j))_q² ≤ ‖Ar b‖² ≤ ‖w‖²,   ‖w‖⁴ = (wᵀ Tᵀ Br (e_i - e_j))² ≤ 2 ‖Brᵀ T w‖² ≤ ε² ‖w‖²,

all in rationals, squares only.
-/

namespace GrossSub

open Finset

/-- The quadratic form `Σ_i Σ_j z_i X_ij z_j`. -/
def qf (r : ℕ) (X : ℕ → ℕ → ℚ) (z : ℕ → ℚ) : ℚ :=
  ∑ i ∈ range r, ∑ j ∈ range r, z i * X i j * z j

theorem qf_sub (r : ℕ) (X Y : ℕ → ℕ → ℚ) (z : ℕ → ℚ) :
    qf r (fun i j => X i j - Y i j) z = qf r X z - qf r Y z := by
  unfold qf
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- `(Σ_k f k)² = Σ_k Σ_l f k f l`. -/
theorem sq_sum (s : Finset ℕ) (f : ℕ → ℚ) : (∑ k ∈ s, f k) ^ 2 = ∑ k ∈ s, ∑ l ∈ s, f k * f l := by
  rw [sq, Finset.sum_mul_sum]

/-- The form of a Gram matrix `Σ_l F_il F_jl` is a sum of squares. -/
theorem qf_gram (r m : ℕ) (F : ℕ → ℕ → ℚ) (z : ℕ → ℚ) :
    qf r (fun i j => ∑ l ∈ range m, F i l * F j l) z =
      ∑ l ∈ range m, (∑ i ∈ range r, z i * F i l) ^ 2 := by
  unfold qf
  simp only [sq_sum]
  have e : ∀ i j, z i * (∑ l ∈ range m, F i l * F j l) * z j =
      ∑ l ∈ range m, z i * F i l * (z j * F j l) := fun i j => by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp only [e]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]

theorem qf_gram_nonneg (r m : ℕ) (F : ℕ → ℕ → ℚ) (z : ℕ → ℚ) :
    0 ≤ qf r (fun i j => ∑ l ∈ range m, F i l * F j l) z := by
  rw [qf_gram]
  exact Finset.sum_nonneg fun l _ => sq_nonneg _

/-- A form whose matrix's diagonal dominates each row and column together is nonnegative:
    `2 D_ii ≥ Σ_{j ≠ i} (|D_ij| + |D_ji|)`. -/
theorem qf_dom_nonneg (r : ℕ) (D : ℕ → ℕ → ℚ)
    (hdom : ∀ i < r, ∑ j ∈ range r, (if j = i then 0 else |D i j| + |D j i|) ≤ D i i + D i i)
    (z : ℕ → ℚ) : 0 ≤ qf r D z := by
  unfold qf
  -- each off-diagonal term is at least `-|D_ij| (z_i² + z_j²) / 2`
  have hterm : ∀ i j, (if j = i then z i * D i i * z i
      else -(|D i j| * (z i ^ 2 + z j ^ 2) / 2)) ≤ z i * D i j * z j := by
    intro i j
    split
    · rename_i h; subst h; exact le_rfl
    · have h1 : -(|D i j| * (z i ^ 2 + z j ^ 2) / 2) ≤ -(|D i j| * |z i * z j|) := by
        have : |z i * z j| ≤ (z i ^ 2 + z j ^ 2) / 2 := by
          rw [abs_mul]
          nlinarith [sq_nonneg (|z i| - |z j|), sq_abs (z i), sq_abs (z j)]
        have := mul_le_mul_of_nonneg_left this (abs_nonneg (D i j))
        linarith
      have h2 : -(|D i j| * |z i * z j|) ≤ z i * D i j * z j := by
        have : |z i * D i j * z j| = |D i j| * |z i * z j| := by
          simp only [abs_mul]; ring
        have := neg_abs_le (z i * D i j * z j)
        linarith
      linarith
  have hlow : ∑ i ∈ range r, ∑ j ∈ range r, (if j = i then z i * D i i * z i
      else -(|D i j| * (z i ^ 2 + z j ^ 2) / 2)) ≤
      ∑ i ∈ range r, ∑ j ∈ range r, z i * D i j * z j :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
  -- the lower bound is `Σ_i z_i² (D_ii - Σ_{j ≠ i} (|D_ij| + |D_ji|) / 2) ≥ 0`
  have hsplit : ∀ i ∈ range r, ∑ j ∈ range r, (if j = i then z i * D i i * z i
      else -(|D i j| * (z i ^ 2 + z j ^ 2) / 2)) =
      z i * D i i * z i - ∑ j ∈ range r, (if j = i then 0 else |D i j| * z i ^ 2 / 2) -
        ∑ j ∈ range r, (if j = i then 0 else |D i j| * z j ^ 2 / 2) := by
    intro i hi
    have e : ∀ j, (if j = i then z i * D i i * z i else -(|D i j| * (z i ^ 2 + z j ^ 2) / 2)) =
        (if j = i then z i * D i i * z i else 0) - (if j = i then 0 else |D i j| * z i ^ 2 / 2) -
          (if j = i then 0 else |D i j| * z j ^ 2 / 2) := fun j => by
      split <;> ring
    rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      Finset.sum_ite_eq' (range r) i, ite_eq_left_iff.mpr fun h => absurd hi h]
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, Finset.sum_sub_distrib] at hlow
  -- swap the last double sum
  have hswap : ∑ i ∈ range r, ∑ j ∈ range r, (if j = i then 0 else |D i j| * z j ^ 2 / 2) =
      ∑ i ∈ range r, ∑ j ∈ range r, (if j = i then 0 else |D j i| * z i ^ 2 / 2) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j = i
    · subst h; simp
    · simp only [h, Ne.symm h, ↓reduceIte]
  rw [hswap] at hlow
  have hdiag : 0 ≤ ∑ i ∈ range r, z i * D i i * z i -
      ∑ i ∈ range r, ∑ j ∈ range r, (if j = i then 0 else |D i j| * z i ^ 2 / 2) -
      ∑ i ∈ range r, ∑ j ∈ range r, (if j = i then 0 else |D j i| * z i ^ 2 / 2) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_nonneg fun i hi => ?_
    have h := hdom i (mem_range.mp hi)
    have e1 : ∑ j ∈ range r, (if j = i then 0 else |D i j| * z i ^ 2 / 2) +
        ∑ j ∈ range r, (if j = i then 0 else |D j i| * z i ^ 2 / 2) =
        z i ^ 2 / 2 * ∑ j ∈ range r, (if j = i then 0 else |D i j| + |D j i|) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      split <;> ring
    have h2 : z i ^ 2 / 2 * ∑ j ∈ range r, (if j = i then 0 else |D i j| + |D j i|) ≤
        z i ^ 2 / 2 * (D i i + D i i) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    nlinarith
  linarith

/-- **Positive semidefinite**, from the certificate: `X - F Fᵀ` dominated by its diagonal. -/
theorem qf_nonneg (r : ℕ) (X F : ℕ → ℕ → ℚ)
    (hdom : ∀ i < r, ∑ j ∈ range r, (if j = i then 0 else
        |X i j - ∑ l ∈ range r, F i l * F j l| + |X j i - ∑ l ∈ range r, F j l * F i l|) ≤
      (X i i - ∑ l ∈ range r, F i l * F i l) + (X i i - ∑ l ∈ range r, F i l * F i l))
    (z : ℕ → ℚ) : 0 ≤ qf r X z := by
  have h1 := qf_gram_nonneg r r F z
  have h2 := qf_dom_nonneg r (fun i j => X i j - ∑ l ∈ range r, F i l * F j l) hdom z
  rw [qf_sub] at h2
  linarith

/-- The form of `Tᵀ M T` at `w` is the form of `M` at `T w`. -/
theorem qf_conj (r : ℕ) (T M : ℕ → ℕ → ℚ) (w : ℕ → ℚ) :
    qf r (fun l m => ∑ a ∈ range r, T a l * ∑ b ∈ range r, M a b * T b m) w =
      qf r M (fun a => ∑ l ∈ range r, T a l * w l) := by
  unfold qf
  have e1 : ∀ l m, w l * (∑ a ∈ range r, T a l * ∑ b ∈ range r, M a b * T b m) * w m =
      ∑ a ∈ range r, ∑ b ∈ range r, T a l * w l * M a b * (T b m * w m) := fun l m => by
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun b _ => by ring
  have e2 : ∀ a b, (∑ l ∈ range r, T a l * w l) * M a b * ∑ m ∈ range r, T b m * w m =
      ∑ l ∈ range r, ∑ m ∈ range r, T a l * w l * M a b * (T b m * w m) := fun a b => by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum]
  simp only [e1, e2]
  -- Σ_l Σ_m Σ_a Σ_b  =  Σ_a Σ_b Σ_l Σ_m
  rw [Finset.sum_congr rfl fun l _ => Finset.sum_comm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_congr rfl fun l _ => Finset.sum_comm, Finset.sum_comm]

theorem qf_diag (r : ℕ) (c : ℚ) (w : ℕ → ℚ) :
    qf r (fun i j => if i = j then c else 0) w = c * ∑ l ∈ range r, w l ^ 2 := by
  unfold qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have e : ∀ j, w i * (if i = j then c else 0) * w j = if i = j then c * w i ^ 2 else 0 :=
    fun j => by split <;> [subst_vars; skip] <;> ring
  rw [Finset.sum_congr rfl fun j _ => e j, Finset.sum_ite_eq (range r) i,
    ite_eq_left_iff.mpr fun h => absurd hi h]

theorem qf_add_self (r : ℕ) (X : ℕ → ℕ → ℚ) (w : ℕ → ℚ) :
    qf r (fun i j => X i j + X i j) w = 2 * qf r X w := by
  unfold qf
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **The `svd` bound.** If `T Tᵀ - Arᵀ Ar ⪰ 0`, `ε² - 2 Tᵀ (Br Brᵀ) T ⪰ 0` and `ε ≥ 0` (the
    matrices as the checker computes them), every row of `Ar Br` spreads by at most `ε`. -/
theorem spread_le_of_psd (V r : ℕ) (Ar Br T : ℕ → ℕ → ℚ) (e : ℚ) (he : 0 ≤ e)
    (h1 : ∀ z, 0 ≤ qf r (fun i j => (∑ l ∈ range r, T i l * T j l) -
      ∑ q ∈ range V, Ar q i * Ar q j) z)
    (h2 : ∀ w, 0 ≤ qf r (fun i j => (if i = j then 0 + e * e else 0) -
      ((∑ a ∈ range r, T a i * ∑ b ∈ range r, (∑ t ∈ range V, Br a t * Br b t) * T b j) +
        (∑ a ∈ range r, T a i * ∑ b ∈ range r, (∑ t ∈ range V, Br a t * Br b t) * T b j))) w)
    {q i j : ℕ} (hq : q < V) (hi : i < V) (hj : j < V) :
    ∑ k ∈ range r, Ar q k * Br k i - ∑ k ∈ range r, Ar q k * Br k j ≤ e := by
  set b : ℕ → ℚ := fun k => Br k i - Br k j with hb
  set w : ℕ → ℚ := fun l => ∑ k ∈ range r, T k l * b k with hw
  set z : ℕ → ℚ := fun a => ∑ l ∈ range r, T a l * w l with hz
  set y : ℕ → ℚ := fun t => ∑ a ∈ range r, z a * Br a t with hy
  set W : ℚ := ∑ l ∈ range r, w l ^ 2 with hW
  set GB : ℕ → ℕ → ℚ := fun a b => ∑ t ∈ range V, Br a t * Br b t with hGB
  have hRb : ∑ k ∈ range r, Ar q k * Br k i - ∑ k ∈ range r, Ar q k * Br k j =
      ∑ k ∈ range r, Ar q k * b k := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hb]; ring
  rw [hRb]
  -- the row against all rows, then the Gram matrix of `Ar`, then `T Tᵀ`
  have s1 : (∑ k ∈ range r, Ar q k * b k) ^ 2 ≤
      ∑ q' ∈ range V, (∑ k ∈ range r, Ar q' k * b k) ^ 2 :=
    Finset.single_le_sum (f := fun q' => (∑ k ∈ range r, Ar q' k * b k) ^ 2)
      (fun _ _ => sq_nonneg _) (mem_range.mpr hq)
  have s2 : ∑ q' ∈ range V, (∑ k ∈ range r, Ar q' k * b k) ^ 2 =
      qf r (fun i j => ∑ q ∈ range V, Ar q i * Ar q j) b := by
    have := qf_gram r V (fun i q => Ar q i) b
    rw [this]
    exact Finset.sum_congr rfl fun q' _ => by
      congr 1; exact Finset.sum_congr rfl fun k _ => by ring
  have s3 : qf r (fun i j => ∑ l ∈ range r, T i l * T j l) b = W := by
    rw [qf_gram, hW]
    exact Finset.sum_congr rfl fun l _ => by
      congr 1; rw [hw]; exact Finset.sum_congr rfl fun k _ => by ring
  have h1b := h1 b
  rw [qf_sub, s3] at h1b
  -- `W = y_i - y_j`
  have s4 : W = y i - y j := by
    have e1 : W = ∑ l ∈ range r, w l * ∑ k ∈ range r, T k l * b k := by
      rw [hW]; exact Finset.sum_congr rfl fun l _ => by rw [hw]; ring
    have e2 : ∑ l ∈ range r, w l * ∑ k ∈ range r, T k l * b k =
        ∑ k ∈ range r, b k * z k := by
      simp only [Finset.mul_sum, hz]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [e1, e2, hy, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [hb]; ring
  -- `‖Brᵀ z‖² = (Tᵀ GB T)[w]`
  have s5 : ∑ t ∈ range V, y t ^ 2 = qf r (fun l m => ∑ a ∈ range r, T a l *
      ∑ b ∈ range r, GB a b * T b m) w := by
    rw [qf_conj, hGB, qf_gram]
  have h2w := h2 w
  rw [qf_sub, qf_diag, qf_add_self, ← s5, ← hW] at h2w
  -- two entries of `y` against all of them
  have s6 : (y i - y j) ^ 2 ≤ 2 * ∑ t ∈ range V, y t ^ 2 := by
    by_cases hij : i = j
    · subst hij
      simp only [sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
      exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun t _ => sq_nonneg _)
    · have hsub : ({i, j} : Finset ℕ) ⊆ range V := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact mem_range.mpr hi
        · rw [Finset.mem_singleton.mp ht]; exact mem_range.mpr hj
      have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun t => y t ^ 2) hsub
        (fun _ _ _ => sq_nonneg _)
      rw [Finset.sum_pair hij] at this
      nlinarith [sq_nonneg (y i + y j)]
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun l _ => sq_nonneg _
  have hWe : W ≤ e * e := by
    have hsq : W * W ≤ e * e * W := by
      have : W * W = (y i - y j) ^ 2 := by rw [s4]; ring
      nlinarith
    rcases hW0.lt_or_eq with hpos | hzero
    · exact le_of_mul_le_mul_right (by linarith) hpos
    · rw [← hzero]; positivity
  have hfin : (∑ k ∈ range r, Ar q k * b k) ^ 2 ≤ e * e := by linarith
  nlinarith [sq_nonneg (∑ k ∈ range r, Ar q k * b k - e)]

end GrossSub
