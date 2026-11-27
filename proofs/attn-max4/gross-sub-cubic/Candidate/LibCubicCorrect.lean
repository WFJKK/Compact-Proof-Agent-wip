import Candidate.LibCubicCheck
import Candidate.LibCubicBound
import Candidate.LibCubicCount

/-!
# The inputs a passing test answers

For each test of the checker of entry 7, the inputs it vouches for are answered correctly:

* `correct_onlyMax`: the input `(m, ..., m)`;
* `correct_queryOnly`: the input `(m, ..., m, q)`;
* `correct_withNonmax`: an input with the query `q`, the largest token `m`, and at the positions of
  a pattern `A` tokens whose verdict at `|A|` passes.

The first two go output by output (`correct_of_sums`); the third through the pessimised bound
(`correct_of_upper`): the bound `u` of the query's direct path, the bound `v` of each key's path,
and, for the positions of `A`, the terms of the worst of their tokens (the largest `φ`), whose
verdict covers the pattern.
-/

namespace GrossCubic

open CompactCheck Common AttnClasses Finset

/-! ## The tables -/

/-- The tables of the checker, for the network `N`. -/
abbrev EUm (N : Net) : List (List Q) := mat N.V N.V N.D

abbrev EVm (N : Net) : List (List Q) := mat N.V N.V (evT N)

abbrev PVm (N : Net) : List (List Q) := mat N.n N.V (pvT N)

theorem at2_mat {m k : ℕ} {f : ℕ → ℕ → ℚ} {i j : ℕ} (hi : i < m) (hj : j < k) :
    at2 Interp.counting (mat m k f) i j = ⟨f i j⟩ := by
  simp [at2, mat, List.getD_eq_getElem?_getD, hi, hj]

theorem le_maxLV_map {α : Type} {l : List α} {f : α → Q} {a : α} (ha : a ∈ l) :
    (f a).val ≤ (maxLV (l.map f)).val :=
  le_maxLV (List.mem_map_of_mem ha)

theorem evT_add_pvT (N : Net) (t p j : ℕ) : evT N t j + pvT N p j = N.O t p j :=
  N.path_eq t p j

/-- `Pp[j]` bounds the positional path's advantage of `j` over `m`, at every position. -/
theorem pv_le_ppess {N : Net} {m j p : ℕ} (hm : m < N.V) (hj : j < N.V) (hp : p < N.n) :
    pvT N p j - pvT N p m ≤ ((ppessV N.V N.n m (PVm N)).getD j ⟨0⟩).val := by
  unfold ppessV
  rw [getD_map_range _ hj]
  have h := le_maxLV_map (f := fun p => (⟨(at2 Interp.counting (PVm N) p j).val -
    (at2 Interp.counting (PVm N) p m).val⟩ : Q)) (List.mem_range.mpr hp)
  rw [at2_mat hp hj, at2_mat hp hm] at h
  exact h

/-- `u` bounds the direct path's advantage of every other output over `m`. -/
theorem D_le_dirU {N : Net} {m t j : ℕ} (hm : m < N.V) (ht : t < N.V) (hj : j < N.V)
    (hjm : j ≠ m) : N.D t j - N.D t m ≤ (dirUV N.V m t (EUm N)).val := by
  unfold dirUV
  have h := le_maxLV_map (f := fun j => at2 Interp.counting (EUm N) t j)
    (mem_others.mpr ⟨hj, hjm⟩)
  rw [at2_mat ht hj] at h
  rw [at2_mat ht hm]
  simp only at h ⊢
  linarith

/-- `v[t]` bounds the advantage of every other output over `m` on the path of `t` at any
    position. -/
theorem O_le_keyE {N : Net} {m t p j : ℕ} (hm : m < N.V) (ht : t < N.V) (hp : p < N.n)
    (hj : j < N.V) (hjm : j ≠ m) :
    N.O t p j - N.O t p m ≤ (keyEV N.V m t (EVm N) (ppessV N.V N.n m (PVm N))).val := by
  have h1 := pv_le_ppess (N := N) hm hj hp
  have h2 := le_maxLV_map (f := fun j => (⟨(at2 Interp.counting (EVm N) t j).val +
    ((ppessV N.V N.n m (PVm N)).getD j ⟨0⟩).val⟩ : Q)) (mem_others.mpr ⟨hj, hjm⟩)
  rw [at2_mat ht hj] at h2
  unfold keyEV
  rw [at2_mat ht hm, ← evT_add_pvT, ← evT_add_pvT]
  simp only at h2 ⊢
  linarith

/-! ## Scores -/

theorem exp_S (N : Net) (q t p : ℕ) :
    Real.exp (N.S q t p) = Real.exp (N.SEf q t) * Real.exp (N.SPf q p) := by
  rw [← N.score_eq q t p, Rat.cast_add, Real.exp_add]
  rfl

/-- The bounds on `exp` of the query part of the scores. -/
abbrev BoundsE (N : Net) (XE : List (List (Q × Q))) : Prop :=
  ∀ q < N.V, ∀ t < N.V, expInterval (N.SEf q t) =
    some ((bt2 Interp.counting XE q t).1.val, (bt2 Interp.counting XE q t).2.val)

/-- The bounds on `exp` of the positional part of the scores. -/
abbrev BoundsP (N : Net) (XP : List (List (Q × Q))) : Prop :=
  ∀ q < N.V, ∀ p < N.n, expInterval (N.SPf q p) =
    some ((bt2 Interp.counting XP q p).1.val, (bt2 Interp.counting XP q p).2.val)

theorem boundE {N : Net} {XE : List (List (Q × Q))} (hXE : BoundsE N XE) {q t : ℕ}
    (hq : q < N.V) (ht : t < N.V) :
    ((bt2 Interp.counting XE q t).1.val : ℝ) ≤ Real.exp (N.SEf q t) ∧
      Real.exp (N.SEf q t) ≤ (bt2 Interp.counting XE q t).2.val :=
  expInterval_spec (hXE q hq t ht)

theorem boundP {N : Net} {XP : List (List (Q × Q))} (hXP : BoundsP N XP) {q p : ℕ}
    (hq : q < N.V) (hp : p < N.n) :
    ((bt2 Interp.counting XP q p).1.val : ℝ) ≤ Real.exp (N.SPf q p) ∧
      Real.exp (N.SPf q p) ≤ (bt2 Interp.counting XP q p).2.val :=
  expInterval_spec (hXP q hq p hp)

/-! ## The input `(m, ..., m)` -/

theorem tk_replicate {n m p : ℕ} (hp : p < n) : Net.tk (List.replicate n m) p = m := by
  simp [Net.tk, List.getD_eq_getElem?_getD, hp]

/-- **Only the largest token.** If `onlyMax` passes, `(m, ..., m)` is answered correctly. -/
theorem correct_onlyMax {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) {task : Task} {m : ℕ} (hm : m < N.V)
    (hl : task.label (List.replicate N.n m) = m)
    (hb : onlyMaxV N.V m (EUm N) (EVm N) (ppessV N.V N.n m (PVm N)) = true) :
    Correct g w task (List.replicate N.n m) := by
  have hn0 : 0 < N.n := by have := hg.2.2.1; omega
  have hxV : ∀ t ∈ List.replicate N.n m, t < N.V := fun t ht => (List.eq_of_mem_replicate ht) ▸ hm
  refine correct_of_sums hg hw hV hn (List.length_replicate) hxV (by rw [hl]; exact hm)
    fun j hj hne => ?_
  rw [hl] at hne ⊢
  unfold onlyMaxV at hb
  rw [decide_eq_true_eq, at2_mat hm hm, at2_mat hm hm] at hb
  have h1 := lt_of_le_of_lt (le_maxLV_map (f := fun j => (⟨(at2 Interp.counting (EUm N) m j).val +
    (at2 Interp.counting (EVm N) m j).val + ((ppessV N.V N.n m (PVm N)).getD j ⟨0⟩).val⟩ : Q))
    (mem_others.mpr ⟨hj, hne⟩)) hb
  rw [at2_mat hm hj, at2_mat hm hj] at h1
  simp only at h1
  have hneg : ∀ p ∈ range N.n, Real.exp (N.S (Net.tk (List.replicate N.n m) (N.n - 1))
      (Net.tk (List.replicate N.n m) p) p) *
      (((N.D (Net.tk (List.replicate N.n m) (N.n - 1)) j : ℝ) -
        N.D (Net.tk (List.replicate N.n m) (N.n - 1)) m) +
      ((N.O (Net.tk (List.replicate N.n m) p) p j : ℝ) -
        N.O (Net.tk (List.replicate N.n m) p) p m)) < 0 := by
    intro p hp
    have hp' := mem_range.mp hp
    rw [tk_replicate hp', tk_replicate (by omega : N.n - 1 < N.n)]
    have h2 := pv_le_ppess (N := N) hm hj hp'
    have h3 : (N.D m j - N.D m m) + (N.O m p j - N.O m p m) < 0 := by
      rw [← evT_add_pvT, ← evT_add_pvT]
      linarith
    have h4 : ((N.D m j : ℝ) - N.D m m) + ((N.O m p j : ℝ) - N.O m p m) < 0 := by
      exact_mod_cast h3
    exact mul_neg_of_pos_of_neg (Real.exp_pos _) h4
  calc _ < ∑ p ∈ range N.n, (0 : ℝ) :=
        Finset.sum_lt_sum_of_nonempty ⟨0, mem_range.mpr hn0⟩ hneg
    _ = 0 := by simp

/-! ## The input `(m, ..., m, q)` -/

theorem sum_range_last {M : Type} [AddCommMonoid M] (f : ℕ → M) {n : ℕ} (hn : 0 < n) :
    ∑ p ∈ range n, f p = ∑ p ∈ range (n - 1), f p + f (n - 1) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp [Finset.sum_range_succ]

theorem tk_query {n m q p : ℕ} (hp : p < n - 1) :
    Net.tk (List.replicate (n - 1) m ++ [q]) p = m := by
  have h : p < (List.replicate (n - 1) m).length := by simpa using hp
  rw [Net.tk, List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  simp [hp]

theorem tk_query_last {n m q : ℕ} : Net.tk (List.replicate (n - 1) m ++ [q]) (n - 1) = q := by
  simp [Net.tk, List.getD_eq_getElem?_getD]

/-- A sum of lower (upper) bounds on the terms is a lower (upper) bound on the sum. -/
theorem sumLV_bounds {L : ℕ} {lo hi : ℕ → ℚ} {e : ℕ → ℝ}
    (h : ∀ p < L, (lo p : ℝ) ≤ e p ∧ e p ≤ hi p) :
    ((sumLV ((List.range L).map fun p => (⟨lo p⟩ : Q))).val : ℝ) ≤ ∑ p ∈ range L, e p ∧
      ∑ p ∈ range L, e p ≤ (sumLV ((List.range L).map fun p => (⟨hi p⟩ : Q))).val := by
  rw [sumLV_val, sumLV_val, List.map_map, List.map_map]
  simp only [Function.comp_def]
  rw [sum_range_eq, sum_range_eq]
  push_cast
  exact ⟨Finset.sum_le_sum fun p hp => (h p (mem_range.mp hp)).1,
    Finset.sum_le_sum fun p hp => (h p (mem_range.mp hp)).2⟩

/-- **The query and the largest token.** If `queryOnly` passes, `(m, ..., m, q)` is answered
    correctly. -/
theorem correct_queryOnly {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) (hn2 : 2 ≤ N.n) {task : Task} {m q : ℕ}
    (hm : m < N.V) (hq : q < N.V) {XE XP : List (List (Q × Q))} (hXE : BoundsE N XE)
    (hXP : BoundsP N XP) (hl : task.label (List.replicate (N.n - 1) m ++ [q]) = m)
    (hb : queryOnlyV N.V N.n m q (EUm N) (EVm N) (ppessV N.V N.n m (PVm N)) XE XP = true) :
    Correct g w task (List.replicate (N.n - 1) m ++ [q]) := by
  have hQ : N.n - 1 < N.n := by omega
  have hlen : (List.replicate (N.n - 1) m ++ [q]).length = N.n := by simp; omega
  have hxV : ∀ t ∈ List.replicate (N.n - 1) m ++ [q], t < N.V := by
    intro t ht
    rcases List.mem_append.mp ht with h | h
    · exact (List.eq_of_mem_replicate h) ▸ hm
    · rw [List.mem_singleton.mp h]; exact hq
  refine correct_of_sums hg hw hV hn hlen hxV (by rw [hl]; exact hm) fun j hj hne => ?_
  rw [hl] at hne ⊢
  rw [tk_query_last]
  set Pp := ppessV N.V N.n m (PVm N) with hPp
  unfold queryOnlyV at hb
  simp only [decide_eq_true_eq] at hb
  have h1 := lt_of_le_of_lt (le_maxLV_map (mem_others.mpr ⟨hj, hne⟩)) hb
  simp only [termV] at h1
  rw [at2_mat hq hj, at2_mat hm hj, at2_mat hq hm, at2_mat hm hm, at2_mat hq hj,
    at2_mat hq hm] at h1
  simp only at h1
  set slo := sumLV ((List.range (N.n - 1)).map fun p => (bt2 Interp.counting XP q p).1)
    with hslo
  set shi := sumLV ((List.range (N.n - 1)).map fun p => (bt2 Interp.counting XP q p).2)
    with hshi
  set wm := prodBV (bt2 Interp.counting XE q m) (slo, shi) with hwm
  set wq := prodBV (bt2 Interp.counting XE q q) (bt2 Interp.counting XP q (N.n - 1)) with hwq
  -- the weights of the positions holding `m`, and of the query
  set Wm : ℝ := Real.exp (N.SEf q m) * ∑ p ∈ range (N.n - 1), Real.exp (N.SPf q p) with hWm
  set Wq : ℝ := Real.exp (N.SEf q q) * Real.exp (N.SPf q (N.n - 1)) with hWq
  have hS : (0 : ℝ) < ∑ p ∈ range (N.n - 1), Real.exp (N.SPf q p) :=
    Finset.sum_pos (fun p _ => Real.exp_pos _) ⟨0, mem_range.mpr (by omega)⟩
  have hsb := sumLV_bounds (L := N.n - 1) (lo := fun p => (bt2 Interp.counting XP q p).1.val)
    (hi := fun p => (bt2 Interp.counting XP q p).2.val) (e := fun p => Real.exp (N.SPf q p))
    fun p hp => boundP hXP hq (by omega)
  have hbm := prodBV_bounds (a := bt2 Interp.counting XE q m) (b := (slo, shi))
    (Real.exp_pos _) hS (boundE hXE hq hm).1 (boundE hXE hq hm).2 hsb.1 hsb.2
  have hbq := prodBV_bounds (a := bt2 Interp.counting XE q q)
    (b := bt2 Interp.counting XP q (N.n - 1)) (Real.exp_pos _) (Real.exp_pos _)
    (boundE hXE hq hq).1 (boundE hXE hq hq).2 (boundP hXP hq hQ).1 (boundP hXP hq hQ).2
  -- the two terms of the test bound the two parts of the sum
  have hT1 := kupV_ge (y := ⟨N.D q j + (Pp.getD j ⟨0⟩).val + evT N m j -
    (N.D q m + evT N m m)⟩) hbm.1 hbm.2
  have hT2 := kupV_ge (y := ⟨N.D q j + (Pp.getD j ⟨0⟩).val + evT N q j -
    (N.D q m + evT N q m)⟩) hbq.1 hbq.2
  have hpp := fun p (hp : p < N.n) => pv_le_ppess (N := N) hm hj hp
  have hrest : ∑ p ∈ range (N.n - 1), Real.exp (N.S q
      (Net.tk (List.replicate (N.n - 1) m ++ [q]) p) p) *
      (((N.D q j : ℝ) - N.D q m) + ((N.O (Net.tk (List.replicate (N.n - 1) m ++ [q]) p) p j : ℝ) -
        N.O (Net.tk (List.replicate (N.n - 1) m ++ [q]) p) p m)) ≤
      Wm * ((N.D q j + (Pp.getD j ⟨0⟩).val + evT N m j - (N.D q m + evT N m m) : ℚ) : ℝ) := by
    rw [hWm, mul_assoc, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' := mem_range.mp hp
    rw [tk_query hp', exp_S, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
    have := hpp p (by omega)
    have e : (N.D q j - N.D q m) + (N.O m p j - N.O m p m) ≤
        N.D q j + (Pp.getD j ⟨0⟩).val + evT N m j - (N.D q m + evT N m m) := by
      rw [← evT_add_pvT, ← evT_add_pvT]; linarith
    exact_mod_cast e
  have hlast : Real.exp (N.S q q (N.n - 1)) *
      (((N.D q j : ℝ) - N.D q m) + ((N.O q (N.n - 1) j : ℝ) - N.O q (N.n - 1) m)) ≤
      Wq * ((N.D q j + (Pp.getD j ⟨0⟩).val + evT N q j - (N.D q m + evT N q m) : ℚ) : ℝ) := by
    rw [hWq, exp_S]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := hpp (N.n - 1) hQ
    have e : (N.D q j - N.D q m) + (N.O q (N.n - 1) j - N.O q (N.n - 1) m) ≤
        N.D q j + (Pp.getD j ⟨0⟩).val + evT N q j - (N.D q m + evT N q m) := by
      rw [← evT_add_pvT, ← evT_add_pvT]; linarith
    exact_mod_cast e
  rw [sum_range_last _ (by omega : 0 < N.n), tk_query_last]
  have h1' : ((kupV wm ⟨N.D q j + (Pp.getD j ⟨0⟩).val + evT N m j -
      (N.D q m + evT N m m)⟩).val : ℝ) + (kupV wq ⟨N.D q j + (Pp.getD j ⟨0⟩).val + evT N q j -
      (N.D q m + evT N q m)⟩).val < 0 := by exact_mod_cast h1
  calc _ ≤ _ := add_le_add hrest hlast
    _ ≤ _ := add_le_add hT1 hT2
    _ < 0 := h1'

/-! ## The inputs with non-maximal tokens -/

/-- The bounds `u` of the direct path, per rank of the query up to `lam`. -/
def usOf (mx : Bool) (N : Net) (lam : ℕ) : List Q :=
  (List.range (lam + 1)).map fun r => dirUV N.V (tok mx N.V lam) (tok mx N.V r) (EUm N)

/-- The bounds `E` of the keys' paths, per rank up to `lam`. -/
def ksOf (mx : Bool) (N : Net) (lam : ℕ) : List Q :=
  (List.range (lam + 1)).map fun r =>
    keyEV N.V (tok mx N.V lam) (tok mx N.V r) (EVm N) (ppessV N.V N.n (tok mx N.V lam) (PVm N))

theorem usOf_get {mx : Bool} {N : Net} {lam r : ℕ} (hr : r ≤ lam) :
    (usOf mx N lam).getD r ⟨0⟩ = dirUV N.V (tok mx N.V lam) (tok mx N.V r) (EUm N) :=
  getD_map_range _ (by omega) _

theorem ksOf_get {mx : Bool} {N : Net} {lam r : ℕ} (hr : r ≤ lam) :
    (ksOf mx N lam).getD r ⟨0⟩ = keyEV N.V (tok mx N.V lam) (tok mx N.V r) (EVm N)
      (ppessV N.V N.n (tok mx N.V lam) (PVm N)) :=
  getD_map_range _ (by omega) _

section Values

variable {mx : Bool} {V n lam rq : ℕ} {us ks : List Q} {XE XP : List (List (Q × Q))}

theorem phisV_get {r : ℕ} (hr : r ≤ lam) :
    (phisV mx V lam rq us ks XE).getD r ⟨0⟩ =
      kupV (bt2 Interp.counting XE (tok mx V rq) (tok mx V r))
        ⟨(ks.getD r ⟨0⟩).val + (us.getD rq ⟨0⟩).val⟩ :=
  getD_map_range _ (by omega) _

theorem psisV_get {r p : ℕ} (hr : r ≤ lam) (hp : p < n - 1) :
    ((psisV mx V n lam rq us ks XE XP).getD r []).getD p ⟨0⟩ =
      kupV (bt2 Interp.counting XP (tok mx V rq) p) ((phisV mx V lam rq us ks XE).getD r ⟨0⟩) := by
  rw [psisV, getD_map_range _ (by omega), getD_map_range _ hp]

/-- `ψ`: the bound on the term of the token of rank `r` at position `p`. -/
def psiAt (mx : Bool) (V n lam rq : ℕ) (us ks : List Q) (XE XP : List (List (Q × Q))) (r p : ℕ) :
    ℚ :=
  (((psisV mx V n lam rq us ks XE XP).getD r []).getD p ⟨0⟩).val

theorem qbV_val :
    (qbV mx V n lam rq us ks XE XP).val =
      ∑ p ∈ range (n - 1), psiAt mx V n lam rq us ks XE XP lam p +
        (psiqV mx V n lam rq us ks XE XP).val := by
  rw [qbV]
  simp only
  rw [sumLV_val]
  congr 1
  rw [psisV, getD_map_range _ (Nat.lt_succ_self lam), List.map_map, sum_range_eq]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [psiAt, psisV_get le_rfl (mem_range.mp hp)]
  rfl

theorem sum_filter_ite {γ : Type} (f : γ → ℚ) (b : γ → Bool) :
    ∀ l : List γ, ((l.filter b).map f).sum = (l.map fun p => if b p then f p else 0).sum
  | [] => by simp
  | a :: l => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← sum_filter_ite f b l]
    cases b a <;> simp

/-- A sum over the positions of a pattern. -/
theorem sum_inPat (f : ℕ → ℚ) (L pat : ℕ) :
    ((inPat L pat).map f).sum = ∑ p ∈ range L, if pat.testBit p then f p else 0 := by
  rw [inPat, sum_filter_ite, sum_range_eq]

/-- A pattern's sum is at most the largest sum over the patterns of as many positions. -/
theorem sum_pat_le_max (f : ℕ → ℚ) {L c pat : ℕ} (hpat : pat < 2 ^ L)
    (hc : (inPat L pat).length = c) :
    ∑ p ∈ range L, (if pat.testBit p then f p else 0) ≤
      (maxLV ((patsOf L c).map fun pat => sumLV ((inPat L pat).map fun p =>
        ((List.range L).map fun p => (⟨f p⟩ : Q)).getD p ⟨0⟩))).val := by
  have hmem : pat ∈ patsOf L c := by
    simp only [patsOf, List.mem_filter, List.mem_range, beq_iff_eq]
    exact ⟨hpat, hc⟩
  refine le_trans (le_of_eq ?_) (le_maxLV_map hmem)
  rw [sumLV_val, List.map_map, ← sum_inPat]
  congr 1
  refine List.map_congr_left fun p hp => ?_
  have hp' : p < L := List.mem_range.mp (List.mem_filter.mp hp).1
  simp only [Function.comp_apply]
  rw [getD_map_range _ hp']

theorem verdV_get {κ c' : ℕ} (hκ : κ < lam) (hc' : c' < ncsOf n lam rq) :
    ((verdV mx V n lam rq us ks XE XP).getD κ []).getD c' false =
      decide ((qbV mx V n lam rq us ks XE XP).val +
        (maxLV ((patsOf (n - 1) (c' + 1)).map fun pat => sumLV ((inPat (n - 1) pat).map fun p =>
          ((List.range (n - 1)).map fun p => (⟨psiAt mx V n lam rq us ks XE XP κ p -
            psiAt mx V n lam rq us ks XE XP lam p⟩ : Q)).getD p ⟨0⟩))).val < 0) := by
  rw [verdV, getD_map_range _ hκ, kverdV, getD_map_range _ hc']
  rfl

/-- **A verdict that passes.** If the verdict of rank `κ` at `c` positions passes, then for every
    pattern `A` of `c` positions, `qb + Σ_{p ∈ A} (ψ(κ, p) - ψ(lam, p)) < 0`. -/
theorem verd_sum {κ c pat : ℕ} (hκ : κ < lam) (hc1 : 1 ≤ c) (hcn : c ≤ ncsOf n lam rq)
    (hpat : pat < 2 ^ (n - 1)) (hc : (inPat (n - 1) pat).length = c)
    (hv : ((verdV mx V n lam rq us ks XE XP).getD κ []).getD (c - 1) false = true) :
    (qbV mx V n lam rq us ks XE XP).val + ∑ p ∈ range (n - 1),
      (if pat.testBit p then psiAt mx V n lam rq us ks XE XP κ p -
        psiAt mx V n lam rq us ks XE XP lam p else 0) < 0 := by
  rw [verdV_get (c' := c - 1) hκ (by omega), Nat.sub_add_cancel hc1, decide_eq_true_eq] at hv
  have := sum_pat_le_max (fun p => psiAt mx V n lam rq us ks XE XP κ p -
    psiAt mx V n lam rq us ks XE XP lam p) hpat hc
  linarith

end Values

/-- **Some non-maximal tokens.** An input with the query of rank `rq`, the largest token of rank
    `lam` at the positions outside the pattern `A` (of `c` positions, `1 ≤ c ≤ ncs`), and at the
    positions of `A` tokens whose verdict at `c` passes, is answered correctly. -/
theorem correct_withNonmax {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) (hn2 : 2 ≤ N.n) (mx : Bool) {task : Task}
    {XE XP : List (List (Q × Q))} (hXE : BoundsE N XE) (hXP : BoundsP N XP)
    {lam rq pat c : ℕ} (hlam : lam < N.V) (hrq : rq ≤ lam) (hpat : pat < 2 ^ (N.n - 1))
    (hc : (inPat (N.n - 1) pat).length = c) (hc1 : 1 ≤ c) (hcn : c ≤ ncsOf N.n lam rq)
    {x : Input} (hx : x.length = N.n) (hxV : ∀ t ∈ x, t < N.V)
    (hl : task.label x = tok mx N.V lam) (hq : Net.tk x (N.n - 1) = tok mx N.V rq)
    (hK : ∀ p < N.n - 1, pat.testBit p = true → tok mx N.V (Net.tk x p) < lam ∧
      ((verdV mx N.V N.n lam rq (usOf mx N lam) (ksOf mx N lam) XE XP).getD
        (tok mx N.V (Net.tk x p)) []).getD (c - 1) false = true)
    (hM : ∀ p < N.n - 1, pat.testBit p = false → Net.tk x p = tok mx N.V lam) :
    Correct g w task x := by
  have hQ : N.n - 1 < N.n := by omega
  have hrqV : rq < N.V := by omega
  have hm : tok mx N.V lam < N.V := tok_lt hlam
  have hqV : tok mx N.V rq < N.V := tok_lt hrqV
  have hxp : ∀ p < N.n, Net.tk x p < N.V := fun p hp => hxV _ (tk_mem (by omega))
  -- the rank of every position is at most `lam`
  have hrank : ∀ p < N.n, tok mx N.V (Net.tk x p) ≤ lam := by
    intro p hp
    by_cases hpq : p < N.n - 1
    · cases hb : pat.testBit p
      · rw [hM p hpq hb, tok_tok hlam]
      · exact (hK p hpq hb).1.le
    · have : p = N.n - 1 := by omega
      subst this
      rw [hq, tok_tok hrqV]
      exact hrq
  set us := usOf mx N lam with hus
  set ks := ksOf mx N lam with hks
  set ψ := psiAt mx N.V N.n lam rq us ks XE XP with hψ
  set φ := fun r => ((phisV mx N.V lam rq us ks XE).getD r ⟨0⟩).val with hφ
  -- the worst token of the pattern: the largest `φ`
  have hKne : ((range (N.n - 1)).filter fun p => pat.testBit p = true).Nonempty := by
    obtain ⟨p, hp⟩ := List.exists_mem_of_length_pos (by omega : 0 < (inPat (N.n - 1) pat).length)
    obtain ⟨hp1, hp2⟩ := List.mem_filter.mp hp
    exact ⟨p, Finset.mem_filter.mpr ⟨mem_range.mpr (List.mem_range.mp hp1), hp2⟩⟩
  obtain ⟨p0, hp0, hmax⟩ := Finset.exists_max_image _
    (fun p => φ (tok mx N.V (Net.tk x p))) hKne
  obtain ⟨hp0n, hp0b⟩ := Finset.mem_filter.mp hp0
  have hp0n' := mem_range.mp hp0n
  set wr := tok mx N.V (Net.tk x p0) with hwr
  obtain ⟨hwlt, hwv⟩ := hK p0 hp0n' hp0b
  -- the bounds, position by position
  set Fq : ℕ → ℚ := fun p => if p < N.n - 1 then (if pat.testBit p then ψ wr p else ψ lam p)
    else (psiqV mx N.V N.n lam rq us ks XE XP).val with hFq
  -- `exp` of a token's score times `u + E` is at most `ψ` of any rank with a larger `φ`
  have hterm : ∀ p < N.n, ∀ ρ ≤ lam, φ (tok mx N.V (Net.tk x p)) ≤ φ ρ →
      Real.exp (N.S (tok mx N.V rq) (Net.tk x p) p) *
        (((us.getD rq ⟨0⟩).val : ℝ) + (ks.getD (tok mx N.V (Net.tk x p)) ⟨0⟩).val) ≤
        ((kupV (bt2 Interp.counting XP (tok mx N.V rq) p)
          ((phisV mx N.V lam rq us ks XE).getD ρ ⟨0⟩)).val : ℝ) := by
    intro p hp ρ hρ hle
    have ht := hxp p hp
    have hr := hrank p hp
    have h1 := kupV_ge (y := ⟨(ks.getD (tok mx N.V (Net.tk x p)) ⟨0⟩).val + (us.getD rq ⟨0⟩).val⟩)
      (b := bt2 Interp.counting XE (tok mx N.V rq) (Net.tk x p))
      (e := Real.exp (N.SEf (tok mx N.V rq) (Net.tk x p)))
      (boundE hXE hqV ht).1 (boundE hXE hqV ht).2
    have h2 : ((kupV (bt2 Interp.counting XE (tok mx N.V rq) (Net.tk x p))
        ⟨(ks.getD (tok mx N.V (Net.tk x p)) ⟨0⟩).val + (us.getD rq ⟨0⟩).val⟩).val : ℝ) ≤
        φ ρ := by
      have := hle
      simp only [hφ] at this
      rw [phisV_get hr, tok_tok ht] at this
      exact_mod_cast this
    have h3 := kupV_ge (y := (phisV mx N.V lam rq us ks XE).getD ρ ⟨0⟩)
      (b := bt2 Interp.counting XP (tok mx N.V rq) p) (boundP hXP hqV hp).1 (boundP hXP hqV hp).2
    rw [exp_S, show ∀ a b c : ℝ, a * b * c = b * (a * c) from fun a b c => by ring]
    calc _ ≤ Real.exp (N.SPf (tok mx N.V rq) p) * (φ ρ : ℝ) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          refine le_trans ?_ h2
          simp only at h1
          push_cast at h1 ⊢
          linarith
      _ ≤ _ := h3
  refine correct_of_upper hg hw hV hn hx hxV (by rw [hl]; exact hm)
    (u := ((us.getD rq ⟨0⟩).val : ℝ))
    (E := fun p => ((ks.getD (tok mx N.V (Net.tk x p)) ⟨0⟩).val : ℝ))
    (F := fun p => (Fq p : ℝ)) ?_ ?_ ?_ ?_
  · -- the direct path
    intro j hj hne
    rw [hl] at hne ⊢
    rw [hq, hus, usOf_get hrq]
    exact_mod_cast D_le_dirU hm hqV hj hne
  · -- the paths through the head
    intro p hp j hj hne
    rw [hl] at hne ⊢
    rw [hks, ksOf_get (hrank p hp), tok_tok (hxp p hp)]
    exact_mod_cast O_le_keyE hm (hxp p hp) hp hj hne
  · -- the weights
    intro p hp
    rw [hq]
    by_cases hpq : p < N.n - 1
    · have hF : (Fq p : ℝ) = (ψ (if pat.testBit p then wr else lam) p : ℝ) := by
        simp only [hFq, hpq, ↓reduceIte]
        split <;> rfl
      rw [hF]
      have hρ : (if pat.testBit p then wr else lam) ≤ lam := by split <;> omega
      have e : (ψ (if pat.testBit p then wr else lam) p : ℝ) =
          ((kupV (bt2 Interp.counting XP (tok mx N.V rq) p)
            ((phisV mx N.V lam rq us ks XE).getD (if pat.testBit p then wr else lam) ⟨0⟩)).val :
              ℝ) := by
        rw [hψ, psiAt, psisV_get hρ hpq]
      rw [e]
      refine hterm p hp _ hρ ?_
      cases hb : pat.testBit p
      · simp only [Bool.false_eq_true, ↓reduceIte]
        rw [hM p hpq hb, tok_tok hlam]
      · simp only [↓reduceIte]
        exact hmax p (Finset.mem_filter.mpr ⟨mem_range.mpr hpq, hb⟩)
    · have hp' : p = N.n - 1 := by omega
      subst hp'
      have hF : (Fq (N.n - 1) : ℝ) = ((psiqV mx N.V N.n lam rq us ks XE XP).val : ℝ) := by
        simp [hFq]
      rw [hF, psiqV]
      exact hterm _ hQ rq hrq (by rw [hq, tok_tok hrqV])
  · -- the sum
    have hv := verd_sum hwlt hc1 hcn hpat hc hwv
    rw [qbV_val] at hv
    have hsum : ∑ p ∈ range N.n, Fq p = ∑ p ∈ range (N.n - 1), ψ lam p +
        (psiqV mx N.V N.n lam rq us ks XE XP).val + ∑ p ∈ range (N.n - 1),
          (if pat.testBit p then ψ wr p - ψ lam p else 0) := by
      rw [sum_range_last _ (by omega : 0 < N.n)]
      have e1 : ∑ p ∈ range (N.n - 1), Fq p = ∑ p ∈ range (N.n - 1),
          (ψ lam p + if pat.testBit p then ψ wr p - ψ lam p else 0) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have hp' := mem_range.mp hp
        simp only [hFq, hp', ↓reduceIte]
        split <;> ring
      rw [e1, Finset.sum_add_distrib]
      simp only [hFq, lt_irrefl, ↓reduceIte]
      ring
    have hq' : ∑ p ∈ range N.n, Fq p < 0 := by rw [hsum]; linarith
    exact_mod_cast hq'

end GrossCubic
