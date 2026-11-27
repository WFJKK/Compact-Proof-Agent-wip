import Candidate.LibSubSteps

/-!
# The inputs a passing class test answers

`correct_class`: an input of a class whose verdict passed (`ClassOK`) is answered correctly. The
argument, for one output `j` other than the largest token `m`, with the softmax's denominator
cleared:

* the score splits as `EQKE[q, t] + PE[q, p]` (`score_split`), with `EQKE` the table step 1
  bounds and `PE` the positional table the checker sorts;
* the weights of `m`'s positions add up to `X = Z (s + c1)`, and the others' to a `Y` between
  `Z e^{-a_hi} (T - s + c2)` and `Z e^{-a_lo} (T - s + c2)`: the gaps of step 1 (`gap_lo`,
  `gap_hi`), `s` the sum of `e^{PE}` over `m`'s positions and `T` over all;
* the logit difference, weighted, is at most `X (F + R_j) + Y (F + W)` (`logit_le`);
* the endpoint the test took bounds it (`endpoint_le`, `combine_lo`, `combine_hi`), the sorted
  sums bounding `s` (`take_le_part`, `subperm_le_drop`).
-/

namespace GrossSub

open CompactCheck Common AttnClasses GrossCubic Finset

/-! ## The network's tables, as the checker builds them -/

section Tables

variable (N : Net)

/-- `Eq = E + P_Q`. -/
def eqF (q a : ℕ) : ℚ := N.r q (N.n - 1) a

/-- `Ek = E + p̄`. -/
def ekF (pbar : ℕ → ℚ) (t a : ℕ) : ℚ := N.E.get (t * N.d + a) + pbar a

/-- The columns of `c W_Q`. -/
def qcF (k a : ℕ) : ℚ := 0 + N.WQ.get (a * N.h + k) * N.C.get 0

/-- The columns of `W_K`. -/
def kcF (k b : ℕ) : ℚ := N.WK.get (b * N.h + k)

/-- `P - p̄`. -/
def perrF (pbar : ℕ → ℚ) (p b : ℕ) : ℚ := N.P.get (p * N.d + b) - pbar b

/-- The query-key part of the score, `EQKE[q, t]`. -/
def eqkeF (pbar : ℕ → ℚ) (q t : ℕ) : ℚ := eqke N.d N.h (eqF N) (ekF N pbar) (qcF N) (kcF N) q t

/-- The positional part `PE[q, p]`, as the checker multiplies it out. -/
def peF (pbar : ℕ → ℚ) (q p : ℕ) : ℚ :=
  ∑ a ∈ range N.d, eqF N q a * ∑ k ∈ range N.h, qcF N k a *
    ∑ b ∈ range N.d, kcF N k b * perrF N pbar p b

/-- Both parts, as one triple sum. -/
theorem triple (d h : ℕ) (X : ℕ → ℚ) (A B : ℕ → ℕ → ℚ) (Y : ℕ → ℚ) :
    ∑ a ∈ range d, X a * ∑ k ∈ range h, A k a * ∑ b ∈ range d, B k b * Y b =
      ∑ k ∈ range h, (∑ a ∈ range d, X a * A k a) * ∑ b ∈ range d, B k b * Y b := by
  rw [show (∑ a ∈ range d, X a * ∑ k ∈ range h, A k a * ∑ b ∈ range d, B k b * Y b) =
    ∑ a ∈ range d, ∑ k ∈ range h, X a * (A k a * ∑ b ∈ range d, B k b * Y b) from
      Finset.sum_congr rfl fun a _ => Finset.mul_sum _ _ _, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun a _ => by ring

/-- **The score splits**, for every `p̄`: `S[q, t, p] = EQKE[q, t] + PE[q, p]`. -/
theorem score_split (pbar : ℕ → ℚ) (q t p : ℕ) :
    N.S q t p = eqkeF N pbar q t + peF N pbar q p := by
  rw [← N.score_eq]
  have e1 : eqkeF N pbar q t = ∑ a ∈ range N.d, eqF N q a * ∑ k ∈ range N.h, qcF N k a *
      ∑ b ∈ range N.d, kcF N k b * ekF N pbar t b := by
    unfold eqkeF eqke bil mqk
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e1, peF, triple, triple, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hq : N.qc q k = ∑ a ∈ range N.d, eqF N q a * qcF N k a := rfl
  have hk : N.ek t k + N.pk p k = ∑ b ∈ range N.d, kcF N k b * ekF N pbar t b +
      ∑ b ∈ range N.d, kcF N k b * perrF N pbar p b := by
    unfold Net.ek Net.pk
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    unfold kcF ekF perrF
    ring
  rw [hq, ← mul_add, ← mul_add, hk]

end Tables

/-! ## Sums over the positions holding the largest token -/

theorem sum_filter_range_gen {M : Type} [AddCommMonoid M] (b : ℕ → Bool) (f : ℕ → M) :
    ∀ L : ℕ, (((List.range L).filter b).map f).sum = ∑ p ∈ range L, if b p then f p else 0
  | 0 => by simp
  | L + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      sum_filter_range_gen b f L, Finset.sum_range_succ]
    by_cases h : b L <;> simp [h]

theorem esum_filter (b : ℕ → Bool) (o : ℕ → ℚ) (L : ℕ) :
    esum (((List.range L).filter b).map o) =
      ∑ p ∈ range L, if b p then Real.exp (o p : ℝ) else 0 := by
  unfold esum
  rw [List.map_map]
  exact sum_filter_range_gen b _ L

theorem esum_append (l l' : List ℚ) : esum (l ++ l') = esum l + esum l' := by
  simp [esum, List.sum_append]

theorem esum_perm {l l' : List ℚ} (h : l.Perm l') : esum l = esum l' :=
  (h.map _).sum_eq

theorem filter_perm (b : ℕ → Bool) (o : ℕ → ℚ) (L : ℕ) :
    (((List.range L).filter b).map o ++ ((List.range L).filter fun p => !b p).map o).Perm
      ((List.range L).map o) := by
  rw [← List.map_append]
  exact (List.filter_append_perm b (List.range L)).map o

/-! ## The plan's gaps -/

theorem one_le_gapOf (gap : ℕ → ℕ → ℕ → ℕ) (rq lam c : ℕ) : 1 ≤ gapOf gap rq lam c := by
  unfold gapOf
  exact Nat.le_max_left _ _

theorem foldl_nat_min_le_init : ∀ (l : List ℕ) (a : ℕ), l.foldl Nat.min a ≤ a
  | [], _ => le_rfl
  | b :: l, a => le_trans (foldl_nat_min_le_init l _) (Nat.min_le_left a b)

theorem foldl_nat_min_le : ∀ (l : List ℕ) (a : ℕ) {x : ℕ}, x ∈ l → l.foldl Nat.min a ≤ x
  | b :: l, a, x, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (foldl_nat_min_le_init l _) (Nat.min_le_right _ _)
    · exact foldl_nat_min_le l _ h

/-- `W`'s gap is at most the gap of each query's class. -/
theorem gapW_le (gap : ℕ → ℕ → ℕ → ℕ) {rq lam c : ℕ} (h : rq ≤ lam) :
    gapW gap lam c ≤ gapOf gap rq lam c := by
  unfold gapW
  exact foldl_nat_min_le _ _ (List.mem_map.mpr ⟨rq, List.mem_range.mpr (by omega), rfl⟩)

theorem valid_spec {gap : ℕ → ℕ → ℕ → ℕ} {rq lam c : ℕ} (h : valid gap rq lam c = true) :
    gapOf gap rq lam c ≤ lam ∧ (rq = lam ∨ gapOf gap rq lam c + rq ≤ lam) := by
  unfold valid at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.ble_eq, beq_iff_eq] at h
  exact h

/-! ## The running extrema the checker takes -/

/-- The query's row of `Ê`, by rank. -/
def rrV (mx : Bool) (V : ℕ) (fEh : ℕ → ℕ → ℚ) (q : ℕ) : List Q :=
  (List.range V).map fun ρ => at2 Interp.counting (mat V V fEh) q (tok mx V ρ)

/-- The running maxima and minima of the rows of `Ê`, by rank. -/
def rmV (mx : Bool) (V : ℕ) (fEh : ℕ → ℕ → ℚ) : List (List Q × List Q) :=
  (List.range V).map fun q => (scanVal max (rrV mx V fEh q), scanVal min (rrV mx V fEh q))

/-- The running maxima of the spreads of the rows of `EVOU`, by rank. -/
def WpreV (mx : Bool) (N : Net) : List Q :=
  scanVal max ((List.range N.V).map fun ρ => (⟨spreadV N.V (evT N (tok mx N.V ρ))⟩ : Q))

theorem rrV_get {mx : Bool} {V : ℕ} {fEh : ℕ → ℕ → ℚ} {q ρ : ℕ} (hq : q < V) (hρ : ρ < V) :
    (rrV mx V fEh q).getD ρ ⟨0⟩ = ⟨fEh q (tok mx V ρ)⟩ := by
  rw [rrV, getD_map_range _ hρ, at2_mat' hq (tok_lt hρ)]

theorem rmax_ge {mx : Bool} {V : ℕ} {fEh : ℕ → ℕ → ℚ} {q j t : ℕ} (hq : q < V) (hj : j < V)
    (ht : t < V) (htj : tok mx V t ≤ j) :
    fEh q t ≤ (at1 Interp.counting ((rmV mx V fEh).getD q ([], [])).1 j).val := by
  rw [rmV, getD_map_range _ hq]
  have := le_scanVal_max (rrV mx V fEh q) (i := j)
    (by rw [rrV, List.length_map, List.length_range]; exact hj) htj
  rw [rrV_get hq (lt_of_le_of_lt htj hj), tok_tok ht] at this
  exact this

theorem rmin_le {mx : Bool} {V : ℕ} {fEh : ℕ → ℕ → ℚ} {q j t : ℕ} (hq : q < V) (hj : j < V)
    (ht : t < V) (htj : tok mx V t ≤ j) :
    (at1 Interp.counting ((rmV mx V fEh).getD q ([], [])).2 j).val ≤ fEh q t := by
  rw [rmV, getD_map_range _ hq]
  have := scanVal_min_le (rrV mx V fEh q) (i := j)
    (by rw [rrV, List.length_map, List.length_range]; exact hj) htj
  rw [rrV_get hq (lt_of_le_of_lt htj hj), tok_tok ht] at this
  exact this

/-- `W` bounds the spread of the row of `EVOU` of every token of rank up to its index. -/
theorem W_ge {mx : Bool} {N : Net} {j t : ℕ} (hj : j < N.V) (ht : t < N.V)
    (htj : tok mx N.V t ≤ j) {i i' : ℕ} (hi : i < N.V) (hi' : i' < N.V) :
    evT N t i - evT N t i' ≤ (at1 Interp.counting (WpreV mx N) j).val := by
  have h1 := spreadV_ge N.V (evT N t) hi hi'
  have h2 := le_scanVal_max ((List.range N.V).map fun ρ =>
    (⟨spreadV N.V (evT N (tok mx N.V ρ))⟩ : Q)) (i := j)
    (by rw [List.length_map, List.length_range]; exact hj) htj
  rw [getD_map_range _ (lt_of_le_of_lt htj hj), tok_tok ht] at h2
  exact le_trans h1 h2

/-! ## A passing endpoint -/

theorem at1_le_RmaxV {V m : ℕ} {Rs : List Q} {j : ℕ} (hj : j < V) (hjm : j ≠ m) :
    (at1 Interp.counting Rs j).val ≤ (RmaxV V m Rs).val :=
  le_maxLV_map (f := at1 Interp.counting Rs) (mem_others.mpr ⟨hj, hjm⟩)

theorem RminV_le_at1 {V m : ℕ} {Rs : List Q} {j : ℕ} (hj : j < V) (hjm : j ≠ m) :
    (RminV V m Rs).val ≤ (at1 Interp.counting Rs j).val :=
  minLV_le (List.mem_map_of_mem (mem_others.mpr ⟨hj, hjm⟩))

/-- **A passing endpoint**, for one output `j`: with weights `a`, `b` within the endpoint's bounds,
    `a (L_j + s + R_j) + b (L_j + s + W) < 0`. -/
theorem endpoint_neg {A B : Q × Q} {V m : ℕ} {Ls Rs : List Q} {W avg one sq : Q}
    (hone : one.val = 1)
    (h : endpointV A B (endConstsV V m Ls Rs (RmaxV V m Rs) (RminV V m Rs) W avg one) sq = true)
    {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha1 : (A.1.val : ℝ) ≤ a) (ha2 : a ≤ A.2.val)
    (hb1 : (B.1.val : ℝ) ≤ b) (hb2 : b ≤ B.2.val) {j : ℕ} (hj : j < V) (hjm : j ≠ m) :
    a * ((at1 Interp.counting Ls j).val + sq.val + (at1 Interp.counting Rs j).val) +
      b * ((at1 Interp.counting Ls j).val + sq.val + W.val) < 0 := by
  have htop := le_topV (Ls := Ls) (Rs := Rs) (avg := avg) hj hjm
  have hRx := at1_le_RmaxV (Rs := Rs) hj hjm
  have hRn := RminV_le_at1 (Rs := Rs) hj hjm
  have key := endpoint_le (A := a) (B := b) (L := ((at1 Interp.counting Ls j).val : ℝ))
    (R := ((at1 Interp.counting Rs j).val : ℝ)) (W := (W.val : ℝ)) (s := (sq.val : ℝ))
    (avg := (avg.val : ℝ)) (top := ((topV V m Ls Rs avg).val : ℝ))
    (Rmax := ((RmaxV V m Rs).val : ℝ)) (Rmin := ((RminV V m Rs).val : ℝ)) ha0 hb0
    (by exact_mod_cast htop) (by exact_mod_cast hRx) (by exact_mod_cast hRn)
  have t1 := endpointV_spec h ha1 ha2 hb1 hb2 List.mem_cons_self
  have t2 := endpointV_spec h ha1 ha2 hb1 hb2 (List.mem_cons_of_mem _ List.mem_cons_self)
  simp only [hone] at t1 t2
  push_cast at t1 t2
  refine lt_of_le_of_lt key (max_lt ?_ ?_)
  · linarith
  · linarith

/-! ## The weights of the largest token's positions and the others' -/

/-- With `e_p = Z e^{o_p}` at the positions holding the largest token (`o_L = 0` at the last,
    the query's), and `Z e^{o_p} e^{-hi} ≤ e_p ≤ Z e^{o_p} e^{-lo}` at the others: the weights of
    the two sides, split at the query. -/
theorem weights_bounds (L : ℕ) (lab : ℕ → Prop) [DecidablePred lab] (e : ℕ → ℝ) (Z lo hi : ℝ)
    (o : ℕ → ℝ) (ho : o L = 0) (hZ : 0 < Z)
    (hm : ∀ p ≤ L, lab p → e p = Z * Real.exp (o p))
    (hlo : ∀ p ≤ L, ¬ lab p → e p ≤ Z * Real.exp (o p) * Real.exp (-lo))
    (hhi : ∀ p ≤ L, ¬ lab p → Z * Real.exp (o p) * Real.exp (-hi) ≤ e p) :
    (∑ p ∈ range (L + 1), if lab p then e p else 0) =
        Z * ((∑ p ∈ range L, if lab p then Real.exp (o p) else 0) + if lab L then 1 else 0) ∧
      (∑ p ∈ range (L + 1), if lab p then 0 else e p) ≤ Z * Real.exp (-lo) *
        ((∑ p ∈ range L, if lab p then 0 else Real.exp (o p)) + if lab L then 0 else 1) ∧
      Z * Real.exp (-hi) * ((∑ p ∈ range L, if lab p then 0 else Real.exp (o p)) +
        if lab L then 0 else 1) ≤ ∑ p ∈ range (L + 1), if lab p then 0 else e p := by
  have hZe : ∀ p, 0 ≤ Z * Real.exp (o p) := fun p => (mul_pos hZ (Real.exp_pos _)).le
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      by_cases h : lab p
      · simp only [h, ↓reduceIte]
        exact hm p (by have := mem_range.mp hp; omega) h
      · simp [h]
    · by_cases h : lab L
      · simp only [h, ↓reduceIte, mul_one]
        rw [hm L le_rfl h, ho, Real.exp_zero, mul_one]
      · simp [h]
  · rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun p hp => ?_) ?_
    · by_cases h : lab p
      · simp [h]
      · simp only [h, ↓reduceIte]
        have := hlo p (by have := mem_range.mp hp; omega) h
        linarith [mul_comm (Z * Real.exp (o p)) (Real.exp (-lo)),
          mul_assoc Z (Real.exp (-lo)) (Real.exp (o p)),
          mul_assoc Z (Real.exp (o p)) (Real.exp (-lo)),
          mul_comm (Real.exp (o p)) (Real.exp (-lo))]
    · by_cases h : lab L
      · simp [h]
      · simp only [h, ↓reduceIte, mul_one]
        have := hlo L le_rfl h
        rw [ho, Real.exp_zero, mul_one] at this
        exact this
  · rw [Finset.sum_range_succ, mul_add, Finset.mul_sum]
    refine add_le_add (Finset.sum_le_sum fun p hp => ?_) ?_
    · by_cases h : lab p
      · simp [h]
      · simp only [h, ↓reduceIte]
        have := hhi p (by have := mem_range.mp hp; omega) h
        linarith [mul_comm (Z * Real.exp (o p)) (Real.exp (-hi)),
          mul_assoc Z (Real.exp (-hi)) (Real.exp (o p)),
          mul_assoc Z (Real.exp (o p)) (Real.exp (-hi)),
          mul_comm (Real.exp (o p)) (Real.exp (-hi))]
    · by_cases h : lab L
      · simp [h]
      · simp only [h, ↓reduceIte, mul_one]
        have := hhi L le_rfl h
        rw [ho, Real.exp_zero, mul_one] at this
        exact this

/-! ## The inputs of a class -/

theorem at1_LsV {V m : ℕ} {fmu : ℕ → ℚ} {Pp : List Q} {j : ℕ} (hj : j < V) (hm : m < V) :
    (at1 Interp.counting (LsV V m (vec V fmu) Pp) j).val =
      (fmu j - fmu m) + (at1 Interp.counting Pp j).val := by
  change ((LsV V m (vec V fmu) Pp).getD j ⟨0⟩).val = _
  unfold LsV
  rw [getD_map_range _ hj, at1_vec hj, at1_vec hm]

theorem at1_RsV {V m : ℕ} {f : ℕ → ℕ → ℚ} {j : ℕ} (hj : j < V) (hm : m < V) :
    (at1 Interp.counting (RsV V m (mat V V f)) j).val = f m j - f m m := by
  change ((RsV V m (mat V V f)).getD j ⟨0⟩).val = _
  unfold RsV
  rw [getD_map_range _ hj, at2_mat' hm hj, at2_mat' hm hm]

theorem c1Of_val {rq lam : ℕ} {one : Q} (hone : one.val = 1) :
    (c1Of rq lam one).val = if rq = lam then 1 else 0 := by
  unfold c1Of; split <;> simp [hone]

theorem c2Of_val {rq lam : ℕ} {one : Q} (hone : one.val = 1) :
    (c2Of rq lam one).val = if rq = lam then 0 else 1 := by
  unfold c2Of; split <;> simp [hone]

/-- **A class.** Every input of a class whose verdict passed is answered correctly: the query of
    rank `rq`, the largest token `m` of rank `λ`, and at the other positions `m` or a token of
    rank at most `λ - g`, `c0 + 1` positions in all (the query among them unless it is `m`). -/
theorem correct_class {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) (hn2 : 2 ≤ N.n) (mx : Bool)
    (gap : ℕ → ℕ → ℕ → ℕ) (pbar : ℕ → ℚ) (fEh : ℕ → ℕ → ℚ) (feps fmu fsp : ℕ → ℚ) (ok : Bool)
    (hErr : ok = true → ErrSpec N.V (eqkeF N pbar) fEh feps)
    (hEu : EupuSpec N.V N.D fmu fsp)
    (srt : List (List (Q × Q) × List (Q × Q)))
    (hsrt : ∀ q < N.V, SortedSpec ((List.range (N.n - 1)).map fun p =>
      peF N pbar q p - peF N pbar q (N.n - 1)) (srt.getD q ([], [])).1 (srt.getD q ([], [])).2)
    (avgs : List Q) (one : Q) (hone : one.val = 1)
    {lam c0 rq : ℕ} (hlam : lam < N.V) (hrq : rq ≤ lam)
    (hok : ClassOK mx N.V N.n gap (mat N.V N.V fEh) (vec N.V feps) ok srt (vec N.V fsp)
      (rmV mx N.V fEh) (WpreV mx N) avgs one lam (tok mx N.V lam)
      (LsV N.V (tok mx N.V lam) (vec N.V fmu) (ppessV N.V N.n (tok mx N.V lam) (PVm N)))
      (RsV N.V (tok mx N.V lam) (EVm N))
      (RmaxV N.V (tok mx N.V lam) (RsV N.V (tok mx N.V lam) (EVm N)))
      (RminV N.V (tok mx N.V lam) (RsV N.V (tok mx N.V lam) (EVm N))) c0 rq)
    {x : Input} (hx : x.length = N.n) (hxV : ∀ t ∈ x, t < N.V)
    (hl : (taskOf mx N.n N.V).label x = tok mx N.V lam)
    (hq : Net.tk x (N.n - 1) = tok mx N.V rq)
    (hK : ∀ p < N.n - 1, Net.tk x p ≠ tok mx N.V lam →
      tok mx N.V (Net.tk x p) + gapOf gap rq lam (c0 + 1) ≤ lam)
    (hc : ((List.range (N.n - 1)).filter fun p => !(Net.tk x p == tok mx N.V lam)).length +
      (if rq = lam then 0 else 1) = c0 + 1) :
    Correct g w (taskOf mx N.n N.V) x := by
  obtain ⟨hgW, hvalid, hokt, elo, ehi, helo, hehi, hct⟩ := hok
  have hE := hErr hokt
  obtain ⟨L, hL⟩ : ∃ L, N.n = L + 1 := ⟨N.n - 1, by omega⟩
  have hL1 : N.n - 1 = L := by omega
  have hm : tok mx N.V lam < N.V := tok_lt hlam
  have hqV : tok mx N.V rq < N.V := tok_lt (by omega)
  have hgg1 := one_le_gapOf gap rq lam (c0 + 1)
  obtain ⟨hggl, hgrq⟩ := valid_spec hvalid
  have hgWg : gapW gap lam (c0 + 1) ≤ gapOf gap rq lam (c0 + 1) := gapW_le gap hrq
  have hxp : ∀ p < N.n, Net.tk x p < N.V := fun p hp => hxV _ (tk_mem (by omega))
  have hqm : tok mx N.V rq = tok mx N.V lam ↔ rq = lam := by
    constructor
    · intro h
      have := congrArg (tok mx N.V) h
      rwa [tok_tok (by omega), tok_tok hlam] at this
    · intro h; rw [h]
  -- the tokens other than the largest have rank at most `λ - g`
  have hlow : ∀ p < N.n, Net.tk x p ≠ tok mx N.V lam →
      tok mx N.V (Net.tk x p) ≤ lam - gapOf gap rq lam (c0 + 1) := by
    intro p hp hne
    by_cases hpL : p < N.n - 1
    · have := hK p hpL hne; omega
    · have hpe : p = N.n - 1 := by omega
      subst hpe
      rw [hq] at hne ⊢
      rw [tok_tok (by omega)]
      rcases hgrq with h | h
      · exact absurd (by rw [h]) hne
      · omega
  -- step 1: the query part of the scores, against the largest token's
  have hj0 : lam - gapOf gap rq lam (c0 + 1) < N.V := by omega
  have halo : (aloV (tok mx N.V rq) (tok mx N.V lam) (mat N.V N.V fEh) (vec N.V feps)
      ((rmV mx N.V fEh).getD (tok mx N.V rq) ([], [])).1 (lam - gapOf gap rq lam (c0 + 1))).val =
      (fEh (tok mx N.V rq) (tok mx N.V lam) - (at1 Interp.counting
        ((rmV mx N.V fEh).getD (tok mx N.V rq) ([], [])).1
          (lam - gapOf gap rq lam (c0 + 1))).val) - feps (tok mx N.V rq) := by
    simp only [aloV, at2_mat' hqV hm, at1_vec hqV]
  have hahi : (ahiV (tok mx N.V rq) (tok mx N.V lam) (mat N.V N.V fEh) (vec N.V feps)
      ((rmV mx N.V fEh).getD (tok mx N.V rq) ([], [])).2 (lam - gapOf gap rq lam (c0 + 1))).val =
      (fEh (tok mx N.V rq) (tok mx N.V lam) - (at1 Interp.counting
        ((rmV mx N.V fEh).getD (tok mx N.V rq) ([], [])).2
          (lam - gapOf gap rq lam (c0 + 1))).val) + feps (tok mx N.V rq) := by
    simp only [ahiV, at2_mat' hqV hm, at1_vec hqV]
  set alo := aloV (tok mx N.V rq) (tok mx N.V lam) (mat N.V N.V fEh) (vec N.V feps)
      ((rmV mx N.V fEh).getD (tok mx N.V rq) ([], [])).1 (lam - gapOf gap rq lam (c0 + 1))
    with haloD
  set ahi := ahiV (tok mx N.V rq) (tok mx N.V lam) (mat N.V N.V fEh) (vec N.V feps)
      ((rmV mx N.V fEh).getD (tok mx N.V rq) ([], [])).2 (lam - gapOf gap rq lam (c0 + 1))
    with hahiD
  have hgap_lo : ∀ t < N.V, tok mx N.V t ≤ lam - gapOf gap rq lam (c0 + 1) →
      eqkeF N pbar (tok mx N.V rq) t - eqkeF N pbar (tok mx N.V rq) (tok mx N.V lam) ≤
        -alo.val := by
    intro t ht htr
    have h1 := hE _ hqV t ht _ hm
    have h2 := rmax_ge (mx := mx) (fEh := fEh) hqV hj0 ht htr
    rw [halo]; linarith
  have hgap_hi : ∀ t < N.V, tok mx N.V t ≤ lam - gapOf gap rq lam (c0 + 1) →
      -ahi.val ≤
        eqkeF N pbar (tok mx N.V rq) t - eqkeF N pbar (tok mx N.V rq) (tok mx N.V lam) := by
    intro t ht htr
    have h1 := hE _ hqV _ hm t ht
    have h2 := rmin_le (mx := mx) (fEh := fEh) hqV hj0 ht htr
    rw [hahi]; linarith
  -- the weights
  set q := tok mx N.V rq with hqd
  set m := tok mx N.V lam with hmd
  set Z : ℝ := Real.exp ((eqkeF N pbar q m + peF N pbar q L : ℚ) : ℝ) with hZd
  have hZ : 0 < Z := Real.exp_pos _
  set e : ℕ → ℝ := fun p => Real.exp (N.S q (Net.tk x p) p : ℝ) with hed
  set o : ℕ → ℚ := fun p => peF N pbar q p - peF N pbar q L with hod
  have he_eq : ∀ p, e p = Z * Real.exp (o p : ℝ) *
      Real.exp ((eqkeF N pbar q (Net.tk x p) - eqkeF N pbar q m : ℚ) : ℝ) := by
    intro p
    simp only [hed, hZd, hod]
    rw [score_split N pbar q (Net.tk x p) p, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hW3 := weights_bounds L (fun p => Net.tk x p = m) e Z alo.val ahi.val
    (fun p => (o p : ℝ)) (by simp [hod]) hZ
    (fun p _ h => by rw [he_eq, h, sub_self]; simp)
    (fun p hp h => by
      rw [he_eq]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_pos hZ (Real.exp_pos _)).le
      have := hgap_lo _ (hxp p (by omega)) (hlow p (by omega) h)
      exact_mod_cast this)
    (fun p hp h => by
      rw [he_eq]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (mul_pos hZ (Real.exp_pos _)).le
      have := hgap_hi _ (hxp p (by omega)) (hlow p (by omega) h)
      exact_mod_cast this)
  rw [← hL] at hW3
  obtain ⟨hX, hYlo, hYhi⟩ := hW3
  -- the positions of `m` and the others, as lists of offsets
  set S : List ℚ := ((List.range L).filter fun p => Net.tk x p == m).map o with hSd
  set C : List ℚ := ((List.range L).filter fun p => !(Net.tk x p == m)).map o with hCd
  have hlabL : (Net.tk x L = m) ↔ rq = lam := by rw [← hL1, hq]; exact hqm
  set c1 : ℝ := if rq = lam then 1 else 0 with hc1d
  set c2 : ℝ := if rq = lam then 0 else 1 with hc2d
  have hc1 : (if Net.tk x L = m then (1 : ℝ) else 0) = c1 := by
    by_cases h : rq = lam
    · rw [ite_eq_left (hlabL.mpr h), hc1d, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hlabL.mp h')), hc1d, ite_eq_right h]
  have hc2 : (if Net.tk x L = m then (0 : ℝ) else 1) = c2 := by
    by_cases h : rq = lam
    · rw [ite_eq_left (hlabL.mpr h), hc2d, ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hlabL.mp h')), hc2d, ite_eq_right h]
  have heS : (∑ p ∈ range L, if Net.tk x p = m then Real.exp (o p : ℝ) else 0) = esum S := by
    rw [hSd, esum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : Net.tk x p = m
    · rw [ite_eq_left h, ite_eq_left (beq_iff_eq.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (by simpa using h)]
  have heC : (∑ p ∈ range L, if Net.tk x p = m then 0 else Real.exp (o p : ℝ)) = esum C := by
    rw [hCd, esum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : Net.tk x p = m
    · rw [ite_eq_left h, ite_eq_right (by simpa using h)]
    · rw [ite_eq_right h, ite_eq_left (by simpa using h)]
  rw [heS, hc1] at hX
  rw [heC, hc2] at hYlo hYhi
  set X : ℝ := ∑ p ∈ range N.n, if Net.tk x p = m then e p else 0 with hXd
  set Y : ℝ := ∑ p ∈ range N.n, if Net.tk x p = m then 0 else e p with hYd
  have hXY : 0 < X + Y := by
    rw [hXd, hYd, ← Finset.sum_add_distrib]
    refine Finset.sum_pos (fun p _ => ?_) ⟨0, mem_range.mpr (by omega)⟩
    rcases em (Net.tk x p = m) with h | h
    · rw [ite_eq_left h, ite_eq_left h, add_zero]; exact Real.exp_pos _
    · rw [ite_eq_right h, ite_eq_right h, zero_add]; exact Real.exp_pos _
  -- the sorted sums
  obtain ⟨ws, hws, hperm, hbd⟩ := hsrt q hqV
  rw [hL1] at hperm hbd
  have hSC : (S ++ C).Perm ws := (filter_perm (fun p => Net.tk x p == m) o L).trans hperm.symm
  have hwl : ws.length = L := by rw [hperm.length_eq, List.length_map, List.length_range]
  have hlenS : S.length + ((List.range L).filter fun p => !(Net.tk x p == m)).length = L := by
    have := List.length_eq_length_filter_add (l := List.range L) (fun p => Net.tk x p == m)
    simp only [List.length_range] at this
    rw [hSd, List.length_map]; omega
  set k := kOf N.n rq lam (c0 + 1) with hkd
  have hSl : S.length = k := by
    rw [hL1] at hc
    rw [hkd, kOf]
    by_cases h : rq = lam
    · simp only [h, ↓reduceIte, add_zero] at hc ⊢
      omega
    · simp only [h, ↓reduceIte] at hc ⊢
      omega
  have hkL : k ≤ L := by rw [← hSl, ← hwl]; exact hSC.length_eq ▸ by simp
  have hmono : Monotone (fun x : ℚ => Real.exp (x : ℝ)) := fun a b hab =>
    Real.exp_le_exp.mpr (by exact_mod_cast hab)
  have hs1 : esum (ws.take k) ≤ esum S := by
    have := take_le_part hmono ws hws S C hSC
    rw [hSl] at this
    exact this
  have hs2 : esum S ≤ esum (ws.drop (L - k)) := by
    have := subperm_le_drop hmono ws hws S C hSC
    rw [hwl, hSl] at this
    exact this
  have hT : esum ws = esum S + esum C := by
    rw [← esum_append]; exact (esum_perm hSC).symm
  have htd : ∀ j, esum (ws.take j) + esum (ws.drop j) = esum ws := fun j =>
    sum_take_drop (fun x : ℚ => Real.exp (x : ℝ)) ws j
  obtain ⟨p1, p2, s1, s2⟩ := hbd k (by simpa using hkL)
  obtain ⟨p1', p2', s1', s2'⟩ := hbd (L - k) (by simp)
  have hc10 : 0 ≤ c1 := by rw [hc1d]; split <;> norm_num
  have hc20 : 0 ≤ c2 := by rw [hc2d]; split <;> norm_num
  have hc12 : c1 + c2 = 1 := by rw [hc1d, hc2d]; split <;> norm_num
  have hS0 := esum_nonneg S
  have hC0 := esum_nonneg C
  -- the bounds of the two endpoints
  have hexlo := expInterval_spec helo
  have hexhi := expInterval_spec hehi
  have hc1v : ((c1Of rq lam one).val : ℝ) = c1 := by
    rw [c1Of_val hone, hc1d]; split <;> norm_num
  have hc2v : ((c2Of rq lam one).val : ℝ) = c2 := by
    rw [c2Of_val hone, hc2d]; split <;> norm_num
  have hbA1 := scaleBV_bounds (ea := elo) (c1 := c1Of rq lam one) (Real.exp_pos _) hexlo.1
    hexlo.2 (esum_nonneg _) p1 p2 (by rw [hc1v]; exact hc10)
  have hbB1 := shiftBV_bounds (c2 := c2Of rq lam one) s1 s2
  have hbA2 := scaleBV_bounds (ea := ehi) (c1 := c1Of rq lam one) (Real.exp_pos _) hexhi.1
    hexhi.2 (esum_nonneg _) s1' s2' (by rw [hc1v]; exact hc10)
  have hbB2 := shiftBV_bounds (c2 := c2Of rq lam one) p1' p2'
  rw [hc1v] at hbA1 hbA2
  rw [hc2v] at hbB1 hbB2
  have hpos : ∀ a s s' : ℝ, 0 ≤ s → 0 ≤ s' → 0 < Real.exp a * (s + c1) + (s' + c2) := by
    intro a s s' hs hs'
    rcases em (rq = lam) with h | h
    · have e1 : c1 = 1 := by rw [hc1d, ite_eq_left h]
      have e2 : c2 = 0 := by rw [hc2d, ite_eq_left h]
      rw [e1, e2]
      have := mul_pos (Real.exp_pos a) (by linarith : (0 : ℝ) < s + 1)
      linarith
    · have e1 : c1 = 0 := by rw [hc1d, ite_eq_right h]
      have e2 : c2 = 1 := by rw [hc2d, ite_eq_right h]
      rw [e1, e2]
      have := mul_nonneg (Real.exp_pos a).le (by linarith : (0 : ℝ) ≤ s + 0)
      linarith
  -- one output
  refine correct_of_sums hg hw hV hn hx hxV (by rw [hl]; exact hm) fun j hj hne => ?_
  rw [hl] at hne ⊢
  rw [hq]
  have hjm : j ≠ m := hne
  have hWj : lam - gapW gap lam (c0 + 1) < N.V := by omega
  have hlog := logit_le N.n e (fun p _ => Real.exp_pos _) (fun p => Net.tk x p = m)
    ((N.D q j : ℝ) - N.D q m) ((fmu j - fmu m + fsp q : ℚ) : ℝ)
    ((at1 Interp.counting (ppessV N.V N.n m (PVm N)) j).val : ℝ)
    ((evT N m j - evT N m m : ℚ) : ℝ)
    ((at1 Interp.counting (WpreV mx N) (lam - gapW gap lam (c0 + 1))).val : ℝ)
    (fun p => ((pvT N p j - pvT N p m : ℚ) : ℝ))
    (fun p => ((evT N (Net.tk x p) j - evT N (Net.tk x p) m : ℚ) : ℝ))
    (by have := hEu q hqV j hj m hm; exact_mod_cast this)
    (fun p hp => by
      have := pv_le_ppess (N := N) hm hj hp
      exact_mod_cast this)
    (fun p _ h => by rw [h])
    (fun p hp h => by
      have := W_ge (mx := mx) (N := N) hWj (hxp p hp) (by have := hlow p hp h; omega) hj hm
      exact_mod_cast this)
  have hgoal : ∑ p ∈ range N.n, Real.exp (N.S q (Net.tk x p) p : ℝ) *
      (((N.D q j : ℝ) - N.D q m) + ((N.O (Net.tk x p) p j : ℝ) - N.O (Net.tk x p) p m)) =
      ∑ p ∈ range N.n, e p * (((N.D q j : ℝ) - N.D q m) +
        (((pvT N p j - pvT N p m : ℚ) : ℝ) +
          ((evT N (Net.tk x p) j - evT N (Net.tk x p) m : ℚ) : ℝ))) := by
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← evT_add_pvT, ← evT_add_pvT]
    push_cast
    ring
  rw [hgoal]
  refine lt_of_le_of_lt hlog ?_
  -- in the endpoints' terms
  have hLs := at1_LsV (fmu := fmu) (Pp := ppessV N.V N.n m (PVm N)) hj hm
  have hRs := at1_RsV (f := evT N) hj hm
  have hsq : (at1 Interp.counting (vec N.V fsp) q).val = fsp q := by rw [at1_vec hqV]
  have hF : ((fmu j - fmu m + fsp q : ℚ) : ℝ) +
      ((at1 Interp.counting (ppessV N.V N.n m (PVm N)) j).val : ℝ) =
      ((at1 Interp.counting (LsV N.V m (vec N.V fmu) (ppessV N.V N.n m (PVm N))) j).val : ℝ) +
        ((at1 Interp.counting (vec N.V fsp) q).val : ℝ) := by
    rw [hLs, hsq]; push_cast; ring
  have hR : ((evT N m j - evT N m m : ℚ) : ℝ) =
      ((at1 Interp.counting (RsV N.V m (EVm N)) j).val : ℝ) := by rw [hRs]
  rw [hF, hR]
  -- the lower endpoint
  have hlo : ∀ avg : Q, endpointV (scaleBV elo ((srt.getD q ([], [])).1.getD k (⟨0⟩, ⟨0⟩))
        (c1Of rq lam one)) (shiftBV ((srt.getD q ([], [])).2.getD k (⟨0⟩, ⟨0⟩))
          (c2Of rq lam one))
        (endConstsV N.V m (LsV N.V m (vec N.V fmu) (ppessV N.V N.n m (PVm N)))
          (RsV N.V m (EVm N)) (RmaxV N.V m (RsV N.V m (EVm N)))
          (RminV N.V m (RsV N.V m (EVm N)))
          (at1 Interp.counting (WpreV mx N) (lam - gapW gap lam (c0 + 1))) avg one)
        (at1 Interp.counting (vec N.V fsp) q) = true →
      ((at1 Interp.counting (RsV N.V m (EVm N)) j).val : ℝ) ≤
        ((at1 Interp.counting (WpreV mx N) (lam - gapW gap lam (c0 + 1))).val : ℝ) →
      X * (((at1 Interp.counting (LsV N.V m (vec N.V fmu) (ppessV N.V N.n m (PVm N))) j).val : ℝ)
          + ((at1 Interp.counting (vec N.V fsp) q).val : ℝ) +
          ((at1 Interp.counting (RsV N.V m (EVm N)) j).val : ℝ)) +
        Y * (((at1 Interp.counting (LsV N.V m (vec N.V fmu) (ppessV N.V N.n m (PVm N))) j).val :
          ℝ) + ((at1 Interp.counting (vec N.V fsp) q).val : ℝ) +
          ((at1 Interp.counting (WpreV mx N) (lam - gapW gap lam (c0 + 1))).val : ℝ)) < 0 := by
    intro avg ht hRW
    have h0a := esum_nonneg (ws.take k)
    have h0b := esum_nonneg (ws.drop k)
    have hneg := endpoint_neg hone ht (mul_nonneg (Real.exp_pos _).le (by linarith))
      (by linarith) hbA1.1 hbA1.2 hbB1.1 hbB1.2 hj hjm
    have hr := ratio_lo (X := X) (Y := Y) (E := Z) (a := alo.val) (s := esum S)
      (sS := esum (ws.take k)) (T := esum ws) (c1 := c1) (c2 := c2) hZ hc10 hc20 hs1
      (by linarith) (esum_nonneg _) hX (by rw [hT]; convert hYlo using 3; ring)
    rw [← htd k, show esum (ws.take k) + esum (ws.drop k) - esum (ws.take k) =
      esum (ws.drop k) by ring] at hr
    exact combine_lo hXY (hpos _ _ _ (esum_nonneg _) (esum_nonneg _)) hr hRW hneg
  -- the upper endpoint
  have hhi : ∀ avg : Q, endpointV (scaleBV ehi ((srt.getD q ([], [])).2.getD (N.n - 1 - k)
        (⟨0⟩, ⟨0⟩)) (c1Of rq lam one)) (shiftBV ((srt.getD q ([], [])).1.getD (N.n - 1 - k)
          (⟨0⟩, ⟨0⟩)) (c2Of rq lam one))
        (endConstsV N.V m (LsV N.V m (vec N.V fmu) (ppessV N.V N.n m (PVm N)))
          (RsV N.V m (EVm N)) (RmaxV N.V m (RsV N.V m (EVm N)))
          (RminV N.V m (RsV N.V m (EVm N)))
          (at1 Interp.counting (WpreV mx N) (lam - gapW gap lam (c0 + 1))) avg one)
        (at1 Interp.counting (vec N.V fsp) q) = true →
      ((at1 Interp.counting (WpreV mx N) (lam - gapW gap lam (c0 + 1))).val : ℝ) ≤
        ((at1 Interp.counting (RsV N.V m (EVm N)) j).val : ℝ) →
      X * (((at1 Interp.counting (LsV N.V m (vec N.V fmu) (ppessV N.V N.n m (PVm N))) j).val : ℝ)
          + ((at1 Interp.counting (vec N.V fsp) q).val : ℝ) +
          ((at1 Interp.counting (RsV N.V m (EVm N)) j).val : ℝ)) +
        Y * (((at1 Interp.counting (LsV N.V m (vec N.V fmu) (ppessV N.V N.n m (PVm N))) j).val :
          ℝ) + ((at1 Interp.counting (vec N.V fsp) q).val : ℝ) +
          ((at1 Interp.counting (WpreV mx N) (lam - gapW gap lam (c0 + 1))).val : ℝ)) < 0 := by
    intro avg ht hRW
    rw [hL1] at ht
    have h0a := esum_nonneg (ws.drop (L - k))
    have h0b := esum_nonneg (ws.take (L - k))
    have hneg := endpoint_neg hone ht (mul_nonneg (Real.exp_pos _).le (by linarith))
      (by linarith) hbA2.1 hbA2.2 hbB2.1 hbB2.2 hj hjm
    have hr := ratio_hi (X := X) (Y := Y) (E := Z) (a := ahi.val) (s := esum S)
      (sL := esum (ws.drop (L - k))) (T := esum ws) (c1 := c1) (c2 := c2) hZ hc10 hc20 hs2
      (by linarith [htd (L - k)]) (esum_nonneg _) hX
      (by rw [hT]; convert hYhi using 3; ring)
    rw [← htd (L - k), show esum (ws.take (L - k)) + esum (ws.drop (L - k)) -
      esum (ws.drop (L - k)) = esum (ws.take (L - k)) by ring] at hr
    have hAB := hpos ahi.val (esum (ws.drop (L - k))) (esum (ws.take (L - k))) (esum_nonneg _)
      (esum_nonneg _)
    exact combine_hi hXY hAB hr hRW hneg
  -- the test passed at the endpoints the slopes call for
  have hRx := at1_le_RmaxV (Rs := RsV N.V m (EVm N)) hj hjm
  have hRn := RminV_le_at1 (Rs := RsV N.V m (EVm N)) hj hjm
  simp only [classTestV, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hct
  rcases hct with (⟨hd1, htl⟩ | ⟨hd2, hth⟩) | ⟨htl, hth⟩
  · exact hlo _ htl (by exact_mod_cast le_of_lt (lt_of_le_of_lt hRx hd1))
  · exact hhi _ hth (by exact_mod_cast le_trans hd2 hRn)
  · rcases le_total ((at1 Interp.counting (RsV N.V m (EVm N)) j).val)
      ((at1 Interp.counting (WpreV mx N) (lam - gapW gap lam (c0 + 1))).val) with h | h
    · exact hlo _ htl (by exact_mod_cast h)
    · exact hhi _ hth (by exact_mod_cast h)

end GrossSub
