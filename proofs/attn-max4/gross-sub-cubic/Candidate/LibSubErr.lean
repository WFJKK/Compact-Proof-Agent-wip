import Candidate.LibSubRuns

/-!
# Step 1 of entry 9: `Ê` and the bounds `ε`

`runs_errOut`: for each method `err`, the run of `errOut` (its value and cost) and what its value
satisfies (`ErrSpec`): every row of `EQKE - Ê` spreads by at most `ε_q`, whenever the method's
certificate check passes (only the `svd` method has one).

`EQKE[q, t] = Eq_q M Ek_tᵀ` with `M = (c W_Q) W_Kᵀ`, as the checker's tables give it (`eqke`).
-/

namespace GrossSub

open CompactCheck Common AttnClasses GrossCubic Finset

variable {env : Env}

/-- `M = (c W_Q) W_Kᵀ` from the columns `Qc` of `c W_Q` and `Kc` of `W_K`. -/
def mqk (h : ℕ) (Qc Kc : ℕ → ℕ → ℚ) (a b : ℕ) : ℚ := ∑ k ∈ range h, Qc k a * Kc k b

/-- The query-key part of the score: `EQKE[q, t] = Eq_q M Ek_tᵀ`. -/
def eqke (d h : ℕ) (Eq Ek Qc Kc : ℕ → ℕ → ℚ) (q t : ℕ) : ℚ :=
  bil d (mqk h Qc Kc) (Eq q) (Ek t)

/-- What step 1 delivers: every row of `E - Ê` spreads by at most `ε_q`. -/
def ErrSpec (V : ℕ) (E Eh : ℕ → ℕ → ℚ) (eps : ℕ → ℚ) : Prop :=
  ∀ q < V, ∀ i < V, ∀ j < V, E q i - E q j ≤ (Eh q i - Eh q j) + eps q

/-- From `E = Ê + R` and a bound on the spread of `R`'s rows. -/
theorem errSpec_of {V : ℕ} {E Eh R : ℕ → ℕ → ℚ} {eps : ℕ → ℚ}
    (hE : ∀ q < V, ∀ t < V, E q t = Eh q t + R q t)
    (hR : ∀ q < V, ∀ i < V, ∀ j < V, R q i - R q j ≤ eps q) : ErrSpec V E Eh eps := by
  intro q hq i hi j hj
  rw [hE q hq i hi, hE q hq j hj]
  have := hR q hq i hi j hj
  linarith

/-! ## Their two factors -/

/-- The inner dimension of the two factors. -/
def facR (d h : ℕ) : ℕ := if h < d then h else d

/-- The left factor: `Eq (c W_Q)` if the head is narrower, else `Eq M`. -/
def facA (d h : ℕ) (Eq Qc Kc : ℕ → ℕ → ℚ) : ℕ → ℕ → ℚ :=
  if h < d then fun q k => ∑ a ∈ range d, Eq q a * Qc k a
  else fun q b => ∑ a ∈ range d, Eq q a * mqk h Qc Kc a b

/-- The right factor: `W_Kᵀ Ekᵀ` if the head is narrower, else `Ekᵀ`. -/
def facB (d h : ℕ) (Ek Kc : ℕ → ℕ → ℚ) : ℕ → ℕ → ℚ :=
  if h < d then fun k t => ∑ b ∈ range d, Kc k b * Ek t b
  else fun b t => Ek t b

def facCost (V d h : ℕ) : ℕ := if h < d then V * h * d + (h * V * d + 0) else V * d * d + 0

theorem runs_factors (V d h : ℕ) (Eq Ek Qc Kc : ℕ → ℕ → ℚ) :
    Runs (factors Interp.counting d h (mat V d Eq) (mat V d Ek) (mat h d Qc) (mat h d Kc)
      (mat d d (mqk h Qc Kc))) env
      (mat V (facR d h) (facA d h Eq Qc Kc), mat (facR d h) V (facB d h Ek Kc))
      (facCost V d h) := by
  unfold factors facR facA facB facCost
  by_cases hd : h < d
  · simp only [hd, ↓reduceIte, Interp.counting_bind]
    exact Runs.bind' (runs_mm V h d Eq Qc) (Runs.bind' (runs_mm h V d Kc Ek) (Runs.pure _)
      rfl rfl) rfl rfl
  · simp only [hd, ↓reduceIte, Interp.counting_bind]
    rw [tr_mat, tr_mat]
    exact Runs.bind' (runs_mm V d d Eq _) (Runs.pure _) rfl rfl

/-- The two factors multiply to `EQKE`. -/
theorem fac_eq (d h : ℕ) (Eq Ek Qc Kc : ℕ → ℕ → ℚ) (q t : ℕ) :
    ∑ k ∈ range (facR d h), facA d h Eq Qc Kc q k * facB d h Ek Kc k t =
      eqke d h Eq Ek Qc Kc q t := by
  unfold facR facA facB eqke
  by_cases hd : h < d
  · simp only [hd, ↓reduceIte]
    rw [show mqk h Qc Kc = fun a b => ∑ k ∈ range h, (fun a k => Qc k a) a k *
      (fun b k => Kc k b) b k from rfl, bil_prod]
  · simp only [hd, ↓reduceIte]
    rw [bil_swap]
    exact Finset.sum_congr rfl fun b _ => by ring

/-! ## The methods -/

theorem replicate_vec (V : ℕ) (e : ℚ) : List.replicate V (⟨e⟩ : Q) = vec V fun _ => e := by
  simp [vec, List.map_const']

/-- The cost of the `svd` family (`err ≤ 2`). -/
def errACost (err V d h : ℕ) : ℕ :=
  facCost V d h + (svdSplitCost V (facR d h) +
    (if err = 0 then svdBoundCost V (facR d h) + 0
     else if err = 1 then rowBoundCost V (facR d h) V + 0
     else V * V * facR d h + (V * (2 * (V - 1) + 1) + 0)))

/-- `R = Ar Br` of the `svd` family. -/
def svdR (V r : ℕ) (A B : ℕ → ℕ → ℚ) (u v : ℕ → ℚ) (q t : ℕ) : ℚ :=
  ∑ k ∈ range r, sAr V u A q k * sBr V B v k t

/-- `EQKE = Ê + Ar Br` for the `svd` family, at any `u`, `v`. -/
theorem svd_split_eqke (V d h : ℕ) (Eq Ek Qc Kc : ℕ → ℕ → ℚ) (u v : ℕ → ℚ) (q t : ℕ) :
    eqke d h Eq Ek Qc Kc q t =
      sEh V (facR d h) (facA d h Eq Qc Kc) (facB d h Ek Kc) u v q t +
        svdR V (facR d h) (facA d h Eq Qc Kc) (facB d h Ek Kc) u v q t := by
  rw [← fac_eq, split_eq V (facR d h) _ _ u v q t]
  unfold sEh svdR sAr sBr sUA sBv
  ring

theorem runs_errA (err V d h off : ℕ) (herr : err ≤ 2) (Eq Ek Qc Kc : ℕ → ℕ → ℚ)
    (hc : off + errCertLen err V d h ≤ env.cert.size) :
    ∃ fEh feps ok, Runs (errOut Interp.counting err V d h off (mat V d Eq) (mat V d Ek)
      (mat h d Qc) (mat h d Kc) (mat d d (mqk h Qc Kc))) env
      (mat V V fEh, vec V feps, ok) (errACost err V d h) ∧
      (ok = true → ErrSpec V (eqke d h Eq Ek Qc Kc) fEh feps) := by
  set r := facR d h with hr
  set A := facA d h Eq Qc Kc
  set B := facB d h Ek Kc
  set u := cDir env off
  set v := cDir env (off + V)
  have hlen : off + 2 * V ≤ env.cert.size := by
    unfold errCertLen at hc
    rcases (by omega : err = 0 ∨ err = 1 ∨ err = 2) with h0 | h0 | h0 <;> subst h0 <;>
      simp at hc <;> omega
  have hsplit : ∀ q < V, ∀ t < V, eqke d h Eq Ek Qc Kc q t =
      sEh V r A B u v q t + svdR V r A B u v q t := fun q _ t _ =>
    svd_split_eqke V d h _ _ _ _ u v q t
  unfold errOut errACost
  simp only [herr, ↓reduceIte, Interp.counting_bind]
  rcases (by omega : err = 0 ∨ err = 1 ∨ err = 2) with h0 | h0 | h0 <;> subst h0
  · -- `svd`: the certified bound
    have hc' : off + 2 * V + 3 * (r * r) + 1 ≤ env.cert.size := by
      unfold errCertLen at hc; simp only [↓reduceIte] at hc; rw [hr]; unfold facR; omega
    refine ⟨sEh V r A B u v, fun _ => cE env r (off + 2 * V),
      psdV r (svdX1 V r (sAr V u A) (cT env r (off + 2 * V))) (cF1 env r (off + 2 * V)) &&
        psdV r (svdX2 V r (sBr V B v) (cT env r (off + 2 * V)) (cE env r (off + 2 * V)))
          (cF2 env r (off + 2 * V)) && decide (0 ≤ cE env r (off + 2 * V)), ?_, ?_⟩
    · simp only [↓reduceIte]
      refine Runs.bind' (runs_factors V d h Eq Ek Qc Kc) ?_ rfl rfl
      refine Runs.bind0 (runs_certVec off V (by omega)) ?_
      refine Runs.bind0 (runs_certVec (off + V) V (by omega)) ?_
      refine Runs.bind' (runs_svdSplit V r A B u v) ?_ rfl rfl
      refine Runs.bind' (runs_svdBound V r (off + 2 * V) _ _ hc') (Runs.pure _) ?_ rfl
      simp only [replicate_vec]
    · intro hok
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨h1, h2⟩, he⟩ := hok
      refine errSpec_of hsplit fun q hq i hi j hj => ?_
      exact spread_le_of_psd V r (sAr V u A) (sBr V B v) (cT env r (off + 2 * V))
        (cE env r (off + 2 * V)) he (fun z => qf_nonneg r _ _ (psdV_dom h1) z)
        (fun w => qf_nonneg r _ _ (psdV_dom h2) w) hq hi hj
  · -- `max_diff`, `mean+max_diff`: the row bound at the certificate's row
    have hc' : off + 2 * V + r ≤ env.cert.size := by
      unfold errCertLen at hc; simp at hc; rw [hr]; unfold facR; omega
    set a := cDir env (off + 2 * V)
    refine ⟨sEh V r A B u v, fun q => spreadV V (fun t => ∑ b ∈ range r, a b * sBr V B v b t) +
      ∑ b ∈ range r, |sAr V u A q b - a b| * spreadV V (sBr V B v b), true, ?_, ?_⟩
    · simp only [↓reduceIte, one_ne_zero]
      refine Runs.bind' (runs_factors V d h Eq Ek Qc Kc) ?_ rfl rfl
      refine Runs.bind0 (runs_certVec off V (by omega)) ?_
      refine Runs.bind0 (runs_certVec (off + V) V (by omega)) ?_
      refine Runs.bind' (runs_svdSplit V r A B u v) ?_ rfl rfl
      refine Runs.bind0 (runs_certVec (off + 2 * V) r hc') ?_
      exact Runs.bind' (runs_rowBound V r V _ _ _) (Runs.pure _) rfl rfl
    · intro _
      refine errSpec_of hsplit fun q hq i hi j hj => ?_
      exact prod_diff_le r (sAr V u A q) (sBr V B v) a (fun b => spreadV V (sBr V B v b)) _ i j
        (fun k _ => spreadV_ge V _ hi hj) (fun k _ => spreadV_ge V _ hj hi)
        (spreadV_ge V (fun t => ∑ b ∈ range r, a b * sBr V B v b t) hi hj)
  · -- `max_diff_exact`: the spread of each row of `Ar Br`, computed
    refine ⟨sEh V r A B u v, fun q => spreadV V (svdR V r A B u v q), true, ?_, ?_⟩
    · simp only [↓reduceIte, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one]
      refine Runs.bind' (runs_factors V d h Eq Ek Qc Kc) ?_ rfl rfl
      refine Runs.bind0 (runs_certVec off V (by omega)) ?_
      refine Runs.bind0 (runs_certVec (off + V) V (by omega)) ?_
      refine Runs.bind' (runs_svdSplit V r A B u v) ?_ rfl rfl
      rw [tr_mat]
      refine Runs.bind' (runs_mm V V r _ _) ?_ rfl rfl
      exact Runs.bind' (runs_mapM_mat V V _ fun q _ => runs_spread V _) (Runs.pure _) rfl rfl
    · intro _
      exact errSpec_of hsplit fun q hq i hi j hj => spreadV_ge V _ hi hj

/-- Reassociating a product of three: `Σ_k (Σ_a f_a g_ak) z_k = Σ_a f_a (Σ_k g_ak z_k)`. -/
theorem sum_assoc (s t : Finset ℕ) (f : ℕ → ℚ) (g : ℕ → ℕ → ℚ) (z : ℕ → ℚ) :
    ∑ k ∈ s, (∑ a ∈ t, f a * g a k) * z k = ∑ a ∈ t, f a * ∑ k ∈ s, g a k * z k := by
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun k _ => by ring

/-! ## `exact_EQKE+max_diff_exact` -/

def errBCost (V d h : ℕ) : ℕ := V * h * d + (V * h * d + (V * V * h + 0))

theorem runs_errB (V d h off : ℕ) (Eq Ek Qc Kc : ℕ → ℕ → ℚ) :
    ∃ fEh feps ok, Runs (errOut Interp.counting 3 V d h off (mat V d Eq) (mat V d Ek)
      (mat h d Qc) (mat h d Kc) (mat d d (mqk h Qc Kc))) env
      (mat V V fEh, vec V feps, ok) (errBCost V d h) ∧
      (ok = true → ErrSpec V (eqke d h Eq Ek Qc Kc) fEh feps) := by
  refine ⟨fun q t => ∑ k ∈ range h, (∑ a ∈ range d, Eq q a * Qc k a) *
    ∑ b ∈ range d, Ek t b * Kc k b, fun _ => 0, true, ?_, ?_⟩
  · unfold errOut errBCost
    simp only [show ¬ (3 ≤ 2) by omega, ↓reduceIte, Interp.counting_bind]
    exact Runs.bind' (runs_mm V h d Eq Qc) (Runs.bind' (runs_mm V h d Ek Kc)
      (Runs.bind' (runs_mm V V h _ _) (Runs.pure _) (by rw [replicate_vec]) rfl) rfl rfl) rfl rfl
  · intro _ q hq i hi j hj
    have e : ∀ t, eqke d h Eq Ek Qc Kc q t = ∑ k ∈ range h, (∑ a ∈ range d, Eq q a * Qc k a) *
        ∑ b ∈ range d, Ek t b * Kc k b := fun t => by
      unfold eqke
      rw [show mqk h Qc Kc = fun a b => ∑ k ∈ range h, (fun a k => Qc k a) a k *
        (fun b k => Kc k b) b k from rfl, bil_prod]
      exact Finset.sum_congr rfl fun k _ => by
        congr 1; exact Finset.sum_congr rfl fun b _ => by ring
    rw [e, e]
    linarith

/-! ## The subproduct methods -/

/-- The remainder `R = (Qe2 Wqe)(Wkeᵀ Ke2ᵀ)` of the subproduct decomposition. -/
def subR (d h : ℕ) (Qe2 Wqe Wke Ke2 : ℕ → ℕ → ℚ) (q t : ℕ) : ℚ :=
  ∑ k ∈ range h, (∑ a ∈ range d, Qe2 q a * Wqe a k) * ∑ b ∈ range d, Wke b k * Ke2 t b

/-- `EQKE = Ê + R` for the subproduct decomposition, at any directions. -/
theorem sub_split_eqke (V d h : ℕ) (Eq Ek Qc Kc : ℕ → ℕ → ℚ) (kd qd skd sqd qu ku : ℕ → ℚ)
    (q t : ℕ) :
    eqke d h Eq Ek Qc Kc q t =
      subEh V d h Eq Ek (fun a k => Qc k a) (fun b k => Kc k b) (mqk h Qc Kc) kd qd skd sqd qu ku
        q t +
      subR d h (subQe2 V Eq qd sqd) (subWqe d (fun a k => Qc k a) qu)
        (subWke d (fun b k => Kc k b) ku) (subKe2 V Ek kd skd) q t := by
  have := sub_eq d h Eq Ek (fun a k => Qc k a) (fun b k => Kc k b) kd qd skd sqd qu ku
    (sUA V kd Ek) (sUA V qd Eq) (sUA V skd (subKe V Ek kd)) (sUA V sqd (subQe V Eq qd))
    (sUA d qu (fun a k => Qc k a)) (sUA d ku (fun b k => Kc k b))
    (sUA d (sUA V qd Eq) (mqk h Qc Kc)) (mv d (mqk h Qc Kc) (sUA V kd Ek))
    (sUA d (sUA V sqd (subQe V Eq qd)) (mqk h Qc Kc))
    (mv d (mqk h Qc Kc) (sUA V skd (subKe V Ek kd)))
    (mv h (fun b k => Kc k b) (sUA d qu (fun a k => Qc k a)))
    (mv h (subWqe d (fun a k => Qc k a) qu) (sUA d ku (fun b k => Kc k b)))
    (mv d Ek (sUA d (sUA V qd Eq) (mqk h Qc Kc)))
    (mv d (subQe V Eq qd) (mv d (mqk h Qc Kc) (sUA V kd Ek)))
    (mv d (subKe V Ek kd) (sUA d (sUA V sqd (subQe V Eq qd)) (mqk h Qc Kc)))
    (mv d (subQe2 V Eq qd sqd) (mv d (mqk h Qc Kc) (sUA V skd (subKe V Ek kd))))
    (mv d (subKe2 V Ek kd skd) (mv h (fun b k => Kc k b) (sUA d qu (fun a k => Qc k a))))
    (mv d (subQe2 V Eq qd sqd) qu)
    (mv d (subQe2 V Eq qd sqd) (mv h (subWqe d (fun a k => Qc k a) qu)
      (sUA d ku (fun b k => Kc k b))))
    (mv d (subKe2 V Ek kd skd) ku)
    (subKe V Ek kd) (subQe V Eq qd) (subKe2 V Ek kd skd) (subQe2 V Eq qd sqd)
    (subWqe d (fun a k => Qc k a) qu) (subWke d (fun b k => Kc k b) ku) q t
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  have e0 : eqke d h Eq Ek Qc Kc q t =
      bil d (fun a b => ∑ k ∈ range h, Qc k a * Kc k b) (Eq q) (Ek t) := rfl
  rw [e0, this]
  unfold subEh subR
  ring

/-- The cost of the break points (`err = 4`). -/
def breakCost (V d h : ℕ) : ℕ :=
  h * V * d + (d * V * h + (V * h * d + (V * d * h + (rowBoundCost V d V + (rowBoundCost V h V +
    (rowBoundCost V d V + (V * (1 + 1) + 0)))))))

/-- The cost of the recursion (`err = 5`). -/
def recCost (V d h : ℕ) : ℕ :=
  d * (2 * (V - 1) + 1) + (V * d + ((2 * (V - 1) + 1) + (h * (d * 4 + 1) + (d * h + (V * d +
    ((2 * (V - 1) + 1) + (d * (h * 4 + 1) + (h * d + (d * h + (V * d + ((2 * (V - 1) + 1) +
    (V * (d * 4 + 1) + 0))))))))))))

/-- The cost of the subproduct methods. -/
def errCCost (err V d h : ℕ) : ℕ :=
  subCost V d h + (if err = 4 then breakCost V d h else recCost V d h)

theorem runs_errC (err V d h off : ℕ) (herr : 4 ≤ err) (Eq Ek Qc Kc : ℕ → ℕ → ℚ)
    (hc : off + errCertLen err V d h ≤ env.cert.size) :
    ∃ fEh feps ok, Runs (errOut Interp.counting err V d h off (mat V d Eq) (mat V d Ek)
      (mat h d Qc) (mat h d Kc) (mat d d (mqk h Qc Kc))) env
      (mat V V fEh, vec V feps, ok) (errCCost err V d h) ∧
      (ok = true → ErrSpec V (eqke d h Eq Ek Qc Kc) fEh feps) := by
  have hlen : off + 4 * V + d + d + (d + h + d) ≤ env.cert.size := by
    unfold errCertLen at hc
    simp only [show err ≠ 0 by omega, show err ≠ 1 by omega, show err ≠ 2 by omega,
      show err ≠ 3 by omega, ↓reduceIte] at hc
    omega
  set kd := cDir env off
  set qd := cDir env (off + V)
  set skd := cDir env (off + 2 * V)
  set sqd := cDir env (off + 3 * V)
  set qu := cDir env (off + 4 * V)
  set ku := cDir env (off + 4 * V + d)
  set Wq : ℕ → ℕ → ℚ := fun a k => Qc k a
  set Wk : ℕ → ℕ → ℚ := fun b k => Kc k b
  set Eh := subEh V d h Eq Ek Wq Wk (mqk h Qc Kc) kd qd skd sqd qu ku
  set Qe2 := subQe2 V Eq qd sqd
  set Wqe := subWqe d Wq qu
  set Wke := subWke d Wk ku
  set Ke2 := subKe2 V Ek kd skd
  set o2 := off + 4 * V + 2 * d
  set a0 := cDir env o2
  set a1 := cDir env (o2 + d)
  set a2 := cDir env (o2 + d + h)
  have hsplit : ∀ q < V, ∀ t < V, eqke d h Eq Ek Qc Kc q t =
      Eh q t + subR d h Qe2 Wqe Wke Ke2 q t := fun q _ t _ =>
    sub_split_eqke V d h Eq Ek Qc Kc kd qd skd sqd qu ku q t
  -- the remainder through the head, read three ways
  set r2 : ℕ → ℕ → ℚ := fun k t => ∑ b ∈ range d, Wke b k * Ke2 t b
  set r1 : ℕ → ℕ → ℚ := fun a t => ∑ k ∈ range h, Wqe a k * r2 k t
  set l2 : ℕ → ℕ → ℚ := fun q k => ∑ a ∈ range d, Qe2 q a * Wqe a k
  set l3 : ℕ → ℕ → ℚ := fun q b => ∑ k ∈ range h, l2 q k * Wke b k
  have hR2 : ∀ q t, subR d h Qe2 Wqe Wke Ke2 q t = ∑ k ∈ range h, l2 q k * r2 k t :=
    fun q t => rfl
  have hR1 : ∀ q t, subR d h Qe2 Wqe Wke Ke2 q t = ∑ a ∈ range d, Qe2 q a * r1 a t :=
    fun q t => sum_assoc _ _ _ _ _
  have hR3 : ∀ q t, subR d h Qe2 Wqe Wke Ke2 q t = ∑ b ∈ range d, l3 q b * Ke2 t b := by
    intro q t
    rw [hR2]
    simp only [r2, l3]
    rw [sum_assoc (range d) (range h) (l2 q) (fun k b => Wke b k) (fun b => Ke2 t b)]
  unfold errOut errCCost
  simp only [show ¬ (err ≤ 2) by omega, show err ≠ 3 by omega, ↓reduceIte, Interp.counting_bind]
  rw [tr_mat, tr_mat]
  rcases (by omega : err = 4 ∨ 4 < err) with h4 | h5
  · -- the break points
    subst h4
    refine ⟨Eh, fun q => min (min
      (spreadV V (fun t => ∑ a ∈ range d, a0 a * r1 a t) +
        ∑ a ∈ range d, |Qe2 q a - a0 a| * spreadV V (r1 a))
      (spreadV V (fun t => ∑ k ∈ range h, a1 k * r2 k t) +
        ∑ k ∈ range h, |l2 q k - a1 k| * spreadV V (r2 k)))
      (spreadV V (fun t => ∑ b ∈ range d, a2 b * Ke2 t b) +
        ∑ b ∈ range d, |l3 q b - a2 b| * spreadV V (fun t => Ke2 t b)), true, ?_, ?_⟩
    · simp only [↓reduceIte]
      unfold breakCost
      refine Runs.bind' (runs_subDecomp V d h off Eq Ek Wq Wk (mqk h Qc Kc) (by omega)) ?_ rfl rfl
      refine Runs.bind0 (runs_certVec o2 d (by omega)) ?_
      refine Runs.bind0 (runs_certVec (o2 + d) h (by omega)) ?_
      refine Runs.bind0 (runs_certVec (o2 + d + h) d (by omega)) ?_
      simp only [tr_mat]
      refine Runs.bind' (runs_mm h V d (fun k b => Wke b k) Ke2) ?_ rfl rfl
      simp only [tr_mat]
      refine Runs.bind' (runs_mm d V h Wqe (fun t k => r2 k t)) ?_ rfl rfl
      refine Runs.bind' (runs_mm V h d Qe2 (fun k a => Wqe a k)) ?_ rfl rfl
      refine Runs.bind' (runs_mm V d h l2 Wke) ?_ rfl rfl
      refine Runs.bind' (runs_rowBound V d V Qe2 r1 a0) ?_ rfl rfl
      refine Runs.bind' (runs_rowBound V h V l2 r2 a1) ?_ rfl rfl
      refine Runs.bind' (runs_rowBound V d V l3 (fun b t => Ke2 t b) a2) ?_ rfl rfl
      refine Runs.bind' (runs_mapM_range V fun q hq => Runs.bind' (runs_min cat _ _)
        (runs_min cat _ _) rfl rfl) (Runs.pure _) ?_ rfl
      refine Prod.ext rfl (Prod.ext ?_ rfl)
      refine List.map_congr_left fun q hq => ?_
      have hq' := List.mem_range.mp hq
      rw [at1_vec hq', at1_vec hq', at1_vec hq']
    · intro _
      refine errSpec_of hsplit fun q hq i hi j hj => ?_
      have b1 := prod_diff_le d (Qe2 q) r1 a0 (fun a => spreadV V (r1 a))
        (spreadV V (fun t => ∑ a ∈ range d, a0 a * r1 a t)) i j
        (fun k _ => spreadV_ge V _ hi hj) (fun k _ => spreadV_ge V _ hj hi)
        (spreadV_ge V (fun t => ∑ a ∈ range d, a0 a * r1 a t) hi hj)
      have b2 := prod_diff_le h (l2 q) r2 a1 (fun k => spreadV V (r2 k))
        (spreadV V (fun t => ∑ k ∈ range h, a1 k * r2 k t)) i j
        (fun k _ => spreadV_ge V _ hi hj) (fun k _ => spreadV_ge V _ hj hi)
        (spreadV_ge V (fun t => ∑ k ∈ range h, a1 k * r2 k t) hi hj)
      have b3 := prod_diff_le d (l3 q) (fun b t => Ke2 t b) a2
        (fun b => spreadV V (fun t => Ke2 t b))
        (spreadV V (fun t => ∑ b ∈ range d, a2 b * Ke2 t b)) i j
        (fun k _ => spreadV_ge V _ hi hj) (fun k _ => spreadV_ge V _ hj hi)
        (spreadV_ge V (fun t => ∑ b ∈ range d, a2 b * Ke2 t b) hi hj)
      rw [← hR1, ← hR1] at b1
      rw [← hR2, ← hR2] at b2
      rw [← hR3, ← hR3] at b3
      simp only [le_min_iff]
      exact ⟨⟨b1, b2⟩, b3⟩
  · -- the recursion
    have h5' : err ≠ 4 := by omega
    -- level by level: rows of `Ke2ᵀ`, of `Wkeᵀ Ke2ᵀ`, of `Wqe Wkeᵀ Ke2ᵀ`, of the remainder
    set f3 : ℕ → ℚ := fun b => spreadV V (fun t => Ke2 t b)
    set f2 : ℕ → ℚ := fun k => spreadV V (fun t => ∑ b ∈ range d, a2 b * Ke2 t b) +
      ∑ b ∈ range d, |Wke b k - a2 b| * f3 b
    set m12 : ℕ → ℚ := fun b => ∑ k ∈ range h, a1 k * Wke b k
    set f1 : ℕ → ℚ := fun a => spreadV V (fun t => ∑ b ∈ range d, m12 b * Ke2 t b) +
      ∑ k ∈ range h, |Wqe a k - a1 k| * f2 k
    set m01 : ℕ → ℚ := fun k => ∑ a ∈ range d, a0 a * Wqe a k
    set m02 : ℕ → ℚ := fun b => ∑ k ∈ range h, m01 k * Wke b k
    refine ⟨Eh, fun q => spreadV V (fun t => ∑ b ∈ range d, m02 b * Ke2 t b) +
      ∑ a ∈ range d, |Qe2 q a - a0 a| * f1 a, true, ?_, ?_⟩
    · simp only [h5', ↓reduceIte]
      unfold recCost
      refine Runs.bind' (runs_subDecomp V d h off Eq Ek Wq Wk (mqk h Qc Kc) (by omega)) ?_ rfl rfl
      refine Runs.bind0 (runs_certVec o2 d (by omega)) ?_
      refine Runs.bind0 (runs_certVec (o2 + d) h (by omega)) ?_
      refine Runs.bind0 (runs_certVec (o2 + d + h) d (by omega)) ?_
      simp only [tr_mat]
      refine Runs.bind' (runs_mapM_mat d V (fun b t => Ke2 t b) fun b _ => runs_spread V _) ?_
        rfl rfl
      refine Runs.bind' (runs_vecMat d V a2 (fun b t => Ke2 t b)) ?_ rfl rfl
      refine Runs.bind' (runs_spread V _) ?_ rfl rfl
      refine Runs.bind' (runs_mapM_mat h d (fun k b => Wke b k) fun k _ =>
        Runs.bind' (runs_absDot_vec d (fun b => Wke b k) a2 f3) (runs_add cat _ _) rfl rfl) ?_
        rfl rfl
      refine Runs.bind' (runs_vecMat h d a1 (fun k b => Wke b k)) ?_ rfl rfl
      refine Runs.bind' (runs_vecMat d V m12 (fun b t => Ke2 t b)) ?_ rfl rfl
      refine Runs.bind' (runs_spread V _) ?_ rfl rfl
      refine Runs.bind' (runs_mapM_mat d h Wqe fun a _ =>
        Runs.bind' (runs_absDot_vec h (Wqe a) a1 f2) (runs_add cat _ _) rfl rfl) ?_ rfl rfl
      refine Runs.bind' (runs_vecMat d h a0 Wqe) ?_ rfl rfl
      refine Runs.bind' (runs_vecMat h d m01 (fun k b => Wke b k)) ?_ rfl rfl
      refine Runs.bind' (runs_vecMat d V m02 (fun b t => Ke2 t b)) ?_ rfl rfl
      refine Runs.bind' (runs_spread V _) ?_ rfl rfl
      exact Runs.bind' (runs_mapM_mat V d Qe2 fun q _ =>
        Runs.bind' (runs_absDot_vec d (Qe2 q) a0 f1) (runs_add cat _ _) rfl rfl) (Runs.pure _)
        rfl rfl
    · intro _
      -- rows of `r2` spread by at most `f2`
      have hr2 : ∀ k, ∀ i < V, ∀ j < V, r2 k i - r2 k j ≤ f2 k := fun k i hi j hj =>
        prod_diff_le d (fun b => Wke b k) (fun b t => Ke2 t b) a2 f3 _ i j
          (fun b _ => spreadV_ge V _ hi hj) (fun b _ => spreadV_ge V _ hj hi)
          (spreadV_ge V (fun t => ∑ b ∈ range d, a2 b * Ke2 t b) hi hj)
      -- rows of `r1` by at most `f1`
      have hm1 : ∀ t, ∑ k ∈ range h, a1 k * r2 k t = ∑ b ∈ range d, m12 b * Ke2 t b := fun t =>
        (sum_assoc (range d) (range h) a1 (fun k b => Wke b k) (fun b => Ke2 t b)).symm
      have hr1 : ∀ a, ∀ i < V, ∀ j < V, r1 a i - r1 a j ≤ f1 a := fun a i hi j hj => by
        have := prod_diff_le h (Wqe a) r2 a1 f2
          (spreadV V (fun t => ∑ b ∈ range d, m12 b * Ke2 t b)) i j
          (fun k _ => hr2 k i hi j hj) (fun k _ => hr2 k j hj i hi)
          (by rw [hm1, hm1]; exact spreadV_ge V _ hi hj)
        exact this
      -- the remainder by at most `ε`
      have hm0 : ∀ t, ∑ a ∈ range d, a0 a * r1 a t = ∑ b ∈ range d, m02 b * Ke2 t b := by
        intro t
        simp only [r1]
        rw [← sum_assoc (range h) (range d) a0 Wqe (fun k => r2 k t)]
        simp only [r2]
        exact (sum_assoc (range d) (range h) m01 (fun k b => Wke b k) (fun b => Ke2 t b)).symm
      refine errSpec_of hsplit fun q hq i hi j hj => ?_
      rw [hR1, hR1]
      exact prod_diff_le d (Qe2 q) r1 a0 f1 (spreadV V (fun t => ∑ b ∈ range d, m02 b * Ke2 t b))
        i j (fun a _ => hr1 a i hi j hj) (fun a _ => hr1 a j hj i hi)
        (by rw [hm0, hm0]; exact spreadV_ge V _ hi hj)

/-! ## Step 1, every method -/

/-- The cost of step 1. -/
def errCost (err V d h : ℕ) : ℕ :=
  if err ≤ 2 then errACost err V d h else if err = 3 then errBCost V d h else errCCost err V d h

/-- **Step 1.** For every method, the run of `errOut` and what it delivers: whenever the method's
    certificate check passes, every row of `EQKE - Ê` spreads by at most `ε_q`. -/
theorem runs_errOut (err V d h off : ℕ) (Eq Ek Qc Kc : ℕ → ℕ → ℚ)
    (hc : off + errCertLen err V d h ≤ env.cert.size) :
    ∃ fEh feps ok, Runs (errOut Interp.counting err V d h off (mat V d Eq) (mat V d Ek)
      (mat h d Qc) (mat h d Kc) (mat d d (mqk h Qc Kc))) env
      (mat V V fEh, vec V feps, ok) (errCost err V d h) ∧
      (ok = true → ErrSpec V (eqke d h Eq Ek Qc Kc) fEh feps) := by
  unfold errCost
  by_cases h2 : err ≤ 2
  · simp only [h2, ↓reduceIte]
    exact runs_errA err V d h off h2 Eq Ek Qc Kc hc
  · by_cases h3 : err = 3
    · subst h3
      simp only [show ¬ (3 ≤ 2) by omega, ↓reduceIte]
      exact runs_errB V d h off Eq Ek Qc Kc
    · simp only [h2, h3, ↓reduceIte]
      exact runs_errC err V d h off (by omega) Eq Ek Qc Kc hc

end GrossSub
