import Candidate.TabSpec2
import Candidate.Checker

/-!
# Specifications of the group stage's building blocks (`lbProdM`, `allM`, `minRangeM`, `hM`, `expAt`,
tables with a predicate per entry).
-/

namespace Candidate.Checker
open CompactCheck Candidate.Loops Candidate.Tables Candidate.Formula Finset

section
variable {env : Env}

/-- `tableM` with a predicate per entry. -/
theorem spec_tableM' {f : Nat → CostM Q} {P : Nat → Q → Prop} (hf : ∀ i, Spec env (f i) (P i)) :
    ∀ (n i : Nat) (arr : Array Q),
      Spec env (tableM Interp.counting f n i arr) fun arr' =>
        ∃ l : List Q, arr'.toList = arr.toList ++ l ∧ l.length = n ∧ ∀ k (hk : k < l.length), P (i + k) l[k]
  | 0, i, arr => by
    simp only [tableM]
    exact spec_pure ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n+1, i, arr => by
    show Spec env (f i >>= fun v => tableM Interp.counting f n (i+1) (arr.push v)) _
    refine spec_bind (hf i) fun v hv => ?_
    refine spec_mono ?_ (spec_tableM' hf n (i+1) (arr.push v))
    intro arr' ⟨l, hl, hlen, hP⟩
    refine ⟨v :: l, ?_, by simp [hlen], ?_⟩
    · rw [hl, Array.toList_push, List.append_assoc, List.singleton_append]
    · intro k hk
      cases k with
      | zero => simpa using hv
      | succ k =>
        have := hP k (by simpa using hk)
        simp only [List.getElem_cons_succ]
        rw [show i + (k + 1) = i + 1 + k by omega]
        exact this

/-- Reading a table built from the empty array with a predicate per entry. -/
theorem tableM'_getD {arr : Array Q} {l : List Q} {P : Nat → Q → Prop} (hl : arr.toList = [] ++ l)
    (hP : ∀ k (hk : k < l.length), P k l[k]) {k : Nat} (hk : k < l.length) : P k (arr.getD k ⟨0⟩) := by
  rw [List.nil_append] at hl
  rw [getD_val_of_list hl hk]
  exact hP k hk

theorem spec_lbProdM (lo hi h : Q) :
    Spec env (lbProdM Interp.counting lo hi h) fun v => v.val = min (lo.val * h.val) (hi.val * h.val) := by
  unfold lbProdM
  refine spec_bind (spec_muladd "" _ lo h) fun a ha => ?_
  refine spec_bind (spec_muladd "" _ hi h) fun b hb => ?_
  refine spec_mono ?_ (spec_min "" a b)
  intro v hv
  rw [hv, ha, hb]
  show min ((0 : ℚ) + _) ((0 : ℚ) + _) = _
  rw [zero_add, zero_add]

/-- The interval product is below the real product. -/
theorem lbProd_cast_le {lo hi h : ℚ} {e : ℝ} (h1 : (lo : ℝ) ≤ e) (h2 : e ≤ hi) :
    ((min (lo * h) (hi * h) : ℚ) : ℝ) ≤ e * (h : ℝ) := by
  rw [Rat.cast_min, Rat.cast_mul, Rat.cast_mul]
  exact lbProd_le h1 h2

theorem spec_allM {f : Nat → CostM Bool} {P : Nat → Prop} (hf : ∀ j, Spec env (f j) fun b => b = true → P j) :
    ∀ (n : Nat) (acc : Bool),
      Spec env (allM Interp.counting f n acc) fun b => b = true → acc = true ∧ ∀ j < n, P j
  | 0, acc => by
    simp only [allM]
    exact spec_pure fun h => ⟨h, fun j hj => absurd hj (Nat.not_lt_zero _)⟩
  | n+1, acc => by
    show Spec env (f n >>= fun b => Interp.counting.band "" acc b >>= fun acc' => allM Interp.counting f n acc') _
    refine spec_bind (hf n) fun b hb => ?_
    refine spec_bind (spec_band "" acc b) fun acc' hacc => ?_
    refine spec_mono ?_ (spec_allM hf n acc')
    intro v hv htrue
    obtain ⟨h1, h2⟩ := hv htrue
    rw [hacc] at h1
    simp only [Bool.and_eq_true] at h1
    refine ⟨h1.1, fun j hj => ?_⟩
    by_cases hjn : j = n
    · subst hjn; exact hb h1.2
    · exact h2 j (by omega)

theorem spec_minRangeM {f : Nat → CostM Q} {g : Nat → ℝ} (t0 : Nat) : ∀ (n : Nat),
    (∀ t, t0 ≤ t → t < t0 + max n 1 → Spec env (f t) fun v => (v.val : ℝ) ≤ g t) →
      Spec env (minRangeM Interp.counting f t0 n) fun v => ∀ t, t0 ≤ t → t < t0 + max n 1 → (v.val : ℝ) ≤ g t
  | 0, hf => by
    simp only [minRangeM]
    refine spec_mono ?_ (hf t0 le_rfl (by omega))
    intro v hv t h1 h2
    have : t = t0 := by omega
    subst this; exact hv
  | 1, hf => by
    simp only [minRangeM]
    refine spec_mono ?_ (hf t0 le_rfl (by omega))
    intro v hv t h1 h2
    have : t = t0 := by omega
    subst this; exact hv
  | n+2, hf => by
    show Spec env (minRangeM Interp.counting f t0 (n+1) >>= fun acc => f (t0+n+1) >>= fun v =>
      CostM.qmin "" acc v) _
    refine spec_bind (spec_minRangeM t0 (n+1) fun t h1 h2 => hf t h1 (by omega)) fun acc hacc => ?_
    refine spec_bind (hf (t0+n+1) (by omega) (by omega)) fun v hv => ?_
    refine spec_mono ?_ (spec_min "" acc v)
    intro r hr t h1 h2
    rw [hr]
    by_cases ht : t = t0 + n + 1
    · subst ht
      rw [Rat.cast_min]
      exact le_trans (min_le_right _ _) hv
    · rw [Rat.cast_min]
      exact le_trans (min_le_left _ _) (hacc t h1 (by omega))

theorem spec_hM (tabs : Tabs Interp.counting) (cpr : Array Q) (m i t j : Nat) :
    Spec env (hM Interp.counting tabs cpr m i t j) fun v =>
      v.val = ((tabs.ov.getD ((i*64+t)*64+m) ⟨0⟩).val - (tabs.ov.getD ((i*64+t)*64+j) ⟨0⟩).val) -
        (cpr.getD j ⟨0⟩).val := by
  unfold hM
  refine spec_bind (spec_sub "" _ _) fun d hd => ?_
  refine spec_mono ?_ (spec_sub "" d _)
  intro v hv
  rw [hv, hd]

theorem spec_expAt (tabs : Tabs Interp.counting) (K : Q) (t3 i t : Nat) :
    Spec env (expAt Interp.counting tabs K t3 i t) fun p =>
      (p.1.val : ℝ) ≤ Real.exp (((tabs.s.getD ((t3*4+i)*64+t) ⟨0⟩).val - K.val : ℚ)) ∧
      Real.exp (((tabs.s.getD ((t3*4+i)*64+t) ⟨0⟩).val - K.val : ℚ)) ≤ p.2.val := by
  unfold expAt
  refine spec_bind (spec_sub "" _ K) fun d hd => ?_
  refine spec_mono ?_ (spec_exp "" d)
  intro p hp
  rw [hd] at hp
  exact hp

end

/-- The real term of position `k` with token `t`, against logit `j`, in group `(t3, m)` with shift `K`. -/
noncomputable def T (E P WQ WK WV WO U C : Tensor ℚ) (t3 m : Nat) (K : ℚ) (k t j : Nat) : ℝ :=
  Real.exp ((SQ E P WQ WK C t3 k t - K : ℚ) : ℝ) *
    (((DmQ E P U t3 m + OVQ E P WV WO U k t m) - (DmQ E P U t3 j + OVQ E P WV WO U k t j) : ℚ) : ℝ)

section
variable {env : Env} {E P WQ WK WV WO U C : Tensor ℚ} {tabs : Tabs Interp.counting}

/-- The `t = m` term of position `i = k/64` against `j = k%64`. -/
theorem spec_termEntry (hT : TabsOk E P WQ WK WV WO U C tabs) {t3 m a : Nat} {K : ℚ} (hm : m < 64)
    (ham : a ≤ m) {cpr exlo exhi : Array Q}
    (hcpr : ∀ j < 64, (cpr.getD j ⟨0⟩).val = DmQ E P U t3 j - DmQ E P U t3 m)
    (hexlo : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      ((exlo.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ) ≤ Real.exp ((SQ E P WQ WK C t3 i t - K : ℚ) : ℝ))
    (hexhi : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      Real.exp ((SQ E P WQ WK C t3 i t - K : ℚ) : ℝ) ≤ ((exhi.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ))
    (k t : Nat) (hta : a ≤ t) (htm : t ≤ m) :
    Spec env (do
        let h ← hM Interp.counting tabs cpr m (k / 64) t (k % 64)
        lbProdM Interp.counting (exlo.getD (k / 64 * 3 + (t - a)) Interp.counting.zero)
          (exhi.getD (k / 64 * 3 + (t - a)) Interp.counting.zero) h)
      fun v => k < 192 → (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K (k / 64) t (k % 64) := by
  refine spec_bind (spec_hM tabs cpr m (k / 64) t (k % 64)) fun h hh => ?_
  refine spec_mono ?_ (spec_lbProdM _ _ h)
  intro v hv hk
  have hi : k / 64 < 3 := by omega
  have hj : k % 64 < 64 := by omega
  have hh' : h.val = (DmQ E P U t3 m + OVQ E P WV WO U (k / 64) t m) -
      (DmQ E P U t3 (k % 64) + OVQ E P WV WO U (k / 64) t (k % 64)) := by
    rw [hh, hT.ov _ _ _ (by omega) (by omega) hm, hT.ov _ _ _ (by omega) (by omega) hj, hcpr _ hj]
    ring
  rw [hv, hh']
  exact lbProd_cast_le (hexlo _ t hi hta htm) (hexhi _ t hi hta htm)

/-- The far bound of position `i` against `j`, over the tokens `t < a`. -/
theorem far_entry (hT : TabsOk E P WQ WK WV WO U C tabs) {t3 m a i j : Nat} {K hi : ℚ} (h3 : t3 < 64)
    (hm : m < 64) (hi3 : i < 3) (hj : j < 64) (ha : a ≤ 64) (cprj : ℚ) (hcprj : cprj = DmQ E P U t3 j - DmQ E P U t3 m)
    (hhi : Real.exp (((tabs.spre.getD ((t3 * 3 + i) * 65 + a) ⟨0⟩).val - K : ℚ) : ℝ) ≤ hi)
    (t : Nat) (ht : t < a) :
    ((0 + -hi * max 0 (cprj + ((tabs.ovmax.getD ((i * 64 + j) * 65 + a) ⟨0⟩).val -
        (tabs.ovmin.getD ((i * 64 + m) * 65 + a) ⟨0⟩).val)) : ℚ) : ℝ) ≤
      T E P WQ WK WV WO U C t3 m K i t j := by
  have ht64 : t < 64 := by omega
  unfold T
  rw [zero_add, Rat.cast_mul, Rat.cast_neg, Rat.cast_max, Rat.cast_zero]
  apply far_le (Real.exp_pos _).le
  · rw [Rat.cast_sub] at hhi ⊢
    refine exp_far_le ?_ hhi
    have := hT.spre t3 i a t h3 hi3 ha ht
    rw [hT.s t3 i t h3 (by omega) ht64] at this
    exact (Rat.cast_le (K := ℝ)).mpr this
  · have h1 := hT.ovmax i j a t hi3 hj ha ht
    have h2 := hT.ovmin i m a t hi3 hm ha ht
    rw [hT.ov i t j (by omega) ht64 hj] at h1
    rw [hT.ov i t m (by omega) ht64 hm] at h2
    have h1' := (Rat.cast_le (K := ℝ)).mpr h1
    have h2' := (Rat.cast_le (K := ℝ)).mpr h2
    rw [hcprj]
    push_cast
    linarith

/-- The entry of `Fm`: a lower bound over the tokens `t < m` of position `i = k/64` against `j = k%64`. -/
theorem spec_FmEntry (hT : TabsOk E P WQ WK WV WO U C tabs) {t3 m a : Nat} {K : ℚ} (h3 : t3 < 64) (hm : m < 64)
    (ham : a + 1 ≤ m) {cpr exlo exhi negEfar : Array Q}
    (hcpr : ∀ j < 64, (cpr.getD j ⟨0⟩).val = DmQ E P U t3 j - DmQ E P U t3 m)
    (hexlo : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      ((exlo.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ) ≤ Real.exp ((SQ E P WQ WK C t3 i t - K : ℚ) : ℝ))
    (hexhi : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      Real.exp ((SQ E P WQ WK C t3 i t - K : ℚ) : ℝ) ≤ ((exhi.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ))
    (hneg : ∀ i < 3, a ≠ 0 → ∃ hi : ℚ, (negEfar.getD i ⟨0⟩).val = -hi ∧
      Real.exp (((tabs.spre.getD ((t3 * 3 + i) * 65 + a) ⟨0⟩).val - K : ℚ) : ℝ) ≤ hi)
    (k : Nat) :
    Spec env (do
        let near ← minRangeM Interp.counting (fun t => do
          let h ← hM Interp.counting tabs cpr m (k / 64) t (k % 64)
          lbProdM Interp.counting (exlo.getD (k / 64 * 3 + (t - a)) Interp.counting.zero)
            (exhi.getD (k / 64 * 3 + (t - a)) Interp.counting.zero) h) a (m - a)
        if a = 0 then pure near else do
          let n1 ← Interp.counting.sub "" (tabs.ovmax.getD ((k / 64 * 64 + k % 64) * 65 + a) Interp.counting.zero)
            (tabs.ovmin.getD ((k / 64 * 64 + m) * 65 + a) Interp.counting.zero)
          let n2 ← Interp.counting.add "" (cpr.getD (k % 64) Interp.counting.zero) n1
          let n3 ← Interp.counting.max "" Interp.counting.zero n2
          let far ← Interp.counting.muladd "" Interp.counting.zero (negEfar.getD (k / 64) Interp.counting.zero) n3
          Interp.counting.min "" near far)
      fun v => k < 192 → ∀ t < m, (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K (k / 64) t (k % 64) := by
  by_cases hk : k < 192
  swap
  · exact fun _ _ _ _ h => absurd h hk
  have hmin := spec_minRangeM (env := env) (g := fun t => T E P WQ WK WV WO U C t3 m K (k / 64) t (k % 64)) a (m - a)
    (f := fun t => do
      let h ← hM Interp.counting tabs cpr m (k / 64) t (k % 64)
      lbProdM Interp.counting (exlo.getD (k / 64 * 3 + (t - a)) Interp.counting.zero)
        (exhi.getD (k / 64 * 3 + (t - a)) Interp.counting.zero) h)
    (fun t h1 h2 => spec_mono (fun v hv => hv hk) (spec_termEntry hT hm (by omega) hcpr hexlo hexhi k t h1 (by omega)))
  refine spec_bind hmin fun near hnear => ?_
  by_cases ha0 : a = 0
  · rw [if_pos ha0]
    refine spec_pure fun _ t ht => hnear t (by omega) (by omega)
  · rw [if_neg ha0]
    refine spec_bind (spec_sub "" _ _) fun n1 hn1 => ?_
    refine spec_bind (spec_add "" _ n1) fun n2 hn2 => ?_
    refine spec_bind (spec_max "" _ n2) fun n3 hn3 => ?_
    refine spec_bind (spec_muladd "" _ _ n3) fun far hfar => ?_
    refine spec_mono ?_ (spec_min "" near far)
    intro v hv _ t ht
    rw [hv, Rat.cast_min]
    by_cases hta : a ≤ t
    · exact le_trans (min_le_left _ _) (hnear t hta (by omega))
    · refine le_trans (min_le_right _ _) ?_
      obtain ⟨hi, hneg1, hneg2⟩ := hneg (k / 64) (by omega) ha0
      rw [hfar, hn3, hn2, hn1, hneg1]
      exact far_entry hT h3 hm (by omega) (by omega) (by omega) _ (hcpr _ (by omega)) hneg2 t (by omega)

/-- The entry of `fx3`: position 3 with token `t3`. -/
theorem spec_fx3Entry (hT : TabsOk E P WQ WK WV WO U C tabs) {t3 m : Nat} {K : ℚ} (h3 : t3 < 64) (hm : m < 64)
    {cpr : Array Q} {e3 : Q × Q}
    (hcpr : ∀ j < 64, (cpr.getD j ⟨0⟩).val = DmQ E P U t3 j - DmQ E P U t3 m)
    (he3 : (e3.1.val : ℝ) ≤ Real.exp (((tabs.s.getD ((t3 * 4 + 3) * 64 + t3) ⟨0⟩).val - K : ℚ)) ∧
      Real.exp (((tabs.s.getD ((t3 * 4 + 3) * 64 + t3) ⟨0⟩).val - K : ℚ)) ≤ e3.2.val)
    (j : Nat) :
    Spec env (do
        let h ← hM Interp.counting tabs cpr m 3 t3 j
        lbProdM Interp.counting e3.1 e3.2 h)
      fun v => j < 64 → (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K 3 t3 j := by
  refine spec_bind (spec_hM tabs cpr m 3 t3 j) fun h hh => ?_
  refine spec_mono ?_ (spec_lbProdM _ _ h)
  intro v hv hj
  have hh' : h.val = (DmQ E P U t3 m + OVQ E P WV WO U 3 t3 m) -
      (DmQ E P U t3 j + OVQ E P WV WO U 3 t3 j) := by
    rw [hh, hT.ov _ _ _ (by omega) h3 hm, hT.ov _ _ _ (by omega) h3 hj, hcpr _ hj]
    ring
  rw [hv, hh']
  have hs := hT.s t3 3 t3 h3 (by omega) h3
  rw [hs] at he3
  exact lbProd_cast_le he3.1 he3.2

/-- The token range of position `i` in the group with the last maximum at `istar`. -/
def InRange (m istar i t : Nat) : Prop := if i = istar then t = m else if i < istar then t ≤ m else t < m

theorem cSel_le {term Fm Fm1 : Array Q} {t3 m : Nat} {K : ℚ} {istar i j t : Nat} (hi : i < 3)
    (hterm : ((term.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i m j)
    (hFm : ∀ t < m, ((Fm.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i t j)
    (hFm1 : ∀ t ≤ m, ((Fm1.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i t j)
    (hr : InRange m istar i t) :
    ((cSel Interp.counting term Fm Fm1 istar i j).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i t j := by
  unfold cSel InRange at *
  by_cases h1 : i = istar
  · rw [if_pos h1] at hr ⊢
    subst hr
    exact hterm
  · rw [if_neg h1] at hr ⊢
    by_cases h2 : i < istar
    · rw [if_pos h2] at hr ⊢
      exact hFm1 t hr
    · rw [if_neg h2] at hr ⊢
      exact hFm t hr

/-- `okOfM` true: every `j ≠ m` has a positive sum over any tokens of the group. -/
theorem spec_okOfM {term Fm Fm1 fx3 : Array Q} {t3 m : Nat} {K : ℚ} (istar : Nat)
    (hterm : ∀ i j, i < 3 → j < 64 → ((term.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i m j)
    (hFm : ∀ i j, i < 3 → j < 64 → ∀ t < m, ((Fm.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i t j)
    (hFm1 : ∀ i j, i < 3 → j < 64 → ∀ t ≤ m, ((Fm1.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i t j)
    (hfx3 : ∀ j < 64, ((fx3.getD j ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K 3 t3 j) :
    Spec env (okOfM Interp.counting term Fm Fm1 fx3 m istar) fun b => b = true →
      ∀ j < 64, j ≠ m → ∀ t0 t1 t2, InRange m istar 0 t0 → InRange m istar 1 t1 → InRange m istar 2 t2 →
        0 < T E P WQ WK WV WO U C t3 m K 0 t0 j + T E P WQ WK WV WO U C t3 m K 1 t1 j +
          T E P WQ WK WV WO U C t3 m K 2 t2 j + T E P WQ WK WV WO U C t3 m K 3 t3 j := by
  unfold okOfM
  refine spec_mono (fun b hb htrue j hj => (hb htrue).2 j hj hj) (spec_allM (P := fun j => j < 64 → j ≠ m → ∀ t0 t1 t2,
    InRange m istar 0 t0 → InRange m istar 1 t1 → InRange m istar 2 t2 →
    0 < T E P WQ WK WV WO U C t3 m K 0 t0 j + T E P WQ WK WV WO U C t3 m K 1 t1 j +
      T E P WQ WK WV WO U C t3 m K 2 t2 j + T E P WQ WK WV WO U C t3 m K 3 t3 j) ?_ 64 true)
  intro j
  by_cases hjm : j = m
  · rw [if_pos hjm]
    exact spec_pure fun _ _ h => absurd hjm h
  · rw [if_neg hjm]
    by_cases hj : j < 64
    swap
    · exact fun _ _ _ _ _ hj' => absurd hj' hj
    refine spec_bind (spec_add "" _ _) fun L0 hL0 => ?_
    refine spec_bind (spec_add "" L0 _) fun L1 hL1 => ?_
    refine spec_bind (spec_add "" L1 _) fun L2 hL2 => ?_
    refine spec_mono ?_ (spec_lt "" _ L2)
    intro b hb htrue _ _ t0 t1 t2 h0 h1 h2
    rw [hb] at htrue
    have hpos : (0 : ℚ) < L2.val := by simpa using htrue
    have hpos' : (0 : ℝ) < (L2.val : ℝ) := by exact_mod_cast hpos
    rw [hL2, hL1, hL0] at hpos'
    push_cast at hpos'
    have c0 := cSel_le (by omega) (hterm 0 j (by omega) hj) (hFm 0 j (by omega) hj) (hFm1 0 j (by omega) hj) h0
    have c1 := cSel_le (by omega) (hterm 1 j (by omega) hj) (hFm 1 j (by omega) hj) (hFm1 1 j (by omega) hj) h1
    have c2 := cSel_le (by omega) (hterm 2 j (by omega) hj) (hFm 2 j (by omega) hj) (hFm1 2 j (by omega) hj) h2
    have c3 := hfx3 j hj
    linarith

/-- A table built from the empty array, read entry by entry. -/
theorem spec_table0 {f : Nat → CostM Q} {P : Nat → Q → Prop} (hf : ∀ i, Spec env (f i) (P i)) (n : Nat) :
    Spec env (tableM Interp.counting f n 0 (E0 Interp.counting)) fun arr' => ∀ k < n, P k (arr'.getD k ⟨0⟩) := by
  refine spec_mono ?_ (spec_tableM' hf n 0 (E0 Interp.counting))
  intro arr' ⟨l, hl, hlen, hP⟩ k hk
  have hk' : k < l.length := by omega
  have := hP k hk'
  rw [Nat.zero_add] at this
  simp only [E0, List.nil_append] at hl
  rw [getD_val_of_list hl hk']
  exact this

/-- The flags of the group `(t3, m)`: a true flag at `istar` means every input of the group `(t3, m, istar)`
    has a positive shifted margin against every `j ≠ m`. -/
theorem spec_groupFlagsK (hT : TabsOk E P WQ WK WV WO U C tabs) (t3 m : Nat) (K : Q) (a : Nat)
    (h3 : t3 < 64) (hm : m < 64) (ham : a + 1 ≤ m) (ha2 : m ≤ a + 2) :
    Spec env (groupFlagsK Interp.counting tabs t3 m K a) fun l =>
      l.length = 4 ∧ ∀ istar, istar < 4 → l.getD istar false = true →
        ∀ j < 64, j ≠ m → ∀ t0 t1 t2, InRange m istar 0 t0 → InRange m istar 1 t1 → InRange m istar 2 t2 →
          0 < T E P WQ WK WV WO U C t3 m K.val 0 t0 j + T E P WQ WK WV WO U C t3 m K.val 1 t1 j +
            T E P WQ WK WV WO U C t3 m K.val 2 t2 j + T E P WQ WK WV WO U C t3 m K.val 3 t3 j := by
  unfold groupFlagsK
  -- cpr
  refine spec_bind (spec_table0 (P := fun j v => v.val = (tabs.dm.getD (t3 * 64 + j) ⟨0⟩).val - (tabs.dm.getD (t3 * 64 + m) ⟨0⟩).val)
    (fun j => spec_sub "" _ _) 64) fun cpr hcpr0 => ?_
  have hcpr : ∀ j < 64, (cpr.getD j ⟨0⟩).val = DmQ E P U t3 j - DmQ E P U t3 m := by
    intro j hj
    rw [hcpr0 j hj, hT.dm t3 j h3 hj, hT.dm t3 m h3 hm]
  -- exlo
  refine spec_bind (spec_table0 (P := fun k v => a + k % 3 ≤ m →
      (v.val : ℝ) ≤ Real.exp (((tabs.s.getD ((t3 * 4 + k / 3) * 64 + (a + k % 3)) ⟨0⟩).val - K.val : ℚ))) ?_ 9)
      fun exlo hP1 => ?_
  · intro k
    by_cases hk : a + k % 3 ≤ m
    · rw [if_pos hk]
      exact spec_bind (spec_expAt tabs K t3 (k / 3) (a + k % 3)) fun p hp => spec_pure fun _ => hp.1
    · rw [if_neg hk]
      exact spec_pure fun h => absurd h hk
  have hexlo : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      ((exlo.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ) ≤ Real.exp ((SQ E P WQ WK C t3 i t - K.val : ℚ) : ℝ) := by
    intro i t hi hat htm
    have := hP1 (i * 3 + (t - a)) (by omega)
    have e1 : (i * 3 + (t - a)) / 3 = i := by omega
    have e2 : a + (i * 3 + (t - a)) % 3 = t := by omega
    rw [e1, e2, hT.s t3 i t h3 (by omega) (by omega)] at this
    exact this htm
  -- exhi
  refine spec_bind (spec_table0 (P := fun k v => a + k % 3 ≤ m →
      Real.exp (((tabs.s.getD ((t3 * 4 + k / 3) * 64 + (a + k % 3)) ⟨0⟩).val - K.val : ℚ)) ≤ (v.val : ℝ)) ?_ 9)
      fun exhi hP2 => ?_
  · intro k
    by_cases hk : a + k % 3 ≤ m
    · rw [if_pos hk]
      exact spec_bind (spec_expAt tabs K t3 (k / 3) (a + k % 3)) fun p hp => spec_pure fun _ => hp.2
    · rw [if_neg hk]
      exact spec_pure fun h => absurd h hk
  have hexhi : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      Real.exp ((SQ E P WQ WK C t3 i t - K.val : ℚ) : ℝ) ≤ ((exhi.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ) := by
    intro i t hi hat htm
    have := hP2 (i * 3 + (t - a)) (by omega)
    have e1 : (i * 3 + (t - a)) / 3 = i := by omega
    have e2 : a + (i * 3 + (t - a)) % 3 = t := by omega
    rw [e1, e2, hT.s t3 i t h3 (by omega) (by omega)] at this
    exact this htm
  -- e3
  refine spec_bind (spec_expAt tabs K t3 3 t3) fun e3 he3 => ?_
  -- negEfar
  refine spec_bind (spec_table0 (P := fun i v => a ≠ 0 → ∃ hi : ℚ, v.val = -hi ∧
      Real.exp (((tabs.spre.getD ((t3 * 3 + i) * 65 + a) ⟨0⟩).val - K.val : ℚ) : ℝ) ≤ hi) ?_ 3)
      fun negEfar hP3 => ?_
  · intro i
    by_cases ha0 : a = 0
    · rw [if_pos ha0]
      exact spec_pure fun h => absurd ha0 h
    · rw [if_neg ha0]
      refine spec_bind (spec_sub "" _ K) fun d hd => ?_
      refine spec_bind (spec_exp "" d) fun p hp => ?_
      refine spec_mono ?_ (spec_neg "" p.2)
      intro v hv _
      refine ⟨p.2.val, hv, ?_⟩
      rw [hd] at hp
      exact hp.2
  have hneg : ∀ i < 3, a ≠ 0 → ∃ hi : ℚ, (negEfar.getD i ⟨0⟩).val = -hi ∧
      Real.exp (((tabs.spre.getD ((t3 * 3 + i) * 65 + a) ⟨0⟩).val - K.val : ℚ) : ℝ) ≤ hi := by
    intro i hi
    exact hP3 i hi
  -- term
  refine spec_bind (spec_table0 (P := fun k v => k < 192 →
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) m (k % 64))
      (fun k => spec_termEntry hT hm (by omega) hcpr hexlo hexhi k m (by omega) le_rfl) 192)
      fun term hP4 => ?_
  have htermk : ∀ k < 192, ((term.getD k ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) m (k % 64) :=
    fun k hk => hP4 k hk hk
  have hterm : ∀ i j, i < 3 → j < 64 → ((term.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val i m j := by
    intro i j hi hj
    have := htermk (i * 64 + j) (by omega)
    have e1 : (i * 64 + j) / 64 = i := by omega
    have e2 : (i * 64 + j) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  -- Fm
  refine spec_bind (spec_table0 (P := fun k v => k < 192 → ∀ t < m,
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) t (k % 64))
      (fun k => spec_FmEntry hT h3 hm ham hcpr hexlo hexhi hneg k) 192)
      fun Fm hP5 => ?_
  have hFmk : ∀ k < 192, ∀ t < m, ((Fm.getD k ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) t (k % 64) :=
    fun k hk => hP5 k hk hk
  have hFm : ∀ i j, i < 3 → j < 64 → ∀ t < m,
      ((Fm.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val i t j := by
    intro i j hi hj
    have := hFmk (i * 64 + j) (by omega)
    have e1 : (i * 64 + j) / 64 = i := by omega
    have e2 : (i * 64 + j) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  -- Fm1
  refine spec_bind (spec_table0 (P := fun k v => k < 192 → ∀ t ≤ m,
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) t (k % 64)) ?_ 192)
      fun Fm1 hP6 => ?_
  · intro k
    refine spec_mono ?_ (spec_min "" _ _)
    intro v hv hk t ht
    rw [hv, Rat.cast_min]
    by_cases htm : t < m
    · exact le_trans (min_le_left _ _) (hFmk k hk t htm)
    · have : t = m := by omega
      subst this
      exact le_trans (min_le_right _ _) (htermk k hk)
  have hFm1 : ∀ i j, i < 3 → j < 64 → ∀ t ≤ m,
      ((Fm1.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val i t j := by
    intro i j hi hj
    have := hP6 (i * 64 + j) (by omega) (by omega)
    have e1 : (i * 64 + j) / 64 = i := by omega
    have e2 : (i * 64 + j) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  -- fx3
  refine spec_bind (spec_table0 (P := fun j v => j < 64 →
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val 3 t3 j)
      (fun j => spec_fx3Entry hT h3 hm hcpr he3 j) 64) fun fx3 hP7 => ?_
  have hfx3 : ∀ j < 64, ((fx3.getD j ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val 3 t3 j :=
    fun j hj => hP7 j hj hj
  -- the flags
  by_cases h3m : t3 = m
  · rw [if_pos h3m]
    refine spec_bind (spec_okOfM 3 hterm hFm hFm1 hfx3) fun ok3 hok3 => ?_
    refine spec_pure ⟨rfl, ?_⟩
    intro istar hi htrue
    match istar with
    | 0 => simp at htrue
    | 1 => simp at htrue
    | 2 => simp at htrue
    | 3 => exact hok3 (by simpa using htrue)
  · rw [if_neg h3m]
    refine spec_bind (spec_okOfM 0 hterm hFm hFm1 hfx3) fun ok0 hok0 => ?_
    refine spec_bind (spec_okOfM 1 hterm hFm hFm1 hfx3) fun ok1 hok1 => ?_
    refine spec_bind (spec_okOfM 2 hterm hFm hFm1 hfx3) fun ok2 hok2 => ?_
    refine spec_pure ⟨rfl, ?_⟩
    intro istar hi htrue
    match istar with
    | 0 => exact hok0 (by simpa using htrue)
    | 1 => exact hok1 (by simpa using htrue)
    | 2 => exact hok2 (by simpa using htrue)
    | 3 => simp at htrue

end

end Candidate.Checker
