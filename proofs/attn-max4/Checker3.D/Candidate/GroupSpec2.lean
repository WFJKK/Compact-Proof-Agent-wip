import Candidate.GroupSpec
import Candidate.Checker2

/-!
# Specifications of the slack-threshold group stage (Checker2): `lo * h` entries are below the real
term up to the slack `d * Hb` (`d`: the widest exp interval, `Hb`: a bound on `|h|`), and the test
`theta < L_j` with `theta = 4 * d * Hb` gives a positive margin.
-/

namespace Candidate.Checker2
open CompactCheck Candidate.Loops Candidate.Tables Candidate.Formula Candidate.Checker Finset

section
variable {env : Env}

theorem spec_loProdM (lo h : Q) :
    Spec env (loProdM Interp.counting lo h) fun v => v.val = lo.val * h.val := by
  unfold loProdM
  refine spec_mono ?_ (spec_muladd "" _ lo h)
  intro v hv
  rw [hv]
  show (0 : ℚ) + _ = _
  rw [zero_add]

/-- `lo * h ≤ e * h + d * Hb` when `lo ≤ e ≤ hi`, `hi - lo ≤ d` and `|h| ≤ Hb`. -/
theorem loProd_cast_le {lo hi h d Hb : ℚ} {e : ℝ} (h1 : (lo : ℝ) ≤ e) (h2 : e ≤ hi) (hd : hi - lo ≤ d)
    (hH : |h| ≤ Hb) : ((lo * h : ℚ) : ℝ) ≤ e * (h : ℝ) + ((d * Hb : ℚ) : ℝ) := by
  push_cast
  have hd' : (hi : ℝ) - lo ≤ d := by exact_mod_cast hd
  have hH' : |(h : ℝ)| ≤ Hb := by exact_mod_cast hH
  have h4 : (lo - e) * (h : ℝ) ≤ |(lo : ℝ) - e| * |(h : ℝ)| := by
    calc (lo - e) * (h : ℝ) ≤ |(lo - e) * (h : ℝ)| := le_abs_self _
      _ = |(lo : ℝ) - e| * |(h : ℝ)| := abs_mul _ _
  have h5 : |(lo : ℝ) - e| ≤ d := by
    rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  have h6 : |(lo : ℝ) - e| * |(h : ℝ)| ≤ d * Hb :=
    mul_le_mul h5 hH' (abs_nonneg _) (le_trans (abs_nonneg _) h5)
  nlinarith

/-- `boundH`: four times a bound on every `|h|`. -/
theorem spec_boundH {E P WQ WK WV WO U C : Tensor ℚ} {tabs : Tabs Interp.counting}
    (hT : TabsOk E P WQ WK WV WO U C tabs) :
    Spec env (boundH Interp.counting tabs) fun H4 => ∃ Hb : ℚ, H4.val = 4 * Hb ∧
      ∀ t3 m i t j, t3 < 64 → m < 64 → i < 4 → t < 64 → j < 64 →
        |(DmQ E P U t3 m + OVQ E P WV WO U i t m) - (DmQ E P U t3 j + OVQ E P WV WO U i t j)| ≤ Hb := by
  unfold boundH
  refine spec_bind (spec_maxM _ 16384 _) fun ovMax hovMax => ?_
  refine spec_bind (spec_minM _ 16384 _) fun ovMin hovMin => ?_
  refine spec_bind (spec_maxM _ 4096 _) fun dmMax hdmMax => ?_
  refine spec_bind (spec_minM _ 4096 _) fun dmMin hdmMin => ?_
  refine spec_bind (spec_sub "" _ _) fun r1 hr1 => ?_
  refine spec_bind (spec_sub "" _ _) fun r2 hr2 => ?_
  refine spec_bind (spec_add "" _ _) fun h hh => ?_
  refine spec_bind (spec_lit "" 4) fun four hfour => ?_
  refine spec_mono ?_ (spec_muladd "" _ four h)
  intro v hv
  refine ⟨h.val, ?_, ?_⟩
  · rw [hv, hfour]
    show (0 : ℚ) + ((4 : ℕ) : ℚ) * h.val = 4 * h.val
    push_cast
    ring
  · intro t3 m i t j h3 hm hi ht hj
    have e1 := hT.ov i t m hi ht hm
    have e2 := hT.ov i t j hi ht hj
    have e3 := hT.dm t3 m h3 hm
    have e4 := hT.dm t3 j h3 hj
    have b1 : (tabs.ov.getD ((i*64+t)*64+m) ⟨0⟩).val ≤ ovMax.val := hovMax.2 _ (by omega)
    have b2 : ovMin.val ≤ (tabs.ov.getD ((i*64+t)*64+m) ⟨0⟩).val := hovMin.2 _ (by omega)
    have b3 : (tabs.ov.getD ((i*64+t)*64+j) ⟨0⟩).val ≤ ovMax.val := hovMax.2 _ (by omega)
    have b4 : ovMin.val ≤ (tabs.ov.getD ((i*64+t)*64+j) ⟨0⟩).val := hovMin.2 _ (by omega)
    have c1 : (tabs.dm.getD (t3*64+m) ⟨0⟩).val ≤ dmMax.val := hdmMax.2 _ (by omega)
    have c2 : dmMin.val ≤ (tabs.dm.getD (t3*64+m) ⟨0⟩).val := hdmMin.2 _ (by omega)
    have c3 : (tabs.dm.getD (t3*64+j) ⟨0⟩).val ≤ dmMax.val := hdmMax.2 _ (by omega)
    have c4 : dmMin.val ≤ (tabs.dm.getD (t3*64+j) ⟨0⟩).val := hdmMin.2 _ (by omega)
    rw [e1] at b1 b2
    rw [e2] at b3 b4
    rw [e3] at c1 c2
    rw [e4] at c3 c4
    rw [hh, hr1, hr2, abs_le]
    constructor <;> linarith

end

section
variable {env : Env} {E P WQ WK WV WO U C : Tensor ℚ} {tabs : Tabs Interp.counting}

/-- The `t = m` term of position `i = k/64` against `j = k%64`, up to the slack. -/
theorem spec_termEntry2 (hT : TabsOk E P WQ WK WV WO U C tabs) {t3 m a : Nat} {K d Hb : ℚ} (hm : m < 64)
    (ham : a ≤ m) {cpr exlo exhi : Array Q}
    (hcpr : ∀ j < 64, (cpr.getD j ⟨0⟩).val = DmQ E P U t3 j - DmQ E P U t3 m)
    (hexlo : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      ((exlo.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ) ≤ Real.exp ((SQ E P WQ WK C t3 i t - K : ℚ) : ℝ))
    (hexhi : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      Real.exp ((SQ E P WQ WK C t3 i t - K : ℚ) : ℝ) ≤ ((exhi.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ))
    (hd : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      (exhi.getD (i * 3 + (t - a)) ⟨0⟩).val - (exlo.getD (i * 3 + (t - a)) ⟨0⟩).val ≤ d)
    (hH : ∀ i t j, i < 4 → t < 64 → j < 64 →
      |(DmQ E P U t3 m + OVQ E P WV WO U i t m) - (DmQ E P U t3 j + OVQ E P WV WO U i t j)| ≤ Hb)
    (k t : Nat) (hta : a ≤ t) (htm : t ≤ m) :
    Spec env (do
        let h ← hM Interp.counting tabs cpr m (k / 64) t (k % 64)
        loProdM Interp.counting (exlo.getD (k / 64 * 3 + (t - a)) Interp.counting.zero) h)
      fun v => k < 192 → (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K (k / 64) t (k % 64) + ((d * Hb : ℚ) : ℝ) := by
  refine spec_bind (spec_hM tabs cpr m (k / 64) t (k % 64)) fun h hh => ?_
  refine spec_mono ?_ (spec_loProdM _ h)
  intro v hv hk
  have hi : k / 64 < 3 := by omega
  have hj : k % 64 < 64 := by omega
  have hh' : h.val = (DmQ E P U t3 m + OVQ E P WV WO U (k / 64) t m) -
      (DmQ E P U t3 (k % 64) + OVQ E P WV WO U (k / 64) t (k % 64)) := by
    rw [hh, hT.ov _ _ _ (by omega) (by omega) hm, hT.ov _ _ _ (by omega) (by omega) hj, hcpr _ hj]
    ring
  rw [hv, hh']
  exact loProd_cast_le (hexlo _ t hi hta htm) (hexhi _ t hi hta htm) (hd _ t hi hta htm)
    (hH (k / 64) t (k % 64) (by omega) (by omega) hj)

/-- The entry of `Fm`: a lower bound (up to the slack) over the tokens `t < m`. -/
theorem spec_FmEntry2 (hT : TabsOk E P WQ WK WV WO U C tabs) {t3 m a : Nat} {K d Hb : ℚ} (h3 : t3 < 64) (hm : m < 64)
    (ham : a + 1 ≤ m) (hsl : 0 ≤ d * Hb) {cpr exlo exhi negEfar : Array Q}
    (hcpr : ∀ j < 64, (cpr.getD j ⟨0⟩).val = DmQ E P U t3 j - DmQ E P U t3 m)
    (hexlo : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      ((exlo.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ) ≤ Real.exp ((SQ E P WQ WK C t3 i t - K : ℚ) : ℝ))
    (hexhi : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      Real.exp ((SQ E P WQ WK C t3 i t - K : ℚ) : ℝ) ≤ ((exhi.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ))
    (hd : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      (exhi.getD (i * 3 + (t - a)) ⟨0⟩).val - (exlo.getD (i * 3 + (t - a)) ⟨0⟩).val ≤ d)
    (hH : ∀ i t j, i < 4 → t < 64 → j < 64 →
      |(DmQ E P U t3 m + OVQ E P WV WO U i t m) - (DmQ E P U t3 j + OVQ E P WV WO U i t j)| ≤ Hb)
    (hneg : ∀ i < 3, a ≠ 0 → ∃ hi : ℚ, (negEfar.getD i ⟨0⟩).val = -hi ∧
      Real.exp (((tabs.spre.getD ((t3 * 3 + i) * 65 + a) ⟨0⟩).val - K : ℚ) : ℝ) ≤ hi)
    (k : Nat) :
    Spec env (do
        let near ← minRangeM Interp.counting (fun t => do
          let h ← hM Interp.counting tabs cpr m (k / 64) t (k % 64)
          loProdM Interp.counting (exlo.getD (k / 64 * 3 + (t - a)) Interp.counting.zero) h) a (m - a)
        if a = 0 then pure near else do
          let n1 ← Interp.counting.sub "" (tabs.ovmax.getD ((k / 64 * 64 + k % 64) * 65 + a) Interp.counting.zero)
            (tabs.ovmin.getD ((k / 64 * 64 + m) * 65 + a) Interp.counting.zero)
          let n2 ← Interp.counting.add "" (cpr.getD (k % 64) Interp.counting.zero) n1
          let n3 ← Interp.counting.max "" Interp.counting.zero n2
          let far ← Interp.counting.muladd "" Interp.counting.zero (negEfar.getD (k / 64) Interp.counting.zero) n3
          Interp.counting.min "" near far)
      fun v => k < 192 → ∀ t < m, (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K (k / 64) t (k % 64) + ((d * Hb : ℚ) : ℝ) := by
  by_cases hk : k < 192
  swap
  · exact fun _ _ _ _ h => absurd h hk
  have hsl' : (0 : ℝ) ≤ ((d * Hb : ℚ) : ℝ) := by exact_mod_cast hsl
  have hmin := spec_minRangeM (env := env)
    (g := fun t => T E P WQ WK WV WO U C t3 m K (k / 64) t (k % 64) + ((d * Hb : ℚ) : ℝ)) a (m - a)
    (f := fun t => do
      let h ← hM Interp.counting tabs cpr m (k / 64) t (k % 64)
      loProdM Interp.counting (exlo.getD (k / 64 * 3 + (t - a)) Interp.counting.zero) h)
    (fun t h1 h2 => spec_mono (fun v hv => hv hk)
      (spec_termEntry2 hT hm (by omega) hcpr hexlo hexhi hd hH k t h1 (by omega)))
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
      refine le_trans (far_entry hT h3 hm (by omega) (by omega) (by omega) _ (hcpr _ (by omega)) hneg2 t (by omega)) ?_
      exact le_add_of_nonneg_right hsl'

/-- The entry of `fx3`: position 3 with token `t3`, up to the slack. -/
theorem spec_fx3Entry2 (hT : TabsOk E P WQ WK WV WO U C tabs) {t3 m : Nat} {K d Hb : ℚ} (h3 : t3 < 64) (hm : m < 64)
    {cpr : Array Q} {e3 : Q × Q}
    (hcpr : ∀ j < 64, (cpr.getD j ⟨0⟩).val = DmQ E P U t3 j - DmQ E P U t3 m)
    (he3 : (e3.1.val : ℝ) ≤ Real.exp (((tabs.s.getD ((t3 * 4 + 3) * 64 + t3) ⟨0⟩).val - K : ℚ)) ∧
      Real.exp (((tabs.s.getD ((t3 * 4 + 3) * 64 + t3) ⟨0⟩).val - K : ℚ)) ≤ e3.2.val)
    (hd3 : e3.2.val - e3.1.val ≤ d)
    (hH : ∀ i t j, i < 4 → t < 64 → j < 64 →
      |(DmQ E P U t3 m + OVQ E P WV WO U i t m) - (DmQ E P U t3 j + OVQ E P WV WO U i t j)| ≤ Hb)
    (j : Nat) :
    Spec env (do
        let h ← hM Interp.counting tabs cpr m 3 t3 j
        loProdM Interp.counting e3.1 h)
      fun v => j < 64 → (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K 3 t3 j + ((d * Hb : ℚ) : ℝ) := by
  refine spec_bind (spec_hM tabs cpr m 3 t3 j) fun h hh => ?_
  refine spec_mono ?_ (spec_loProdM _ h)
  intro v hv hj
  have hh' : h.val = (DmQ E P U t3 m + OVQ E P WV WO U 3 t3 m) -
      (DmQ E P U t3 j + OVQ E P WV WO U 3 t3 j) := by
    rw [hh, hT.ov _ _ _ (by omega) h3 hm, hT.ov _ _ _ (by omega) h3 hj, hcpr _ hj]
    ring
  rw [hv, hh']
  have hs := hT.s t3 3 t3 h3 (by omega) h3
  rw [hs] at he3
  exact loProd_cast_le he3.1 he3.2 hd3 (hH 3 t3 j (by omega) h3 hj)

theorem cSel_le' {term Fm Fm1 : Array Q} {g : Nat → Nat → ℝ} {m istar i j t : Nat}
    (hterm : ((term.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ g i m)
    (hFm : ∀ t < m, ((Fm.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ g i t)
    (hFm1 : ∀ t ≤ m, ((Fm1.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ g i t)
    (hr : InRange m istar i t) :
    ((cSel Interp.counting term Fm Fm1 istar i j).val : ℝ) ≤ g i t := by
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
theorem spec_okOfM2 {term Fm Fm1 fx3 : Array Q} {t3 m : Nat} {K : ℚ} {sl : ℝ} (istar : Nat) (theta : Q)
    (htheta : 4 * sl ≤ (theta.val : ℝ))
    (hterm : ∀ i j, i < 3 → j < 64 → ((term.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i m j + sl)
    (hFm : ∀ i j, i < 3 → j < 64 → ∀ t < m, ((Fm.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i t j + sl)
    (hFm1 : ∀ i j, i < 3 → j < 64 → ∀ t ≤ m, ((Fm1.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i t j + sl)
    (hfx3 : ∀ j < 64, ((fx3.getD j ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K 3 t3 j + sl) :
    Spec env (okOfM Interp.counting term Fm Fm1 fx3 theta m istar) fun b => b = true →
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
    refine spec_mono ?_ (spec_lt "" theta L2)
    intro b hb htrue _ _ t0 t1 t2 h0 h1 h2
    rw [hb] at htrue
    have hpos : theta.val < L2.val := by simpa using htrue
    have hpos' : (theta.val : ℝ) < (L2.val : ℝ) := by exact_mod_cast hpos
    rw [hL2, hL1, hL0] at hpos'
    push_cast at hpos'
    have c0 := cSel_le' (g := fun i t => T E P WQ WK WV WO U C t3 m K i t j + sl)
      (hterm 0 j (by omega) hj) (hFm 0 j (by omega) hj) (hFm1 0 j (by omega) hj) h0
    have c1 := cSel_le' (g := fun i t => T E P WQ WK WV WO U C t3 m K i t j + sl)
      (hterm 1 j (by omega) hj) (hFm 1 j (by omega) hj) (hFm1 1 j (by omega) hj) h1
    have c2 := cSel_le' (g := fun i t => T E P WQ WK WV WO U C t3 m K i t j + sl)
      (hterm 2 j (by omega) hj) (hFm 2 j (by omega) hj) (hFm1 2 j (by omega) hj) h2
    have c3 := hfx3 j hj
    linarith

end

end Candidate.Checker2