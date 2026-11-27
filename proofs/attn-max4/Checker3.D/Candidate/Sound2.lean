import Candidate.GroupSpec2
import Candidate.Sound

/-!
# Soundness of the slack-threshold checker (`Candidate.Checker2.D`).
-/

namespace Candidate.Checker2
open CompactCheck Candidate.Loops Candidate.Tables Candidate.Formula Candidate.Checker Finset

section
variable {env : Env} {E P WQ WK WV WO U C : Tensor ℚ} {tabs : Tabs Interp.counting}

/-- The flags of the group `(t3, m)`: a true flag at `istar` means every input of the group `(t3, m, istar)`
    has a positive shifted margin against every `j ≠ m`. -/
theorem spec_groupFlagsK2 (hT : TabsOk E P WQ WK WV WO U C tabs) (H4 : Q) (Hb : ℚ) (hH4 : H4.val = 4 * Hb)
    (t3 m : Nat) (K : Q) (a : Nat)
    (hH : ∀ i t j, i < 4 → t < 64 → j < 64 →
      |(DmQ E P U t3 m + OVQ E P WV WO U i t m) - (DmQ E P U t3 j + OVQ E P WV WO U i t j)| ≤ Hb)
    (h3 : t3 < 64) (hm : m < 64) (ham : a + 1 ≤ m) (ha2 : m ≤ a + 2) :
    Spec env (groupFlagsK Interp.counting tabs H4 t3 m K a) fun l =>
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
  -- the widest interval and the threshold
  refine spec_bind (spec_table0 (P := fun k v => v.val = (exhi.getD k ⟨0⟩).val - (exlo.getD k ⟨0⟩).val)
    (fun k => spec_sub "" _ _) 9) fun dtab hdtab => ?_
  refine spec_bind (spec_sub "" e3.2 e3.1) fun d3 hd3 => ?_
  refine spec_bind (spec_maxM _ 9 d3) fun dmax hdmax => ?_
  refine spec_bind (spec_muladd "" _ dmax H4) fun theta htheta => ?_
  have hd : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      (exhi.getD (i * 3 + (t - a)) ⟨0⟩).val - (exlo.getD (i * 3 + (t - a)) ⟨0⟩).val ≤ dmax.val := by
    intro i t hi hat htm
    have h1 : (dtab.getD (i * 3 + (t - a)) ⟨0⟩).val ≤ dmax.val := hdmax.2 _ (by omega)
    rw [hdtab _ (by omega)] at h1
    exact h1
  have hd3' : e3.2.val - e3.1.val ≤ dmax.val := by
    rw [← hd3]
    exact hdmax.1
  have hsl : 0 ≤ dmax.val * Hb := by
    apply mul_nonneg
    · have h1 : (e3.1.val : ℝ) ≤ e3.2.val := le_trans he3.1 he3.2
      have h2 : e3.1.val ≤ e3.2.val := by exact_mod_cast h1
      linarith
    · have := hH 0 0 0 (by omega) (by omega) (by omega)
      exact le_trans (abs_nonneg _) this
  have hth : 4 * ((dmax.val * Hb : ℚ) : ℝ) ≤ (theta.val : ℝ) := by
    rw [htheta, hH4]
    show 4 * ((dmax.val * Hb : ℚ) : ℝ) ≤ (((0 : ℚ) + dmax.val * (4 * Hb) : ℚ) : ℝ)
    exact le_of_eq (by push_cast; ring)
  -- term
  refine spec_bind (spec_table0 (P := fun k v => k < 192 →
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) m (k % 64) + ((dmax.val * Hb : ℚ) : ℝ))
      (fun k => spec_termEntry2 hT hm (by omega) hcpr hexlo hexhi hd hH k m (by omega) le_rfl) 192)
      fun term hP4 => ?_
  have htermk : ∀ k < 192, ((term.getD k ⟨0⟩).val : ℝ) ≤
      T E P WQ WK WV WO U C t3 m K.val (k / 64) m (k % 64) + ((dmax.val * Hb : ℚ) : ℝ) :=
    fun k hk => hP4 k hk hk
  have hterm : ∀ i j, i < 3 → j < 64 → ((term.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤
      T E P WQ WK WV WO U C t3 m K.val i m j + ((dmax.val * Hb : ℚ) : ℝ) := by
    intro i j hi hj
    have := htermk (i * 64 + j) (by omega)
    have e1 : (i * 64 + j) / 64 = i := by omega
    have e2 : (i * 64 + j) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  -- Fm
  refine spec_bind (spec_table0 (P := fun k v => k < 192 → ∀ t < m,
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) t (k % 64) + ((dmax.val * Hb : ℚ) : ℝ))
      (fun k => spec_FmEntry2 hT h3 hm ham hsl hcpr hexlo hexhi hd hH hneg k) 192)
      fun Fm hP5 => ?_
  have hFmk : ∀ k < 192, ∀ t < m, ((Fm.getD k ⟨0⟩).val : ℝ) ≤
      T E P WQ WK WV WO U C t3 m K.val (k / 64) t (k % 64) + ((dmax.val * Hb : ℚ) : ℝ) :=
    fun k hk => hP5 k hk hk
  have hFm : ∀ i j, i < 3 → j < 64 → ∀ t < m,
      ((Fm.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val i t j + ((dmax.val * Hb : ℚ) : ℝ) := by
    intro i j hi hj
    have := hFmk (i * 64 + j) (by omega)
    have e1 : (i * 64 + j) / 64 = i := by omega
    have e2 : (i * 64 + j) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  -- Fm1
  refine spec_bind (spec_table0 (P := fun k v => k < 192 → ∀ t ≤ m,
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) t (k % 64) + ((dmax.val * Hb : ℚ) : ℝ)) ?_ 192)
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
      ((Fm1.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val i t j + ((dmax.val * Hb : ℚ) : ℝ) := by
    intro i j hi hj
    have := hP6 (i * 64 + j) (by omega) (by omega)
    have e1 : (i * 64 + j) / 64 = i := by omega
    have e2 : (i * 64 + j) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  -- fx3
  refine spec_bind (spec_table0 (P := fun j v => j < 64 →
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val 3 t3 j + ((dmax.val * Hb : ℚ) : ℝ))
      (fun j => spec_fx3Entry2 hT h3 hm hcpr he3 hd3' hH j) 64) fun fx3 hP7 => ?_
  have hfx3 : ∀ j < 64, ((fx3.getD j ⟨0⟩).val : ℝ) ≤
      T E P WQ WK WV WO U C t3 m K.val 3 t3 j + ((dmax.val * Hb : ℚ) : ℝ) :=
    fun j hj => hP7 j hj hj
  -- the flags
  by_cases h3m : t3 = m
  · rw [if_pos h3m]
    refine spec_bind (spec_okOfM2 3 theta hth hterm hFm hFm1 hfx3) fun ok3 hok3 => ?_
    refine spec_pure ⟨rfl, ?_⟩
    intro istar hi htrue
    match istar with
    | 0 => simp at htrue
    | 1 => simp at htrue
    | 2 => simp at htrue
    | 3 => exact hok3 (by simpa using htrue)
  · rw [if_neg h3m]
    refine spec_bind (spec_okOfM2 0 theta hth hterm hFm hFm1 hfx3) fun ok0 hok0 => ?_
    refine spec_bind (spec_okOfM2 1 theta hth hterm hFm hFm1 hfx3) fun ok1 hok1 => ?_
    refine spec_bind (spec_okOfM2 2 theta hth hterm hFm hFm1 hfx3) fun ok2 hok2 => ?_
    refine spec_pure ⟨rfl, ?_⟩
    intro istar hi htrue
    match istar with
    | 0 => exact hok0 (by simpa using htrue)
    | 1 => exact hok1 (by simpa using htrue)
    | 2 => exact hok2 (by simpa using htrue)
    | 3 => simp at htrue

/-- The four flags of one `(t3, m)`, as computed by `groupsM`'s body. -/
theorem spec_groupStep2 (hT : TabsOk E P WQ WK WV WO U C tabs) (H4 : Q) (Hb : ℚ) (hH4 : H4.val = 4 * Hb)
    (hH : ∀ t3 m i t j, t3 < 64 → m < 64 → i < 4 → t < 64 → j < 64 →
      |(DmQ E P U t3 m + OVQ E P WV WO U i t m) - (DmQ E P U t3 j + OVQ E P WV WO U i t j)| ≤ Hb)
    (plan : List Nat) (lo hi g2 : Nat) :
    Spec env (stepFlags Interp.counting tabs H4 plan lo hi g2)
      fun fl => ∀ istar < 4, fl.getD istar false = true → GroupOk E P WQ WK WV WO U C tabs g2 istar := by
  unfold stepFlags
  by_cases hc : (g2 / 64 ≤ g2 % 64 && g2 % 64 ≠ 0 && lo ≤ g2 / 64 && g2 / 64 < hi) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    unfold groupFlags
    intro c v c' hr istar hi hfl h3
    have hm : g2 % 64 < 64 := Nat.mod_lt _ (by omega)
    have := spec_groupFlagsK2 hT H4 Hb hH4 (g2 / 64) (g2 % 64) _
      (if plan.getD (2 + g2 % 64) 2 = 1 then g2 % 64 - 1 else g2 % 64 - 2)
      (fun i t j hi ht hj => hH (g2 / 64) (g2 % 64) i t j h3 hm hi ht hj) h3 hm
      (by split_ifs <;> omega) (by split_ifs <;> omega) c v c' hr
    exact this.2 istar hi hfl
  · rw [if_neg hc]
    refine spec_pure fun istar hi hfl => ?_
    exfalso
    match istar with
    | 0 => simp at hfl
    | 1 => simp at hfl
    | 2 => simp at hfl
    | 3 => simp at hfl

theorem spec_groupsM2 (hT : TabsOk E P WQ WK WV WO U C tabs) (H4 : Q) (Hb : ℚ) (hH4 : H4.val = 4 * Hb)
    (hH : ∀ t3 m i t j, t3 < 64 → m < 64 → i < 4 → t < 64 → j < 64 →
      |(DmQ E P U t3 m + OVQ E P WV WO U i t m) - (DmQ E P U t3 j + OVQ E P WV WO U i t j)| ≤ Hb)
    (plan : List Nat) (lo hi : Nat) :
    ∀ (n g2 : Nat) (arr : Array Bool),
    Spec env (groupsM Interp.counting tabs H4 plan lo hi n g2 arr) fun arr' =>
      ∃ l : List Bool, arr'.toList = arr.toList ++ l ∧ l.length = 4 * n ∧
        ∀ k (hk : k < l.length), l[k] = true → GroupOk E P WQ WK WV WO U C tabs (g2 + k / 4) (k % 4)
  | 0, g2, arr => by
    simp only [groupsM]
    exact spec_pure ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n+1, g2, arr => by
    unfold groupsM
    refine spec_bind (spec_groupStep2 hT H4 Hb hH4 hH plan lo hi g2) fun fl hfl => ?_
    refine spec_mono ?_ (spec_groupsM2 hT H4 Hb hH4 hH plan lo hi n (g2+1) _)
    intro arr' ⟨l, hl, hlen, hP⟩
    refine ⟨[fl.getD 0 false, fl.getD 1 false, fl.getD 2 false, fl.getD 3 false] ++ l, ?_, ?_, ?_⟩
    · rw [hl]
      simp [Array.toList_push]
    · simp [hlen]; ring
    · intro k hk htrue
      by_cases hk4 : k < 4
      · rw [List.getElem_append_left (by simpa using hk4)] at htrue
        have e1 : g2 + k / 4 = g2 := by omega
        rw [e1]
        match k, hk4 with
        | 0, _ => exact hfl 0 (by omega) (by simpa using htrue)
        | 1, _ => exact hfl 1 (by omega) (by simpa using htrue)
        | 2, _ => exact hfl 2 (by omega) (by simpa using htrue)
        | 3, _ => exact hfl 3 (by omega) (by simpa using htrue)
      · have hge : [fl.getD 0 false, fl.getD 1 false, fl.getD 2 false, fl.getD 3 false].length ≤ k := by
          simp; omega
        rw [List.getElem_append_right hge] at htrue
        have hk' : k - 4 < l.length := by
          simp only [List.length_append] at hk
          simp at hk
          omega
        have := hP (k - 4) (by simpa using hk') (by simpa using htrue)
        have e1 : g2 + 1 + (k - 4) / 4 = g2 + k / 4 := by omega
        have e2 : (k - 4) % 4 = k % 4 := by omega
        rw [e1, e2] at this
        exact this

end

open Classical Protected.N_attn_max4_v64_s0 in
/-- Soundness of the checker: whatever the weights, the plan and the certificate, the count never exceeds
    the number of inputs answered correctly. -/
theorem D_sound : ∀ (p : List Nat) (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D p Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro p w c n cost h
  unfold numCorrect
  suffices hS : Spec ⟨w, c⟩ (D p Interp.counting) fun n =>
      n ≤ (allInputs task.space).countP fun x => decide (Correct graph w task x) from hS [] n cost h
  unfold D
  refine spec_bind spec_shapesOk fun ok hok => ?_
  by_cases hok' : ok = true
  swap
  · have hf : (!ok) = true := by simp [hok']
    rw [if_pos hf]
    exact spec_pure (Nat.zero_le _)
  · have hf : ¬ ((!ok) = true) := by simp [hok']
    rw [if_neg hf]
    obtain ⟨⟨E, hE, hEs, hEn⟩, ⟨P, hP, hPs, hPn⟩, ⟨WQ, hWQ, hWQs, hWQn⟩, ⟨WK, hWK, hWKs, hWKn⟩,
      ⟨WV, hWV, hWVs, hWVn⟩, ⟨WO, hWO, hWOs, hWOn⟩, ⟨U, hU, hUs, hUn⟩, ⟨C, hC, hCs, hCn⟩⟩ := hok hok'
    refine spec_bind (spec_buildTabs hE hP hWQ hC hWK hWV hWO hU) fun tabs hT => ?_
    refine spec_bind (spec_boundH hT) fun H4 ⟨Hb, hH4, hH⟩ => ?_
    refine spec_bind (spec_groupsM2 hT H4 Hb hH4 hH p (p.getD 0 0) (p.getD 1 64) 4096 0 (Array.mk []))
      fun flags ⟨l, hl, hlen, hPl⟩ => ?_
    refine spec_pure ?_
    rw [sumInputs_eq, space_eq]
    apply sum_le_countP'
    intro x hx
    obtain ⟨t0, t1, t2, t3, rfl, h0, h1, h2, h3⟩ := mem_space hx
    simp only [Interp.counting_countB, Interp.counting_bfalse]
    have hl' : flags.toList = l := by simpa using hl
    by_cases hf : flags.getD (gidx [t0, t1, t2, t3]) false = true
    · rw [hf]
      have hg : gidx [t0, t1, t2, t3] < l.length := by
        rw [hlen, gidx_eq]
        simp only
        split_ifs <;> omega
      rw [getD_of_toList hl' hg] at hf
      have hG := hPl _ hg hf
      rw [Nat.zero_add] at hG
      have hc := correct_of_flag (c := c) hE hEs hEn hP hPs hPn hWQ hWQs hWQn hC hCs hCn hWK hWKs hWKn
        hWV hWVs hWVn hWO hWOs hWOn hU hUs hUn t0 t1 t2 t3 h0 h1 h2 h3 hG
      simp [hc]
    · simp only [Bool.not_eq_true] at hf
      rw [hf]
      exact Nat.zero_le _

end Candidate.Checker2