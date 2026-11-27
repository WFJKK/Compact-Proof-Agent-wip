import Candidate.GroupSpec

/-!
# The flags of all groups (`groupsM`) and the soundness of the checker.
-/

namespace Candidate.Checker
open CompactCheck Candidate.Loops Candidate.Tables Candidate.Formula Finset

section
variable {env : Env} {E P WQ WK WV WO U C : Tensor ℚ} {tabs : Tabs Interp.counting}

/-- What a true flag of group `g` (= t3*64+m) with last maximum at `istar` means. -/
def GroupOk (E P WQ WK WV WO U C : Tensor ℚ) (tabs : Tabs Interp.counting) (g istar : Nat) : Prop :=
  g / 64 < 64 → ∀ j < 64, j ≠ g % 64 → ∀ t0 t1 t2, InRange (g % 64) istar 0 t0 → InRange (g % 64) istar 1 t1 →
    InRange (g % 64) istar 2 t2 →
    0 < T E P WQ WK WV WO U C (g / 64) (g % 64) (tabs.kk.getD (g / 64 * 64 + g % 64) ⟨0⟩).val 0 t0 j +
      T E P WQ WK WV WO U C (g / 64) (g % 64) (tabs.kk.getD (g / 64 * 64 + g % 64) ⟨0⟩).val 1 t1 j +
      T E P WQ WK WV WO U C (g / 64) (g % 64) (tabs.kk.getD (g / 64 * 64 + g % 64) ⟨0⟩).val 2 t2 j +
      T E P WQ WK WV WO U C (g / 64) (g % 64) (tabs.kk.getD (g / 64 * 64 + g % 64) ⟨0⟩).val 3 (g / 64) j

/-- The four flags of one `(t3, m)`, as computed by `groupsM`'s body. -/
theorem spec_groupStep (hT : TabsOk E P WQ WK WV WO U C tabs) (lo hi g2 : Nat) :
    Spec env (stepFlags Interp.counting tabs lo hi g2)
      fun fl => ∀ istar < 4, fl.getD istar false = true → GroupOk E P WQ WK WV WO U C tabs g2 istar := by
  unfold stepFlags
  by_cases hc : (g2 / 64 ≤ g2 % 64 && g2 % 64 ≠ 0 && lo ≤ g2 / 64 && g2 / 64 < hi) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq] at hc
    unfold groupFlags
    intro c v c' hr istar hi hfl h3
    have hm : g2 % 64 < 64 := Nat.mod_lt _ (by omega)
    have := spec_groupFlagsK hT (g2 / 64) (g2 % 64) _ (g2 % 64 - 2) h3 hm (by omega) (by omega) c v c' hr
    exact this.2 istar hi hfl
  · rw [if_neg hc]
    refine spec_pure fun istar hi hfl => ?_
    exfalso
    match istar with
    | 0 => simp at hfl
    | 1 => simp at hfl
    | 2 => simp at hfl
    | 3 => simp at hfl

theorem spec_groupsM (hT : TabsOk E P WQ WK WV WO U C tabs) (lo hi : Nat) : ∀ (n g2 : Nat) (arr : Array Bool),
    Spec env (groupsM Interp.counting tabs lo hi n g2 arr) fun arr' =>
      ∃ l : List Bool, arr'.toList = arr.toList ++ l ∧ l.length = 4 * n ∧
        ∀ k (hk : k < l.length), l[k] = true → GroupOk E P WQ WK WV WO U C tabs (g2 + k / 4) (k % 4)
  | 0, g2, arr => by
    simp only [groupsM]
    exact spec_pure ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n+1, g2, arr => by
    unfold groupsM
    refine spec_bind (spec_groupStep hT lo hi g2) fun fl hfl => ?_
    refine spec_mono ?_ (spec_groupsM hT lo hi n (g2+1) _)
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

theorem spec_weightShape (name : String) :
    Spec env (CostM.weightShape name) fun s => ∃ t, List.lookup name env.weights = some t ∧ t.shape = s := by
  intro c v c' hr
  simp only [CostM.weightShape] at hr
  split at hr
  · rename_i t ht
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    exact ⟨t, ht, hr.1⟩
  · cases hr

theorem spec_weightSize (name : String) :
    Spec env (CostM.weightSize name) fun n => ∃ t, List.lookup name env.weights = some t ∧ t.data.size = n := by
  intro c v c' hr
  obtain ⟨t, ht, hn, _⟩ := CostM.weightSize_spec hr
  exact ⟨t, ht, hn⟩

/-- A weight with the right shape and size, from the shape and size reads. -/
theorem weight_of_reads {name : String} {s : List Nat} {n : Nat}
    (h1 : ∃ t, List.lookup name env.weights = some t ∧ t.shape = s)
    (h2 : ∃ t, List.lookup name env.weights = some t ∧ t.data.size = n) {s0 : List Nat} {n0 : Nat}
    (hs : (s == s0) = true) (hn : (n == n0) = true) :
    ∃ t, List.lookup name env.weights = some t ∧ t.shape = s0 ∧ t.data.size = n0 := by
  obtain ⟨t, ht, hts⟩ := h1
  obtain ⟨t', ht', htn⟩ := h2
  rw [ht] at ht'
  cases ht'
  exact ⟨t, ht, by rw [hts]; exact beq_iff_eq.mp hs, by rw [htn]; exact beq_iff_eq.mp hn⟩

theorem spec_shapesOk : Spec env (shapesOk Interp.counting) fun ok => ok = true →
    (∃ t, List.lookup "E" env.weights = some t ∧ t.shape = [64, 32] ∧ t.data.size = 2048) ∧
    (∃ t, List.lookup "P" env.weights = some t ∧ t.shape = [4, 32] ∧ t.data.size = 128) ∧
    (∃ t, List.lookup "WQ" env.weights = some t ∧ t.shape = [32, 32] ∧ t.data.size = 1024) ∧
    (∃ t, List.lookup "WK" env.weights = some t ∧ t.shape = [32, 32] ∧ t.data.size = 1024) ∧
    (∃ t, List.lookup "WV" env.weights = some t ∧ t.shape = [32, 32] ∧ t.data.size = 1024) ∧
    (∃ t, List.lookup "WO" env.weights = some t ∧ t.shape = [32, 32] ∧ t.data.size = 1024) ∧
    (∃ t, List.lookup "U" env.weights = some t ∧ t.shape = [32, 64] ∧ t.data.size = 2048) ∧
    (∃ t, List.lookup "#const0" env.weights = some t ∧ t.shape = [] ∧ t.data.size = 1) := by
  unfold shapesOk
  refine spec_bind (spec_weightShape "E") fun sE hsE => ?_
  refine spec_bind (spec_weightSize "E") fun nE hnE => ?_
  refine spec_bind (spec_weightShape "P") fun sP hsP => ?_
  refine spec_bind (spec_weightSize "P") fun nP hnP => ?_
  refine spec_bind (spec_weightShape "WQ") fun sQ hsQ => ?_
  refine spec_bind (spec_weightSize "WQ") fun nQ hnQ => ?_
  refine spec_bind (spec_weightShape "WK") fun sK hsK => ?_
  refine spec_bind (spec_weightSize "WK") fun nK hnK => ?_
  refine spec_bind (spec_weightShape "WV") fun sV hsV => ?_
  refine spec_bind (spec_weightSize "WV") fun nV hnV => ?_
  refine spec_bind (spec_weightShape "WO") fun sO hsO => ?_
  refine spec_bind (spec_weightSize "WO") fun nO hnO => ?_
  refine spec_bind (spec_weightShape "U") fun sU hsU => ?_
  refine spec_bind (spec_weightSize "U") fun nU hnU => ?_
  refine spec_bind (spec_weightShape "#const0") fun sC hsC => ?_
  refine spec_bind (spec_weightSize "#const0") fun nC hnC => ?_
  refine spec_pure fun hok => ?_
  simp only [Bool.and_eq_true] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩, h14⟩, h15⟩, h16⟩ := hok
  exact ⟨weight_of_reads hsE hnE h1 h2, weight_of_reads hsP hnP h3 h4, weight_of_reads hsQ hnQ h5 h6,
    weight_of_reads hsK hnK h7 h8, weight_of_reads hsV hnV h9 h10, weight_of_reads hsO hnO h11 h12,
    weight_of_reads hsU hnU h13 h14, weight_of_reads hsC hnC h15 h16⟩

theorem sum_le_countP' {α : Type} (f : α → Nat) (p : α → Bool) :
    ∀ (l : List α), (∀ x ∈ l, f x ≤ cond (p x) 1 0) → (l.map f).sum ≤ l.countP p
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons, List.countP_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := sum_le_countP' f p l fun x hx => h x (List.mem_cons_of_mem _ hx)
    rcases hpa : p a with _ | _ <;> simp [hpa] at h1 ⊢ <;> omega

/-- The token ranges of the group of `[t0, t1, t2, t3]`. -/
theorem inRange_of_facts (m istar t0 t1 t2 t3 : Nat) (hget : [t0, t1, t2, t3].getD istar 0 = m)
    (hlt : ∀ i, istar < i → i < 4 → [t0, t1, t2, t3].getD i 0 < m) (hle : ∀ i, [t0, t1, t2, t3].getD i 0 ≤ m) :
    InRange m istar 0 t0 ∧ InRange m istar 1 t1 ∧ InRange m istar 2 t2 := by
  refine ⟨?_, ?_, ?_⟩
  · unfold InRange
    split_ifs with e1 e2
    · subst e1; exact hget
    · exact hle 0
    · omega
  · unfold InRange
    split_ifs with e1 e2
    · subst e1; exact hget
    · exact hle 1
    · exact hlt 1 (by omega) (by omega)
  · unfold InRange
    split_ifs with e1 e2
    · subst e1; exact hget
    · exact hle 2
    · exact hlt 2 (by omega) (by omega)

end

open Protected.N_attn_max4_v64_s0 in
/-- A true flag at the group of `x = [t0, t1, t2, t3]` means `x` is answered correctly. -/
theorem correct_of_flag {w : Weights ℚ} {c : Cert} {E P WQ WK WV WO U C : Tensor ℚ} {tabs : Tabs Interp.counting}
    (hE : List.lookup "E" w = some E) (hEs : E.shape = [64, 32]) (hEn : E.data.size = 2048)
    (hP : List.lookup "P" w = some P) (hPs : P.shape = [4, 32]) (hPn : P.data.size = 128)
    (hWQ : List.lookup "WQ" w = some WQ) (hWQs : WQ.shape = [32, 32]) (hWQn : WQ.data.size = 1024)
    (hC : List.lookup "#const0" w = some C) (hCs : C.shape = []) (hCn : C.data.size = 1)
    (hWK : List.lookup "WK" w = some WK) (hWKs : WK.shape = [32, 32]) (hWKn : WK.data.size = 1024)
    (hWV : List.lookup "WV" w = some WV) (hWVs : WV.shape = [32, 32]) (hWVn : WV.data.size = 1024)
    (hWO : List.lookup "WO" w = some WO) (hWOs : WO.shape = [32, 32]) (hWOn : WO.data.size = 1024)
    (hU : List.lookup "U" w = some U) (hUs : U.shape = [32, 64]) (hUn : U.data.size = 2048)
    (t0 t1 t2 t3 : Nat) (h0 : t0 < 64) (h1 : t1 < 64) (h2 : t2 < 64) (h3 : t3 < 64)
    (hG : GroupOk E P WQ WK WV WO U C tabs (gidx [t0, t1, t2, t3] / 4) (gidx [t0, t1, t2, t3] % 4)) :
    Correct graph w task [t0, t1, t2, t3] := by
  obtain ⟨hget, hlt, hle, hi4⟩ := istar_facts t0 t1 t2 t3
  have hx : ([t0, t1, t2, t3] : Input).length = 4 := rfl
  have hall : ([t0, t1, t2, t3] : Input).all (· < 64) = true := by simp [h0, h1, h2, h3]
  rw [gidx_eq] at hG
  simp only at hG hget hlt hle hi4
  set m := max (max (max (max 0 t0) t1) t2) t3 with hm
  set istar := (if t3 = m then 3 else if t2 = m then 2 else if t1 = m then 1 else 0) with histar
  have hm64 : m < 64 := by omega
  have e1 : ((t3 * 64 + m) * 4 + istar) / 4 = t3 * 64 + m := by omega
  have e2 : ((t3 * 64 + m) * 4 + istar) % 4 = istar := by omega
  rw [e1, e2] at hG
  unfold GroupOk at hG
  have e3 : (t3 * 64 + m) / 64 = t3 := by omega
  have e4 : (t3 * 64 + m) % 64 = m := by omega
  rw [e3, e4] at hG
  have hlab : task.label [t0, t1, t2, t3] = m := label_eq t0 t1 t2 t3
  obtain ⟨r0, r1, r2⟩ := inRange_of_facts m istar t0 t1 t2 t3 hget hlt hle
  apply correct_of_delta hE hEs hEn hP hPs hPn hWQ hWQs hWQn hC hCs hCn hWK hWKs hWKn hWV hWVs hWVn
    hWO hWOs hWOn hU hUs hUn hx hall (by rw [hlab]; exact hm64) ((tabs.kk.getD (t3 * 64 + m) ⟨0⟩).val : ℝ)
  intro j hj hne
  rw [hlab] at hne ⊢
  have := hG h3 j hj hne t0 t1 t2 r0 r1 r2
  unfold T at this
  simp only [Rat.cast_sub, Rat.cast_add, cast_DmQ hEs hPs hUs, cast_OVQ hEs hPs hWVs hWOs hUs] at this
  rw [sum_range4_expand]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [eT_cast hEs hPs hWQs hWKs hCs, eT_cast hEs hPs hWQs hWKs hCs, eT_cast hEs hPs hWQs hWKs hCs,
    eT_cast hEs hPs hWQs hWKs hCs]
  simp only [Rat.cast_sub]
  exact this

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
    refine spec_bind (spec_groupsM hT (p.getD 0 0) (p.getD 1 64) 4096 0 (Array.mk []))
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

end Candidate.Checker
