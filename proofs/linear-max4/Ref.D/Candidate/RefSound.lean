import Candidate.RefSpec

/-!
# Soundness of the reference checker: `D_sound`
-/

namespace Candidate.Ref

open CompactCheck Protected.N_max4_v64_s0 Candidate.Linear Candidate.Boxes Candidate.Counted

/-- The network's weights, as the checker found them. -/
structure WCtx (w : Weights ℚ) (E L U : Tensor ℚ) (d V : Nat) : Prop where
  hgP : graph.positions = 4
  hgV : graph.values = V
  hE : List.lookup "embedding.weight" w = some E
  hEs : E.shape = [d, V]
  hEsz : E.data.size = d * V
  hL : List.lookup "linear.weight" w = some L
  hLs : L.shape = [d, d]
  hLsz : L.data.size = d * d
  hU : List.lookup "unembedding.weight" w = some U
  hUs : U.shape = [V, d]
  hUsz : U.data.size = V * d

/-- The context of a class `(m, k)`: the rows `D_j(t)`, and what its safe test says. -/
structure CCtx (E L U : Tensor ℚ) (d V m k : Nat) (J : List Nat) (sf : Bool) (dr pm : List (List Q)) : Prop where
  hm : m < V
  hdr : ∀ j < V, j ≠ m → ∀ t ≤ m, ((dr.getD j []).getD t ⟨0⟩).val = Mat E L U d V m t - Mat E L U d V j t
  hpr : ∀ j, PrOk ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val)
  hpl : ∀ j < V, j ≠ m → m ≤ (pm.getD j []).length
  hsf : 0 < k → sf = true → ∀ j < V, j ≠ m → j ∉ J →
      0 < (k : ℚ) * ((dr.getD j []).getD m ⟨0⟩).val + ((4 - k : Nat) : ℚ) * ((pm.getD j []).getD (m - 1) ⟨0⟩).val

/-- Every true verdict in the table stands for its key. -/
def Inv (E L U : Tensor ℚ) (d V m : Nat) (tbl : List (Box × List (Box × Bool))) : Prop :=
  ∀ g ∈ tbl, ∀ e ∈ g.2, e.2 = true → Passes E L U d V m e.1

theorem forall2_rep : ∀ (c : Box) (n : Nat), c.length = n → (∀ s ∈ c, s.Nodup ∧ ∀ t ∈ s, t < 64) →
    List.Forall₂ (fun (s : List Nat) v => s.Nodup ∧ ∀ t ∈ s, t < v) c (List.replicate n 64)
  | [], 0, _, _ => List.Forall₂.nil
  | s :: c, n + 1, hl, h => List.Forall₂.cons (h s List.mem_cons_self)
      (forall2_rep c n (by simpa using hl) (fun s' hs' => h s' (List.mem_cons_of_mem _ hs')))
  | [], _ + 1, hl, _ => by simp at hl
  | _ :: _, 0, hl, _ => by simp at hl

open Classical in
theorem bsz_le (w : Weights ℚ) (c : Box) (hc : WF c) (hall : ∀ x, inS c x = true → Correct graph w task x) :
    bsz c ≤ cP (fun x => decide (Correct graph w task x)) (allInputs task.space) c := by
  rw [← countP_inS c task.space (by rw [task_space]; exact forall2_rep c 4 hc.1 hc.2)]
  unfold cP
  apply List.countP_mono_left
  intro x _ hx
  simp [hx, hall x hx]

theorem foldl_nadd (h : (Box × (Box × Bool)) → Nat) :
    ∀ (l : List (Box × (Box × Bool))) (a : Nat), l.foldl (fun n x => Nat.add n (h x)) a = a + (l.map h).sum
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_nadd h l, List.map_cons, List.sum_cons]
    simp only [Nat.add_eq]
    omega

theorem zip_sum_le (f : (Box × (Box × Bool)) → Nat) (g : Box → Nat) :
    ∀ (ds : List Box) (es : List (Box × Bool)), (∀ d ∈ ds, ∀ e ∈ es, f (d, e) ≤ g d) →
      ((ds.zip es).map f).sum ≤ (ds.map g).sum
  | [], _, _ => by simp
  | _ :: _, [], _ => by simp
  | d :: ds, e :: es, h => by
    simp only [List.zip_cons_cons, List.map_cons, List.sum_cons]
    have h1 := h d List.mem_cons_self e List.mem_cons_self
    have h2 := zip_sum_le f g ds es (fun d' hd' e' he' => h d' (List.mem_cons_of_mem _ hd') e' (List.mem_cons_of_mem _ he'))
    omega

open Classical in
/-- What a group's sub-boxes count is at most what is correct in them. -/
theorem cnt_le (w : Weights ℚ) (E L U : Tensor ℚ) (d V : Nat) (wc : WCtx w E L U d V) (m : Nat) (hm : m < V)
    (p : Nat) (subs : List Box) (es : List (Box × Bool)) (hsubs : ∀ b ∈ subs, WF b)
    (hes : ∀ e ∈ es, e.2 = true → Passes E L U d V m e.1) :
    cnt Interp.counting p subs es ≤
      (subs.map (cP (fun x => decide (Correct graph w task x)) (allInputs task.space))).sum := by
  simp only [cnt, Interp.counting_nadd, Interp.counting_nscale, Interp.counting_nzero]
  rw [foldl_nadd, Nat.zero_add]
  apply zip_sum_le
  intro b hb e he
  cases hchk : (srt (b.eraseIdx p ++ [b.getD p []]) == e.1)
  · simp
  · cases hg : e.2
    · simp
    · simp only [Bool.cond_true]
      have hP := hes e he hg
      have hkey : srt (b.eraseIdx p ++ [b.getD p []]) = e.1 := by simpa using hchk
      have hlen4 : (b.eraseIdx p ++ [b.getD p []]).length = 4 := by
        rw [← (srt_perm _).length_eq, hkey, hP.1]
      have hbl := (hsubs b hb).1
      have hp : p < b.length := by
        by_contra hpn
        rw [List.eraseIdx_of_length_le (by omega)] at hlen4
        simp at hlen4
        omega
      have hperm : b.Perm e.1 := by
        rw [← hkey]
        exact (perm_eraseIdx b p hp).trans (srt_perm _).symm
      exact bsz_le w b (hsubs b hb) (fun x hx => correct_of_passes w E L U d 4 V wc.hgP wc.hgV wc.hE wc.hEs wc.hEsz
        wc.hL wc.hLs wc.hLsz wc.hU wc.hUs wc.hUsz rfl e.1 b m hm hP hperm x hx)

open Classical in
/-- A leaf box: what it counts is correct, and the table stays true. -/
theorem leaf_spec (env : Env) (w : Weights ℚ) (E L U : Tensor ℚ) (d V : Nat) (wc : WCtx w E L U d V)
    (m k : Nat) (J J1 : List Nat) (sf : Bool) (dr pm : List (List Q)) (cc : CCtx E L U d V m k J sf dr pm)
    (c : Box) (S : List Nat) (rf : Nat) (hrf : rf = c.count S) (hc : WF c)
    (tbl : List (Box × List (Box × Bool))) (hinv : Inv E L U d V m tbl) (n : Nat)
    (tbl' : List (Box × List (Box × Bool))) (c0 c' : Cost)
    (h : (leaf Interp.counting m k J J1 sf dr pm c S rf tbl).run env c0 = some ((n, tbl'), c')) :
    Inv E L U d V m tbl' ∧ n ≤ cP (fun x => decide (Correct graph w task x)) (allInputs task.space) c := by
  generalize hpd : cond (rf == 1) (c.idxOf S) 3 = p at h
  generalize hsd : cond (rf == 1) (splitAt p c S) [c] = subs at h
  have hp : p < c.length := by
    rw [← hpd, hc.1]
    cases hr : (rf == 1)
    · simp
    · have h1 : rf = 1 := by simpa using hr
      have hS : S ∈ c := List.count_pos_iff.mp (by rw [← hrf, h1]; norm_num)
      simp only [Bool.cond_true]
      rw [← hc.1]
      exact List.idxOf_lt_length_iff.mpr hS
  have hsubs : ∀ b ∈ subs, WF b := by
    rw [← hsd]
    cases hr : (rf == 1)
    · simp only [Bool.cond_false, List.mem_singleton]; intro b hb; rw [hb]; exact hc
    · simp only [Bool.cond_true]; exact WF_splitAt _ c S hc
  have hW : ∀ v ∈ subs.map (·.getD p []), ∀ t ∈ v, t ∈ c.getD p [] := by
    intro v hv t ht
    rw [List.mem_map] at hv
    obtain ⟨b, hb, rfl⟩ := hv
    rw [← hsd] at hb
    cases hr : (rf == 1)
    · rw [hr] at hb
      simp only [Bool.cond_false, List.mem_singleton] at hb
      rw [hb] at ht
      exact ht
    · rw [hr] at hb
      simp only [Bool.cond_true] at hb
      obtain ⟨X, hX, rfl⟩ := splitAt_shape p c S b hb
      rw [getD_set_self c p X hp] at ht
      exact hX.subset ht
  have hsum : (subs.map (cP (fun x => decide (Correct graph w task x)) (allInputs task.space))).sum =
      cP (fun x => decide (Correct graph w task x)) (allInputs task.space) c := by
    rw [← hsd]
    cases hr : (rf == 1)
    · simp
    · simp only [Bool.cond_true]
      exact splitAt_sum _ _ p c hp S
  simp only [leaf] at h
  rw [hpd, hsd] at h
  split at h
  · rename_i e he
    simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    refine ⟨hinv, ?_⟩
    rw [← hsum]
    exact cnt_le w E L U d V wc m cc.hm p subs e.2 hsubs (hinv e (List.mem_of_find?_eq_some he))
  · simp only [Interp.counting_bind, CostM.run_bind] at h
    split at h
    · rename_i es c1 hes
      simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      have hesP : ∀ e ∈ es, e.2 = true → Passes E L U d V m e.1 := by
        intro e he hg
        obtain ⟨v, hkey, hk, hs, hJ⟩ := grp_spec env m k J J1 sf dr pm cc.hpr _ _ _ hW c0 es c1 hes e he hg
        exact passes_of E L U d V m k J sf dr pm cc.hpr cc.hpl cc.hdr cc.hsf e.1 _ v hkey hk hs hJ
      refine ⟨?_, ?_⟩
      · intro g hg
        rw [List.mem_append, List.mem_singleton] at hg
        rcases hg with hg | rfl
        · exact hinv g hg
        · exact hesP
      · rw [← hsum]
        exact cnt_le w E L U d V wc m cc.hm p subs es hsubs hesP
    · cases h

theorem fold_spec {T : Type} (env : Env) (g : Box → Nat) (P : T → Prop)
    (body : Nat × T → Box → Interp.counting.M (Nat × T)) :
    ∀ (ds : List Box), (∀ b ∈ ds, ∀ st c r c', P st.2 → (body st b).run env c = some (r, c') →
      P r.2 ∧ r.1 ≤ st.1 + g b) →
    ∀ (st : Nat × T) (c : Cost) (r : Nat × T) (c' : Cost), P st.2 → (ds.foldlM body st).run env c = some (r, c') →
      P r.2 ∧ r.1 ≤ st.1 + (ds.map g).sum
  | [], _, st, c, r, c', hP, h => by
    simp only [List.foldlM, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hP, by simp⟩
  | b :: ds, hbody, st, c, r, c', hP, h => by
    simp only [List.foldlM, Interp.counting_bind, CostM.run_bind] at h
    split at h
    · rename_i r1 c1 h1
      obtain ⟨hP1, hle1⟩ := hbody b List.mem_cons_self st c r1 c1 hP h1
      obtain ⟨hP2, hle2⟩ := fold_spec env g P body ds (fun b' hb' => hbody b' (List.mem_cons_of_mem _ hb')) r1 c1 r c'
        hP1 h
      refine ⟨hP2, ?_⟩
      simp only [List.map_cons, List.sum_cons]
      omega
    · cases h

open Classical in
/-- The walk of a class box: what it counts is correct, and the table stays true. -/
theorem walk_spec (env : Env) (w : Weights ℚ) (E L U : Tensor ℚ) (d V : Nat) (wc : WCtx w E L U d V)
    (m k : Nat) (e : (List Nat × List Nat) × List Nat × List (List Nat)) (sf : Bool) (dr pm : List (List Q))
    (cc : CCtx E L U d V m k e.1.1 sf dr pm) :
    ∀ (fuel : Nat) (c : Box) (S F : List Nat) (tbl : List (Box × List (Box × Bool))) (n : Nat)
      (tbl' : List (Box × List (Box × Bool))) (c0 c' : Cost), WF c → Inv E L U d V m tbl →
    (walk Interp.counting m k e sf dr pm fuel c S F tbl).run env c0 = some ((n, tbl'), c') →
    Inv E L U d V m tbl' ∧ n ≤ cP (fun x => decide (Correct graph w task x)) (allInputs task.space) c
  | 0, c, S, F, tbl, n, tbl', c0, c', hc, hinv, h => by
    simp only [walk] at h
    exact leaf_spec env w E L U d V wc m k e.1.1 e.1.2 sf dr pm cc c S _ rfl hc tbl hinv n tbl' c0 c' h
  | fuel + 1, c, S, F, tbl, n, tbl', c0, c', hc, hinv, h => by
    simp only [walk] at h
    generalize hB : cond (decide (2 ≤ c.count S)) (planB e F) [] = B at h
    cases hBe : B.isEmpty
    · rw [hBe] at h
      simp only [Bool.cond_false] at h
      obtain ⟨hWF, hsum⟩ := refine_spec (fun x => decide (Correct graph w task x)) (allInputs task.space) c S B hc
      have hf := fold_spec env (cP (fun x => decide (Correct graph w task x)) (allInputs task.space))
        (Inv E L U d V m) _ (refine c S B) ?_ (0, tbl) c0 (n, tbl') c' hinv h
      · rw [← hsum]
        simpa using hf
      · intro b hb st c1 r c2 hst hr
        cases hz : (bsz b == 0)
        · rw [hz] at hr
          simp only [Bool.cond_false, Interp.counting_bind, CostM.run_bind] at hr
          split at hr
          · rename_i r0 c3 h0
            simp only [Interp.counting_pure, CostM.run_pure, Interp.counting_nadd, Option.some.injEq,
              Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            have hr0 : Inv E L U d V m r0.2 ∧
                r0.1 ≤ cP (fun x => decide (Correct graph w task x)) (allInputs task.space) b := by
              cases hcnt : (b.count (S.filter fun t => !B.contains t) == c.count S)
              · rw [hcnt] at h0
                simp only [Bool.cond_false] at h0
                exact walk_spec env w E L U d V wc m k e sf dr pm cc fuel b _ _ st.2 r0.1 r0.2 c1 c3 (hWF b hb) hst h0
              · rw [hcnt] at h0
                simp only [Bool.cond_true] at h0
                exact leaf_spec env w E L U d V wc m k e.1.1 e.1.2 sf dr pm cc b _ _ (beq_iff_eq.mp hcnt).symm (hWF b hb)
                  st.2 hst r0.1 r0.2 c1 c3 h0
            refine ⟨hr0.1, ?_⟩
            simp only [Nat.add_eq]
            omega
          · cases hr
        · rw [hz] at hr
          simp only [Bool.cond_true, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          exact ⟨hst, by omega⟩
    · rw [hBe] at h
      simp only [Bool.cond_true] at h
      exact leaf_spec env w E L U d V wc m k e.1.1 e.1.2 sf dr pm cc c S _ rfl hc tbl hinv n tbl' c0 c' h

/-! ## The matrix and the rows of a level (from the agent's TreeCheck.lean) -/

theorem getD_range_map' {γ : Type} (V t : Nat) (f : Nat → γ) (dflt : γ) (ht : t < V) :
    ((List.range V).map f).getD t dflt = f t := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]

def MatOk (E L U : Tensor ℚ) (d V : Nat) (mat : List (List Q)) : Prop :=
  mat.map (fun row => row.map Q.val) =
    (List.range V).map fun j => (List.range V).map fun t => Mat E L U d V j t

theorem mat_row (E L U : Tensor ℚ) (d V : Nat) (mat : List (List Q)) (hmat : MatOk E L U d V mat)
    (j : Nat) (hj : j < V) :
    (mat.getD j []).map Q.val = (List.range V).map fun t => Mat E L U d V j t := by
  have h1 : (mat.getD j []).map Q.val = (mat.map (fun row => row.map Q.val)).getD j [] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
    cases mat[j]? <;> rfl
  rw [h1, hmat, getD_range_map' V j _ [] hj]

theorem mat_len (E L U : Tensor ℚ) (d V : Nat) (mat : List (List Q)) (hmat : MatOk E L U d V mat)
    (j : Nat) (hj : j < V) : (mat.getD j []).length = V := by
  have := congrArg List.length (mat_row E L U d V mat hmat j hj)
  simpa using this

theorem mat_entry (E L U : Tensor ℚ) (d V : Nat) (mat : List (List Q)) (hmat : MatOk E L U d V mat)
    (j : Nat) (hj : j < V) (t : Nat) (ht : t < V) :
    ((mat.getD j []).getD t ⟨0⟩).val = Mat E L U d V j t := by
  rw [getD_val, mat_row E L U d V mat hmat j hj, getD_range_map' V t _ 0 ht]

theorem getD_take {β : Type} (l : List β) (n t : Nat) (dflt : β) (ht : t < n) :
    (l.take n).getD t dflt = l.getD t dflt := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_take, ht]

theorem k_of_index : ∀ (k : Nat) (h1 : 0 < k) (h4 : k ≤ 4), [1, 2, 3, 4][k - 1]'(by simp; omega) = k
  | 1, _, _ => rfl
  | 2, _, _ => rfl
  | 3, _, _ => rfl
  | 4, _, _ => rfl
  | 0, h, _ => absurd h (by decide)
  | _ + 5, _, h => absurd h (by omega)

open Classical in
/-- A level: what the 15 class boxes and the next level count is correct. -/
theorem top_spec (env : Env) (w : Weights ℚ) (E L U : Tensor ℚ) (d V : Nat) (wc : WCtx w E L U d V)
    (mat : List (List Q)) (hmat : MatOk E L U d V mat) (tab : List ((List Nat × List Nat) × List Nat × List (List Nat))) :
    ∀ (fuel : Nat) (c : Box) (n : Nat) (c0 c' : Cost), fuel ≤ V → WF c →
    (top Interp.counting V mat tab fuel c).run env c0 = some (n, c') →
    n ≤ cP (fun x => decide (Correct graph w task x)) (allInputs task.space) c
  | 0, c, n, c0, c', _, _, h => by
    simp only [top, Interp.counting_pure, CostM.run_pure, Interp.counting_nzero, Option.some.injEq,
      Prod.mk.injEq] at h
    omega
  | m + 1, c, n, c0, c', hle, hc, h => by
    have hm : m < V := by omega
    simp only [top, Interp.counting_bind, CostM.run_bind] at h
    split at h
    · rename_i dr c1 hdr
      split at h
      · rename_i pm c2 hpm
        split at h
        · rename_i sfs c3 hsfs
          split at h
          · rename_i r c4 hr
            simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            -- the rows D_j(t), t ≤ m
            have hD := mapC_spec env _ (fun j (row : List Q) => j ≠ m → ∀ t,
                t < ((mat.getD m []).take (m + 1)).length → t < ((mat.getD j []).take (m + 1)).length →
                (row.getD t ⟨0⟩).val = (((mat.getD m []).take (m + 1)).getD t ⟨0⟩).val -
                  (((mat.getD j []).take (m + 1)).getD t ⟨0⟩).val) (List.range V)
              (fun j _ c r c' hr hjm => by
                have hb : (j == m) = false := by simpa using hjm
                rw [hb] at hr
                exact subZip_spec env _ _ c r c' hr) c0 dr c1 hdr
            have hdrS : ∀ j < V, j ≠ m → ∀ t ≤ m,
                ((dr.getD j []).getD t ⟨0⟩).val = Mat E L U d V m t - Mat E L U d V j t := by
              intro j hj hjm t ht
              have h1 := forall2_getD _ [] _ _ hD j (by simpa using hj)
              simp only [List.getElem_range] at h1
              specialize h1 hjm
              have hlm : ((mat.getD m []).take (m + 1)).length = m + 1 := by
                rw [List.length_take, mat_len E L U d V mat hmat m hm]; omega
              have hlj : ((mat.getD j []).take (m + 1)).length = m + 1 := by
                rw [List.length_take, mat_len E L U d V mat hmat j hj]; omega
              rw [h1 t (by omega) (by omega), getD_take _ _ _ _ (by omega), getD_take _ _ _ _ (by omega),
                mat_entry E L U d V mat hmat m hm t (by omega), mat_entry E L U d V mat hmat j hj t (by omega)]
            -- the minima below m
            have hP := mapC_spec env _ (fun j (pr : List Q) => PrOk ((dr.getD j []).map Q.val) (pr.map Q.val) ∧
                (j ≠ m → pr.length = m - 1 + 1)) (List.range V) (fun j _ c r c' hr => by
                cases hb : (j == m)
                · rw [hb] at hr
                  have := scan_spec env _ m c r c' hr
                  exact ⟨this.1, fun _ => this.2⟩
                · rw [hb] at hr
                  simp only [Bool.cond_true, Interp.counting_pure, CostM.run_pure, Option.some.injEq,
                    Prod.mk.injEq] at hr
                  obtain ⟨rfl, rfl⟩ := hr
                  exact ⟨PrOk_nil _, fun h => absurd (by simpa using hb) h⟩) c1 pm c2 hpm
            have hpmL : pm.length = V := by have := hP.length_eq; simpa using this.symm
            have hpr : ∀ j, PrOk ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val) := by
              intro j
              by_cases hj : j < V
              · have h1 := forall2_getD _ [] _ _ hP j (by simpa using hj)
                simp only [List.getElem_range] at h1
                exact h1.1
              · have hpj : pm.getD j [] = [] := by
                  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
                  rfl
                rw [hpj]
                exact PrOk_nil _
            have hpl : ∀ j < V, j ≠ m → m ≤ (pm.getD j []).length := by
              intro j hj hjm
              have h1 := forall2_getD _ [] _ _ hP j (by simpa using hj)
              simp only [List.getElem_range] at h1
              rw [h1.2 hjm]
              omega
            -- the safe tests, one per k
            have hS := mapC_spec env _ (fun k (sf : Bool) => sf = true → ∀ j < V, j ≠ m →
                j ∉ (tab.getD (m * 4 + k - 1) e0).1.1 →
                0 < (k : ℚ) * ((dr.getD j []).getD m ⟨0⟩).val + ((4 - k : Nat) : ℚ) * ((pm.getD j []).getD (m - 1) ⟨0⟩).val)
              [1, 2, 3, 4] (fun k _ c r c' hr => safe_spec env V m k _ dr pm c r c' hr) c2 sfs c3 hsfs
            have hlen4 : sfs.length = 4 := by have := hS.length_eq; simpa using this.symm
            have hcc : ∀ k, CCtx E L U d V m k (tab.getD (m * 4 + k - 1) e0).1.1
                (sfs.getD (k - 1) false) dr pm := by
              intro k
              refine ⟨hm, hdrS, hpr, hpl, fun hk0 hsf j hj hjm hjJ => ?_⟩
              have hk4 : k ≤ 4 := by
                by_contra hk
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hsf
                simp at hsf
              have h1 := forall2_getD _ false _ _ hS (k - 1) (by simp; omega)
              rw [k_of_index k hk0 hk4] at h1
              exact h1 hsf j hj hjm hjJ
            obtain ⟨hWF, hsum⟩ := refine_spec (fun x => decide (Correct graph w task x)) (allInputs task.space)
              c (c.headD []) [m] hc
            have hf := fold_spec env (cP (fun x => decide (Correct graph w task x)) (allInputs task.space))
              (Inv E L U d V m) _ (refine c (c.headD []) [m]) ?_ (0, []) c3 r c4 (by intro g hg; simp at hg) hr
            · rw [← hsum]
              simpa using hf.2
            · intro b hb st c5 r' c6 hst hr'
              cases hz : (bsz b == 0)
              · rw [hz] at hr'
                simp only [Bool.cond_false] at hr'
                cases hall : (b.all (· == (c.headD []).filter (· != m)))
                · rw [hall] at hr'
                  simp only [Bool.cond_false, Interp.counting_bind, CostM.run_bind] at hr'
                  split at hr'
                  · rename_i r0 c7 h0
                    simp only [Interp.counting_pure, CostM.run_pure, Interp.counting_nadd, Option.some.injEq,
                      Prod.mk.injEq] at hr'
                    obtain ⟨rfl, rfl⟩ := hr'
                    have := walk_spec env w E L U d V wc m (b.count [m]) _ _ dr pm (hcc (b.count [m])) 3 b _ [] st.2
                      r0.1 r0.2 c5 c7 (hWF b hb) hst h0
                    refine ⟨this.1, ?_⟩
                    simp only [Nat.add_eq]
                    omega
                  · cases hr'
                · rw [hall] at hr'
                  simp only [Bool.cond_true, Interp.counting_bind, CostM.run_bind] at hr'
                  split at hr'
                  · rename_i n0 c7 h0
                    simp only [Interp.counting_pure, CostM.run_pure, Interp.counting_nadd, Option.some.injEq,
                      Prod.mk.injEq] at hr'
                    obtain ⟨rfl, rfl⟩ := hr'
                    have := top_spec env w E L U d V wc mat hmat tab m b n0 c5 c7 (by omega) (hWF b hb) h0
                    refine ⟨hst, ?_⟩
                    simp only [Nat.add_eq]
                    omega
                  · cases hr'
              · rw [hz] at hr'
                simp only [Bool.cond_true, Interp.counting_pure, CostM.run_pure, Option.some.injEq,
                  Prod.mk.injEq] at hr'
                obtain ⟨rfl, rfl⟩ := hr'
                exact ⟨hst, by omega⟩
          · cases h
        · cases h
      · cases h
    · cases h

open Classical in
/-- Soundness, for every plan, every weights and every certificate. -/
theorem D_sound : ∀ (p : List Nat) (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D p Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro p w cert n cost h
  cases hE : List.lookup "embedding.weight" w with
  | none => simp [CostM.exec, D, Interp.counting_bind, CostM.run_bind, CostM.weightShape, nE, hE] at h
  | some E =>
  cases hL : List.lookup "linear.weight" w with
  | none => simp [CostM.exec, D, Interp.counting_bind, CostM.run_bind, CostM.weightShape, nE, nL, hE, hL] at h
  | some L =>
  cases hU : List.lookup "unembedding.weight" w with
  | none =>
    simp [CostM.exec, D, Interp.counting_bind, CostM.run_bind, CostM.weightShape, nE, nL, nU, hE, hL, hU] at h
  | some U =>
  simp only [CostM.exec, D, Interp.counting_bind, CostM.run_bind,
    CostM.weightShape, CostM.weightSize, nE, nL, nU, hE, hL, hU] at h
  have hE' : List.lookup "embedding.weight" (Env.mk w cert).weights = some E := hE
  have hL' : List.lookup "linear.weight" (Env.mk w cert).weights = some L := hL
  have hU' : List.lookup "unembedding.weight" (Env.mk w cert).weights = some U := hU
  split at h
  · split at h
    · rename_i d V hEs hcond
      obtain ⟨hLs, hUs, hEsz, hLsz, hUsz, hgV⟩ := hcond
      simp only [CostM.run_bind] at h
      split at h
      · rename_i le c1 hle
        split at h
        · rename_i mat c2 hmat
          have hleS := forall2_map_eq (fun row : List Q => row.map Q.val)
            (fun k => (List.range V).map fun t => LE E L d V k t) _ _
            (mapC_spec _ _ _ (List.range d)
              (fun k _ c r c' hr => leRow_spec _ E L d V k hE' hL' c r c' hr) _ _ _ hle)
          have hmatS : MatOk E L U d V mat := forall2_map_eq (fun row : List Q => row.map Q.val)
            (fun j => (List.range V).map fun t => Mat E L U d V j t) _ _
            (mapC_spec _ _ _ (List.range V)
              (fun j _ c r c' hr => matRow_spec _ E L U d V j hU' le hleS c r c' hr) _ _ _ hmat)
          have wc : WCtx w E L U d V := ⟨graph_positions, hgV, hE, hEs, hEsz, hL, hLs, hLsz, hU, hUs, hUsz⟩
          have hV : V = 64 := hgV.symm.trans graph_values
          have hc : WF (List.replicate 4 (List.range V)) := by
            refine ⟨by simp, fun s hs => ?_⟩
            rw [List.eq_of_mem_replicate hs]
            exact ⟨List.nodup_range, fun t ht => by rw [← hV]; exact List.mem_range.mp ht⟩
          have := top_spec ⟨w, cert⟩ w E L U d V wc mat hmatS (decode V p) V _ n c2 cost (le_refl V) hc h
          refine le_trans this ?_
          unfold cP numCorrect
          apply List.countP_mono_left
          intro x _ hx
          exact ((Bool.and_eq_true _ _).mp hx).2
        · cases h
      · cases h
    · simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
      omega
  · simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    omega

end Candidate.Ref
