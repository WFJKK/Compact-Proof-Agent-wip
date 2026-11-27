import Candidate.CvxSpec

/-!
# Soundness of the convexity-only checker: `D_sound`
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
/-- A box that passes the test: what it counts is correct. -/
theorem box_le (w : Weights ℚ) (E L U : Tensor ℚ) (d V : Nat) (wc : WCtx w E L U d V) (m : Nat) (hm : m < V)
    (b : Box) (hb : WF b) (hP : Passes E L U d V m b) :
    bsz b ≤ cP (fun x => decide (Correct graph w task x)) (allInputs task.space) b :=
  bsz_le w b hb (fun x hx => correct_of_passes w E L U d 4 V wc.hgP wc.hgV wc.hE wc.hEs wc.hEsz
    wc.hL wc.hLs wc.hLsz wc.hU wc.hUs wc.hUsz rfl b b m hm hP (List.Perm.refl b) x hx)

open Classical in
/-- A node: what it counts is correct, and the table of minima stays right, given the same of `k`. -/
theorem nodeW_spec (env : Env) (w : Weights ℚ) (E L U : Tensor ℚ) (d V : Nat) (wc : WCtx w E L U d V)
    (m : Nat) (rws : List (Nat × Array Q × List Q × List Q)) (ro : ROk E L U d V m rws)
    (tab : List (List Nat × List Nat))
    (k : Box → List Nat → List Nat → List ((Nat × Nat) × List Nat × List Q) →
      Interp.counting.M (Nat × List ((Nat × Nat) × List Nat × List Q)))
    (hk : ∀ (b : Box) (G F : List Nat) (tbl : List ((Nat × Nat) × List Nat × List Q)) (n : Nat)
      (tbl' : List ((Nat × Nat) × List Nat × List Q)) (c0 c' : Cost),
      WF b → MInv rws tbl → (k b G F tbl).run env c0 = some ((n, tbl'), c') →
      MInv rws tbl' ∧ n ≤ cP (fun x => decide (Correct graph w task x)) (allInputs task.space) b)
    (c : Box) (S F : List Nat) (tbl : List ((Nat × Nat) × List Nat × List Q)) (n : Nat)
    (tbl' : List ((Nat × Nat) × List Nat × List Q)) (c0 c' : Cost) (hc : WF c) (hinv : MInv rws tbl)
    (h : (nodeW Interp.counting m rws tab k c S F tbl).run env c0 = some ((n, tbl'), c')) :
    MInv rws tbl' ∧ n ≤ cP (fun x => decide (Correct graph w task x)) (allInputs task.space) c := by
  simp only [nodeW] at h
  generalize hB : (tab.lookup F).getD [] = B at h
  generalize hG : S.filter (fun t => !B.contains t) = G at h
  cases hr0 : (c.count S == 0)
  · rw [hr0] at h
    simp only [Bool.cond_false] at h
    obtain ⟨hWF, hsum⟩ := refine_spec (fun x => decide (Correct graph w task x)) (allInputs task.space) c S B hc
    have hf := fold_spec env (cP (fun x => decide (Correct graph w task x)) (allInputs task.space))
      (MInv rws) _ (refine c S B) ?_ (0, tbl) c0 (n, tbl') c' hinv h
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
          have hr0' : MInv rws r0.2 ∧
              r0.1 ≤ cP (fun x => decide (Correct graph w task x)) (allInputs task.space) b := by
            cases hself : (b.count G == c.count S)
            · rw [hself] at h0
              simp only [Bool.cond_false] at h0
              cases h1 : (c.count S == 1)
              · rw [h1] at h0
                simp only [Bool.cond_false] at h0
                exact hk b _ _ st.2 r0.1 r0.2 c1 c3 (hWF b hb) hst h0
              · rw [h1] at h0
                simp only [Bool.cond_true, Interp.counting_pure, CostM.run_pure, Interp.counting_nzero,
                  Option.some.injEq, Prod.mk.injEq] at h0
                obtain ⟨rfl, rfl⟩ := h0
                exact ⟨hst, Nat.zero_le _⟩
            · rw [hself] at h0
              simp only [Bool.cond_true, Interp.counting_bind, CostM.run_bind] at h0
              split at h0
              · rename_i mt c4 hmt
                split at h0
                · rename_i g c5 hg5
                  simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h0
                  obtain ⟨rfl, rfl⟩ := h0
                  obtain ⟨hinv', hF⟩ := mins_spec env rws (fun r hr => (ro.ok r hr).2.2) G st.2 hst mt.1 mt.2 c1 c4 hmt
                  refine ⟨hinv', ?_⟩
                  cases g
                  · simp
                  · simp only [Interp.counting_nscale, Bool.cond_true]
                    exact box_le w E L U d V wc m ro.hm b (hWF b hb)
                      (tst_spec env E L U d V m rws ro b G mt.1 hF c4 c5 true hg5 rfl)
                · cases h0
              · cases h0
          refine ⟨hr0'.1, ?_⟩
          simp only [Nat.add_eq]
          omega
        · cases hr
      · rw [hz] at hr
        simp only [Bool.cond_true, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        exact ⟨hst, by omega⟩
  · rw [hr0] at h
    simp only [Bool.cond_true, Interp.counting_bind, CostM.run_bind] at h
    split at h
    · rename_i g c1 hg1
      simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      refine ⟨hinv, ?_⟩
      cases g
      · simp
      · simp only [Interp.counting_nscale, Bool.cond_true]
        exact box_le w E L U d V wc m ro.hm c hc
          (tst_spec env E L U d V m rws ro c [] _ (MinOk_nil rws _) c0 c1 true hg1 rfl)
    · cases h

open Classical in
/-- The walk of a class box: what it counts is correct, and the table of minima stays right. -/
theorem walk_spec (env : Env) (w : Weights ℚ) (E L U : Tensor ℚ) (d V : Nat) (wc : WCtx w E L U d V)
    (m : Nat) (rws : List (Nat × Array Q × List Q × List Q)) (ro : ROk E L U d V m rws)
    (tab : List (List Nat × List Nat)) :
    ∀ (fuel : Nat) (c : Box) (S F : List Nat) (tbl : List ((Nat × Nat) × List Nat × List Q)) (n : Nat)
      (tbl' : List ((Nat × Nat) × List Nat × List Q)) (c0 c' : Cost), WF c → MInv rws tbl →
    (walk Interp.counting m rws tab fuel c S F tbl).run env c0 = some ((n, tbl'), c') →
    MInv rws tbl' ∧ n ≤ cP (fun x => decide (Correct graph w task x)) (allInputs task.space) c
  | 0, c, S, F, tbl, n, tbl', c0, c', hc, hinv, h => by
    simp only [walk] at h
    refine nodeW_spec env w E L U d V wc m rws ro tab _ ?_ c S F tbl n tbl' c0 c' hc hinv h
    intro b G F tbl n tbl' c0 c' _ hinv h
    simp only [Interp.counting_pure, CostM.run_pure, Interp.counting_nzero, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨hinv, Nat.zero_le _⟩
  | fuel + 1, c, S, F, tbl, n, tbl', c0, c', hc, hinv, h => by
    simp only [walk] at h
    exact nodeW_spec env w E L U d V wc m rws ro tab _
      (fun b G F tbl n tbl' c0 c' hb hinv h => walk_spec env w E L U d V wc m rws ro tab fuel b G F tbl n tbl' c0 c'
        hb hinv h) c S F tbl n tbl' c0 c' hc hinv h

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

open Classical in
/-- A level: what the 15 class boxes and the next level count is correct. -/
theorem top_spec (env : Env) (w : Weights ℚ) (E L U : Tensor ℚ) (d V : Nat) (wc : WCtx w E L U d V)
    (mat : List (List Q)) (hmat : MatOk E L U d V mat) (tabs : List (List (List Nat × List Nat))) (depth : Nat) :
    ∀ (fuel : Nat) (c : Box) (n : Nat) (c0 c' : Cost), fuel ≤ V → WF c →
    (top Interp.counting V mat tabs depth fuel c).run env c0 = some (n, c') →
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
          -- the running minima
          have hP := mapC_spec env _ (fun j (pr : List Q) => PrOk ((dr.getD j []).map Q.val) (pr.map Q.val))
            (List.range V) (fun j _ c r c' hr => by
              cases hb : (j == m)
              · rw [hb] at hr
                exact (scan_spec env _ m c r c' hr).1
              · rw [hb] at hr
                simp only [Bool.cond_true, Interp.counting_pure, CostM.run_pure, Option.some.injEq,
                  Prod.mk.injEq] at hr
                obtain ⟨rfl, rfl⟩ := hr
                exact PrOk_nil _) c1 pm c2 hpm
          have hpr : ∀ j, PrOk ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val) := by
            intro j
            by_cases hj : j < V
            · have h1 := forall2_getD _ [] _ _ hP j (by simpa using hj)
              simp only [List.getElem_range] at h1
              exact h1
            · have hpj : pm.getD j [] = [] := by
                rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by have := hP.length_eq; simp at this; omega)]
                rfl
              rw [hpj]
              exact PrOk_nil _
          generalize hrws : ((List.range V).filter (· != m)).map
            (fun j => (j, Array.mk (dr.getD j []), dr.getD j [], pm.getD j [])) = rws at hr
          have ro : ROk E L U d V m rws := by
            refine ⟨hm, fun r hr => ?_, fun j hj hjm => ?_⟩
            · rw [← hrws, List.mem_map] at hr
              obtain ⟨j, hj, rfl⟩ := hr
              simp only [List.mem_filter, List.mem_range, bne_iff_ne, ne_eq] at hj
              exact ⟨rfl, hdrS j hj.1 hj.2, hpr j⟩
            · refine ⟨(j, Array.mk (dr.getD j []), dr.getD j [], pm.getD j []), ?_, rfl⟩
              rw [← hrws, List.mem_map]
              exact ⟨j, by simp [hj, hjm], rfl⟩
          obtain ⟨hWF, hsum⟩ := refine_spec (fun x => decide (Correct graph w task x)) (allInputs task.space)
            c (c.headD []) [m] hc
          have hf := fold_spec env (cP (fun x => decide (Correct graph w task x)) (allInputs task.space))
            (MInv rws) _ (refine c (c.headD []) [m]) ?_ (0, []) c2 r c4 (by intro e he; simp at he) hr
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
                  have := walk_spec env w E L U d V wc m rws ro _ depth b _ [] st.2 r0.1 r0.2 c5 c7 (hWF b hb) hst h0
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
                  have := top_spec env w E L U d V wc mat hmat tabs depth m b n0 c5 c7 (by omega) (hWF b hb) h0
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
          have := top_spec ⟨w, cert⟩ w E L U d V wc mat hmatS (decode V p) (p.headD 0) V _ n c2 cost (le_refl V) hc h
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
