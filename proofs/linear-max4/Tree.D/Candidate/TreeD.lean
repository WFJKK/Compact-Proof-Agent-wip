import Candidate.TreeCheck

namespace Candidate.Tree

open CompactCheck Protected.N_max4_v64_s0 Candidate.Linear Candidate.Boxes Candidate.Counted

/-! ## The tree generator (concrete data; nothing to prove about it) -/

def cuts (m : Nat) : List Nat := [m - 1, m - 2, m - 4, m - 8, m - 16, m - 32].filter (fun c => 0 < c)

def ivs (hi : Nat) : List Nat → List (Nat × Nat)
  | [] => [(0, hi)]
  | c :: cs => (c, hi) :: ivs c cs

def famOf (m : Nat) : List (Nat × Nat) := ivs (m + 1) (m :: cuts m)

def refine (p : Nat) : List Nat → BTree → BTree
  | [], next => next
  | c :: cs, next => .split p c (refine p cs next) next

def refineCoords (m i : Nat) : List Nat → BTree
  | [] => .leaf
  | q :: qs => if q = i then refineCoords m i qs
    else refine q (if q < i then cuts m else m :: cuts m) (refineCoords m i qs)

def genSplits (P m : Nat) : List Nat → BTree → BTree
  | [], tail => tail
  | i :: is, tail => .split i m (genSplits P m is tail) (refineCoords m i (List.range P))

def genM (P : Nat) : Nat → Nat → BTree
  | 0, _ => .skip
  | fuel + 1, m => genSplits P m (List.range P) (if m = 0 then .skip else .useM (m - 1) (genM P fuel (m - 1)))

/-! ## The checker -/

def nE : String := "embedding.weight"
def nL : String := "linear.weight"
def nU : String := "unembedding.weight"

def D : Checker := fun I => do
  let es ← I.weightShape nE
  let ls ← I.weightShape nL
  let us ← I.weightShape nU
  let esz ← I.weightSize nE
  let lsz ← I.weightSize nL
  let usz ← I.weightSize nU
  match es with
  | [d, V] =>
    if ls = [d, d] ∧ us = [V, d] ∧ esz = d * V ∧ lsz = d * d ∧ usz = V * d ∧ graph.values = V then do
      let le ← mapC I (fun k => leRow I d V k) (List.range d)
      let mat ← mapC I (fun j => matRow I d V j le) (List.range V)
      countTree I mat graph.positions V famOf V [] (List.replicate graph.positions (0, V))
        (.useM (V - 1) (genM graph.positions V (V - 1)))
    else pure I.nzero
  | _ => pure I.nzero

/-! ## Soundness -/

open Classical in
theorem countTree_le (env : Env) (E L U : Tensor ℚ) (d P V : Nat)
    (hgP : graph.positions = P) (hgV : graph.values = V)
    (hE : List.lookup "embedding.weight" env.weights = some E) (hEs : E.shape = [d, V])
    (hEsz : E.data.size = d * V)
    (hL : List.lookup "linear.weight" env.weights = some L) (hLs : L.shape = [d, d])
    (hLsz : L.data.size = d * d)
    (hU : List.lookup "unembedding.weight" env.weights = some U) (hUs : U.shape = [V, d])
    (hUsz : U.data.size = V * d)
    (mat : List (List Q)) (hmat : MatOk E L U d V mat) (fam : Nat → List (Nat × Nat)) :
    ∀ (t : BTree) (m : Nat) (tbl : List (List Q)) (bs : List (Nat × Nat)) (c : Cost) (n : Nat) (c' : Cost),
    (m < V → TblOk E L U d V fam m tbl) → (∀ b ∈ bs, b.2 ≤ V) →
    (countTree Interp.counting mat P V fam m tbl bs t).run env c = some (n, c') →
    n ≤ (allInputs task.space).countP
      (fun x => inBox bs x && decide (Correct graph env.weights task x))
  | .leaf, m, tbl, bs, c, n, c', htbl, hbs, h => by
    simp only [countTree] at h
    split at h
    · rename_i hsh
      simp only [Interp.counting_bind, CostM.run_bind] at h
      split at h
      · rename_i ok c1 hok
        simp only [Interp.counting_pure, CostM.run_pure, Interp.counting_nscale, Option.some.injEq,
          Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        cases ok with
        | false => simp
        | true =>
          simp only [Bool.cond_true]
          simp only [leafShape, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.any_eq_true,
            decide_eq_true_eq] at hsh
          obtain ⟨⟨⟨hlen, hm⟩, hfit⟩, hS⟩ := hsh
          have hall := (allOk_spec env (fam m) tbl bs _ true c c1 hok).2
          have hcor : ∀ x, inBox bs x = true → Correct graph env.weights task x := by
            intro x hx
            apply correct_of_box env.weights E L U d P V hgP hgV hE hEs hEsz hL hLs hLsz hU hUs hUsz
              bs hlen m hm hfit hS _ x hx
            intro j hj hne
            obtain ⟨vs, hvs, hpos⟩ := hall j (by simp [List.mem_filter, hj, hne])
            have hf2 := lookups_spec _ (fam m) (tbl.getD j [])
              (lookupIv_spec _ _ _ (htbl hm j hj)) bs vs hvs
            refine ⟨fun p => (vs.getD p ⟨0⟩).val, ?_, ?_⟩
            · intro p hp t h1 h2
              exact forall2_getD _ ⟨0⟩ bs vs hf2 p hp t h1 h2
                (by have := hfit bs[p] (List.getElem_mem hp); omega)
            · rw [sum_eq_sum_getD, List.length_map, ← hf2.length_eq, hlen] at hpos
              simpa only [getD_val] using hpos
          have h1 : (allInputs task.space).countP (inBox bs) ≤ (allInputs task.space).countP
              (fun x => inBox bs x && decide (Correct graph env.weights task x)) := by
            apply List.countP_mono_left
            intro x _ hx
            simp [hx, hcor x hx]
          have hV : V = 64 := hgV.symm.trans graph_values
          have hP : P = 4 := hgP.symm.trans graph_positions
          have h2 := countP_inBox bs task.space (by
            rw [task_space]
            have := forall2_of_bound bs P V hlen hbs
            rw [hV, hP] at this
            exact this)
          omega
      · cases h
    · simp only [Interp.counting_pure, CostM.run_pure, Interp.counting_nzero, Option.some.injEq,
        Prod.mk.injEq] at h
      omega
  | .skip, m, tbl, bs, c, n, c', htbl, hbs, h => by
    simp only [countTree, Interp.counting_pure, CostM.run_pure, Interp.counting_nzero, Option.some.injEq,
      Prod.mk.injEq] at h
    omega
  | .split p mid l r, m, tbl, bs, c, n, c', htbl, hbs, h => by
    simp only [countTree] at h
    split at h
    · rename_i lo hi hbp
      split at h
      · rename_i hcond
        simp only [Interp.counting_bind, CostM.run_bind] at h
        split at h
        · rename_i a c1 ha
          split at h
          · rename_i b c2 hb
            simp only [Interp.counting_pure, CostM.run_pure, Interp.counting_nadd, Option.some.injEq,
              Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hmem : (lo, hi) ∈ bs := List.mem_of_getElem? hbp
            have hhi := hbs _ hmem
            have hb1 : ∀ b ∈ bs.set p (lo, mid), b.2 ≤ V := by
              intro b hb
              rcases List.mem_or_eq_of_mem_set hb with hb | rfl
              · exact hbs b hb
              · simp only at hhi ⊢; omega
            have hb2 : ∀ b ∈ bs.set p (mid, hi), b.2 ≤ V := by
              intro b hb
              rcases List.mem_or_eq_of_mem_set hb with hb | rfl
              · exact hbs b hb
              · exact hhi
            have iha := countTree_le env E L U d P V hgP hgV hE hEs hEsz hL hLs hLsz hU hUs hUsz mat hmat
              fam l m tbl _ _ a _ htbl hb1 ha
            have ihb := countTree_le env E L U d P V hgP hgV hE hEs hEsz hL hLs hLsz hU hUs hUsz mat hmat
              fam r m tbl _ _ b _ htbl hb2 hb
            have hsplit := countP_split_or (inBox bs) (inBox (bs.set p (lo, mid))) (inBox (bs.set p (mid, hi)))
              (fun x => decide (Correct graph env.weights task x))
              (fun x => (inBox_split bs p lo hi mid x hbp hcond.1 hcond.2).1)
              (fun x => (inBox_split bs p lo hi mid x hbp hcond.1 hcond.2).2) (allInputs task.space)
            rw [hsplit]
            simp only [Nat.add_eq]
            omega
          · cases h
        · cases h
      · simp only [Interp.counting_pure, CostM.run_pure, Interp.counting_nzero, Option.some.injEq,
          Prod.mk.injEq] at h
        omega
    · simp only [Interp.counting_pure, CostM.run_pure, Interp.counting_nzero, Option.some.injEq,
        Prod.mk.injEq] at h
      omega
  | .useM m' t, m, tbl, bs, c, n, c', htbl, hbs, h => by
    simp only [countTree, Interp.counting_bind, CostM.run_bind] at h
    split at h
    · rename_i tbl' c1 ht
      exact countTree_le env E L U d P V hgP hgV hE hEs hEsz hL hLs hLsz hU hUs hUsz mat hmat fam t m' tbl'
        bs c1 n c' (fun hm => mkTable_spec env E L U d V fam mat hmat m' hm c tbl' c1 ht) hbs h
    · cases h

open Classical in
theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w cert n cost h
  cases hE : List.lookup "embedding.weight" w with
  | none => simp [CostM.exec, D, Interp.counting_bind, CostM.run_bind, CostM.weightShape, nE, hE] at h
  | some E =>
  cases hL : List.lookup "linear.weight" w with
  | none => simp [CostM.exec, D, Interp.counting_bind, CostM.run_bind, CostM.weightShape, nE, nL, hE, hL] at h
  | some L =>
  cases hU : List.lookup "unembedding.weight" w with
  | none => simp [CostM.exec, D, Interp.counting_bind, CostM.run_bind, CostM.weightShape, nE, nL, nU, hE, hL, hU] at h
  | some U =>
  simp only [CostM.exec, D, Interp.counting_bind, CostM.run_bind, Interp.counting_weightShape,
    Interp.counting_weightSize, CostM.weightShape, CostM.weightSize, nE, nL, nU, hE, hL, hU] at h
  have hE' : List.lookup "embedding.weight" (Env.mk w cert).weights = some E := hE
  have hL' : List.lookup "linear.weight" (Env.mk w cert).weights = some L := hL
  have hU' : List.lookup "unembedding.weight" (Env.mk w cert).weights = some U := hU
  split at h
  · split at h
    · rename_i d V hEs hcond
      ·
            obtain ⟨hLs, hUs, hEsz, hLsz, hUsz, hgV⟩ := hcond
            simp only [Interp.counting_bind, CostM.run_bind] at h
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
                have hbs : ∀ b ∈ List.replicate graph.positions ((0, V) : Nat × Nat), b.2 ≤ V := by
                  intro b hb
                  rw [List.eq_of_mem_replicate hb]
                have := countTree_le ⟨w, cert⟩ E L U d graph.positions V rfl hgV hE' hEs hEsz hL' hLs hLsz
                  hU' hUs hUsz mat hmatS famOf _ V [] _ _ n cost (fun hm => absurd hm (lt_irrefl V)) hbs h
                refine le_trans this ?_
                unfold numCorrect
                apply List.countP_mono_left
                intro x _ hx
                exact ((Bool.and_eq_true _ _).mp hx).2
              · cases h
            · cases h
    · simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
      omega
  · simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    omega

end Candidate.Tree
