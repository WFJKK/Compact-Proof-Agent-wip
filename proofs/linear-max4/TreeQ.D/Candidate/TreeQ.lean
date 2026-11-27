import Candidate.TreeD

namespace Candidate.TreeQ

open CompactCheck Protected.N_max4_v64_s0 Candidate.Linear Candidate.Boxes Candidate.Counted Candidate.Tree

/-! ## The tree generator, steered by a plan: per m (in order m = 0, 1, ...), a count n then n deltas;
    cut_1 = m - 1 - d_1, cut_{k+1} = cut_k - 1 - d_{k+1}. -/

def decodeCuts (prev : Nat) : Nat → List Nat → List Nat × List Nat
  | 0, rest => ([], rest)
  | k + 1, rest =>
    let c := prev - 1 - rest.headD 0
    let r := decodeCuts c k rest.tail
    (c :: r.1, r.2)

def decodeAll (m : Nat) : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | fuel + 1, rest =>
    let r := decodeCuts m (rest.headD 0) rest.tail
    r.1 :: decodeAll (m + 1) fuel r.2

def cutsOf (tbl : List (List Nat)) (m : Nat) : List Nat := tbl.getD m []

def famP (tbl : List (List Nat)) (m : Nat) : List (Nat × Nat) := ivs (m + 1) (m :: cutsOf tbl m)

def refineCoordsP (tbl : List (List Nat)) (m i : Nat) : List Nat → BTree
  | [] => .leaf
  | q :: qs => if q = i then refineCoordsP tbl m i qs
    else refine q (if q < i then cutsOf tbl m else m :: cutsOf tbl m) (refineCoordsP tbl m i qs)

def genSplitsP (tbl : List (List Nat)) (P m : Nat) : List Nat → BTree → BTree
  | [], tail => tail
  | i :: is, tail => .split i m (genSplitsP tbl P m is tail) (refineCoordsP tbl m i (List.range P))

def genMP (tbl : List (List Nat)) (P : Nat) : Nat → Nat → BTree
  | 0, _ => .skip
  | fuel + 1, m => genSplitsP tbl P m (List.range P) (if m = 0 then .skip else .useM (m - 1) (genMP tbl P fuel (m - 1)))

/-! ## The checker -/

def D (p : List Nat) : Checker := fun I => do
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
      let tbl := decodeAll 0 V p
      countTree I mat graph.positions V (famP tbl) V [] (List.replicate graph.positions (0, V))
        (.useM (V - 1) (genMP tbl graph.positions V (V - 1)))
    else pure I.nzero
  | _ => pure I.nzero

open Classical in
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
  | none => simp [CostM.exec, D, Interp.counting_bind, CostM.run_bind, CostM.weightShape, nE, nL, nU, hE, hL, hU] at h
  | some U =>
  simp only [CostM.exec, D, Interp.counting_bind, CostM.run_bind,
    CostM.weightShape, CostM.weightSize, nE, nL, nU, hE, hL, hU] at h
  have hE' : List.lookup "embedding.weight" (Env.mk w cert).weights = some E := hE
  have hL' : List.lookup "linear.weight" (Env.mk w cert).weights = some L := hL
  have hU' : List.lookup "unembedding.weight" (Env.mk w cert).weights = some U := hU
  split at h
  · split at h
    · rename_i d V hEs hcond
      ·
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
                have hbs : ∀ b ∈ List.replicate graph.positions ((0, V) : Nat × Nat), b.2 ≤ V := by
                  intro b hb
                  rw [List.eq_of_mem_replicate hb]
                have := countTree_le ⟨w, cert⟩ E L U d graph.positions V rfl hgV hE' hEs hEsz hL' hLs hLsz
                  hU' hUs hUsz mat hmatS (famP (decodeAll 0 V p)) _ V [] _ _ n cost
                  (fun hm => absurd hm (lt_irrefl V)) hbs h
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

end Candidate.TreeQ
