import Candidate.TreeD

namespace Candidate.TreeP

open CompactCheck Protected.N_max4_v64_s0 Candidate.Linear Candidate.Boxes Candidate.Counted Candidate.Tree

/-! ## The tree generator, steered by a plan: per m, K singleton cuts below m, then blocks sz0, 2 sz0, ... -/

def blocks : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | f + 1, c, sz => if c ≤ sz then [] else (c - sz) :: blocks f (c - sz) (2 * sz)

def cutsP (m K sz0 : Nat) : List Nat :=
  ((List.range K).map (fun i => m - 1 - i)).filter (fun c => 0 < c) ++ blocks 64 (m - K) sz0

def cutsOf (p : List Nat) (m : Nat) : List Nat := cutsP m (p.getD (2 * m) 0) (p.getD (2 * m + 1) 1)

def famP (p : List Nat) (m : Nat) : List (Nat × Nat) := ivs (m + 1) (m :: cutsOf p m)

def refineCoordsP (p : List Nat) (m i : Nat) : List Nat → BTree
  | [] => .leaf
  | q :: qs => if q = i then refineCoordsP p m i qs
    else refine q (if q < i then cutsOf p m else m :: cutsOf p m) (refineCoordsP p m i qs)

def genSplitsP (p : List Nat) (P m : Nat) : List Nat → BTree → BTree
  | [], tail => tail
  | i :: is, tail => .split i m (genSplitsP p P m is tail) (refineCoordsP p m i (List.range P))

def genMP (p : List Nat) (P : Nat) : Nat → Nat → BTree
  | 0, _ => .skip
  | fuel + 1, m => genSplitsP p P m (List.range P) (if m = 0 then .skip else .useM (m - 1) (genMP p P fuel (m - 1)))

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
      countTree I mat graph.positions V (famP p) V [] (List.replicate graph.positions (0, V))
        (.useM (V - 1) (genMP p graph.positions V (V - 1)))
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
                  hU' hUs hUsz mat hmatS (famP p) _ V [] _ _ n cost (fun hm => absurd hm (lt_irrefl V)) hbs h
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

end Candidate.TreeP
