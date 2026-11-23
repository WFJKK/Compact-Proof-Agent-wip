import Protected.N_attn_max4_v64_s0
import CompactCheck.Soundness
import CompactCheck.CountedOps
import CompactCheck.CountedGeneralSound

/-!
# A probe for the dry start: the single-input rule on the first inputs of the network

Not a proof of anything worth having: it certifies at most as many inputs as the last position has values.
Its use is to see, before a run, that the Lean service exports this network, compiles a module against it,
checks a soundness theorem, runs the compiled checker here and scores it, and how long that takes.

The inputs are those with every position 0 but the last (`firstInputs`), built without `allInputs`: on a
network of millions of inputs a compiled checker that mentions `allInputs task.space` builds the whole list
before anything else. They are a sublist of all inputs for any space, which is all the soundness needs.
-/

namespace Candidate.Probe

open CompactCheck Protected.N_attn_max4_v64_s0

/-- The single rule for general networks (`I.gsingle`, the exact forward pass) on each input of `xs`,
counting the passes; each call is billed. -/
def countSingles (I : Interp) (g : Graph) (task : Task) : List Input → I.M I.N
  | [] => pure I.nzero
  | x :: xs => do
    let ok ← I.gsingle g task x
    let n ← countSingles I g task xs
    pure (I.nadd (I.countB ok) n)

/-- Every position 0 but the last, which takes each of its values. -/
def firstInputs : List Nat → List Input
  | [] => [[]]
  | [v] => (List.range v).map fun t => [t]
  | v :: w :: vs => if v = 0 then [] else (firstInputs (w :: vs)).map (0 :: ·)

/-- The checker: the first inputs of the task's space. -/
def D : Checker := fun I => countSingles I graph task (firstInputs task.space)

open Classical in
/-- `countSingles` never counts more than the inputs that are correct, for any weights and bill. -/
theorem countSingles_le (env : Env) : ∀ (xs : List Input) (c : Cost) (n : Nat) (c' : Cost),
    (countSingles Interp.counting graph task xs).run env c = some (n, c') →
    n ≤ xs.countP (fun x => decide (Correct graph env.weights task x))
  | [], c, n, c', h => by
    simp only [countSingles, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    omega
  | x :: xs, c, n, c', h => by
    simp only [countSingles, CostM.run_bind] at h
    split at h
    · rename_i ok c1 hs
      split at h
      · rename_i m c2 hm
        have ih := countSingles_le env xs c1 m c2 hm
        rw [List.countP_cons]
        simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
        cases ok with
        | false => simp only [Bool.cond_false, Nat.add_eq] at h; omega
        | true =>
          have hc : Correct graph env.weights task x := CostM.gsingle_correct hs
          simp only [Bool.cond_true, Nat.add_eq] at h
          simp only [hc, decide_true, ite_true]
          omega
      · cases h
    · cases h

/-- The first inputs are a sublist of all inputs, for any space. -/
theorem firstInputs_sublist : ∀ (space : List Nat), List.Sublist (firstInputs space) (allInputs space)
  | [] => by simp only [firstInputs, allInputs]; exact List.Sublist.refl _
  | [v] => by
    have h : allInputs [v] = (List.range v).map fun t => [t] := by
      simp only [allInputs, List.map_cons, List.map_nil]
      induction List.range v with
      | nil => rfl
      | cons a l ih => simp only [List.flatMap_cons, List.map_cons, ih]; rfl
    rw [h]; simp only [firstInputs]; exact List.Sublist.refl _
  | v :: w :: vs => by
    simp only [firstInputs]
    split
    · exact List.nil_sublist _
    · rename_i hv
      obtain ⟨k, rfl⟩ : ∃ k, v = k + 1 := ⟨v - 1, by omega⟩
      have ih := firstInputs_sublist (w :: vs)
      show List.Sublist _ ((List.range (k + 1)).flatMap fun t => (allInputs (w :: vs)).map (t :: ·))
      rw [List.range_succ_eq_map, List.flatMap_cons]
      exact List.Sublist.trans (ih.map (0 :: ·)) (List.sublist_append_left _ _)

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  unfold numCorrect
  exact Nat.le_trans (countSingles_le ⟨w, c⟩ (firstInputs task.space) [] n cost h)
    (firstInputs_sublist task.space).countP_le

end Candidate.Probe
