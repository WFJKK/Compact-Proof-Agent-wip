import Candidate.Inputs
import Candidate.Bounds

/-!
# Template: specifications of the first tables of `buildTabs` (last, dm) under the counting interpreter.
-/

namespace Candidate.Tables
open CompactCheck Candidate.Loops Candidate.Formula Finset

section
variable {env : Env} {E P U : Tensor ℚ}

/-- The `last` table: entry `t3*32+d` is `E[t3*32+d] + P[96+d]`. -/
theorem spec_last (hE : List.lookup "E" env.weights = some E) (hP : List.lookup "P" env.weights = some P) :
    Spec env (tableM Interp.counting (fun k => do
        let e ← Interp.counting.weight "E" k
        let p ← Interp.counting.weight "P" (96 + k % 32)
        Interp.counting.add "" e p) 2048 0 (E0 Interp.counting))
      fun arr => arr.toList.map Q.val = (List.range 2048).map fun k => E.get k + P.get (96 + k % 32) := by
  have h := spec_tableM (env := env) (g := fun k => E.get k + P.get (96 + k % 32))
    (f := fun k => do
        let e ← Interp.counting.weight "E" k
        let p ← Interp.counting.weight "P" (96 + k % 32)
        Interp.counting.add "" e p) ?_ 2048 0 (E0 Interp.counting)
  · refine spec_mono ?_ h
    intro arr harr
    rw [harr]
    simp [E0]
  · intro i
    refine spec_bind (spec_weight hE i) fun e he => ?_
    refine spec_bind (spec_weight hP _) fun p hp => ?_
    refine spec_mono ?_ (spec_add "" e p)
    intro v hv
    rw [hv, he, hp]

/-- A table of dot products of a known table with a weight: entry `k` is `Σ_d a (k/64*32+d) * U[d*64 + k%64]`. -/
theorem spec_dm (hU : List.lookup "U" env.weights = some U) (lastv : Array Q) (lastf : Nat → ℚ)
    (hlast : ∀ k, (lastv.getD k ⟨0⟩).val = lastf k) :
    Spec env (tableM Interp.counting (fun k =>
        dotM Interp.counting (fun d => pure (lastv.getD (k / 64 * 32 + d) Interp.counting.zero))
          (fun d => Interp.counting.weight "U" (d * 64 + k % 64)) 32 Interp.counting.zero) 4096 0 (E0 Interp.counting))
      fun arr => arr.toList.map Q.val =
        (List.range 4096).map fun k => ∑ d ∈ range 32, lastf (k / 64 * 32 + d) * U.get (d * 64 + k % 64) := by
  have h := spec_tableM (env := env)
    (g := fun k => ∑ d ∈ range 32, lastf (k / 64 * 32 + d) * U.get (d * 64 + k % 64))
    (f := fun k => dotM Interp.counting (fun d => pure (lastv.getD (k / 64 * 32 + d) Interp.counting.zero))
          (fun d => Interp.counting.weight "U" (d * 64 + k % 64)) 32 Interp.counting.zero)
    ?_ 4096 0 (E0 Interp.counting)
  · refine spec_mono ?_ h
    intro arr harr
    rw [harr]
    simp [E0]
  · intro k
    refine spec_mono ?_ (spec_dotM (fa := fun d => lastf (k / 64 * 32 + d))
      (fb := fun d => U.get (d * 64 + k % 64)) 32 Interp.counting.zero ?_ ?_)
    · intro v hv
      rw [hv]
      show (0 : ℚ) + _ = _
      rw [zero_add]
    · intro d _
      exact spec_pure (hlast _)
    · intro d _
      exact spec_weight hU _

end

end Candidate.Tables
