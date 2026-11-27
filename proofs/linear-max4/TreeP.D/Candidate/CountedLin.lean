import Candidate.BoxCorrect

/-!
# Counted-language helpers for the checker: reading weight entries and dot products, with their
specifications under the counting interpreter.
-/

namespace Candidate.Counted

open CompactCheck

/-- Read the entries of weight `name` at the given indices (free). -/
def readIdx (I : Interp) (name : String) : List Nat → I.M (List I.V)
  | [] => pure []
  | i :: is => do
    let v ← I.weight name i
    let vs ← readIdx I name is
    pure (v :: vs)

/-- `acc + Σ x_i * y_i` by multiply-adds, 1 each. -/
def dot (I : Interp) : List I.V → List I.V → I.V → I.M I.V
  | x :: xs, y :: ys, acc => do
    let acc' ← I.muladd "mac" acc x y
    dot I xs ys acc'
  | _, _, acc => pure acc

theorem readIdx_spec (env : Env) (name : String) (t : Tensor ℚ)
    (ht : List.lookup name env.weights = some t) :
    ∀ (is : List Nat) (c : Cost) (vs : List Q) (c' : Cost),
    (readIdx Interp.counting name is).run env c = some (vs, c') →
    vs.map Q.val = is.map t.get ∧ c' = c
  | [], c, vs, c', h => by
    simp only [readIdx, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | i :: is, c, vs, c', h => by
    simp only [readIdx, Interp.counting_bind, CostM.run_bind, Interp.counting_weight] at h
    split at h
    · rename_i v c1 hv
      obtain ⟨hv1, rfl⟩ := CostM.weight_run_get ht hv
      split at h
      · rename_i vs1 c2 hvs
        obtain ⟨ih1, rfl⟩ := readIdx_spec env name t ht is _ vs1 c2 hvs
        simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        simp [hv1, ih1]
      · cases h
    · cases h

theorem dot_spec (env : Env) : ∀ (xs ys : List Q) (acc : Q) (c : Cost) (r : Q) (c' : Cost),
    (dot Interp.counting xs ys acc).run env c = some (r, c') →
    r.val = acc.val + (List.zipWith (fun x y : Q => x.val * y.val) xs ys).sum
  | [], ys, acc, c, r, c', h => by
    simp only [dot, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | x :: xs, [], acc, c, r, c', h => by
    simp only [dot, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | x :: xs, y :: ys, acc, c, r, c', h => by
    simp only [dot, Interp.counting_bind, CostM.run_bind, Interp.counting_muladd, CostM.qmuladd] at h
    have ih := dot_spec env xs ys ⟨acc.val + x.val * y.val⟩ (c.add "mac" 1) r c' h
    rw [ih]
    simp [add_assoc]

end Candidate.Counted
