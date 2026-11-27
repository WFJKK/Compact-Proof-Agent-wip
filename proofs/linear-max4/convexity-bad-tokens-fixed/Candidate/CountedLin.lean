import Candidate.BoxCorrect

/-!
# Counted-language helpers: a counted map, reading weight entries and dot products, with their specifications
under the counting interpreter. (After the agent's CountedLin.lean; `readIdx` and `dot` are written with `mapC`
and `List.foldlM` here, which keeps the checker's description small.)
-/

namespace Candidate.Counted

open CompactCheck

/-- The one bill category. -/
def ct : String := "op"

def mapC (I : Interp) {α β : Type} (f : α → I.M β) : List α → I.M (List β)
  | [] => pure []
  | a :: as => do
    let v ← f a
    let vs ← mapC I f as
    pure (v :: vs)

theorem mapC_spec {α β : Type} (env : Env) (f : α → CostM β) (R : α → β → Prop) :
    ∀ (as : List α), (∀ a ∈ as, ∀ c r c', (f a).run env c = some (r, c') → R a r) →
    ∀ (c : Cost) (vs : List β) (c' : Cost),
    (mapC Interp.counting f as).run env c = some (vs, c') → List.Forall₂ R as vs
  | [], _, c, vs, c', h => by
    simp only [mapC, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact List.Forall₂.nil
  | a :: as, hf, c, vs, c', h => by
    simp only [mapC, Interp.counting_bind, CostM.run_bind] at h
    split at h
    · rename_i v c1 hv
      have hv1 := hf a List.mem_cons_self c v c1 hv
      split at h
      · rename_i vs1 c2 hvs
        have ih := mapC_spec env f R as (fun a ha => hf a (List.mem_cons_of_mem _ ha)) c1 vs1 c2 hvs
        simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact List.Forall₂.cons hv1 ih
      · cases h
    · cases h

theorem forall2_map_eq {α β γ : Type} (g : β → γ) (F : α → γ) (as : List α) (bs : List β)
    (h : List.Forall₂ (fun a b => g b = F a) as bs) : bs.map g = as.map F := by
  induction h with
  | nil => rfl
  | cons h1 _ ih => simp [ih, h1]

/-- Read the entries of weight `name` at the given indices (free). -/
def readIdx (I : Interp) (name : String) (is : List Nat) : I.M (List I.V) := mapC I (I.weight name) is

/-- `acc + Σ x_i * y_i` by multiply-adds, 1 each. -/
def dot (I : Interp) (xs ys : List I.V) (acc : I.V) : I.M I.V :=
  (xs.zip ys).foldlM (fun a p => I.muladd ct a p.1 p.2) acc

theorem readIdx_spec (env : Env) (name : String) (t : Tensor ℚ)
    (ht : List.lookup name env.weights = some t) (is : List Nat) (c : Cost) (vs : List Q) (c' : Cost)
    (h : (readIdx Interp.counting name is).run env c = some (vs, c')) :
    vs.map Q.val = is.map t.get ∧ c' = c := by
  unfold readIdx at h
  have hc : ∀ (is : List Nat) (c : Cost) (vs : List Q) (c' : Cost),
      (mapC Interp.counting (Interp.counting.weight name) is).run env c = some (vs, c') → c' = c := by
    intro is
    induction is with
    | nil =>
      intro c vs c' h
      simp only [mapC, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
      exact h.2.symm
    | cons i is ih =>
      intro c vs c' h
      simp only [mapC, Interp.counting_bind, CostM.run_bind] at h
      split at h
      · rename_i v c1 hv
        have hc1 := (CostM.weight_run_get ht hv).2
        split at h
        · rename_i vs1 c2 hvs
          have hc2 := ih c1 vs1 c2 hvs
          simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2, hc2, hc1]
        · cases h
      · cases h
  refine ⟨forall2_map_eq Q.val t.get is vs (mapC_spec env _ (fun i (v : Q) => v.val = t.get i) is
    (fun i _ c r c' hr => (CostM.weight_run_get ht hr).1) c vs c' h), hc is c vs c' h⟩

theorem dot_spec (env : Env) : ∀ (xs ys : List Q) (acc : Q) (c : Cost) (r : Q) (c' : Cost),
    (dot Interp.counting xs ys acc).run env c = some (r, c') →
    r.val = acc.val + (List.zipWith (fun x y : Q => x.val * y.val) xs ys).sum
  | [], ys, acc, c, r, c', h => by
    simp only [dot, List.zip_nil_left, List.foldlM, Interp.counting_pure, CostM.run_pure, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | x :: xs, [], acc, c, r, c', h => by
    simp only [dot, List.zip_nil_right, List.foldlM, Interp.counting_pure, CostM.run_pure, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | x :: xs, y :: ys, acc, c, r, c', h => by
    simp only [dot, List.zip_cons_cons, List.foldlM, Interp.counting_bind, CostM.run_bind, Interp.counting_muladd,
      CostM.qmuladd] at h
    have ih := dot_spec env xs ys ⟨acc.val + x.val * y.val⟩ (c.add ct 1) r c' (by unfold dot; exact h)
    rw [ih]
    simp [add_assoc]

end Candidate.Counted
