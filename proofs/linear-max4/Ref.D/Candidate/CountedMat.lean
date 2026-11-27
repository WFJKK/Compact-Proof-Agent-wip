import Candidate.CountedLin

/-!
# The matrix `L·E` and `U·L·E` in the counted language, with their specifications.
-/

namespace Candidate.Counted

open CompactCheck Candidate.Linear

theorem forList_spec (env : Env) (f : Nat → CostM Q) (F : Nat → ℚ) :
    ∀ (is : List Nat), (∀ i ∈ is, ∀ c r c', (f i).run env c = some (r, c') → r.val = F i) →
    ∀ (c : Cost) (vs : List Q) (c' : Cost),
    (mapC Interp.counting f is).run env c = some (vs, c') → vs.map Q.val = is.map F := by
  intro is hf c vs c' h
  exact forall2_map_eq Q.val F is vs (mapC_spec env f (fun i (v : Q) => v.val = F i) is hf c vs c' h)

theorem zipWith_self_eq (f : Nat → Nat → ℚ) (l : List Nat) :
    List.zipWith f l l = l.map fun x => f x x := by
  induction l with
  | nil => rfl
  | cons x l ih => simp [List.zipWith_cons_cons, ih]

theorem zip_sum_eq (xs ys : List Q) (d : Nat) (a b : Nat → ℚ)
    (hx : xs.map Q.val = (List.range d).map a) (hy : ys.map Q.val = (List.range d).map b) :
    (List.zipWith (fun x y : Q => x.val * y.val) xs ys).sum = ∑ l ∈ Finset.range d, a l * b l := by
  have : List.zipWith (fun x y : Q => x.val * y.val) xs ys =
      List.zipWith (· * ·) (xs.map Q.val) (ys.map Q.val) := by
    rw [List.zipWith_map]
  rw [this, hx, hy, List.zipWith_map, zipWith_self_eq, sum_range_eq]

/-- Row `k` of `L·E` over `t < V`. -/
def leRow (I : Interp) (d V k : Nat) : I.M (List I.V) := do
  let lrow ← readIdx I "linear.weight" ((List.range d).map fun l => k * d + l)
  mapC I (fun t => do
    let ecol ← readIdx I "embedding.weight" ((List.range d).map fun l => l * V + t)
    dot I lrow ecol I.zero) (List.range V)

theorem leRow_spec (env : Env) (E L : Tensor ℚ) (d V k : Nat)
    (hE : List.lookup "embedding.weight" env.weights = some E)
    (hL : List.lookup "linear.weight" env.weights = some L)
    (c : Cost) (vs : List Q) (c' : Cost)
    (h : (leRow Interp.counting d V k).run env c = some (vs, c')) :
    vs.map Q.val = (List.range V).map fun t => LE E L d V k t := by
  simp only [leRow, Interp.counting_bind, CostM.run_bind] at h
  split at h
  · rename_i lrow c1 hl
    obtain ⟨hl1, rfl⟩ := readIdx_spec env _ L hL _ _ _ _ hl
    apply forList_spec env _ (fun t => LE E L d V k t) (List.range V) _ _ vs c' h
    intro t _ c2 r c3 hr
    simp only [Interp.counting_bind, CostM.run_bind] at hr
    split at hr
    · rename_i ecol c4 he
      obtain ⟨he1, rfl⟩ := readIdx_spec env _ E hE _ _ _ _ he
      have hd := dot_spec env lrow ecol _ _ r c3 hr
      rw [hd]
      rw [zip_sum_eq lrow ecol d (fun l => L.get (k * d + l)) (fun l => E.get (l * V + t))
        (by rw [hl1, List.map_map]; rfl) (by rw [he1, List.map_map]; rfl)]
      simp [Candidate.Linear.LE]
    · cases hr
  · cases h

/-- Row `j` of `U·L·E` over `t < V`, from the rows of `L·E` (`le`, one list of `V` values per `k < d`). -/
def matRow (I : Interp) (d V j : Nat) (le : List (List I.V)) : I.M (List I.V) := do
  let urow ← readIdx I "unembedding.weight" ((List.range d).map fun k => j * d + k)
  mapC I (fun t => dot I urow (le.map fun row => row.getD t I.zero) I.zero) (List.range V)

theorem getD_val (row : List Q) (t : Nat) :
    (row.getD t ⟨0⟩).val = (row.map Q.val).getD t 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases row[t]? <;> rfl

theorem getD_range_map (V t : Nat) (f : Nat → ℚ) (ht : t < V) :
    ((List.range V).map f).getD t 0 = f t := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]

theorem matRow_spec (env : Env) (E L U : Tensor ℚ) (d V j : Nat)
    (hU : List.lookup "unembedding.weight" env.weights = some U)
    (le : List (List Q))
    (hle : le.map (fun row => row.map Q.val) =
      (List.range d).map fun k => (List.range V).map fun t => LE E L d V k t)
    (c : Cost) (vs : List Q) (c' : Cost)
    (h : (matRow Interp.counting d V j le).run env c = some (vs, c')) :
    vs.map Q.val = (List.range V).map fun t => Mat E L U d V j t := by
  simp only [matRow, Interp.counting_bind, CostM.run_bind] at h
  split at h
  · rename_i urow c1 hu
    obtain ⟨hu1, rfl⟩ := readIdx_spec env _ U hU _ _ _ _ hu
    apply forList_spec env _ (fun t => Mat E L U d V j t) (List.range V) _ _ vs c' h
    intro t ht c2 r c3 hr
    rw [List.mem_range] at ht
    have hd := dot_spec env urow _ _ _ r c3 hr
    rw [hd]
    have hcol : (le.map fun row => row.getD t (⟨0⟩ : Q)).map Q.val =
        (List.range d).map fun k => LE E L d V k t := by
      rw [List.map_map]
      have hf : (Q.val ∘ fun row : List Q => row.getD t ⟨0⟩) =
          fun row => (row.map Q.val).getD t 0 := by
        funext row
        exact getD_val row t
      have h2 : le.map (fun row => (row.map Q.val).getD t 0) =
          (le.map fun row => row.map Q.val).map (fun r => r.getD t 0) := by
        rw [List.map_map]
        rfl
      rw [hf, h2, hle, List.map_map]
      apply List.map_congr_left
      intro k _
      exact getD_range_map V t _ ht
    rw [zip_sum_eq urow _ d (fun k => U.get (j * d + k)) (fun k => LE E L d V k t)
      (by rw [hu1, List.map_map]; rfl) hcol]
    simp [Candidate.Linear.Mat]
  · cases h

end Candidate.Counted
