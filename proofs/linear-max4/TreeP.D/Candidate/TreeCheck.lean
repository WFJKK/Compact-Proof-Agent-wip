import Candidate.CountedMat
import Candidate.BoxCorrect

namespace Candidate.Tree

open CompactCheck Protected.N_max4_v64_s0 Candidate.Linear Candidate.Boxes Candidate.Counted

/-! ## Generic counted helpers -/

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

theorem forall2_getD {α β : Type} (R : α → β → Prop) (dβ : β) (as : List α) (bs : List β)
    (h : List.Forall₂ R as bs) : ∀ i (hi : i < as.length), R as[i] (bs.getD i dβ) := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons h1 _ ih =>
    intro i hi
    cases i with
    | zero => simpa using h1
    | succ i => simpa using ih i (by simpa using hi)

theorem getD_range_map' {γ : Type} (V t : Nat) (f : Nat → γ) (dflt : γ) (ht : t < V) :
    ((List.range V).map f).getD t dflt = f t := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range ht]

theorem sum_eq_sum_getD : ∀ (l : List ℚ), l.sum = ∑ p ∈ Finset.range l.length, l.getD p 0
  | [] => by simp
  | a :: l => by
    rw [List.sum_cons, List.length_cons, Finset.sum_range_succ', sum_eq_sum_getD l]
    simp [List.getD_cons_succ, List.getD_cons_zero, add_comm]

def subRows (I : Interp) : List I.V → List I.V → I.M (List I.V)
  | a :: as, b :: bs => do
    let v ← I.sub "sub" a b
    let vs ← subRows I as bs
    pure (v :: vs)
  | _, _ => pure []

theorem subRows_spec (env : Env) : ∀ (xs ys : List Q) (c : Cost) (vs : List Q) (c' : Cost),
    (subRows Interp.counting xs ys).run env c = some (vs, c') →
    ∀ t, t < xs.length → t < ys.length →
      (vs.getD t ⟨0⟩).val = (xs.getD t ⟨0⟩).val - (ys.getD t ⟨0⟩).val
  | [], _, _, _, _, _ => by intro t ht; simp at ht
  | _ :: _, [], _, _, _, _ => by intro t _ ht; simp at ht
  | a :: as, b :: bs, c, vs, c', h => by
    simp only [subRows, Interp.counting_bind, CostM.run_bind, Interp.counting_sub, CostM.qsub] at h
    split at h
    · rename_i vs1 c2 hvs
      have ih := subRows_spec env as bs _ vs1 c2 hvs
      simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro t h1 h2
      cases t with
      | zero => simp
      | succ t => simpa using ih t (by simpa using h1) (by simpa using h2)
    · cases h

def minList (I : Interp) (row : List I.V) : List Nat → I.V → I.M I.V
  | [], acc => pure acc
  | t :: ts, acc => do
    let a ← I.min "min" acc (row.getD t I.zero)
    minList I row ts a

theorem minList_spec (env : Env) (row : List Q) :
    ∀ (ts : List Nat) (acc : Q) (c : Cost) (r : Q) (c' : Cost),
    (minList Interp.counting row ts acc).run env c = some (r, c') →
    r.val ≤ acc.val ∧ ∀ t ∈ ts, r.val ≤ (row.getD t ⟨0⟩).val
  | [], acc, c, r, c', h => by
    simp only [minList, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨le_refl _, by simp⟩
  | t :: ts, acc, c, r, c', h => by
    simp only [minList, Interp.counting_bind, CostM.run_bind, Interp.counting_min, CostM.qmin,
      Interp.counting_zero] at h
    have ih := minList_spec env row ts _ _ r c' h
    refine ⟨le_trans ih.1 (min_le_left _ _), ?_⟩
    intro u hu
    rw [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact le_trans ih.1 (min_le_right _ _)
    · exact ih.2 u hu

def minIv (I : Interp) (row : List I.V) (iv : Nat × Nat) : I.M I.V :=
  minList I row (List.range' (iv.1 + 1) (iv.2 - iv.1 - 1)) (row.getD iv.1 I.zero)

theorem minIv_spec (env : Env) (row : List Q) (iv : Nat × Nat) (c : Cost) (r : Q) (c' : Cost)
    (h : (minIv Interp.counting row iv).run env c = some (r, c')) :
    ∀ t, iv.1 ≤ t → t < iv.2 → r.val ≤ (row.getD t ⟨0⟩).val := by
  simp only [minIv, Interp.counting_zero] at h
  have hs := minList_spec env row _ _ c r c' h
  intro t h1 h2
  rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
  · exact hs.1
  · exact hs.2 t (by rw [List.mem_range'_1]; omega)

def mkTable (I : Interp) (V : Nat) (fam : Nat → List (Nat × Nat)) (mat : List (List I.V)) (m : Nat) :
    I.M (List (List I.V)) :=
  mapC I (fun j => do
    let drow ← subRows I (mat.getD m []) (mat.getD j [])
    mapC I (minIv I drow) (fam m)) (List.range V)

def TblOk (E L U : Tensor ℚ) (d V : Nat) (fam : Nat → List (Nat × Nat)) (m : Nat)
    (tbl : List (List Q)) : Prop :=
  ∀ j < V, List.Forall₂ (fun (iv : Nat × Nat) (v : Q) => ∀ t, iv.1 ≤ t → t < iv.2 → t < V →
    v.val ≤ Mat E L U d V m t - Mat E L U d V j t) (fam m) (tbl.getD j [])

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

theorem mkTable_spec (env : Env) (E L U : Tensor ℚ) (d V : Nat) (fam : Nat → List (Nat × Nat))
    (mat : List (List Q)) (hmat : MatOk E L U d V mat) (m : Nat) (hm : m < V)
    (c : Cost) (tbl : List (List Q)) (c' : Cost)
    (h : (mkTable Interp.counting V fam mat m).run env c = some (tbl, c')) :
    TblOk E L U d V fam m tbl := by
  have hf := mapC_spec env _ (fun j (row : List Q) => List.Forall₂
    (fun (iv : Nat × Nat) (v : Q) => ∀ t, iv.1 ≤ t → t < iv.2 → t < V →
      v.val ≤ Mat E L U d V m t - Mat E L U d V j t) (fam m) row) (List.range V) ?_ c tbl c' h
  · intro j hj
    have := forall2_getD _ [] _ _ hf j (by simpa using hj)
    simpa using this
  · intro j hj c2 r c3 hr
    rw [List.mem_range] at hj
    simp only [Interp.counting_bind, CostM.run_bind] at hr
    split at hr
    · rename_i drow c4 hd
      have hds := subRows_spec env _ _ _ _ _ hd
      apply mapC_spec env _ _ (fam m) _ c4 r c3 hr
      intro iv _ c5 v c6 hv t h1 h2 htV
      have hmin := minIv_spec env drow iv c5 v c6 hv t h1 h2
      have hd1 := hds t (by rw [mat_len E L U d V mat hmat m hm]; exact htV)
        (by rw [mat_len E L U d V mat hmat j hj]; exact htV)
      rw [hd1, mat_entry E L U d V mat hmat m hm t htV, mat_entry E L U d V mat hmat j hj t htV] at hmin
      exact hmin
    · cases hr

/-! ## Lookups and the leaf test -/

def lookupIv (I : Interp) : List (Nat × Nat) → List I.V → Nat × Nat → Option I.V
  | iv :: fam, v :: tbl, q => if iv = q then some v else lookupIv I fam tbl q
  | _, _, _ => none

theorem lookupIv_spec (R : Nat × Nat → Q → Prop) (fam : List (Nat × Nat)) (tbl : List Q)
    (h : List.Forall₂ R fam tbl) : ∀ q v, lookupIv Interp.counting fam tbl q = some v → R q v := by
  induction h with
  | nil => intro q v hq; simp [lookupIv] at hq
  | cons h1 _ ih =>
    intro q v hq
    simp only [lookupIv] at hq
    split at hq
    · rename_i heq
      subst heq
      cases hq
      exact h1
    · exact ih q v hq

def lookups (I : Interp) (fam : List (Nat × Nat)) (tbl : List I.V) : List (Nat × Nat) → Option (List I.V)
  | [] => some []
  | b :: bs => match lookupIv I fam tbl b, lookups I fam tbl bs with
    | some v, some vs => some (v :: vs)
    | _, _ => none

theorem lookups_spec (R : Nat × Nat → Q → Prop) (fam : List (Nat × Nat)) (tbl : List Q)
    (hl : ∀ q v, lookupIv Interp.counting fam tbl q = some v → R q v) :
    ∀ (bs : List (Nat × Nat)) (vs : List Q), lookups Interp.counting fam tbl bs = some vs →
      List.Forall₂ R bs vs
  | [], vs, h => by
    simp only [lookups, Option.some.injEq] at h
    subst h
    exact List.Forall₂.nil
  | b :: bs, vs, h => by
    simp only [lookups] at h
    split at h
    · rename_i v vs1 hv hvs
      cases h
      exact List.Forall₂.cons (hl b v hv) (lookups_spec R fam tbl hl bs vs1 hvs)
    · cases h

def sumFrom (I : Interp) : I.V → List I.V → I.M I.V
  | acc, [] => pure acc
  | acc, v :: vs => do
    let a ← I.add "add" acc v
    sumFrom I a vs

theorem sumFrom_spec (env : Env) : ∀ (vs : List Q) (acc : Q) (c : Cost) (r : Q) (c' : Cost),
    (sumFrom Interp.counting acc vs).run env c = some (r, c') → r.val = acc.val + (vs.map Q.val).sum
  | [], acc, c, r, c', h => by
    simp only [sumFrom, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | v :: vs, acc, c, r, c', h => by
    simp only [sumFrom, Interp.counting_bind, CostM.run_bind, Interp.counting_add, CostM.qadd] at h
    have ih := sumFrom_spec env vs _ _ r c' h
    rw [ih]
    simp [add_assoc]

def allOk (I : Interp) (fam : List (Nat × Nat)) (tbl : List (List I.V)) (bs : List (Nat × Nat)) :
    List Nat → I.B → I.M I.B
  | [], acc => pure acc
  | j :: js, acc =>
    match lookups I fam (tbl.getD j []) bs with
    | some vs => do
      let s ← sumFrom I I.zero vs
      let ok ← I.lt "lt" I.zero s
      let acc' ← I.band "and" acc ok
      allOk I fam tbl bs js acc'
    | none => pure I.bfalse

theorem allOk_spec (env : Env) (fam : List (Nat × Nat)) (tbl : List (List Q)) (bs : List (Nat × Nat)) :
    ∀ (js : List Nat) (acc : Bool) (c : Cost) (c' : Cost),
    (allOk Interp.counting fam tbl bs js acc).run env c = some (true, c') →
    acc = true ∧ ∀ j ∈ js, ∃ vs : List Q,
      lookups Interp.counting fam (tbl.getD j []) bs = some vs ∧ 0 < (vs.map Q.val).sum
  | [], acc, c, c', h => by
    simp only [allOk, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨h.1, by simp⟩
  | j :: js, acc, c, c', h => by
    simp only [allOk] at h
    split at h
    · rename_i vs hvs
      simp only [Interp.counting_bind, CostM.run_bind] at h
      split at h
      · rename_i s c1 hs
        have hsum := sumFrom_spec env vs _ _ s c1 hs
        simp only [Interp.counting_lt, CostM.qlt, Interp.counting_zero, Interp.counting_band_run] at h
        have ih := allOk_spec env fam tbl bs js _ _ c' h
        obtain ⟨hacc, hrest⟩ := ih
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
        refine ⟨hacc.1, ?_⟩
        intro j' hj'
        rw [List.mem_cons] at hj'
        rcases hj' with rfl | hj'
        · refine ⟨vs, hvs, ?_⟩
          have := hacc.2
          rw [hsum] at this
          simpa using this
        · exact hrest j' hj'
      · cases h
    · simp [Interp.counting_pure, CostM.run_pure, Interp.counting_bfalse] at h

/-! ## The tree -/

inductive BTree where
  | leaf : BTree
  | skip : BTree
  | split (p mid : Nat) (l r : BTree) : BTree
  | useM (m : Nat) (t : BTree) : BTree

def leafShape (P V m : Nat) (bs : List (Nat × Nat)) : Bool :=
  bs.length == P && decide (m < V) && bs.all (fun b => decide (b.2 ≤ m + 1)) && bs.any (fun b => b.1 == m)

def countTree (I : Interp) (mat : List (List I.V)) (P V : Nat) (fam : Nat → List (Nat × Nat)) :
    Nat → List (List I.V) → List (Nat × Nat) → BTree → I.M I.N
  | m, tbl, bs, .leaf =>
    if leafShape P V m bs then do
      let ok ← allOk I (fam m) tbl bs ((List.range V).filter (fun j => j != m)) I.btrue
      pure (I.nscale (boxSize bs) ok)
    else pure I.nzero
  | _, _, _, .skip => pure I.nzero
  | m, tbl, bs, .split p mid l r =>
    match bs[p]? with
    | some (lo, hi) =>
      if lo ≤ mid ∧ mid ≤ hi then do
        let a ← countTree I mat P V fam m tbl (bs.set p (lo, mid)) l
        let b ← countTree I mat P V fam m tbl (bs.set p (mid, hi)) r
        pure (I.nadd a b)
      else pure I.nzero
    | none => pure I.nzero
  | _, _, bs, .useM m' t => do
    let tbl' ← mkTable I V fam mat m'
    countTree I mat P V fam m' tbl' bs t

/-! ## Splitting a box -/

theorem inBox_split : ∀ (bs : List (Nat × Nat)) (p lo hi mid : Nat) (x : Input),
    bs[p]? = some (lo, hi) → lo ≤ mid → mid ≤ hi →
    (inBox bs x = (inBox (bs.set p (lo, mid)) x || inBox (bs.set p (mid, hi)) x)) ∧
    ¬ (inBox (bs.set p (lo, mid)) x = true ∧ inBox (bs.set p (mid, hi)) x = true)
  | [], p, lo, hi, mid, x, hp, _, _ => by simp at hp
  | b :: bs, 0, lo, hi, mid, x, hp, h1, h2 => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
    subst hp
    simp only [List.set_cons_zero]
    cases x with
    | nil => simp [Boxes.inBox]
    | cons t x =>
      simp only [Boxes.inBox]
      cases inBox bs x
      · simp
      · constructor
        · rw [Bool.eq_iff_iff]
          simp only [Bool.and_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]
          omega
        · simp only [Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
          omega
  | b :: bs, p + 1, lo, hi, mid, x, hp, h1, h2 => by
    simp only [List.getElem?_cons_succ] at hp
    simp only [List.set_cons_succ]
    cases x with
    | nil => simp [Boxes.inBox]
    | cons t x =>
      obtain ⟨ih1, ih2⟩ := inBox_split bs p lo hi mid x hp h1 h2
      obtain ⟨blo, bhi⟩ := b
      rcases Bool.eq_false_or_eq_true (decide (blo ≤ t) && decide (t < bhi)) with hc | hc <;>
        simp only [Boxes.inBox, hc, ih1, Bool.false_and, Bool.true_and] <;> simp [ih2]

theorem countP_split_or {α : Type} (A A1 A2 C : α → Bool)
    (hA : ∀ x, A x = (A1 x || A2 x)) (hd : ∀ x, ¬ (A1 x = true ∧ A2 x = true)) :
    ∀ (l : List α), l.countP (fun x => A x && C x) =
      l.countP (fun x => A1 x && C x) + l.countP (fun x => A2 x && C x)
  | [] => by simp
  | x :: l => by
    simp only [List.countP_cons, countP_split_or A A1 A2 C hA hd l, hA x]
    have := hd x
    cases h1 : A1 x <;> cases h2 : A2 x <;> cases hc : C x <;> simp_all <;> omega

theorem forall2_of_bound : ∀ (bs : List (Nat × Nat)) (n V : Nat), bs.length = n → (∀ b ∈ bs, b.2 ≤ V) →
    List.Forall₂ (fun (b : Nat × Nat) v => b.2 ≤ v) bs (List.replicate n V)
  | [], 0, _, _, _ => List.Forall₂.nil
  | b :: bs, n + 1, V, hl, hb => List.Forall₂.cons (hb b List.mem_cons_self)
      (forall2_of_bound bs n V (by simpa using hl) (fun b' hb' => hb b' (List.mem_cons_of_mem _ hb')))
  | [], _ + 1, _, hl, _ => by simp at hl
  | _ :: _, 0, _, hl, _ => by simp at hl

end Candidate.Tree
