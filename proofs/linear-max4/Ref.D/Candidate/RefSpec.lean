import Candidate.RefBox
import Mathlib.Data.List.GetD

/-!
# Specifications of the counted parts of the checker, under the counting interpreter
-/

namespace Candidate.Ref

open CompactCheck Protected.N_max4_v64_s0 Candidate.Linear Candidate.Boxes Candidate.Counted

theorem forall2_getD {α β : Type} (R : α → β → Prop) (dβ : β) (as : List α) (bs : List β)
    (h : List.Forall₂ R as bs) : ∀ i (hi : i < as.length), R as[i] (bs.getD i dβ) := by
  induction h with
  | nil => intro i hi; simp at hi
  | cons h1 _ ih =>
    intro i hi
    cases i with
    | zero => simpa using h1
    | succ i => simpa using ih i (by simpa using hi)

/-- The differences of two rows, entry by entry. -/
theorem subZip_spec (env : Env) (xs ys : List Q) (c : Cost) (vs : List Q) (c' : Cost)
    (h : (mapC Interp.counting (fun ab : Q × Q => Interp.counting.sub ct ab.1 ab.2) (xs.zip ys)).run env c =
      some (vs, c')) :
    ∀ t, t < xs.length → t < ys.length → (vs.getD t ⟨0⟩).val = (xs.getD t ⟨0⟩).val - (ys.getD t ⟨0⟩).val := by
  have hF := mapC_spec env _ (fun (ab : Q × Q) (v : Q) => v.val = ab.1.val - ab.2.val) (xs.zip ys)
    (fun ab _ c r c' hr => by
      simp only [Interp.counting_sub, CostM.qsub, Option.some.injEq, Prod.mk.injEq] at hr
      rw [← hr.1]) c vs c' h
  intro t h1 h2
  have := forall2_getD _ ⟨0⟩ _ _ hF t (by simp; omega)
  rw [List.getElem_zip] at this
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some]
  exact this

/-- The length of the prefix of `s` that reads `0, 1, 2, ...`. -/
def pre (s : List Nat) : Nat := ((List.range s.length).takeWhile fun i => s.getD i 0 == i).length

theorem pre_spec (s : List Nat) : pre s ≤ s.length ∧ ∀ i < pre s, s.getD i 0 = i := by
  have hp := List.takeWhile_prefix (fun i => s.getD i 0 == i) (l := List.range s.length)
  have hle := hp.length_le
  simp only [List.length_range] at hle
  refine ⟨hle, fun i hi => ?_⟩
  have heq := List.prefix_iff_eq_take.mp hp
  have hmem : i ∈ (List.range s.length).takeWhile fun i => s.getD i 0 == i := by
    rw [heq]
    rw [List.mem_take_iff_getElem]
    refine ⟨i, ?_, by simp⟩
    simp only [List.length_range]
    unfold pre at hi
    omega
  have := List.all_eq_true.mp (List.all_takeWhile (p := fun i => s.getD i 0 == i) (l := List.range s.length)) i hmem
  simpa using this

theorem mem_take_pre (s : List Nat) (c : Nat) (hc : c ≤ pre s) (t : Nat) (ht : t ∈ s.take c) : t < c := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  have hil : i < c := by simp at hi; omega
  have h2 := (pre_spec s).2 i (by omega)
  rw [List.getElem_take]
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hi; omega), Option.getD_some] at h2
  rw [h2]
  exact hil

/-- Running minima: entry `i` is at most every `dq t`, `t ≤ i`, and equal to one of them. -/
def PrOk (dq pq : List ℚ) : Prop :=
  (∀ i < pq.length, ∀ t ≤ i, pq.getD i 0 ≤ dq.getD t 0) ∧ (∀ i < pq.length, ∃ t ≤ i, pq.getD i 0 = dq.getD t 0)

theorem PrOk_nil (dq : List ℚ) : PrOk dq [] := ⟨fun i hi => by simp at hi, fun i hi => by simp at hi⟩

/-- The value `lo` computes. -/
def LOq (dq pq : List ℚ) (s : List Nat) : ℚ :=
  (s.drop (max (min (pre s) pq.length) 1)).foldl (fun a t => min a (dq.getD t 0))
    (cond (min (pre s) pq.length == 0) (dq.getD (s.headD 0) 0) (pq.getD (min (pre s) pq.length - 1) 0))

theorem foldlM_min (env : Env) (d : List Q) : ∀ (ts : List Nat) (acc : Q) (c : Cost) (v : Q) (c' : Cost),
    (ts.foldlM (fun a t => Interp.counting.min ct a (d.getD t Interp.counting.zero)) acc).run env c = some (v, c') →
    v.val = ts.foldl (fun a t => min a ((d.map Q.val).getD t 0)) acc.val
  | [], acc, c, v, c', h => by
    simp only [List.foldlM, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | t :: ts, acc, c, v, c', h => by
    simp only [List.foldlM, Interp.counting_bind, CostM.run_bind, Interp.counting_min, CostM.qmin,
      Interp.counting_zero] at h
    rw [foldlM_min env d ts _ _ v c' h]
    simp only [List.foldl_cons, getD_val]

theorem lo_run (env : Env) (d pr : List Q) (s : List Nat) (c : Cost) (v : Q) (c' : Cost)
    (h : (lo Interp.counting d pr s).run env c = some (v, c')) : v.val = LOq (d.map Q.val) (pr.map Q.val) s := by
  unfold lo at h
  rw [foldlM_min env d _ _ c v c' h, LOq, List.length_map]
  congr 1
  unfold pre
  cases (min ((List.range s.length).takeWhile fun i => s.getD i 0 == i).length pr.length == 0) <;>
    simp [Interp.counting_zero, getD_val]

theorem foldl_min_le (dq : List ℚ) : ∀ (ts : List Nat) (acc : ℚ),
    ts.foldl (fun a t => min a (dq.getD t 0)) acc ≤ acc ∧
      ∀ t ∈ ts, ts.foldl (fun a t => min a (dq.getD t 0)) acc ≤ dq.getD t 0
  | [], acc => ⟨le_refl _, by simp⟩
  | t :: ts, acc => by
    have ih := foldl_min_le dq ts (min acc (dq.getD t 0))
    refine ⟨le_trans ih.1 (min_le_left _ _), fun u hu => ?_⟩
    rw [List.mem_cons] at hu
    rcases hu with rfl | hu
    · exact le_trans ih.1 (min_le_right _ _)
    · exact ih.2 u hu

theorem foldl_min_mem (dq : List ℚ) : ∀ (ts : List Nat) (acc : ℚ),
    ts.foldl (fun a t => min a (dq.getD t 0)) acc = acc ∨
      ∃ t ∈ ts, ts.foldl (fun a t => min a (dq.getD t 0)) acc = dq.getD t 0
  | [], acc => Or.inl rfl
  | t :: ts, acc => by
    rcases foldl_min_mem dq ts (min acc (dq.getD t 0)) with h | ⟨u, hu, h⟩
    · rw [List.foldl_cons, h]
      rcases min_choice acc (dq.getD t 0) with h2 | h2
      · exact Or.inl h2
      · exact Or.inr ⟨t, List.mem_cons_self, h2⟩
    · exact Or.inr ⟨u, List.mem_cons_of_mem _ hu, by rw [List.foldl_cons]; exact h⟩

theorem LOq_le (dq pq : List ℚ) (hpq : PrOk dq pq) (s : List Nat) : ∀ t ∈ s, LOq dq pq s ≤ dq.getD t 0 := by
  intro t ht
  have hf := foldl_min_le dq (s.drop (max (min (pre s) pq.length) 1))
    (cond (min (pre s) pq.length == 0) (dq.getD (s.headD 0) 0) (pq.getD (min (pre s) pq.length - 1) 0))
  unfold LOq
  rw [← List.take_append_drop (max (min (pre s) pq.length) 1) s, List.mem_append] at ht
  rcases ht with ht | ht
  · refine le_trans hf.1 ?_
    cases hc : (min (pre s) pq.length == 0)
    · -- c ≥ 1: t is in the prefix 0..c-1
      simp only [Bool.cond_false]
      have hc0 : min (pre s) pq.length ≠ 0 := by simpa using hc
      rw [Nat.max_eq_left (a := min (pre s) pq.length) (b := 1) (by omega)] at ht
      have htc := mem_take_pre s _ (Nat.min_le_left _ _) t ht
      exact hpq.1 (min (pre s) pq.length - 1) (by have := Nat.min_le_right (pre s) pq.length; omega) t (by omega)
    · simp only [Bool.cond_true]
      have hc0 : min (pre s) pq.length = 0 := by simpa using hc
      rw [hc0] at ht
      cases s with
      | nil => simp at ht
      | cons a s => simp at ht; rw [ht]; simp
  · exact hf.2 t ht

theorem LOq_mem (dq pq : List ℚ) (hpq : PrOk dq pq) (s : List Nat) (hs : s ≠ []) :
    ∃ t ∈ s, LOq dq pq s = dq.getD t 0 := by
  unfold LOq
  rcases foldl_min_mem dq (s.drop (max (min (pre s) pq.length) 1))
    (cond (min (pre s) pq.length == 0) (dq.getD (s.headD 0) 0) (pq.getD (min (pre s) pq.length - 1) 0))
    with h | ⟨u, hu, h⟩
  · rw [h]
    cases hc : (min (pre s) pq.length == 0)
    · simp only [Bool.cond_false]
      have hc0 : min (pre s) pq.length ≠ 0 := by simpa using hc
      have hcl := Nat.min_le_right (pre s) pq.length
      obtain ⟨t, ht, heq⟩ := hpq.2 (min (pre s) pq.length - 1) (by omega)
      refine ⟨t, ?_, heq⟩
      have hps := pre_spec s
      have htp : t < pre s := by have := Nat.min_le_left (pre s) pq.length; omega
      have := hps.2 t htp
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some] at this
      rw [← this]
      exact List.getElem_mem _
    · simp only [Bool.cond_true]
      cases s with
      | nil => exact absurd rfl hs
      | cons a s => exact ⟨a, List.mem_cons_self, by simp⟩
  · exact ⟨u, List.mem_of_mem_drop hu, h⟩

/-- The minimum over a side is at most the minimum over any nonempty part of it. -/
theorem LOq_mono (dq pq : List ℚ) (hpq : PrOk dq pq) (v W : List Nat) (hv : v ≠ []) (hsub : ∀ t ∈ v, t ∈ W) :
    LOq dq pq W ≤ LOq dq pq v := by
  obtain ⟨t, ht, heq⟩ := LOq_mem dq pq hpq v hv
  rw [heq]
  exact LOq_le dq pq hpq W t (hsub t ht)

theorem scan_fold (env : Env) (d : List Q) : ∀ (k s : Nat) (acc : List Q) (c : Cost) (r : List Q) (c' : Cost),
    acc.length = s → 0 < s → PrOk (d.map Q.val) (acc.map Q.val) →
    ((List.range' s k).foldlM (fun (acc : List Q) (t : Nat) => do
      let v ← Interp.counting.min ct (acc.getLastD Interp.counting.zero) (d.getD t Interp.counting.zero)
      pure (acc ++ [v])) acc).run env c = some (r, c') →
    PrOk (d.map Q.val) (r.map Q.val) ∧ r.length = s + k
  | 0, s, acc, c, r, c', hl, _, hP, h => by
    simp only [List.range'_zero, List.foldlM, Interp.counting_pure, CostM.run_pure, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hP, by omega⟩
  | k + 1, s, acc, c, r, c', hl, hs, hP, h => by
    simp only [List.range'_succ, List.foldlM, Interp.counting_bind, CostM.run_bind, Interp.counting_min,
      CostM.qmin, Interp.counting_pure, CostM.run_pure, Interp.counting_zero] at h
    have hlast : (acc.getLastD ⟨0⟩).val = (acc.map Q.val).getD (s - 1) 0 := by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hl, ← List.getD_eq_getElem?_getD, getD_val]
    have hP' : PrOk (d.map Q.val) ((acc ++ [(⟨min (acc.getLastD ⟨0⟩).val (d.getD s ⟨0⟩).val⟩ : Q)]).map Q.val) := by
      have hlm : (acc.map Q.val).length = s := by simp [hl]
      refine ⟨fun i hi t ht => ?_, fun i hi => ?_⟩
      · simp only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_cons,
          List.length_nil, hlm] at hi ⊢
        by_cases his : i < s
        · rw [List.getD_append _ _ _ _ (by simp; omega)]
          exact hP.1 i (by simp; omega) t ht
        · have hi' : i = s := by omega
          subst hi'
          rw [List.getD_append_right _ _ _ _ (by simp [hl]), List.length_map, hl, Nat.sub_self]
          simp only [List.getD_cons_zero]
          rw [hlast]
          by_cases hts : t = i
          · rw [hts, ← getD_val d i]; exact min_le_iff.mpr (Or.inr le_rfl)
          · exact min_le_iff.mpr (Or.inl (hP.1 (i - 1) (by simp [hl]; omega) t (by omega)))
      · simp only [List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_cons,
          List.length_nil, hlm] at hi ⊢
        by_cases his : i < s
        · rw [List.getD_append _ _ _ _ (by simp; omega)]
          obtain ⟨t, ht, heq⟩ := hP.2 i (by simp; omega)
          exact ⟨t, ht, heq⟩
        · have hi' : i = s := by omega
          subst hi'
          rw [List.getD_append_right _ _ _ _ (by simp [hl]), List.length_map, hl, Nat.sub_self]
          simp only [List.getD_cons_zero]
          rw [hlast]
          rcases min_choice ((acc.map Q.val).getD (i - 1) 0) (d.getD i ⟨0⟩).val with h2 | h2
          · obtain ⟨t, ht, heq⟩ := hP.2 (i - 1) (by simp [hl]; omega)
            exact ⟨t, by omega, by rw [h2, heq]⟩
          · exact ⟨i, le_refl i, by rw [h2, getD_val]⟩
    have := scan_fold env d k (s + 1) _ _ r c' (by simp [hl]) (by omega) hP' h
    exact ⟨this.1, by omega⟩

theorem scan_spec (env : Env) (d : List Q) (n : Nat) (c : Cost) (r : List Q) (c' : Cost)
    (h : (scan Interp.counting d n).run env c = some (r, c')) :
    PrOk (d.map Q.val) (r.map Q.val) ∧ r.length = n - 1 + 1 := by
  unfold scan at h
  have h0 : PrOk (d.map Q.val) ([d.getD 0 Interp.counting.zero].map Q.val) := by
    refine ⟨fun i hi t ht => ?_, fun i hi => ?_⟩
    · simp at hi; subst hi
      have : t = 0 := by omega
      subst this
      simp [getD_val]
    · simp at hi; subst hi
      exact ⟨0, le_refl 0, by simp [getD_val]⟩
  have := scan_fold env d (n - 1) 1 _ c r c' (by simp) (by omega) h0 h
  exact ⟨this.1, by omega⟩

theorem safe_fold (env : Env) (X Y : Nat → Q) (lk lr : Q) : ∀ (js : List Nat) (acc : Bool) (c : Cost) (r : Bool)
    (c' : Cost),
    (js.foldlM (fun acc j => do
      let a ← Interp.counting.muladd ct Interp.counting.zero lk (X j)
      let v ← Interp.counting.muladd ct a lr (Y j)
      let ok ← Interp.counting.lt ct Interp.counting.zero v
      Interp.counting.band ct acc ok) acc).run env c = some (r, c') →
    r = true → acc = true ∧ ∀ j ∈ js, 0 < lk.val * (X j).val + lr.val * (Y j).val
  | [], acc, c, r, c', h, hr => by
    simp only [List.foldlM, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hr, by simp⟩
  | j :: js, acc, c, r, c', h, hr => by
    simp only [List.foldlM, Interp.counting_bind, CostM.run_bind, Interp.counting_muladd, CostM.qmuladd,
      Interp.counting_lt, CostM.qlt, Interp.counting_zero, Interp.counting_band_run] at h
    obtain ⟨h1, h2⟩ := safe_fold env X Y lk lr js _ _ r c' h hr
    simp only [Bool.and_eq_true, decide_eq_true_eq, zero_add] at h1
    refine ⟨h1.1, fun j' hj' => ?_⟩
    rw [List.mem_cons] at hj'
    rcases hj' with rfl | hj'
    · exact h1.2
    · exact h2 j' hj'

/-- The safe test: every competitor outside `J` loses on the whole class. -/
theorem safe_spec (env : Env) (V m k : Nat) (J : List Nat) (dr pm : List (List Q)) (c : Cost) (r : Bool)
    (c' : Cost) (h : (safe Interp.counting V m k J dr pm).run env c = some (r, c')) (hr : r = true) :
    ∀ j < V, j ≠ m → j ∉ J →
      0 < (k : ℚ) * ((dr.getD j []).getD m ⟨0⟩).val + ((4 - k : Nat) : ℚ) * ((pm.getD j []).getD (m - 1) ⟨0⟩).val := by
  simp only [safe, Interp.counting_bind, CostM.run_bind, Interp.counting_lit, CostM.lit] at h
  intro j hj hjm hjJ
  have := (safe_fold env (fun j => (dr.getD j []).getD m Interp.counting.zero)
    (fun j => (pm.getD j []).getD (m - 1) Interp.counting.zero) ⟨(k : ℚ)⟩ ⟨((4 - k : Nat) : ℚ)⟩ _ _ _ r c' h hr).2 j (by
      simp [hj, hjm, hjJ])
  simpa using this

theorem baseSum (env : Env) (dj pj : List Q) : ∀ (base : Box) (acc : Q) (c : Cost) (b : Q) (c' : Cost),
    (base.foldlM (fun a s => do
      let l ← lo Interp.counting dj pj s
      Interp.counting.sub ct a l) acc).run env c = some (b, c') →
    b.val = acc.val - (base.map (LOq (dj.map Q.val) (pj.map Q.val))).sum
  | [], acc, c, b, c', h => by
    simp only [List.foldlM, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | s :: base, acc, c, b, c', h => by
    simp only [List.foldlM, Interp.counting_bind, CostM.run_bind] at h
    split at h
    · rename_i a1 c1 h1
      split at h1
      · rename_i l c2 hl
        simp only [Interp.counting_sub, CostM.qsub, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rw [baseSum env dj pj base _ _ b c' h, lo_run env dj pj s _ l c2 hl]
        simp only [List.map_cons, List.sum_cons]
        ring
      · cases h1
    · cases h

theorem varFold (env : Env) (dr pm : List (List Q)) (v : List Nat) :
    ∀ (jbs : List (Nat × Q)) (acc : Bool) (c : Cost) (g : Bool) (c' : Cost),
    (jbs.foldlM (fun (acc : Bool) (jb : Nat × Q) => do
      let l ← lo Interp.counting (dr.getD jb.1 []) (pm.getD jb.1 []) v
      let ok ← Interp.counting.lt ct jb.2 l
      Interp.counting.band ct acc ok) acc).run env c = some (g, c') →
    g = true → acc = true ∧ ∀ jb ∈ jbs, jb.2.val < LOq ((dr.getD jb.1 []).map Q.val) ((pm.getD jb.1 []).map Q.val) v
  | [], acc, c, g, c', h, hg => by
    simp only [List.foldlM, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hg, by simp⟩
  | jb :: jbs, acc, c, g, c', h, hg => by
    simp only [List.foldlM, Interp.counting_bind, CostM.run_bind] at h
    split at h
    · rename_i a1 c1 h1
      split at h1
      · rename_i l c2 hl
        simp only [Interp.counting_lt, CostM.qlt, Interp.counting_band_run, CostM.run_bind, Option.some.injEq,
          Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨h2, h3⟩ := varFold env dr pm v jbs _ _ g c' h hg
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        refine ⟨h2.1, fun jb' hjb' => ?_⟩
        rw [List.mem_cons] at hjb'
        rcases hjb' with rfl | hjb'
        · rw [← lo_run env _ _ v _ l c2 hl]; exact h2.2
        · exact h3 jb' hjb'
      · cases h1
    · cases h

theorem forall2_mem_right {α β : Type} (R : α → β → Prop) (as : List α) (bs : List β) (h : List.Forall₂ R as bs) :
    ∀ b ∈ bs, ∃ a ∈ as, R a b := by
  induction h with
  | nil => intro b hb; simp at hb
  | cons h1 _ ih =>
    intro b hb
    rw [List.mem_cons] at hb
    rcases hb with rfl | hb
    · exact ⟨_, List.mem_cons_self, h1⟩
    · obtain ⟨a, ha, hab⟩ := ih b hb
      exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem forall2_zip {α β : Type} (R : α → β → Prop) (as : List α) (bs : List β) (h : List.Forall₂ R as bs) :
    ∀ a ∈ as, ∃ b, (a, b) ∈ as.zip bs ∧ R a b := by
  induction h with
  | nil => intro a ha; simp at ha
  | cons h1 _ ih =>
    intro a ha
    rw [List.mem_cons] at ha
    rcases ha with rfl | ha
    · exact ⟨_, by simp, h1⟩
    · obtain ⟨b, hb, hab⟩ := ih a ha
      exact ⟨b, by simp only [List.zip_cons_cons, List.mem_cons]; exact Or.inr hb, hab⟩

theorem tst_spec (env : Env) (dr pm : List (List Q)) (s : List Nat) (jbs : List (Nat × Q)) (acc : Bool) (c : Cost)
    (g : Bool) (c' : Cost) (h : (tst Interp.counting dr pm s jbs acc).run env c = some (g, c')) (hg : g = true) :
    acc = true ∧ ∀ jb ∈ jbs, jb.2.val < LOq ((dr.getD jb.1 []).map Q.val) ((pm.getD jb.1 []).map Q.val) s := by
  unfold tst at h
  exact varFold env dr pm s jbs acc c g c' h hg

/-- The verdicts of a group: a true one stands for its key, `srt (base ++ [v])`. -/
theorem grp_spec (env : Env) (m k : Nat) (J J1 : List Nat) (sf : Bool) (dr pm : List (List Q))
    (hpr : ∀ j, PrOk ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val)) (base : Box)
    (W : List Nat) (vs : List (List Nat)) (hW : ∀ v ∈ vs, ∀ t ∈ v, t ∈ W) (c : Cost) (es : List (Box × Bool))
    (c' : Cost) (h : (grp Interp.counting m k J J1 sf dr pm base W vs).run env c = some (es, c')) :
    ∀ e ∈ es, e.2 = true → ∃ v, e.1 = srt (base ++ [v]) ∧ kok m k e.1 = true ∧ sf = true ∧
      ∀ j ∈ J, 0 < ((base ++ [v]).map (LOq ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val))).sum := by
  simp only [grp, Interp.counting_bind, CostM.run_bind] at h
  split at h
  · rename_i bs c1 hbs
    have hB := mapC_spec env _ (fun j (b : Q) => b.val = 0 - (base.map (LOq ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val))).sum) J
      (fun j _ c r c' hr => by simpa using baseSum env (dr.getD j []) (pm.getD j []) base _ c r c' hr) c bs c1 hbs
    split at h
    · rename_i hv c2 hh
      have hE := mapC_spec env _ (fun (v : List Nat) (e : Box × Bool) => e.2 = true → e.1 = srt (base ++ [v]) ∧
        kok m k e.1 = true ∧ sf = true ∧ ∀ j ∈ J, 0 < ((base ++ [v]).map (LOq ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val))).sum) vs
        ?_ c2 es c' h
      · intro e he hg
        obtain ⟨v, _, hv'⟩ := forall2_mem_right _ vs es hE e he
        exact ⟨v, hv' hg⟩
      · intro v hvs c3 e c4 he
        simp only [CostM.run_bind] at he
        cases hk : kok m k (srt (base ++ [v]))
        · rw [hk] at he
          simp only [Bool.cond_false, Interp.counting_pure, CostM.run_pure, Interp.counting_bfalse,
            Option.some.injEq, Prod.mk.injEq] at he
          obtain ⟨rfl, rfl⟩ := he
          intro hg; cases hg
        · rw [hk] at he
          simp only [Bool.cond_true] at he
          split at he
          · rename_i g c5 hg5
            simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at he
            obtain ⟨rfl, rfl⟩ := he
            intro hg
            obtain ⟨hhv, hin⟩ := tst_spec env dr pm v _ hv c3 g c5 hg5 hg
            obtain ⟨hsf, hout⟩ := tst_spec env dr pm W _ sf c1 hv c2 hh hhv
            -- v is a nonempty set of the key
            have hvne : v ≠ [] := by
              have hmem : v ∈ srt (base ++ [v]) := (srt_perm _).symm.subset (by simp)
              simp only [kok, Bool.and_eq_true, List.all_eq_true] at hk
              have := hk.2 v hmem
              intro hv0
              rw [hv0] at this
              simp at this
            refine ⟨rfl, hk, hsf, fun j hj => ?_⟩
            obtain ⟨b, hjb, hb⟩ := forall2_zip _ J bs hB j hj
            have hlt : b.val < LOq ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val) v := by
              by_cases hj1 : j ∈ J1
              · exact hin (j, b) (List.mem_filter.mpr ⟨hjb, by simpa using hj1⟩)
              · exact lt_of_lt_of_le (hout (j, b) (List.mem_filter.mpr ⟨hjb, by simpa using hj1⟩))
                  (LOq_mono _ _ (hpr j) v W hvne (hW v hvs))
            rw [hb] at hlt
            simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
            linarith
          · cases he
    · cases h
  · cases h

/-- A true verdict of a group stands for its key: `Passes`, from the tests and the safe test of the class. -/
theorem passes_of (E L U : Tensor ℚ) (d V m k : Nat) (J : List Nat) (sf : Bool) (dr pm : List (List Q))
    (hpr : ∀ j, PrOk ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val))
    (hpl : ∀ j < V, j ≠ m → m ≤ (pm.getD j []).length)
    (hdr : ∀ j < V, j ≠ m → ∀ t ≤ m, ((dr.getD j []).getD t ⟨0⟩).val = Mat E L U d V m t - Mat E L U d V j t)
    (hsf : 0 < k → sf = true → ∀ j < V, j ≠ m → j ∉ J →
      0 < (k : ℚ) * ((dr.getD j []).getD m ⟨0⟩).val +
        ((4 - k : Nat) : ℚ) * ((pm.getD j []).getD (m - 1) ⟨0⟩).val)
    (key base : Box) (v : List Nat) (hkey : key = srt (base ++ [v])) (hk : kok m k key = true) (hs : sf = true)
    (hJ : ∀ j ∈ J, 0 < ((base ++ [v]).map (LOq ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val))).sum) :
    Passes E L U d V m key := by
  have hperm : key.Perm (base ++ [v]) := by rw [hkey]; exact srt_perm _
  simp only [kok, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', List.isEmpty_eq_false_iff, decide_eq_true_eq] at hk
  obtain ⟨⟨⟨hlen, hcnt⟩, hk0⟩, hsets⟩ := hk
  have hk0' : 0 < k := Nat.pos_of_ne_zero hk0
  have hle : ∀ s ∈ key, ∀ t ∈ s, t ≤ m := by
    intro s hs t ht
    rcases hsets s hs with h | h
    · rw [h] at ht; rw [List.mem_singleton.mp ht]
    · exact Nat.le_of_lt (h.2 t ht)
  have hlt : ∀ s ∈ key, s ≠ [m] → ∀ t ∈ s, t < m := by
    intro s hs hne t ht
    rcases hsets s hs with h | h
    · exact absurd h hne
    · exact h.2 t ht
  refine ⟨hlen, ?_, hle, ?_⟩
  · apply List.count_pos_iff.mp
    rw [hcnt]; exact hk0'
  · intro j hj hjm
    by_cases hjJ : j ∈ J
    · refine ⟨LOq ((dr.getD j []).map Q.val) ((pm.getD j []).map Q.val), fun s hs t ht => ?_, ?_⟩
      · have h1 := LOq_le ((dr.getD j []).map Q.val) _ (hpr j) s t ht
        rw [← getD_val, hdr j hj hjm t (hle s hs t ht)] at h1
        exact h1
      · rw [(hperm.map _).sum_eq]
        exact hJ j hjJ
    · have h0 := hsf hk0' hs j hj hjm hjJ
      refine ⟨fun s => if s == [m] then ((dr.getD j []).getD m ⟨0⟩).val
        else ((pm.getD j []).getD (m - 1) ⟨0⟩).val, fun s hs t ht => ?_, ?_⟩
      · dsimp only
        by_cases hsm : s = [m]
        · rw [if_pos (beq_iff_eq.mpr hsm)]
          rw [hsm, List.mem_singleton] at ht
          rw [ht, hdr j hj hjm m (le_refl m)]
        · rw [if_neg (by simpa using hsm)]
          have htm := hlt s hs hsm t ht
          have h1 := (hpr j).1 (m - 1) (by have := hpl j hj hjm; rw [List.length_map]; omega) t (by omega)
          rw [← getD_val, ← getD_val, hdr j hj hjm t (Nat.le_of_lt htm)] at h1
          exact h1
      · rw [count_map_ite, hcnt, hlen]
        have hk4 : k ≤ 4 := by rw [← hcnt, ← hlen]; exact List.count_le_length
        have : ((4 - k : Nat) : ℚ) = (4 : ℚ) - (k : ℚ) := by rw [Nat.cast_sub hk4]; norm_num
        rw [this] at h0
        push_cast
        linarith

end Candidate.Ref
