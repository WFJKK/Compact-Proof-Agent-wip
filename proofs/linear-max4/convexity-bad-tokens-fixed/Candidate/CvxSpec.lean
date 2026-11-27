import Candidate.RefBox
import Mathlib.Data.List.GetD

/-!
# Specifications of the counted parts of the convexity-only checker, under the counting interpreter

The rows, running minima and set minima are as in Ref.D (`RefSpec.lean`); new are the array reads, the minima
table of an `m` and the box test against every competitor.
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


theorem arr_getD (l : List Q) (t : Nat) (dflt : Q) : (Array.mk l).getD t dflt = l.getD t dflt := by
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, List.getElem?_toArray]

/-- The sum over a box's sides, as `tst` adds it. -/
theorem sum_fold (env : Env) (x : Q) (a : Array Q) : ∀ (sd : List (Bool × Nat)) (acc : Q) (c : Cost) (v : Q)
    (c' : Cost),
    (sd.foldlM (fun (acc : Q) (q : Bool × Nat) => Interp.counting.add ct acc (cond q.1 x (a.getD q.2 Interp.counting.zero))) acc).run env c =
      some (v, c') →
    v.val = acc.val + (sd.map fun q => (cond q.1 x (a.getD q.2 ⟨0⟩)).val).sum
  | [], acc, c, v, c', h => by
    simp only [List.foldlM, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | q :: sd, acc, c, v, c', h => by
    simp only [List.foldlM, Interp.counting_bind, CostM.run_bind, Interp.counting_add, CostM.qadd,
      Interp.counting_zero] at h
    rw [sum_fold env x a sd _ _ v c' h]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The loop over competitors: a true verdict means every competitor's sum is positive. -/
theorem pos_fold (env : Env) (sd : List (Bool × Nat)) :
    ∀ (zs : List ((Nat × Array Q × List Q × List Q) × Q)) (acc : Bool) (c : Cost) (g : Bool) (c' : Cost),
    (zs.foldlM (fun (acc : Bool) (rm : (Nat × Array Q × List Q × List Q) × Q) => do
      let v ← sd.tail.foldlM (fun (a : Q) (q : Bool × Nat) => Interp.counting.add ct a (cond q.1 rm.2 (rm.1.2.1.getD q.2 Interp.counting.zero)))
        (cond (sd.headD (false, 0)).1 rm.2 (rm.1.2.1.getD (sd.headD (false, 0)).2 Interp.counting.zero))
      let ok ← Interp.counting.lt ct Interp.counting.zero v
      Interp.counting.band ct acc ok) acc).run env c = some (g, c') →
    g = true → acc = true ∧ ∀ rm ∈ zs,
      0 < (cond (sd.headD (false, 0)).1 rm.2 (rm.1.2.1.getD (sd.headD (false, 0)).2 ⟨0⟩)).val +
        (sd.tail.map fun q => (cond q.1 rm.2 (rm.1.2.1.getD q.2 ⟨0⟩)).val).sum
  | [], acc, c, g, c', h, hg => by
    simp only [List.foldlM, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hg, by simp⟩
  | rm :: zs, acc, c, g, c', h, hg => by
    simp only [List.foldlM, Interp.counting_bind, CostM.run_bind] at h
    split at h
    · rename_i a1 c1 h1
      split at h1
      · rename_i v c2 hv
        simp only [Interp.counting_lt, CostM.qlt, Interp.counting_band_run, CostM.run_bind, Option.some.injEq,
          Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        obtain ⟨h2, h3⟩ := pos_fold env sd zs _ _ g c' h hg
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
        have hs := sum_fold env rm.2 rm.1.2.1 sd.tail _ c v c2 hv
        refine ⟨h2.1, fun rm' hrm' => ?_⟩
        rw [List.mem_cons] at hrm'
        rcases hrm' with rfl | hrm'
        · have h4 := h2.2
          rw [hs] at h4
          exact h4
        · exact h3 rm' hrm'
      · cases h1
    · cases h

/-- The competitors of a level `m`: every `j ≠ m` below `V` has an entry, with its row `d_j(t)`, `t ≤ m`, as a
    list and as an array, and its running minima. -/
structure ROk (E L U : Tensor ℚ) (d V m : Nat) (rws : List (Nat × Array Q × List Q × List Q)) : Prop where
  hm : m < V
  ok : ∀ r ∈ rws, r.2.1 = Array.mk r.2.2.1 ∧
    (∀ t ≤ m, (r.2.2.1.getD t ⟨0⟩).val = Mat E L U d V m t - Mat E L U d V r.1 t) ∧
    PrOk (r.2.2.1.map Q.val) (r.2.2.2.map Q.val)
  cov : ∀ j < V, j ≠ m → ∃ r ∈ rws, r.1 = j

/-- Minima aligned with the competitors: each at most the row on every token of `G`. -/
def MinOk (rws : List (Nat × Array Q × List Q × List Q)) (G : List Nat) (ms : List Q) : Prop :=
  List.Forall₂ (fun (r : Nat × Array Q × List Q × List Q) (v : Q) => ∀ t ∈ G, v.val ≤ (r.2.2.1.getD t ⟨0⟩).val) rws ms

/-- The table of minima of a level: every entry's minima are right for its set. -/
def MInv (rws : List (Nat × Array Q × List Q × List Q)) (tbl : List ((Nat × Nat) × List Nat × List Q)) : Prop :=
  ∀ e ∈ tbl, MinOk rws e.2.1 e.2.2

theorem MinOk_nil (rws : List (Nat × Array Q × List Q × List Q)) (z : Q) : MinOk rws [] (rws.map fun _ => z) := by
  unfold MinOk
  induction rws with
  | nil => exact List.Forall₂.nil
  | cons r rws ih => exact List.Forall₂.cons (fun t ht => by simp at ht) ih

theorem mins_spec (env : Env) (rws : List (Nat × Array Q × List Q × List Q))
    (hpr : ∀ r ∈ rws, PrOk (r.2.2.1.map Q.val) (r.2.2.2.map Q.val)) (G : List Nat)
    (tbl : List ((Nat × Nat) × List Nat × List Q)) (hinv : MInv rws tbl) (ms : List Q)
    (tbl' : List ((Nat × Nat) × List Nat × List Q)) (c c' : Cost)
    (h : (mins Interp.counting rws G tbl).run env c = some ((ms, tbl'), c')) :
    MInv rws tbl' ∧ MinOk rws G ms := by
  unfold mins at h
  split at h
  · rename_i e he
    simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    have hp := List.find?_some he
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    have := hinv e (List.mem_of_find?_eq_some he)
    rw [hp.2] at this
    exact ⟨hinv, this⟩
  · simp only [Interp.counting_bind, CostM.run_bind] at h
    split at h
    · rename_i ms0 c1 hms
      simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      have hF : MinOk rws G ms0 := mapC_spec env _
        (fun (r : Nat × Array Q × List Q × List Q) (v : Q) => ∀ t ∈ G, v.val ≤ (r.2.2.1.getD t ⟨0⟩).val) rws
        (fun r hr c v c' hv => by
          intro t ht
          rw [lo_run env _ _ G c v c' hv, getD_val]
          exact LOq_le _ _ (hpr r hr) G t ht) c ms0 c1 hms
      refine ⟨fun e he => ?_, hF⟩
      rw [List.mem_cons] at he
      rcases he with rfl | he
      · exact hF
      · exact hinv e he
    · cases h

/-- A true verdict of the box test: the box `Passes`, as its own key. -/
theorem tst_spec (env : Env) (E L U : Tensor ℚ) (d V m : Nat) (rws : List (Nat × Array Q × List Q × List Q))
    (ro : ROk E L U d V m rws) (c : Box) (G : List Nat) (ms : List Q) (hms : MinOk rws G ms)
    (c0 c' : Cost) (g : Bool) (h : (tst Interp.counting m rws c G ms).run env c0 = some (g, c')) (hg : g = true) :
    Passes E L U d V m c := by
  unfold tst at h
  cases hgd : (c.length == 4 && c.contains [m] && c.all fun s => s.all (· ≤ m) && (s == G || s.length == 1))
  · rw [hgd] at h
    simp only [Bool.cond_false, Interp.counting_pure, CostM.run_pure, Interp.counting_bfalse, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    cases hg
  · rw [hgd] at h
    simp only [Bool.cond_true] at h
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem, List.all_eq_true, Bool.or_eq_true,
      decide_eq_true_eq] at hgd
    obtain ⟨⟨hlen, hmem⟩, hall⟩ := hgd
    obtain ⟨-, hpos⟩ := pos_fold env (c.map fun s => (s == G, s.headD 0)) (rws.zip ms) _ c0 g c' h hg
    refine ⟨hlen, hmem, fun s hs t ht => (hall s hs).1 t ht, fun j hj hjm => ?_⟩
    obtain ⟨r, hr, rfl⟩ := ro.cov j hj hjm
    obtain ⟨v, hrv, hv⟩ := forall2_zip _ rws ms hms r hr
    obtain ⟨harr, hrow, _⟩ := ro.ok r hr
    refine ⟨fun s => (cond (s == G) v (r.2.1.getD (s.headD 0) ⟨0⟩)).val, fun s hs t ht => ?_, ?_⟩
    · have htm : t ≤ m := (hall s hs).1 t ht
      dsimp only
      cases hsG : (s == G)
      · simp only [Bool.cond_false]
        have hs1 : s.length = 1 := by
          rcases (hall s hs).2 with h1 | h1
          · exact absurd h1 (by simpa using hsG)
          · exact h1
        obtain ⟨u, rfl⟩ := List.length_eq_one_iff.mp hs1
        rw [List.mem_singleton] at ht
        subst ht
        rw [harr, arr_getD, List.headD_cons]
        exact le_of_eq (hrow _ htm)
      · simp only [Bool.cond_true]
        have hsG' : s = G := by simpa using hsG
        rw [← hrow t htm]
        exact hv t (hsG' ▸ ht)
    · have := hpos (r, v) hrv
      cases c with
      | nil => simp at hlen
      | cons s0 c1 =>
        simpa [List.map_map, Function.comp_def] using this

end Candidate.Ref
