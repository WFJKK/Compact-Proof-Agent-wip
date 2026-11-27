import Candidate.LibSubErr
import Candidate.LibSubSpec
import Candidate.LibCubicSound

/-!
# Steps 2 to 5 of entry 9, run

The helpers of steps 2 to 5 as runs (`Runs`: value and cost), and the two functions that call
`exp`, which a run can fail, by what a run that succeeds returns and costs (`RS`): the sorted sums
of the positional errors (`rs_sortedSums`) and the test of one class (`rs_classTest`).
-/

namespace GrossSub

open CompactCheck Common AttnClasses GrossCubic Finset

/-! ## Runs that may fail, with their cost -/

/-- Every run of `x` that succeeds returns a value with `P` and adds `n` to the bill's total. -/
def RS {α : Type} (x : CostM α) (env : Env) (P : α → Prop) (n : ℕ) : Prop :=
  ∀ c v c', x.run env c = some (v, c') → P v ∧ c'.total = c.total + n

namespace RS

variable {α β : Type} {env : Env}

theorem of_runs {x : CostM α} {v : α} {n : ℕ} (h : Runs x env v n) : RS x env (· = v) n :=
  fun _ _ _ hr => h.det hr

theorem pure {P : α → Prop} {v : α} (h : P v) : RS (Pure.pure v : CostM α) env P 0 := by
  intro c v' c' hr
  simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨h, by simp⟩

theorem bind {x : CostM α} {f : α → CostM β} {P : α → Prop} {R : β → Prop} {n m : ℕ}
    (hx : RS x env P n) (hf : ∀ a, P a → RS (f a) env R m) : RS (x >>= f) env R (n + m) := by
  intro c v c' hr
  obtain ⟨a, c1, h1, h2⟩ := Runs.bind_some hr
  obtain ⟨ha, t1⟩ := hx c a c1 h1
  obtain ⟨hv, t2⟩ := hf a ha c1 v c' h2
  exact ⟨hv, by omega⟩

theorem mono {x : CostM α} {P R : α → Prop} {n : ℕ} (hx : RS x env P n) (h : ∀ a, P a → R a) :
    RS x env R n := fun c v c' hr => ⟨h v (hx c v c' hr).1, (hx c v c' hr).2⟩

theorem congr {x : CostM α} {P : α → Prop} {n n' : ℕ} (hx : RS x env P n) (h : n = n') :
    RS x env P n' := h ▸ hx

theorem sat {x : CostM α} {P : α → Prop} {n : ℕ} (hx : RS x env P n) : Sat x env P :=
  fun c v c' hr => (hx c v c' hr).1

/-- A whole computation that succeeds, from the empty bill: its value has `P`, its bill is `n`. -/
theorem billed {x : CostM α} {P : α → Prop} {n : ℕ} (hx : RS x env P n) {v : α} {k : ℕ}
    (h : CostM.billed x env = some (v, k)) : P v ∧ k = n := by
  unfold CostM.billed CostM.exec at h
  match hr : x.run env [] with
  | some (v', c') =>
    rw [hr] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨hp, ht⟩ := hx [] v' c' hr
    refine ⟨hp, ?_⟩
    rw [ht]
    simp [Cost.total]
  | none => rw [hr] at h; cases h

end RS

/-- One deterministic step of a run that may fail later. -/
macro "rstep " t:term : tactic =>
  `(tactic| (refine RS.bind (RS.of_runs $t) fun _ h => ?_; subst h))

/-- One free deterministic step. -/
theorem RS.bind0 {α β : Type} {env : Env} {x : CostM α} {f : α → CostM β} {a : α} {R : β → Prop}
    {m : ℕ} (hx : Runs x env a 0) (hf : RS (f a) env R m) : RS (x >>= f) env R m :=
  (RS.bind (RS.of_runs hx) fun _ h => h ▸ hf).congr (Nat.zero_add m)

theorem rs_mapM_loop {α β : Type} {env : Env} {f : α → Interp.counting.M β} {P : α → β → Prop}
    {c : α → ℕ} : ∀ (l : List α) (bs : List β), (∀ a ∈ l, RS (f a) env (P a) (c a)) →
      RS (@List.mapM.loop Interp.counting.M (instMonadInterp Interp.counting) α β f l bs) env
        (fun out => ∃ ys, out = bs.reverse ++ ys ∧ List.Forall₂ P l ys) (l.map c).sum
  | [], bs, _ => (RS.pure ⟨[], by simp, List.Forall₂.nil⟩).congr (by simp)
  | a :: l, bs, h => by
    simp only [List.mapM.loop, Interp.counting_bind]
    refine (RS.bind (m := (l.map c).sum) (h a List.mem_cons_self) fun b hb => ?_).congr (by simp)
    refine (rs_mapM_loop l (b :: bs) fun a' ha' => h a' (List.mem_cons_of_mem _ ha')).mono ?_
    rintro out ⟨ys, rfl, hys⟩
    exact ⟨b :: ys, by simp, List.Forall₂.cons hb hys⟩

/-- A map of steps that may fail: at each position a value with its step's property, and the
    costs added. -/
theorem rs_mapM {α β : Type} {env : Env} {f : α → Interp.counting.M β} {P : α → β → Prop}
    {c : α → ℕ} (l : List α) (h : ∀ a ∈ l, RS (f a) env (P a) (c a)) :
    RS (@List.mapM Interp.counting.M (instMonadInterp Interp.counting) α β f l) env
      (fun out => List.Forall₂ P l out) (l.map c).sum := by
  refine (rs_mapM_loop l [] h).mono ?_
  rintro out ⟨ys, rfl, hys⟩
  simpa using hys

/-- `exp`: the bounds of `expInterval`, when it accepts the argument. -/
theorem rs_exp {env : Env} (s : Q) :
    RS (Interp.counting.exp cat s) env
      (fun b => expInterval s.val = some (b.1.val, b.2.val)) 3 := by
  intro c b c' hr
  simp only [CostM.qexp] at hr
  split at hr
  · rename_i lo hi hlh
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨hlh, CompactCheck.Cost.total_add _ _ _⟩
  · cases hr

variable {env : Env}

/-! ## Entrywise differences -/

theorem runs_vsub (k : ℕ) (f g : ℕ → ℚ) :
    Runs (vsub Interp.counting (vec k f) (vec k g)) env (vec k fun a => f a - g a) k := by
  unfold vsub
  refine (runs_mapM (g := fun pr => (⟨pr.1.val - pr.2.val⟩ : Q)) (c := fun _ => 1) _
    fun pr _ => runs_sub cat _ _).congr ?_ (by simp [vec, zip_map_map, Function.comp_def])
  simp [vec, zip_map_map]

/-! ## Sorting -/

theorem runs_insertV (x : Q) : ∀ ys : List Q,
    Runs (insertV Interp.counting x ys) env (insVal x ys) (2 * ys.length)
  | [] => Runs.pure _
  | y :: ys => by
    unfold insertV
    simp only [Interp.counting_bind]
    exact Runs.bind' (runs_min cat x y) (Runs.bind' (runs_max cat x y)
      (Runs.bind' (runs_insertV _ ys) (Runs.pure _) rfl rfl) rfl rfl) rfl
      (by simp only [List.length_cons]; ring)

/-- The comparisons of an insertion sort of `k` entries. -/
def sortCost : ℕ → ℕ
  | 0 => 0
  | k + 1 => sortCost k + 2 * k

theorem sortCost_eq (k : ℕ) : sortCost k = k * (k - 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [sortCost, ih]
    rcases k with _ | k
    · rfl
    · simp only [Nat.add_sub_cancel]
      ring

theorem runs_sortV : ∀ xs : List Q,
    Runs (sortV Interp.counting xs) env (sortVal xs) (sortCost xs.length)
  | [] => Runs.pure _
  | x :: xs => by
    unfold sortV
    simp only [Interp.counting_bind]
    refine Runs.bind' (runs_sortV xs) (runs_insertV x _) rfl ?_
    rw [length_sortVal, List.length_cons, sortCost]

/-! ## Running sums -/

/-- Running sums from `a`. -/
def psAux : ℚ → List Q → List Q
  | _, [] => []
  | a, v :: vs => (⟨a + v.val⟩ : Q) :: psAux (a + v.val) vs

/-- The value of `prefixSums`. -/
def prefV (xs : List Q) : List Q := ⟨0⟩ :: psAux 0 xs

theorem foldl_ps : ∀ (xs : List Q) (a : ℚ) (out : List Q),
    (xs.foldl (fun (p : Q × List Q) v => ((⟨p.1.val + v.val⟩ : Q), p.2 ++ [⟨p.1.val + v.val⟩]))
      (⟨a⟩, out)).2 = out ++ psAux a xs
  | [], _, out => by simp [psAux]
  | v :: vs, a, out => by
    rw [List.foldl_cons, foldl_ps vs, psAux, List.append_assoc]
    rfl

theorem runs_prefixSums (xs : List Q) :
    Runs (prefixSums Interp.counting xs) env (prefV xs) xs.length := by
  unfold prefixSums
  simp only [Interp.counting_bind, Interp.counting_pure]
  refine Runs.bind' (runs_foldlM (c := fun _ => 1) (g := fun (p : Q × List Q) v =>
    ((⟨p.1.val + v.val⟩ : Q), p.2 ++ [⟨p.1.val + v.val⟩])) xs (⟨0⟩, [⟨0⟩]) fun p v _ => ?_)
    (Runs.pure _) ?_ (by simp)
  · exact Runs.bind' (runs_add cat p.1 v) (Runs.pure _) rfl rfl
  · rw [foldl_ps]
    rfl

theorem length_psAux : ∀ (a : ℚ) (xs : List Q), (psAux a xs).length = xs.length
  | _, [] => rfl
  | _, _ :: vs => by simp [psAux, length_psAux _ vs]

theorem length_prefV (xs : List Q) : (prefV xs).length = xs.length + 1 := by
  simp [prefV, length_psAux]

theorem psAux_get : ∀ (a : ℚ) (xs : List Q) (k : ℕ), k < xs.length →
    ((psAux a xs).getD k ⟨0⟩).val = a + ((xs.take (k + 1)).map (·.val)).sum
  | _, [], _, h => absurd h (by simp)
  | a, v :: vs, 0, _ => by simp [psAux]
  | a, v :: vs, k + 1, h => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at h
    simp only [psAux, List.getD_cons_succ, List.take_succ_cons, List.map_cons, List.sum_cons]
    rw [psAux_get _ vs k h]
    ring

/-- Entry `k` of the prefix sums: the sum of the first `k` entries. -/
theorem prefV_get (xs : List Q) {k : ℕ} (hk : k ≤ xs.length) :
    ((prefV xs).getD k ⟨0⟩).val = ((xs.take k).map (·.val)).sum := by
  rcases k with _ | k
  · simp [prefV]
  · simp only [prefV, List.getD_cons_succ]
    rw [psAux_get 0 xs k (by omega), zero_add]

/-- The value of `suffixSums`. -/
def sufV (xs : List Q) : List Q := (prefV xs.reverse).reverse

theorem runs_suffixSums (xs : List Q) :
    Runs (suffixSums Interp.counting xs) env (sufV xs) xs.length := by
  unfold suffixSums
  simp only [Interp.counting_bind, Interp.counting_pure]
  exact Runs.bind' (runs_prefixSums _) (Runs.pure _) rfl (by simp)

theorem length_sufV (xs : List Q) : (sufV xs).length = xs.length + 1 := by
  simp [sufV, length_prefV]

/-- Entry `k` of the suffix sums: the sum of the entries from the `k`-th on. -/
theorem sufV_get (xs : List Q) {k : ℕ} (hk : k ≤ xs.length) :
    ((sufV xs).getD k ⟨0⟩).val = ((xs.drop k).map (·.val)).sum := by
  have hl : (prefV xs.reverse).length = xs.length + 1 := by
    rw [length_prefV, List.length_reverse]
  unfold sufV
  rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega), hl,
    ← List.getD_eq_getElem?_getD, show xs.length + 1 - 1 - k = xs.length - k by omega,
    prefV_get _ (by simp), List.take_reverse, show xs.length - (xs.length - k) = k by omega,
    List.map_reverse, List.sum_reverse]

/-! ## The bounds of one endpoint -/

/-- The value of `scaleB`. -/
def scaleBV (ea s : Q × Q) (c1 : Q) : Q × Q :=
  (⟨0 + max 0 ea.1.val * (s.1.val + c1.val)⟩, ⟨0 + ea.2.val * (s.2.val + c1.val)⟩)

theorem runs_scaleB (ea s : Q × Q) (c1 : Q) :
    Runs (scaleB Interp.counting ea s c1) env (scaleBV ea s c1) 5 := by
  unfold scaleB
  simp only [Interp.counting_bind]
  exact Runs.bind' (runs_max cat _ _) (Runs.bind' (runs_add cat _ _) (Runs.bind' (runs_add cat _ _)
    (Runs.bind' (runs_muladd cat _ _ _) (Runs.bind' (runs_muladd cat _ _ _) (Runs.pure _) rfl rfl)
      rfl rfl) rfl rfl) rfl rfl) rfl rfl

/-- `scaleB` bounds `e (x + c1)`, for `e > 0` and `x ≥ 0` within their bounds. -/
theorem scaleBV_bounds {ea s : Q × Q} {c1 : Q} {e x : ℝ} (he : 0 < e) (he1 : (ea.1.val : ℝ) ≤ e)
    (he2 : e ≤ ea.2.val) (hx : 0 ≤ x) (hx1 : (s.1.val : ℝ) ≤ x) (hx2 : x ≤ s.2.val)
    (hc : (0 : ℝ) ≤ c1.val) :
    ((scaleBV ea s c1).1.val : ℝ) ≤ e * (x + c1.val) ∧
      e * (x + c1.val) ≤ (scaleBV ea s c1).2.val := by
  unfold scaleBV
  push_cast
  simp only [zero_add]
  constructor
  · rcases le_or_gt ((s.1.val : ℝ) + c1.val) 0 with h | h
    · exact le_trans (mul_nonpos_of_nonneg_of_nonpos (le_max_left _ _) h)
        (mul_nonneg he.le (by linarith))
    · exact mul_le_mul (max_le he.le he1) (by linarith) h.le he.le
  · exact mul_le_mul he2 (by linarith) (by linarith) (he.le.trans he2)

/-- The value of `shiftB`. -/
def shiftBV (s : Q × Q) (c2 : Q) : Q × Q := (⟨s.1.val + c2.val⟩, ⟨s.2.val + c2.val⟩)

theorem runs_shiftB (s : Q × Q) (c2 : Q) :
    Runs (shiftB Interp.counting s c2) env (shiftBV s c2) 2 := by
  unfold shiftB
  simp only [Interp.counting_bind]
  exact Runs.bind' (runs_add cat _ _) (Runs.bind' (runs_add cat _ _) (Runs.pure _) rfl rfl) rfl rfl

theorem shiftBV_bounds {s : Q × Q} {c2 : Q} {x : ℝ} (hx1 : (s.1.val : ℝ) ≤ x)
    (hx2 : x ≤ s.2.val) :
    ((shiftBV s c2).1.val : ℝ) ≤ x + c2.val ∧ x + c2.val ≤ (shiftBV s c2).2.val := by
  unfold shiftBV
  push_cast
  constructor <;> linarith

/-! ## The test of one endpoint -/

/-- The value of `endTest`. -/
def endTestV (A B : Q × Q) (yA yB : Q) : Bool := decide ((kupV A yA).val + (kupV B yB).val < 0)

theorem runs_endTest (A B : Q × Q) (yA yB : Q) :
    Runs (endTest Interp.counting A B yA yB) env (endTestV A B yA yB) 8 := by
  unfold endTest
  simp only [Interp.counting_bind]
  exact Runs.bind' (runs_kup _ _) (Runs.bind' (runs_kup _ _) (Runs.bind' (runs_add cat _ _)
    (runs_lt cat _ _) rfl rfl) rfl rfl) rfl rfl

/-- The value of `endpoint`. -/
def endpointV (A B : Q × Q) (K : List (Q × Q)) (sq : Q) : Bool :=
  (K.map fun k => endTestV A B ⟨k.1.val + sq.val⟩ ⟨k.2.val + sq.val⟩).foldl (· && ·) true

theorem runs_endpoint (A B : Q × Q) (K : List (Q × Q)) (sq : Q) :
    Runs (endpoint Interp.counting A B K sq) env (endpointV A B K sq) (K.length * 11) := by
  unfold endpoint
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_mapM (c := fun _ => 10) _ fun k _ => Runs.bind' (runs_add cat _ _)
    (Runs.bind' (runs_add cat _ _) (runs_endTest _ _ _ _) rfl rfl) rfl rfl)
    (foldl_band_cost _ _) rfl ?_
  simp only [sum_map_const', List.length_map]
  ring

theorem foldl_and_true : ∀ (l : List Bool) (b : Bool), l.foldl (· && ·) b = true →
    b = true ∧ ∀ x ∈ l, x = true
  | [], b, h => ⟨h, by simp⟩
  | x :: l, b, h => by
    simp only [List.foldl_cons] at h
    obtain ⟨h1, h2⟩ := foldl_and_true l _ h
    simp only [Bool.and_eq_true] at h1
    exact ⟨h1.1, fun y hy => by
      rcases List.mem_cons.mp hy with rfl | hy
      · exact h1.2
      · exact h2 y hy⟩

/-- **A passing endpoint.** For every weight `a` within `A`'s bounds and `b` within `B`'s, and
    every pair of constants `k` of the list, `a (k₁ + sq) + b (k₂ + sq) < 0`. -/
theorem endpointV_spec {A B : Q × Q} {K : List (Q × Q)} {sq : Q} (h : endpointV A B K sq = true)
    {a b : ℝ} (ha1 : (A.1.val : ℝ) ≤ a) (ha2 : a ≤ A.2.val) (hb1 : (B.1.val : ℝ) ≤ b)
    (hb2 : b ≤ B.2.val) {k : Q × Q} (hk : k ∈ K) :
    a * ((k.1.val : ℝ) + sq.val) + b * ((k.2.val : ℝ) + sq.val) < 0 := by
  have ht := (foldl_and_true _ _ h).2 _ (List.mem_map_of_mem hk)
  simp only [endTestV, decide_eq_true_eq] at ht
  have h1 := kupV_ge (y := (⟨k.1.val + sq.val⟩ : Q)) ha1 ha2
  have h2 := kupV_ge (y := (⟨k.2.val + sq.val⟩ : Q)) hb1 hb2
  have h3 : ((kupV A ⟨k.1.val + sq.val⟩).val : ℝ) + (kupV B ⟨k.2.val + sq.val⟩).val < 0 := by
    exact_mod_cast ht
  push_cast at h1 h2
  linarith

/-! ## The constants of the endpoints -/

/-- The largest `L_j + avg R_j` over the other outputs. -/
def topV (V m : ℕ) (Ls Rs : List Q) (avg : Q) : Q :=
  maxLV ((others V m).map fun j =>
    (⟨(at1 Interp.counting Ls j).val + avg.val * (at1 Interp.counting Rs j).val⟩ : Q))

/-- The value of `endConsts`. -/
def endConstsV (V m : ℕ) (Ls Rs : List Q) (Rmax Rmin W avg one : Q) : List (Q × Q) :=
  [Rmax, Rmin].map fun Rx =>
    ((⟨(topV V m Ls Rs avg).val + (one.val - avg.val) * W.val +
        (one.val - avg.val) * (Rx.val - W.val)⟩ : Q),
      (⟨(topV V m Ls Rs avg).val + (one.val - avg.val) * W.val -
        (0 + avg.val * (Rx.val - W.val))⟩ : Q))

/-- The cost of `endConsts`. -/
def endConstsCost (V : ℕ) : ℕ := (V - 1) + ((V - 1) - 1) + 1 + 1 + 8

/-- One pair of constants. -/
theorem runs_endPair (g0 om W avg Rx : Q) :
    Runs (do
      let dx ← CostM.qsub cat Rx W
      let ka ← CostM.qmuladd cat g0 om dx
      let t ← CostM.qmuladd cat ⟨0⟩ avg dx
      let kb ← CostM.qsub cat g0 t
      pure (ka, kb)) env
      ((⟨g0.val + om.val * (Rx.val - W.val)⟩ : Q),
        (⟨g0.val - (0 + avg.val * (Rx.val - W.val))⟩ : Q)) 4 :=
  Runs.bind' (runs_sub cat _ _) (Runs.bind' (runs_muladd cat _ _ _) (Runs.bind'
    (runs_muladd cat _ _ _) (Runs.bind' (runs_sub cat _ _) (Runs.pure _) rfl rfl) rfl rfl) rfl rfl)
    rfl rfl

theorem runs_endConsts {V m : ℕ} (hm : m < V) (Ls Rs : List Q) (Rmax Rmin W avg one : Q) :
    Runs (endConsts Interp.counting V m Ls Rs Rmax Rmin W avg one) env
      (endConstsV V m Ls Rs Rmax Rmin W avg one) (endConstsCost V) := by
  unfold endConsts endConstsCost
  simp only [Interp.counting_bind, Interp.counting_pure]
  refine (Runs.bind (runs_mapM (c := fun _ => 1) _ fun j _ => runs_muladd cat _ _ _)
    (Runs.bind (runs_maxL _) (Runs.bind (runs_sub cat _ _) (Runs.bind (runs_muladd cat _ _ _)
      (runs_mapM (c := fun _ => 4) _ fun Rx _ => runs_endPair _ _ _ _ Rx))))).congr ?_ ?_
  · simp [endConstsV, topV]
  · simp only [sum_map_const', List.length_map, length_others hm, List.length_cons,
      List.length_nil]
    omega

/-- Every other output's `L_j + avg R_j` is at most the top. -/
theorem le_topV {V m : ℕ} {Ls Rs : List Q} {avg : Q} {j : ℕ} (hj : j < V) (hjm : j ≠ m) :
    (at1 Interp.counting Ls j).val + avg.val * (at1 Interp.counting Rs j).val ≤
      (topV V m Ls Rs avg).val :=
  le_maxLV_map (f := fun j => (⟨(at1 Interp.counting Ls j).val +
    avg.val * (at1 Interp.counting Rs j).val⟩ : Q)) (mem_others.mpr ⟨hj, hjm⟩)

end GrossSub

namespace GrossSub

open CompactCheck Common AttnClasses GrossCubic Finset

variable {env : Env}

/-! ## The sorted sums of one query -/

/-- `Σ e^x` over a list of rationals. -/
noncomputable def esum (l : List ℚ) : ℝ := (l.map fun x : ℚ => Real.exp (x : ℝ)).sum

/-- What the sorted sums deliver for the offsets `o`: an arrangement `ws` of them in increasing
    order, `pre[k]` bounding `Σ e^w` over its first `k` entries and `suf[k]` over the rest. -/
def SortedSpec (o : List ℚ) (pre suf : List (Q × Q)) : Prop :=
  ∃ ws : List ℚ, ws.Pairwise (· ≤ ·) ∧ ws.Perm o ∧ ∀ k ≤ o.length,
    ((pre.getD k (⟨0⟩, ⟨0⟩)).1.val : ℝ) ≤ esum (ws.take k) ∧
    esum (ws.take k) ≤ (pre.getD k (⟨0⟩, ⟨0⟩)).2.val ∧
    ((suf.getD k (⟨0⟩, ⟨0⟩)).1.val : ℝ) ≤ esum (ws.drop k) ∧
    esum (ws.drop k) ≤ (suf.getD k (⟨0⟩, ⟨0⟩)).2.val

/-- The cost of `sortedSums`: the offsets, the sort, `exp`, and the four running sums. -/
def sortedCost (n : ℕ) : ℕ :=
  (n - 1) + (sortCost (n - 1) + (3 * (n - 1) + ((n - 1) + ((n - 1) + ((n - 1) + ((n - 1) + 0))))))

theorem getD_zip {α β : Type} (l1 : List α) (l2 : List β) (a : α) (b : β) {k : ℕ}
    (h1 : k < l1.length) (h2 : k < l2.length) :
    (List.zip l1 l2).getD k (a, b) = (l1.getD k a, l2.getD k b) := by
  simp [List.getD_eq_getElem?_getD, h1, h2]

theorem esum_cons (x : ℚ) (l : List ℚ) : esum (x :: l) = Real.exp (x : ℝ) + esum l := by
  simp [esum]

theorem esum_nonneg (l : List ℚ) : 0 ≤ esum l :=
  List.sum_nonneg fun y hy => by
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hy
    exact (Real.exp_pos _).le

/-- Termwise bounds on `exp`, summed over the first `k` entries. -/
theorem forall₂_take : ∀ {w : List Q} {ex : List (Q × Q)},
    List.Forall₂ (fun s b => expInterval s.val = some (b.1.val, b.2.val)) w ex → ∀ k : ℕ,
    (((((ex.map (·.1)).take k).map (·.val)).sum : ℚ) : ℝ) ≤ esum ((w.map (·.val)).take k) ∧
      esum ((w.map (·.val)).take k) ≤ (((((ex.map (·.2)).take k).map (·.val)).sum : ℚ) : ℝ)
  | [], [], List.Forall₂.nil, k => by simp [esum]
  | s :: w, b :: ex, List.Forall₂.cons hsb hrest, k => by
    rcases k with _ | k
    · simp [esum]
    · obtain ⟨h1, h2⟩ := forall₂_take hrest k
      have hb := expInterval_spec hsb
      simp only [List.map_cons, List.take_succ_cons, List.sum_cons, esum_cons, Rat.cast_add]
      constructor <;> linarith [hb.1, hb.2]

/-- Termwise bounds on `exp`, summed over the entries from the `k`-th on. -/
theorem forall₂_drop : ∀ {w : List Q} {ex : List (Q × Q)},
    List.Forall₂ (fun s b => expInterval s.val = some (b.1.val, b.2.val)) w ex → ∀ k : ℕ,
    (((((ex.map (·.1)).drop k).map (·.val)).sum : ℚ) : ℝ) ≤ esum ((w.map (·.val)).drop k) ∧
      esum ((w.map (·.val)).drop k) ≤ (((((ex.map (·.2)).drop k).map (·.val)).sum : ℚ) : ℝ)
  | [], [], List.Forall₂.nil, k => by simp [esum]
  | s :: w, b :: ex, List.Forall₂.cons hsb hrest, k => by
    rcases k with _ | k
    · obtain ⟨h1, h2⟩ := forall₂_drop hrest 0
      have hb := expInterval_spec hsb
      simp only [List.map_cons, List.drop_zero, List.sum_cons, esum_cons, Rat.cast_add] at h1 h2 ⊢
      constructor <;> linarith [hb.1, hb.2]
    · simpa using forall₂_drop hrest k

theorem runs_offsets (n : ℕ) (r : ℕ → ℚ) :
    Runs ((List.range (n - 1)).mapM fun p => Interp.counting.sub cat
        (at1 Interp.counting (vec n r) p) (at1 Interp.counting (vec n r) (n - 1))) env
      (vec (n - 1) fun p => r p - r (n - 1)) (n - 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0
    exact Runs.pure _
  refine (runs_mapM_range (n - 1) fun p hp => runs_sub cat _ _).congr ?_ (by ring)
  refine List.map_congr_left fun p hp => ?_
  rw [at1_vec (by have := List.mem_range.mp hp; omega), at1_vec (by omega)]

/-- **The sorted sums.** A run that succeeds returns, for the offsets `r p - r (n - 1)` of the
    positions other than the last, the bounds of `SortedSpec`. -/
theorem rs_sortedSums (n : ℕ) (r : ℕ → ℚ) :
    RS (sortedSums Interp.counting n (vec n r)) env
      (fun res => SortedSpec ((List.range (n - 1)).map fun p => r p - r (n - 1)) res.1 res.2)
      (sortedCost n) := by
  unfold sortedSums sortedCost
  simp only [Interp.counting_bind, Interp.counting_pure]
  set o : List Q := vec (n - 1) fun p => r p - r (n - 1) with ho
  have hol : o.length = n - 1 := length_vec _ _
  rstep (runs_offsets n r)
  refine RS.bind ((RS.of_runs (runs_sortV o)).congr (by rw [hol])) fun w hw => ?_
  subst hw
  refine RS.bind ((rs_mapM (c := fun _ => 3) (sortVal o) fun s _ => rs_exp s).congr
    (by rw [sum_map_const', length_sortVal, hol]; ring)) fun ex hex => ?_
  have hexl : ex.length = n - 1 := by
    rw [List.Forall₂.length_eq hex |>.symm, length_sortVal, hol]
  refine RS.bind ((RS.of_runs (runs_prefixSums _)).congr (by rw [List.length_map, hexl]))
    fun plo hplo => ?_
  subst hplo
  refine RS.bind ((RS.of_runs (runs_prefixSums _)).congr (by rw [List.length_map, hexl]))
    fun phi hphi => ?_
  subst hphi
  refine RS.bind ((RS.of_runs (runs_suffixSums _)).congr (by rw [List.length_map, hexl]))
    fun slo hslo => ?_
  subst hslo
  refine RS.bind ((RS.of_runs (runs_suffixSums _)).congr (by rw [List.length_map, hexl]))
    fun shi hshi => ?_
  subst hshi
  refine RS.pure ⟨(sortVal o).map (·.val), sortVal_sorted o, ?_, fun k hk => ?_⟩
  · refine (sortVal_perm o).trans (List.Perm.of_eq ?_)
    simp [ho, vec, Function.comp_def]
  · have hk' : k ≤ n - 1 := by simpa using hk
    have hl1 : ∀ f : Q × Q → Q, (prefV (ex.map f)).length = n - 1 + 1 := fun f => by
      rw [length_prefV, List.length_map, hexl]
    have hl2 : ∀ f : Q × Q → Q, (sufV (ex.map f)).length = n - 1 + 1 := fun f => by
      rw [length_sufV, List.length_map, hexl]
    rw [getD_zip _ _ _ _ (by rw [hl1]; omega) (by rw [hl1]; omega),
      getD_zip _ _ _ _ (by rw [hl2]; omega) (by rw [hl2]; omega)]
    simp only
    have hkx : k ≤ (ex.map (·.1)).length := by rw [List.length_map, hexl]; exact hk'
    have hkx' : k ≤ (ex.map (·.2)).length := by rw [List.length_map, hexl]; exact hk'
    rw [prefV_get _ hkx, prefV_get _ hkx', sufV_get _ hkx, sufV_get _ hkx']
    obtain ⟨t1, t2⟩ := forall₂_take hex k
    obtain ⟨d1, d2⟩ := forall₂_drop hex k
    exact ⟨t1, t2, d1, d2⟩

end GrossSub

namespace GrossSub

open CompactCheck Common AttnClasses GrossCubic Finset

variable {env : Env}

/-! ## The test of one class -/

/-- `Ê[q, m] - max_{ρ ≤ j} Ê[q, ρ] - ε_q`: at most the query part of the score of `m` over any
    token of rank at most `j`. -/
def aloV (q m : ℕ) (Eh : List (List Q)) (eps rmax : List Q) (j : ℕ) : Q :=
  ⟨((at2 Interp.counting Eh q m).val - (at1 Interp.counting rmax j).val) -
    (at1 Interp.counting eps q).val⟩

/-- `Ê[q, m] - min_{ρ ≤ j} Ê[q, ρ] + ε_q`: at least that difference. -/
def ahiV (q m : ℕ) (Eh : List (List Q)) (eps rmin : List Q) (j : ℕ) : Q :=
  ⟨((at2 Interp.counting Eh q m).val - (at1 Interp.counting rmin j).val) +
    (at1 Interp.counting eps q).val⟩

/-- The number of positions, other than the query's, that hold the largest token. -/
def kOf (n rq lam c : ℕ) : ℕ := if rq = lam then n - c - 1 else n - c

/-- The query's own weight on the largest token's side: one if it is the largest token. -/
def c1Of (rq lam : ℕ) (one : Q) : Q := if rq = lam then one else ⟨0⟩

/-- The query's own weight on the other side. -/
def c2Of (rq lam : ℕ) (one : Q) : Q := if rq = lam then ⟨0⟩ else one

/-- The test at the endpoint of the smallest attention on the largest token. -/
def tloV (n rq lam c : ℕ) (pre suf KL : List (Q × Q)) (sq one : Q) (elo : Q × Q) : Bool :=
  endpointV (scaleBV elo (pre.getD (kOf n rq lam c) (⟨0⟩, ⟨0⟩)) (c1Of rq lam one))
    (shiftBV (suf.getD (kOf n rq lam c) (⟨0⟩, ⟨0⟩)) (c2Of rq lam one)) KL sq

/-- The test at the endpoint of the largest attention. -/
def thiV (n rq lam c : ℕ) (pre suf KH : List (Q × Q)) (sq one : Q) (ehi : Q × Q) : Bool :=
  endpointV (scaleBV ehi (suf.getD (n - 1 - kOf n rq lam c) (⟨0⟩, ⟨0⟩)) (c1Of rq lam one))
    (shiftBV (pre.getD (n - 1 - kOf n rq lam c) (⟨0⟩, ⟨0⟩)) (c2Of rq lam one)) KH sq

/-- The value of `classTest`, from the bounds `elo`, `ehi` that `exp` returned. -/
def classTestV (n rq lam c : ℕ) (pre suf KL KH : List (Q × Q)) (dir : Bool × Bool) (sq one : Q)
    (elo ehi : Q × Q) : Bool :=
  (dir.1 && tloV n rq lam c pre suf KL sq one elo ||
    dir.2 && thiV n rq lam c pre suf KH sq one ehi) ||
  (tloV n rq lam c pre suf KL sq one elo && thiV n rq lam c pre suf KH sq one ehi)

/-- The cost of `classTest` with `a` and `b` pairs of constants at the two endpoints. -/
def classTestCost (a b : ℕ) : ℕ := 29 + a * 11 + b * 11

/-- **One class.** A run that succeeds has `exp` accept both ends of the query's gaps, and returns
    `classTestV` of the bounds it gave. -/
theorem rs_classTest (n rq lam c g q m : ℕ) (Eh : List (List Q)) (eps rmax rmin : List Q)
    (pre suf KL KH : List (Q × Q)) (dir : Bool × Bool) (sq one : Q) :
    RS (classTest Interp.counting n rq lam c g q m Eh eps rmax rmin pre suf KL KH dir sq one) env
      (fun b => ∃ elo ehi : Q × Q,
        expInterval (aloV q m Eh eps rmax (lam - g)).val = some (elo.1.val, elo.2.val) ∧
        expInterval (ahiV q m Eh eps rmin (lam - g)).val = some (ehi.1.val, ehi.2.val) ∧
        b = classTestV n rq lam c pre suf KL KH dir sq one elo ehi)
      (classTestCost KL.length KH.length) := by
  unfold classTest
  simp only [Interp.counting_bind]
  refine RS.congr (n := 1 + (1 + (1 + (1 + (3 + (3 + (5 + (2 + (5 + (2 + (KL.length * 11 +
    (KH.length * 11 + (1 + (1 + (1 + (1 + 1)))))))))))))))) ?_ (by unfold classTestCost; ring)
  rstep (runs_sub cat _ _)
  rstep (runs_sub cat _ _)
  rstep (runs_sub cat _ _)
  rstep (runs_add cat _ _)
  refine RS.bind (rs_exp _) fun elo helo => ?_
  refine RS.bind (rs_exp _) fun ehi hehi => ?_
  rstep (runs_scaleB _ _ _)
  rstep (runs_shiftB _ _)
  rstep (runs_scaleB _ _ _)
  rstep (runs_shiftB _ _)
  rstep (runs_endpoint _ _ _ _)
  rstep (runs_endpoint _ _ _ _)
  rstep (runs_band cat _ _)
  rstep (runs_band cat _ _)
  rstep (runs_band cat _ _)
  rstep (runs_bor cat _ _)
  refine (RS.of_runs (runs_bor cat _ _)).mono fun b hb => ⟨elo, ehi, helo, hehi, ?_⟩
  rw [hb]
  rfl

/-! ## The direct path -/

/-- What the direct path delivers: `D[q, j] - D[q, m] ≤ μU_j - μU_m + s_q` for every query `q`
    and outputs `j`, `m`. -/
def EupuSpec (V : ℕ) (D : ℕ → ℕ → ℚ) (muU sp : ℕ → ℚ) : Prop :=
  ∀ q < V, ∀ j < V, ∀ m < V, D q j - D q m ≤ (muU j - muU m) + sp q

/-- The cost of `eupuOut`. -/
def eupuCost (eu V d : ℕ) : ℕ :=
  if eu = 0 then V * d + (d * (2 * (V - 1) + 1) + (V * (d * 4) + 0))
  else if eu = 1 then V * (2 * (V - 1) + 1) + 0
  else V * (V - 1) + (V * (V - 1) + ((V - 1) + ((V - 1) + (1 + 0))))

theorem runs_maxL_vec (k : ℕ) (f : ℕ → ℚ) :
    Runs (maxL Interp.counting (vec k f)) env (maxLV (vec k f)) (k - 1) :=
  (runs_maxL _).congr rfl (by rw [length_vec])

theorem runs_minL_vec (k : ℕ) (f : ℕ → ℚ) :
    Runs (minL Interp.counting (vec k f)) env (minLV (vec k f)) (k - 1) :=
  (runs_minL _).congr rfl (by rw [length_vec])

/-- **The direct path.** For every method, the run of `eupuOut` and the bound it delivers on the
    table `D = Eq U`. -/
theorem runs_eupuOut (eu V d : ℕ) (Eq U : ℕ → ℕ → ℚ) (mu : ℕ → ℚ) :
    ∃ fmu fsp, Runs (eupuOut Interp.counting eu V d (mat V d Eq)
        (mat V V fun q j => ∑ a ∈ range d, Eq q a * U a j) (mat d V U) (vec d mu)) env
      (vec V fmu, vec V fsp) (eupuCost eu V d) ∧
      EupuSpec V (fun q j => ∑ a ∈ range d, Eq q a * U a j) fmu fsp := by
  set D : ℕ → ℕ → ℚ := fun q j => ∑ a ∈ range d, Eq q a * U a j with hD
  unfold eupuOut eupuCost
  rcases (by omega : eu = 0 ∨ eu = 1 ∨ 2 ≤ eu) with h0 | h0 | h0
  · subst h0
    refine ⟨fun j => ∑ a ∈ range d, mu a * U a j,
      fun q => ∑ a ∈ range d, |Eq q a - mu a| * spreadV V (U a), ?_, ?_⟩
    · simp only [↓reduceIte, Interp.counting_bind, Interp.counting_pure]
      refine Runs.bind' (runs_vecMat d V mu U) ?_ rfl rfl
      refine Runs.bind' (runs_mapM_mat d V U fun a _ => runs_spread V (U a)) ?_ rfl rfl
      exact Runs.bind' (runs_mapM_mat V d Eq fun q _ => runs_absDot_vec d (Eq q) mu _)
        (Runs.pure _) rfl rfl
    · intro q _ j hj m hm
      exact prod_diff_le d (Eq q) U mu (fun a => spreadV V (U a)) _ j m
        (fun a _ => spreadV_ge V _ hj hm) (fun a _ => spreadV_ge V _ hm hj) le_rfl
  · subst h0
    refine ⟨fun _ => 0, fun q => spreadV V (D q), ?_, ?_⟩
    · simp only [one_ne_zero, ↓reduceIte, Interp.counting_bind, Interp.counting_pure]
      exact Runs.bind' (runs_mapM_mat V V D fun q _ => runs_spread V (D q)) (Runs.pure _)
        (by rw [replicate_vec]; rfl) rfl
    · intro q _ j hj m hm
      have := spreadV_ge V (D q) hj hm
      simp only [sub_self, zero_add]
      exact this
  · have h0' : eu ≠ 0 := by omega
    have h1' : eu ≠ 1 := by omega
    set top := maxLV ((List.range V).map fun q => maxLV (vec V (D q)))
    set bot := minLV ((List.range V).map fun q => minLV (vec V (D q)))
    refine ⟨fun _ => 0, fun _ => top.val - bot.val, ?_, ?_⟩
    · simp only [h0', h1', ↓reduceIte, Interp.counting_bind, Interp.counting_pure]
      refine Runs.bind' (runs_mapM_mat V V D fun q _ => runs_maxL_vec V (D q)) ?_ rfl rfl
      refine Runs.bind' (runs_mapM_mat V V D fun q _ => runs_minL_vec V (D q)) ?_ rfl rfl
      refine Runs.bind' ((runs_maxL _).congr rfl (by simp)) ?_ rfl rfl
      refine Runs.bind' ((runs_minL _).congr rfl (by simp)) ?_ rfl rfl
      exact Runs.bind' (runs_sub cat _ _) (Runs.pure _) (by rw [replicate_vec, replicate_vec])
        rfl
    · intro q hq j hj m hm
      have h1 : D q j ≤ (maxLV (vec V (D q))).val :=
        le_maxLV (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
      have h2 : (maxLV (vec V (D q))).val ≤ top.val :=
        le_maxLV_map (f := fun q => maxLV (vec V (D q))) (List.mem_range.mpr hq)
      have h3 : (minLV (vec V (D q))).val ≤ D q m :=
        minLV_le (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩)
      have h4 : bot.val ≤ (minLV (vec V (D q))).val :=
        minLV_le (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩)
      simp only [sub_self, zero_add]
      linarith

end GrossSub

namespace GrossSub

open CompactCheck Common AttnClasses GrossCubic Finset

variable {env : Env}

/-! ## A block: the inputs of one largest token -/

/-- `R_j = EVOU[m, j] - EVOU[m, m]`, the label's path through the head, per output. -/
def RsV (V m : ℕ) (EV : List (List Q)) : List Q :=
  (List.range V).map fun j =>
    ⟨(at2 Interp.counting EV m j).val - (at2 Interp.counting EV m m).val⟩

/-- `L_j = μU_j - μU_m + Pp_j`: the direct path's shared part and the positional path. -/
def LsV (V m : ℕ) (muU Pp : List Q) : List Q :=
  (List.range V).map fun j =>
    ⟨((at1 Interp.counting muU j).val - (at1 Interp.counting muU m).val) +
      (at1 Interp.counting Pp j).val⟩

/-- `R_max` and `R_min` over the outputs other than `m`. -/
def RmaxV (V m : ℕ) (Rs : List Q) : Q := maxLV ((others V m).map (at1 Interp.counting Rs))

def RminV (V m : ℕ) (Rs : List Q) : Q := minLV ((others V m).map (at1 Interp.counting Rs))

/-- What a passing verdict of the class of `c0 + 1` other positions and the query of rank `rq`
    says: the class is one of the plan's, `W` is in range, step 1's check passed, `exp` accepted
    both ends of the query's gaps, and the test passed on the bounds it gave. -/
def ClassOK (mx : Bool) (V n : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (Eh : List (List Q)) (eps : List Q)
    (ok : Bool) (srt : List (List (Q × Q) × List (Q × Q))) (sp : List Q)
    (rm : List (List Q × List Q)) (Wpre avgs : List Q) (one : Q) (lam m : ℕ) (Ls Rs : List Q)
    (Rmax Rmin : Q) (c0 rq : ℕ) : Prop :=
  gapW gap lam (c0 + 1) ≤ lam ∧ valid gap rq lam (c0 + 1) = true ∧ ok = true ∧
  ∃ elo ehi : Q × Q,
    expInterval (aloV (tok mx V rq) m Eh eps (rm.getD (tok mx V rq) ([], [])).1
      (lam - gapOf gap rq lam (c0 + 1))).val = some (elo.1.val, elo.2.val) ∧
    expInterval (ahiV (tok mx V rq) m Eh eps (rm.getD (tok mx V rq) ([], [])).2
      (lam - gapOf gap rq lam (c0 + 1))).val = some (ehi.1.val, ehi.2.val) ∧
    classTestV n rq lam (c0 + 1) (srt.getD (tok mx V rq) ([], [])).1
      (srt.getD (tok mx V rq) ([], [])).2
      (endConstsV V m Ls Rs Rmax Rmin (at1 Interp.counting Wpre (lam - gapW gap lam (c0 + 1)))
        (at1 Interp.counting avgs (lam * n + (c0 + 1))) one)
      (endConstsV V m Ls Rs Rmax Rmin (at1 Interp.counting Wpre (lam - gapW gap lam (c0 + 1)))
        (at1 Interp.counting avgs (V * n + lam * n + (c0 + 1))) one)
      (decide (Rmax.val < (at1 Interp.counting Wpre (lam - gapW gap lam (c0 + 1))).val),
        decide ((at1 Interp.counting Wpre (lam - gapW gap lam (c0 + 1))).val ≤ Rmin.val))
      (at1 Interp.counting sp (tok mx V rq)) one elo ehi = true

/-- The count of a block, from its verdicts. -/
def blockSum (gap : ℕ → ℕ → ℕ → ℕ) (n lam : ℕ) (b0 : Bool) (verd : List (List Bool)) : ℕ :=
  (List.range (lam + 1)).foldl (fun a rq =>
    (List.range (Nat.pow 2 (n - 1))).foldl (fun a pat =>
      Nat.add a (cntOf Interp.counting gap lam rq (inPat (n - 1) pat).length b0 verd)) a) 0

/-- The cost of one row of verdicts (one number of other positions). -/
def rowCost (V lam : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (c0 : ℕ) : ℕ :=
  if Nat.ble (gapW gap lam (c0 + 1)) lam = true then
    endConstsCost V + (endConstsCost V + (1 + (1 + ((List.range (lam + 1)).map fun rq =>
      if valid gap rq lam (c0 + 1) = true then classTestCost 2 2 + 1 else 0).sum)))
  else 0

/-- The cost of a block. -/
def subBlockCost (V n : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (lam : ℕ) : ℕ :=
  V * (n + (n - 1)) + ((2 * (V - 1) + (V - 1 - 1) + 2) + (V * 1 + ((V - 1 - 1) + ((V - 1 - 1) +
    (V * 2 + (((List.range (n - 1)).map (rowCost V lam gap)).sum + 0))))))

theorem length_endConstsV (V m : ℕ) (Ls Rs : List Q) (Rmax Rmin W avg one : Q) :
    (endConstsV V m Ls Rs Rmax Rmin W avg one).length = 2 := rfl

/-- A map over `[0, k)` related to its values: entry `i` of the values, for `i < k`. -/
theorem forall₂_range_getD {β : Type} {R : ℕ → β → Prop} {k : ℕ} {out : List β}
    (h : List.Forall₂ R (List.range k) out) (z : β) {i : ℕ} (hi : i < k) : R i (out.getD i z) := by
  obtain ⟨hl, hg⟩ := AttnClasses.forall₂_get h
  have hi' : i < out.length := by rw [hl, List.length_range]; exact hi
  have := hg i (by simpa using hi) hi'
  simp only [List.getElem_range] at this
  rw [getD_of_lt hi']
  exact this

theorem forall₂_range_length {β : Type} {R : ℕ → β → Prop} {k : ℕ} {out : List β}
    (h : List.Forall₂ R (List.range k) out) : out.length = k := by
  rw [(AttnClasses.forall₂_get h).1, List.length_range]

/-- **A block.** A run that succeeds returns the count of `blockSum` over verdicts each of which,
    when it passes, says `ClassOK`. -/
theorem rs_block (mx : Bool) {V : ℕ} (n : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (EU EV PV Eh : List (List Q))
    (eps : List Q) (ok : Bool) (srt : List (List (Q × Q) × List (Q × Q))) (muU sp : List Q)
    (rm : List (List Q × List Q)) (Wpre avgs : List Q) (one : Q) {lam : ℕ} (hlam : lam < V) :
    RS (block Interp.counting mx V n gap EU EV PV Eh eps ok srt muU sp rm Wpre avgs one lam) env
      (fun cnt => ∃ verd : List (List Bool),
        (∀ c0 rq, (verd.getD c0 []).getD rq false = true → c0 < n - 1 ∧ rq ≤ lam ∧
          ClassOK mx V n gap Eh eps ok srt sp rm Wpre avgs one lam (tok mx V lam)
            (LsV V (tok mx V lam) muU (ppessV V n (tok mx V lam) PV)) (RsV V (tok mx V lam) EV)
            (RmaxV V (tok mx V lam) (RsV V (tok mx V lam) EV))
            (RminV V (tok mx V lam) (RsV V (tok mx V lam) EV)) c0 rq) ∧
        cnt = blockSum gap n lam (onlyMaxV V (tok mx V lam) EU EV
          (ppessV V n (tok mx V lam) PV)) verd)
      (subBlockCost V n gap lam) := by
  have hm : tok mx V lam < V := tok_lt hlam
  set m := tok mx V lam with hmdef
  unfold block subBlockCost
  simp only [Interp.counting_bind, Interp.counting_pure]
  rstep (runs_ppess V n m PV)
  refine RS.bind ((RS.of_runs (runs_onlyMax V m EU EV _)).congr (by rw [length_others hm]))
    fun b0 hb0 => ?_
  subst hb0
  rstep (runs_mapM_range V fun j _ => runs_sub cat _ _)
  refine RS.bind ((RS.of_runs (runs_maxL _)).congr (by rw [List.length_map, length_others hm]))
    fun Rmax hRmax => ?_
  subst hRmax
  refine RS.bind ((RS.of_runs (runs_minL _)).congr (by rw [List.length_map, length_others hm]))
    fun Rmin hRmin => ?_
  subst hRmin
  rstep (runs_mapM_range V fun j _ => Runs.bind' (runs_sub cat _ _) (runs_add cat _ _) rfl rfl)
  refine RS.bind (rs_mapM (c := rowCost V lam gap) (P := fun c0 row => ∀ rq,
      row.getD rq false = true → rq ≤ lam ∧
        ClassOK mx V n gap Eh eps ok srt sp rm Wpre avgs one lam m (LsV V m muU (ppessV V n m PV))
          (RsV V m EV) (RmaxV V m (RsV V m EV)) (RminV V m (RsV V m EV)) c0 rq) _
      fun c0 _ => ?_) fun verd hverd => ?_
  · -- one row
    unfold rowCost
    by_cases hb : Nat.ble (gapW gap lam (c0 + 1)) lam = true
    · simp only [hb, ↓reduceIte]
      rstep (runs_endConsts hm _ _ _ _ _ _ _)
      rstep (runs_endConsts hm _ _ _ _ _ _ _)
      rstep (runs_lt cat _ _)
      rstep (runs_le cat _ _)
      refine (rs_mapM (P := fun rq b => b = true →
        ClassOK mx V n gap Eh eps ok srt sp rm Wpre avgs one lam m (LsV V m muU (ppessV V n m PV))
          (RsV V m EV) (RmaxV V m (RsV V m EV)) (RminV V m (RsV V m EV)) c0 rq) _
        fun rq _ => ?_).mono fun row hrow rq hrq => ?_
      · by_cases hv : valid gap rq lam (c0 + 1) = true
        · simp only [hv, ↓reduceIte]
          refine RS.bind ((rs_classTest _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).congr
            (by rw [length_endConstsV, length_endConstsV])) fun t ht => ?_
          refine (RS.of_runs (runs_band cat _ _)).mono fun b hb' hbt => ?_
          rw [hb', Bool.and_eq_true] at hbt
          obtain ⟨elo, ehi, h1, h2, h3⟩ := ht
          rw [h3] at hbt
          exact ⟨Nat.le_of_ble_eq_true hb, hv, hbt.2, elo, ehi, h1, h2, hbt.1⟩
        · simp only [hv, ↓reduceIte, Bool.false_eq_true]
          exact RS.pure fun h => absurd h (by simp)
      · have hl := forall₂_range_length hrow
        by_cases hrl : rq < lam + 1
        · exact ⟨by omega, forall₂_range_getD hrow false hrl hrq⟩
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at hrq
          simp at hrq
    · simp only [hb, ↓reduceIte, Bool.false_eq_true]
      refine RS.pure fun rq hrq => ?_
      rw [List.getD_eq_getElem?_getD] at hrq
      by_cases hrl : rq < lam + 1
      · simp [hrl] at hrq
      · simp [hrl] at hrq
  · -- the count
    refine RS.pure ⟨verd, fun c0 rq h => ?_, rfl⟩
    have hl := forall₂_range_length hverd
    by_cases hc : c0 < n - 1
    · obtain ⟨h1, h2⟩ := forall₂_range_getD hverd [] hc rq h
      exact ⟨hc, h1, h2⟩
    · rw [List.getD_eq_getElem?_getD (l := verd), List.getElem?_eq_none (by omega)] at h
      simp at h

end GrossSub
