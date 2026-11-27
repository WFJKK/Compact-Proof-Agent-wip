import Candidate.LibAttnFamily

/-!
# What the checker of entry 6 computes, and what it costs

Each function of the checker, run by the counting interpreter, as a `Runs`: its value and its exact
number of operations. The tables are matrices written as `mat m k f`, the list of rows
`[f i 0, ..., f i (k-1)]` for `i < m`; every product of the checker is one of `mat m k fA` with
the rows `mat p k fB`, and costs `m p k` (`runs_mm`).

`exp` can fail (on an argument of `2^12` or more, or one that is not dyadic), so the table of
bounds on `exp` of the scores is described by what a run that succeeds returns (`Sat`), and its
`Runs` needs every call to succeed.
-/

namespace AttnClasses

open CompactCheck Common Finset

/-! ## Runs that succeed -/

/-- Every run of `x` that succeeds returns a value with `P`. -/
def Sat {α : Type} (x : CostM α) (env : Env) (P : α → Prop) : Prop :=
  ∀ c v c', x.run env c = some (v, c') → P v

namespace Sat

variable {α β : Type} {env : Env}

theorem of_runs {x : CostM α} {v : α} {n : ℕ} (h : Runs x env v n) : Sat x env (· = v) :=
  fun _ _ _ hr => (h.det hr).1

theorem pure {P : α → Prop} {v : α} (h : P v) : Sat (Pure.pure v : CostM α) env P := by
  intro c v' c' hr
  simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
  exact hr.1 ▸ h

theorem bind {x : CostM α} {f : α → CostM β} {P : α → Prop} {R : β → Prop}
    (hx : Sat x env P)
    (hf : ∀ a, P a → Sat (f a) env R) : Sat (x >>= f) env R := by
  intro c v c' hr
  obtain ⟨a, c1, h1, h2⟩ := Runs.bind_some hr
  exact hf a (hx c a c1 h1) c1 v c' h2

theorem mono {x : CostM α} {P R : α → Prop} (hx : Sat x env P) (h : ∀ a, P a → R a) :
    Sat x env R :=
  fun c v c' hr => h v (hx c v c' hr)

end Sat

/-- A run of a map of counted steps that succeeds returns, at each position, a value some run
    of that step returns. -/
theorem sat_mapM_loop {α β : Type} {env : Env} {f : α → Interp.counting.M β}
    {P : α → β → Prop} :
    ∀ (l : List α) (bs : List β), (∀ a ∈ l, Sat (f a) env (P a)) →
      Sat (@List.mapM.loop Interp.counting.M (instMonadInterp Interp.counting) α β f l bs) env
        (fun out => ∃ ys, out = bs.reverse ++ ys ∧ List.Forall₂ (fun a b => P a b) l ys)
  | [], bs, _ => Sat.pure ⟨[], by simp, List.Forall₂.nil⟩
  | a :: l, bs, h => by
    simp only [List.mapM.loop, Interp.counting_bind]
    refine Sat.bind (h a List.mem_cons_self) fun b hb => ?_
    refine (sat_mapM_loop l (b :: bs) fun a' ha' => h a' (List.mem_cons_of_mem _ ha')).mono ?_
    rintro out ⟨ys, rfl, hys⟩
    exact ⟨b :: ys, by simp, List.Forall₂.cons hb hys⟩

theorem sat_mapM {α β : Type} {env : Env} {f : α → Interp.counting.M β}
    {P : α → β → Prop}
    (l : List α) (h : ∀ a ∈ l, Sat (f a) env (P a)) :
    Sat (@List.mapM Interp.counting.M (instMonadInterp Interp.counting) α β f l) env
      (fun out => List.Forall₂ (fun a b => P a b) l out) := by
  refine (sat_mapM_loop l [] h).mono ?_
  rintro out ⟨ys, rfl, hys⟩
  simpa using hys

/-! ## Matrices -/

/-- The rows `[f i 0, ..., f i (k - 1)]` for `i < m`. -/
def mat (m k : ℕ) (f : ℕ → ℕ → ℚ) : List (List Q) :=
  (List.range m).map fun i => (List.range k).map fun a => (⟨f i a⟩ : Q)

/-- The vector `[f 0, ..., f (k - 1)]`. -/
def vec (k : ℕ) (f : ℕ → ℚ) : List Q := (List.range k).map fun a => (⟨f a⟩ : Q)

theorem mat_eq (m k : ℕ) (f : ℕ → ℕ → ℚ) :
    mat m k f = (List.range m).map fun i => vec k (f i) :=
  rfl

theorem Q_ext {a b : Q} (h : a.val = b.val) : a = b := by
  cases a; cases b; simp only at h; rw [h]

theorem zip_map_map {γ δ ε : Type} (l : List γ) (f : γ → δ) (g : γ → ε) :
    List.zip (l.map f) (l.map g) = l.map fun a => (f a, g a) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem getD_vec {k : ℕ} {f : ℕ → ℚ} {a : ℕ} (ha : a < k) (z : Q) :
    (vec k f).getD a z = ⟨f a⟩ := by
  simp [vec, List.getD_eq_getElem?_getD, ha]

theorem getD_mat {m k : ℕ} {f : ℕ → ℕ → ℚ} {i : ℕ} (hi : i < m) (z : List Q) :
    (mat m k f).getD i z = vec k (f i) := by
  simp [mat, vec, List.getD_eq_getElem?_getD, hi]

theorem length_vec (k : ℕ) (f : ℕ → ℚ) : (vec k f).length = k := by simp [vec]

theorem length_mat (m k : ℕ) (f : ℕ → ℕ → ℚ) : (mat m k f).length = m := by simp [mat]

theorem sum_map_const' {γ : Type} (l : List γ) (c : ℕ) :
    (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Nat.succ_mul, Nat.add_comm]

/-! ## The helpers, as runs -/

section Helpers

variable {env : Env}

/-- The value of `dot`: `Σ_i x_i y_i`, folded. -/
def dotV (xs ys : List Q) : Q :=
  (List.zip xs ys).foldl (fun s p => ⟨s.val + p.1.val * p.2.val⟩) ⟨0⟩

theorem runs_dot (xs ys : List Q) :
    Runs (dot Interp.counting xs ys) env (dotV xs ys) (List.zip xs ys).length := by
  unfold dot dotV
  exact (runs_foldlM (c := fun _ => 1) _ _ fun b a _ => runs_muladd cat b a.1 a.2).congr
    (by simp) (by simp)

theorem foldl_acc {γ : Type} (F : γ → ℚ) : ∀ (l : List γ) (a : ℚ),
    (l.foldl (fun s p => (⟨s.val + F p⟩ : Q)) ⟨a⟩).val = a + (l.map F).sum
  | [], a => by simp
  | p :: l, a => by
    rw [List.foldl_cons, foldl_acc F l, List.map_cons, List.sum_cons]
    ring

theorem dotV_vec (k : ℕ) (f g : ℕ → ℚ) :
    dotV (vec k f) (vec k g) = ⟨∑ a ∈ range k, f a * g a⟩ := by
  apply Q_ext
  rw [dotV, vec, vec, zip_map_map, foldl_acc, List.map_map, zero_add, sum_range_eq]
  rfl

theorem runs_dot_vec (k : ℕ) (f g : ℕ → ℚ) :
    Runs (dot Interp.counting (vec k f) (vec k g)) env ⟨∑ a ∈ range k, f a * g a⟩ k :=
  (runs_dot _ _).congr (dotV_vec k f g) (by simp [vec, zip_map_map])

/-- **Products.** The rows of `fA` times the rows of `fB`, both of length `k`: `m p k`
    multiply-adds. -/
theorem runs_mm (m p k : ℕ) (fA fB : ℕ → ℕ → ℚ) :
    Runs (mm Interp.counting (mat m k fA) (mat p k fB)) env
      (mat m p fun i j => ∑ a ∈ range k, fA i a * fB j a) (m * p * k) := by
  unfold mm
  refine (runs_mapM (g := fun r => (mat p k fB).map (dotV r)) (c := fun _ => p * k) _
    fun r hr => ?_).congr ?_ ?_
  · refine (runs_mapM (g := dotV r) (c := fun _ => k) _ fun c hc => ?_).congr rfl
      (by simp [mat, Function.comp_def])
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hc
    exact (runs_dot _ _).congr rfl (by simp [zip_map_map])
  · simp only [mat, List.map_map]
    refine List.map_congr_left fun i _ => List.map_congr_left fun j _ => ?_
    exact dotV_vec k (fA i) (fB j)
  · simp [mat, Function.comp_def]
    ring

theorem runs_vadd (k : ℕ) (f g : ℕ → ℚ) :
    Runs (vadd Interp.counting (vec k f) (vec k g)) env (vec k fun a => f a + g a) k := by
  unfold vadd
  refine (runs_mapM (g := fun pr => (⟨pr.1.val + pr.2.val⟩ : Q)) (c := fun _ => 1) _
    fun pr _ => runs_add cat _ _).congr ?_
      (by simp [vec, zip_map_map, Function.comp_def])
  simp [vec, zip_map_map]

/-- A row of a weight. -/
theorem runs_row {nm : String} {t : Tensor ℚ} (ht : List.lookup nm env.weights = some t)
    {m cols : ℕ} (hsz : t.data.size = m * cols) {i : ℕ} (hi : i < m) :
    Runs (row Interp.counting nm cols i) env (vec cols fun j => t.get (i * cols + j)) 0 := by
  unfold row
  refine (runs_mapM (c := fun _ => 0) _ fun j hj => ?_).congr rfl (by simp)
  exact runs_weight ht (by rw [hsz]; exact lt_mul_of_row hi (List.mem_range.mp hj))

/-- A column of a weight. -/
theorem runs_col {nm : String} {t : Tensor ℚ} (ht : List.lookup nm env.weights = some t)
    {rows cols : ℕ} (hsz : t.data.size = rows * cols) {j : ℕ} (hj : j < cols) :
    Runs (col Interp.counting nm rows cols j) env (vec rows fun i => t.get (i * cols + j)) 0 := by
  unfold col
  refine (runs_mapM (c := fun _ => 0) _ fun i hi => ?_).congr rfl (by simp)
  exact runs_weight ht (by rw [hsz]; exact lt_mul_of_row (List.mem_range.mp hi) hj)

/-- All rows of a weight, as a matrix. -/
theorem runs_rows {nm : String} {t : Tensor ℚ} (ht : List.lookup nm env.weights = some t)
    {m cols : ℕ} (hsz : t.data.size = m * cols) :
    Runs ((List.range m).mapM (row Interp.counting nm cols)) env
      (mat m cols fun i j => t.get (i * cols + j)) 0 :=
  (runs_mapM (c := fun _ => 0) _ fun i hi => runs_row ht hsz (List.mem_range.mp hi)).congr rfl
    (by simp)

/-- All columns of a weight, as a matrix of their entries. -/
theorem runs_cols {nm : String} {t : Tensor ℚ} (ht : List.lookup nm env.weights = some t)
    {rows cols : ℕ} (hsz : t.data.size = rows * cols) :
    Runs ((List.range cols).mapM (col Interp.counting nm rows cols)) env
      (mat cols rows fun j i => t.get (i * cols + j)) 0 :=
  (runs_mapM (c := fun _ => 0) _ fun j hj => runs_col ht hsz (List.mem_range.mp hj)).congr rfl
    (by simp)

/-! ### Running maxima and minima -/

/-- The running values of `F` after the first entry `a`. -/
def scanAux (F : ℚ → ℚ → ℚ) : Q → List Q → List Q
  | _, [] => []
  | a, v :: vs => (⟨F a.val v.val⟩ : Q) :: scanAux F ⟨F a.val v.val⟩ vs

/-- The value of `scan`: `out[i] = F (... F (r_0, r_1) ..., r_i)`. -/
def scanVal (F : ℚ → ℚ → ℚ) : List Q → List Q
  | [] => []
  | a :: rs => a :: scanAux F a rs

theorem foldl_scan (F : ℚ → ℚ → ℚ) : ∀ (rs : List Q) (acc : Q) (out : List Q),
    (rs.foldl (fun (p : Q × List Q) v =>
        ((⟨F p.1.val v.val⟩ : Q), p.2 ++ [⟨F p.1.val v.val⟩]))
      (acc, out)).2 = out ++ scanAux F acc rs
  | [], _, out => by simp [scanAux]
  | v :: vs, acc, out => by
    rw [List.foldl_cons, foldl_scan F vs, scanAux, List.append_assoc]
    rfl

theorem runs_scan {f : Q → Q → Interp.counting.M Q} {F : ℚ → ℚ → ℚ}
    (hf : ∀ a b, Runs (f a b) env ⟨F a.val b.val⟩ 1) (r : List Q) :
    Runs (scan Interp.counting f r) env (scanVal F r) (r.length - 1) := by
  cases r with
  | nil => exact (Runs.pure _).congr rfl rfl
  | cons a rs =>
    unfold scan
    simp only [Interp.counting_bind, Interp.counting_pure]
    refine Runs.bind' (runs_foldlM (c := fun _ => 1) (g := fun (p : Q × List Q) v =>
      ((⟨F p.1.val v.val⟩ : Q), p.2 ++ [⟨F p.1.val v.val⟩])) rs (a, [a]) fun p v _ => ?_)
      (Runs.pure _) ?_ (by simp)
    · exact Runs.bind' (hf p.1 v) (Runs.pure _) rfl rfl
    · rw [foldl_scan, scanVal]
      rfl

theorem length_scanAux (F : ℚ → ℚ → ℚ) :
    ∀ (a : Q) (rs : List Q), (scanAux F a rs).length = rs.length
  | _, [] => rfl
  | _, _ :: vs => by simp [scanAux, length_scanAux F _ vs]

theorem length_scanVal (F : ℚ → ℚ → ℚ) (r : List Q) :
    (scanVal F r).length = r.length := by
  cases r <;> simp [scanVal, length_scanAux]

/-- A running maximum is at least every entry up to it. -/
theorem le_scanAux_max : ∀ (a : Q) (rs : List Q) (i : ℕ), i < rs.length →
    a.val ≤ ((scanAux max a rs).getD i ⟨0⟩).val ∧
      ∀ j ≤ i, (rs.getD j ⟨0⟩).val ≤ ((scanAux max a rs).getD i ⟨0⟩).val
  | _, [], _, h => absurd h (by simp)
  | a, v :: vs, 0, _ => by
    simp only [scanAux, List.getD_cons_zero]
    refine ⟨le_max_left _ _, fun j hj => ?_⟩
    rw [Nat.le_zero.mp hj, List.getD_cons_zero]
    exact le_max_right _ _
  | a, v :: vs, i + 1, h => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at h
    obtain ⟨h1, h2⟩ := le_scanAux_max ⟨max a.val v.val⟩ vs i h
    simp only [scanAux, List.getD_cons_succ]
    refine ⟨le_trans (le_max_left _ _) h1, fun j hj => ?_⟩
    rcases j with _ | j
    · simp only [List.getD_cons_zero]
      exact le_trans (le_max_right _ _) h1
    · simp only [List.getD_cons_succ]
      exact h2 j (by omega)

theorem le_scanVal_max (r : List Q) {i : ℕ} (hi : i < r.length) {j : ℕ} (hj : j ≤ i) :
    (r.getD j ⟨0⟩).val ≤ ((scanVal max r).getD i ⟨0⟩).val := by
  cases r with
  | nil => simp at hi
  | cons a rs =>
    rcases i with _ | i
    · rw [Nat.le_zero.mp hj]
      simp [scanVal]
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      obtain ⟨h1, h2⟩ := le_scanAux_max a rs i hi
      simp only [scanVal, List.getD_cons_succ]
      rcases j with _ | j
      · simpa using h1
      · simpa using h2 j (by omega)

/-- A running minimum is at most every entry up to it. -/
theorem scanAux_min_le : ∀ (a : Q) (rs : List Q) (i : ℕ), i < rs.length →
    ((scanAux min a rs).getD i ⟨0⟩).val ≤ a.val ∧
      ∀ j ≤ i, ((scanAux min a rs).getD i ⟨0⟩).val ≤ (rs.getD j ⟨0⟩).val
  | _, [], _, h => absurd h (by simp)
  | a, v :: vs, 0, _ => by
    simp only [scanAux, List.getD_cons_zero]
    refine ⟨min_le_left _ _, fun j hj => ?_⟩
    rw [Nat.le_zero.mp hj, List.getD_cons_zero]
    exact min_le_right _ _
  | a, v :: vs, i + 1, h => by
    simp only [List.length_cons, Nat.add_lt_add_iff_right] at h
    obtain ⟨h1, h2⟩ := scanAux_min_le ⟨min a.val v.val⟩ vs i h
    simp only [scanAux, List.getD_cons_succ]
    refine ⟨le_trans h1 (min_le_left _ _), fun j hj => ?_⟩
    rcases j with _ | j
    · simp only [List.getD_cons_zero]
      exact le_trans h1 (min_le_right _ _)
    · simp only [List.getD_cons_succ]
      exact h2 j (by omega)

theorem scanVal_min_le (r : List Q) {i : ℕ} (hi : i < r.length) {j : ℕ} (hj : j ≤ i) :
    ((scanVal min r).getD i ⟨0⟩).val ≤ (r.getD j ⟨0⟩).val := by
  cases r with
  | nil => simp at hi
  | cons a rs =>
    rcases i with _ | i
    · rw [Nat.le_zero.mp hj]
      simp [scanVal]
    · simp only [List.length_cons, Nat.add_lt_add_iff_right] at hi
      obtain ⟨h1, h2⟩ := scanAux_min_le a rs i hi
      simp only [scanVal, List.getD_cons_succ]
      rcases j with _ | j
      · simpa using h1
      · simpa using h2 j (by omega)

/-! ### Margins against every other entry -/

/-- The largest entry other than `l`, as `marg` takes it from the running maxima. -/
def margMax (r : List Q) (l : ℕ) : ℚ :=
  if l = 0 then ((scanVal max r.reverse).getD (r.length - 2) ⟨0⟩).val
  else if l + 1 = r.length then ((scanVal max r).getD (l - 1) ⟨0⟩).val
  else max ((scanVal max r).getD (l - 1) ⟨0⟩).val
    ((scanVal max r.reverse).getD (r.length - 2 - l) ⟨0⟩).val

/-- The value of `marg`. -/
def margVal (r : List Q) : List Q :=
  (List.range r.length).map fun l => ⟨(r.getD l ⟨0⟩).val - margMax r l⟩

/-- The operations of `marg` on `L` entries: the running maxima from either end, `L - 2` maxima
    of the two, and `L` differences. -/
def margCost (L : ℕ) : ℕ := (L - 1) + (L - 1) + (L - 2) + L

theorem sum_inner (L : ℕ) :
    ((List.range L).map fun l => (if l = 0 then 0 else if l + 1 = L then 0 else 1) + 1).sum =
      (L - 2) + L := by
  rw [sum_range_eq]
  rcases L with _ | _ | M
  · simp
  · simp
  · rw [Finset.sum_range_succ, Finset.sum_range_succ']
    have : ∀ i ∈ range M,
        ((if i + 1 = 0 then 0 else if i + 1 + 1 = M + 1 + 1 then 0 else 1) + 1) = 2 := by
      intro i hi
      have := Finset.mem_range.mp hi
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
    rw [Finset.sum_congr rfl this]
    simp
    omega

theorem runs_marg (r : List Q) :
    Runs (marg Interp.counting r) env (margVal r) (margCost r.length) := by
  unfold marg
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_scan (F := max) (fun a b => runs_max cat a b) r)
    (Runs.bind' (runs_scan (F := max) (fun a b => runs_max cat a b) r.reverse)
      (m := (r.length - 2) + r.length) ?_ rfl rfl) rfl ?_
  · refine (runs_mapM (g := fun l => (⟨(r.getD l ⟨0⟩).val - margMax r l⟩ : Q))
      (c := fun l => (if l = 0 then 0 else if l + 1 = r.length then 0 else 1) + 1) _
      fun l _ => ?_).congr rfl (by rw [sum_inner])
    by_cases h0 : l = 0
    · simp only [h0, ↓reduceIte, Interp.counting_pure]
      refine Runs.bind' (Runs.pure _) (runs_sub cat _ _) ?_ (by simp)
      simp [margMax]
    · by_cases h1 : l + 1 = r.length
      · simp only [h0, h1, ↓reduceIte, Interp.counting_pure]
        refine Runs.bind' (Runs.pure _) (runs_sub cat _ _) ?_ (by simp)
        simp [margMax, h0, h1]
      · simp only [h0, h1, ↓reduceIte]
        refine Runs.bind' (runs_max cat _ _) (runs_sub cat _ _) ?_ (by simp)
        simp [margMax, h0, h1]
  · simp [margCost, List.length_reverse]
    omega

theorem getD_reverse_Q {r : List Q} {k : ℕ} (hk : k < r.length) :
    r.reverse.getD k ⟨0⟩ = r.getD (r.length - 1 - k) ⟨0⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_reverse hk]

/-- **What a margin bounds.** Entry `l` of `marg r` is at most `r[l] - r[j]` for every other
    entry `j`. -/
theorem margVal_le (r : List Q) {l j : ℕ} (hl : l < r.length) (hj : j < r.length)
    (hne : j ≠ l) :
    ((margVal r).getD l ⟨0⟩).val ≤ (r.getD l ⟨0⟩).val - (r.getD j ⟨0⟩).val := by
  have hget : (margVal r).getD l ⟨0⟩ = ⟨(r.getD l ⟨0⟩).val - margMax r l⟩ := by
    simp [margVal, List.getD_eq_getElem?_getD, hl]
  rw [hget]
  simp only
  suffices (r.getD j ⟨0⟩).val ≤ margMax r l by linarith
  have hrev : ∀ k, k < r.length → l < r.length - 1 - k →
      (r.getD (r.length - 1 - k) ⟨0⟩).val ≤
        ((scanVal max r.reverse).getD (r.length - 2 - l) ⟨0⟩).val := by
    intro k hk hlk
    rw [← getD_reverse_Q hk]
    exact le_scanVal_max r.reverse (by simp; omega) (by omega)
  unfold margMax
  by_cases h0 : l = 0
  · subst h0
    simp only [↓reduceIte]
    have := hrev (r.length - 1 - j) (by omega) (by omega)
    rwa [show r.length - 1 - (r.length - 1 - j) = j by omega, Nat.sub_zero] at this
  · by_cases h1 : l + 1 = r.length
    · simp only [h0, h1, ↓reduceIte]
      exact le_scanVal_max r (by omega) (by omega)
    · simp only [h0, h1, ↓reduceIte]
      rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
      · exact le_trans (le_scanVal_max r (by omega) (by omega)) (le_max_left _ _)
      · have := hrev (r.length - 1 - j) (by omega) (by omega)
        rw [show r.length - 1 - (r.length - 1 - j) = j by omega] at this
        exact le_trans this (le_max_right _ _)

theorem length_margVal (r : List Q) : (margVal r).length = r.length := by simp [margVal]

/-! ### One term of a class's sum -/

theorem runs_kterm (b : Q × Q) (dd gg : Q) :
    Runs (kterm Interp.counting b dd gg) env
      ⟨min (b.1.val * (dd.val + gg.val)) (b.2.val * (dd.val + gg.val))⟩ 4 := by
  unfold kterm
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_add cat _ _) (Runs.bind' (runs_muladd cat _ _ _)
    (Runs.bind' (runs_muladd cat _ _ _) (runs_min cat _ _) rfl rfl) rfl rfl) ?_ rfl
  simp

end Helpers

/-! ## The tables -/

namespace Net

variable (N : Net)

/-- `E W_K`, entry `(t, k)`. -/
def ek (t k : ℕ) : ℚ := ∑ a ∈ range N.d, N.E.get (t * N.d + a) * N.WK.get (a * N.h + k)

/-- `P W_K`, entry `(p, k)`. -/
def pk (p k : ℕ) : ℚ := ∑ a ∈ range N.d, N.P.get (p * N.d + a) * N.WK.get (a * N.h + k)

/-- `W_V W_O`, entry `(a, b)`. -/
def vo (a b : ℕ) : ℚ := ∑ k ∈ range N.h, N.WV.get (a * N.h + k) * N.WO.get (k * N.d + b)

/-- `W_V W_O U`, entry `(a, j)`. -/
def vou (a j : ℕ) : ℚ := ∑ b ∈ range N.d, N.vo a b * N.U.get (b * N.V + j)

/-- The query, as the checker computes it: the scale applied to `W_Q` first. -/
def qc (q k : ℕ) : ℚ :=
  ∑ a ∈ range N.d, N.r q (N.n - 1) a * (0 + N.WQ.get (a * N.h + k) * N.C.get 0)

theorem qc_eq (q k : ℕ) : N.qc q k = N.qv q k := by
  unfold qc qv
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem score_eq (q t p : ℕ) :
    (∑ k ∈ range N.h, N.qc q k * N.ek t k) + (∑ k ∈ range N.h, N.qc q k * N.pk p k) =
      N.S q t p := by
  unfold S key ek pk r
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [qc_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem direct_eq (q j : ℕ) :
    (∑ a ∈ range N.d, N.E.get (q * N.d + a) * N.U.get (a * N.V + j)) +
      (∑ a ∈ range N.d, N.P.get ((N.n - 1) * N.d + a) * N.U.get (a * N.V + j)) = N.D q j := by
  unfold D r
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

theorem path_eq (t p j : ℕ) :
    (∑ a ∈ range N.d, N.E.get (t * N.d + a) * N.vou a j) +
      (∑ a ∈ range N.d, N.P.get (p * N.d + a) * N.vou a j) = N.O t p j := by
  set F : ℕ → ℕ → ℕ → ℚ := fun a b k => N.r t p a * N.WV.get (a * N.h + k) *
    N.WO.get (k * N.d + b) * N.U.get (b * N.V + j) with hF
  have lhs : (∑ a ∈ range N.d, N.E.get (t * N.d + a) * N.vou a j) +
      (∑ a ∈ range N.d, N.P.get (p * N.d + a) * N.vou a j) =
      ∑ a ∈ range N.d, ∑ b ∈ range N.d, ∑ k ∈ range N.h, F a b k := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← add_mul, vou, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [vo, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hF, Net.r]
    ring
  have rhs :
      N.O t p j = ∑ k ∈ range N.h, ∑ a ∈ range N.d, ∑ b ∈ range N.d, F a b k := by
    unfold O val
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hF]
    ring
  rw [lhs, rhs, Finset.sum_congr rfl fun a _ => Finset.sum_comm]
  exact Finset.sum_comm

end Net

/-! ### The tables as runs -/

section Tables

variable {env : Env} {N : Net}

theorem runs_Qc (hw : N.WF env.weights) :
    Runs ((List.range N.h).mapM fun k => do
        let w ← col Interp.counting nQ N.d N.h k
        w.mapM fun v => Interp.counting.muladd cat Interp.counting.zero v ⟨N.C.get 0⟩) env
      (mat N.h N.d fun k a => 0 + N.WQ.get (a * N.h + k) * N.C.get 0) (N.h * N.d) := by
  refine (runs_mapM (g := fun k => vec N.d fun a => 0 + N.WQ.get (a * N.h + k) * N.C.get 0)
    (c := fun _ => N.d) _ fun k hk => ?_).congr rfl (by simp)
  refine Runs.bind0 (runs_col hw.hQ hw.hQn (List.mem_range.mp hk)) ?_
  refine (runs_mapM (g := fun v => (⟨0 + v.val * N.C.get 0⟩ : Q)) (c := fun _ => 1) _
    fun v _ => runs_muladd cat _ _ _).congr ?_ (by simp [vec, Function.comp_def])
  simp [vec]

theorem runs_rq (N : Net) :
    Runs ((mat N.V N.d fun t a => N.E.get (t * N.d + a)).mapM
        (vadd Interp.counting · (vec N.d fun a => N.P.get ((N.n - 1) * N.d + a)))) env
      (mat N.V N.d fun t a => N.r t (N.n - 1) a) (N.V * N.d) := by
  refine (runs_mapM (g := fun r => (List.zip r (vec N.d fun a => N.P.get ((N.n - 1) * N.d + a))).map
      fun p => (⟨p.1.val + p.2.val⟩ : Q)) (c := fun _ => N.d) _ fun r hr => ?_).congr ?_
    (by simp [mat, Function.comp_def])
  · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hr
    exact (runs_vadd N.d _ _).congr (by simp [vec, zip_map_map]) rfl
  · simp [mat, vec, zip_map_map, Net.r]

/-- The transpose of `mat d V f`, as the checker takes it. -/
theorem transpose_mat (d V : ℕ) (f : ℕ → ℕ → ℚ) :
    ((List.range V).map fun j => (mat d V f).map (·.getD j (⟨0⟩ : Q))) =
      mat V d fun j a => f a j := by
  simp only [mat, List.map_map]
  refine List.map_congr_left fun j hj => List.map_congr_left fun a _ => ?_
  simp [List.getD_eq_getElem?_getD, List.mem_range.mp hj]

theorem runs_Dd (N : Net) :
    Runs ((mat N.V N.V fun t j =>
        ∑ a ∈ range N.d, N.E.get (t * N.d + a) * N.U.get (a * N.V + j)).mapM
        fun r => do
          let s ← vadd Interp.counting r
            ((mat 1 N.V fun _ j => ∑ a ∈ range N.d,
              N.P.get ((N.n - 1) * N.d + a) * N.U.get (a * N.V + j)).getD 0 [])
          marg Interp.counting s) env
      ((List.range N.V).map fun t => margVal (vec N.V (N.D t))) (N.V * (N.V + margCost N.V)) := by
  refine (runs_mapM (g := fun r => margVal ((List.zip r (vec N.V fun j => ∑ a ∈ range N.d,
      N.P.get ((N.n - 1) * N.d + a) * N.U.get (a * N.V + j))).map
        fun p => (⟨p.1.val + p.2.val⟩ : Q)))
      (c := fun _ => N.V + margCost N.V) _ fun r hr => ?_).congr ?_
    (by simp [mat, Function.comp_def])
  · obtain ⟨t, -, rfl⟩ := List.mem_map.mp hr
    rw [getD_mat (by omega)]
    exact Runs.bind' (runs_vadd N.V _ _) (runs_marg _)
      (by simp [vec, zip_map_map, Function.comp_def])
      (by simp [length_vec])
  · simp only [mat, List.map_map, vec, zip_map_map, Function.comp_def]
    refine List.map_congr_left fun t _ => ?_
    congr 1
    refine List.map_congr_left fun j _ => ?_
    rw [← N.direct_eq]

theorem runs_G (N : Net) :
    Runs ((mat N.V N.V fun t j => ∑ a ∈ range N.d, N.E.get (t * N.d + a) * N.vou a j).mapM
        fun r => (mat N.n N.V fun p j =>
          ∑ a ∈ range N.d, N.P.get (p * N.d + a) * N.vou a j).mapM
          fun s => do marg Interp.counting (← vadd Interp.counting r s)) env
      ((List.range N.V).map fun t => (List.range N.n).map fun p => margVal (vec N.V (N.O t p)))
      (N.V * (N.n * (N.V + margCost N.V))) := by
  refine (runs_mapM (g := fun r =>
      (mat N.n N.V fun p j => ∑ a ∈ range N.d, N.P.get (p * N.d + a) * N.vou a j).map
        fun s => margVal ((List.zip r s).map fun p => (⟨p.1.val + p.2.val⟩ : Q)))
      (c := fun _ => N.n * (N.V + margCost N.V)) _ fun r hr => ?_).congr ?_
    (by simp [mat, Function.comp_def])
  · refine (runs_mapM (c := fun _ => N.V + margCost N.V) _ fun s hs => ?_).congr rfl
      (by simp [mat, Function.comp_def])
    obtain ⟨t, -, rfl⟩ := List.mem_map.mp hr
    obtain ⟨p, -, rfl⟩ := List.mem_map.mp hs
    exact Runs.bind' (runs_vadd N.V _ _) (runs_marg _)
      (by simp [vec, zip_map_map, Function.comp_def])
      (by simp [length_vec])
  · simp only [mat, List.map_map, vec, zip_map_map, Function.comp_def]
    refine List.map_congr_left fun t _ => List.map_congr_left fun p _ => ?_
    congr 1
    refine List.map_congr_left fun j _ => ?_
    rw [← N.path_eq]

end Tables

/-! ### Bounds on `exp` of the scores -/

/-- The bounds on `exp s`, as a pair of numbers (zero if `exp` refuses `s`). -/
def expPair (s : ℚ) : Q × Q :=
  match expInterval s with
  | some (lo, hi) => (⟨lo⟩, ⟨hi⟩)
  | none => (⟨0⟩, ⟨0⟩)

/-- The table of bounds, for the scores `f q t p`. -/
def expTab (V n : ℕ) (f : ℕ → ℕ → ℕ → ℚ) : List (List (List (Q × Q))) :=
  (List.range V).map fun q => (List.range V).map fun t =>
    (List.range n).map fun p => expPair (f q t p)

theorem getD_of_lt {γ : Type} {l : List γ} {i : ℕ} (h : i < l.length) (z : γ) :
    l.getD i z = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem forall₂_get {γ δ : Type} {R : γ → δ → Prop} :
    ∀ {l : List γ} {out : List δ}, List.Forall₂ R l out →
      out.length = l.length ∧ ∀ i (h : i < l.length) (h' : i < out.length), R l[i] out[i]
  | [], [], _ => ⟨rfl, fun i h => absurd h (by simp)⟩
  | a :: l, b :: out, List.Forall₂.cons hab hrest => by
    obtain ⟨hlen, hget⟩ := forall₂_get hrest
    refine ⟨by simp [hlen], fun i h h' => ?_⟩
    rcases i with _ | i
    · exact hab
    · exact hget i (by simpa using h) (by simpa using h')

section Exp

variable {env : Env}

theorem runs_expStep {s s' : Q} (h : (expInterval (s.val + s'.val)).isSome) :
    Runs (do Interp.counting.exp cat (← Interp.counting.add cat s s')) env
      (expPair (s.val + s'.val)) 4 := by
  refine Runs.bind' (runs_add cat s s') (m := 3) ?_ rfl rfl
  obtain ⟨⟨lo, hi⟩, hlh⟩ := Option.isSome_iff_exists.mp h
  intro c
  refine ⟨c.add cat 3, ?_, CompactCheck.Cost.total_add _ _ _⟩
  simp [CostM.qexp, hlh, expPair]

theorem sat_expStep (s s' : Q) :
    Sat (do Interp.counting.exp cat (← Interp.counting.add cat s s')) env
      (fun b => expInterval (s.val + s'.val) = some (b.1.val, b.2.val)) := by
  refine Sat.bind (Sat.of_runs (runs_add cat s s')) fun a ha => ?_
  subst ha
  intro c b c' hr
  simp only [CostM.qexp] at hr
  split at hr
  · rename_i lo hi hlh
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    rw [← hr.1]
    exact hlh
  · cases hr

theorem runs_X (V n : ℕ) (fSE fSP : ℕ → ℕ → ℚ)
    (h : ∀ q < V, ∀ t < V, ∀ p < n, (expInterval (fSE q t + fSP q p)).isSome) :
    Runs ((List.zip (mat V V fSE) (mat V n fSP)).mapM fun pr => pr.1.mapM fun s =>
        pr.2.mapM fun s' => do Interp.counting.exp cat (← Interp.counting.add cat s s')) env
      (expTab V n fun q t p => fSE q t + fSP q p) (V * (V * (n * 4))) := by
  rw [mat, mat, zip_map_map]
  refine (runs_mapM (g := fun pr => pr.1.map fun s => pr.2.map fun s' => expPair (s.val + s'.val))
    (c := fun _ => V * (n * 4)) _ fun pr hpr => ?_).congr ?_
    (by simp [Function.comp_def])
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hpr
    refine (runs_mapM (g := fun s => ((List.range n).map fun a => (⟨fSP q a⟩ : Q)).map
      fun s' => expPair (s.val + s'.val)) (c := fun _ => n * 4) _ fun s hs => ?_).congr rfl
      (by simp [Function.comp_def])
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
    refine (runs_mapM (g := fun s' => expPair ((⟨fSE q t⟩ : Q).val + s'.val))
      (c := fun _ => 4) _
      fun s' hs' => ?_).congr rfl (by simp [Function.comp_def])
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hs'
    exact runs_expStep
      (h q (List.mem_range.mp hq) t (List.mem_range.mp ht) p (List.mem_range.mp hp))
  · simp [expTab, Function.comp_def]

/-- What a run of the table that succeeds returns: at `(q, t, p)`, the bounds `exp` gives on
    `fSE q t + fSP q p`. -/
theorem sat_X (V n : ℕ) (fSE fSP : ℕ → ℕ → ℚ) :
    Sat ((List.zip (mat V V fSE) (mat V n fSP)).mapM fun pr => pr.1.mapM fun s =>
        pr.2.mapM fun s' => do Interp.counting.exp cat (← Interp.counting.add cat s s')) env
      (fun X => ∀ q < V, ∀ t < V, ∀ p < n,
        expInterval (fSE q t + fSP q p) =
          some ((((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).1.val,
            (((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).2.val)) := by
  rw [mat, mat, zip_map_map]
  refine (sat_mapM _ fun pr _ => sat_mapM _ fun s _ => sat_mapM _ fun s' _ =>
    sat_expStep s s').mono ?_
  intro X hX q hq t ht p hp
  obtain ⟨hl1, hg1⟩ := forall₂_get hX
  have hq1 : q < X.length := by rw [hl1]; simpa using hq
  have h1 := hg1 q (by simpa using hq) hq1
  simp only [List.getElem_map, List.getElem_range] at h1
  obtain ⟨hl2, hg2⟩ := forall₂_get h1
  have ht2 : t < X[q].length := by rw [hl2]; simpa using ht
  have h2 := hg2 t (by simpa using ht) ht2
  simp only [List.getElem_map, List.getElem_range] at h2
  obtain ⟨hl3, hg3⟩ := forall₂_get h2
  have hp3 : p < X[q][t].length := by rw [hl3]; simpa using hp
  have h3 := hg3 p (by simpa using hp) hp3
  simp only [List.getElem_map, List.getElem_range] at h3
  rw [getD_of_lt hq1, getD_of_lt ht2, getD_of_lt hp3]
  exact h3

end Exp

/-! ### The classes of one query rank and label rank -/

/-- The value of `kterm` on the tables: the lower bound on `exp(S) (Dd + G)` for the query token
    `q`, the token `t` at position `p` and the label `l`. -/
def kV (X : List (List (List (Q × Q)))) (Dd : List (List Q)) (G : List (List (List Q)))
    (q t p l : ℕ) : Q :=
  let b := ((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)
  let dd := (Dd.getD q []).getD l ⟨0⟩
  let gg := ((G.getD t []).getD p []).getD l ⟨0⟩
  ⟨min (b.1.val * (dd.val + gg.val)) (b.2.val * (dd.val + gg.val))⟩

/-- The operations of one pattern of a block. -/
def patCost (n ρq lam pat : ℕ) : ℕ :=
  if ρq ≠ lam ∧ (List.range (n - 1)).filter pat.testBit = [] then 0 else
    ((List.range (n - 1)).filter pat.testBit).length +
      (if (List.range (n - 1)).filter (fun p => !pat.testBit p) = [] then 1
        else lam * (((List.range (n - 1)).filter fun p => !pat.testBit p).length + 1))

/-- The operations of `block`: the query's term, the label's terms, the rows of the other
    positions and their running minima (when some class needs them), and the patterns. -/
def blockCost (n ρq lam : ℕ) : ℕ :=
  4 + (n - 1) * 4 + (if ρq = lam ∨ 3 ≤ n then (n - 1) * (lam * 4 + (lam - 1)) else 0) +
    ((List.range (2 ^ (n - 1))).map (patCost n ρq lam)).sum

section Block

variable {env : Env}

theorem runs_addFold (f : ℕ → Q) (P : List ℕ) (b : Q) :
    Runs (P.foldlM (fun s p => Interp.counting.add cat s (f p)) b) env
      (P.foldl (fun s p => (⟨s.val + (f p).val⟩ : Q)) b) P.length := by
  exact (runs_foldlM (c := fun _ => 1) P b fun s p _ => runs_add cat s (f p)).congr rfl
    (by simp)

theorem runs_minRows (mx : Bool) (V n lam : ℕ) {K : ℕ → ℕ → Interp.counting.M Q}
    {kv : ℕ → ℕ → Q} (hK : ∀ t p, Runs (K t p) env (kv t p) 4) :
    Runs (minRows Interp.counting mx V n lam K) env
      ((List.range (n - 1)).map fun p =>
        scanVal min ((List.range lam).map fun ρ => kv (tok mx V ρ) p))
      ((n - 1) * (lam * 4 + (lam - 1))) := by
  unfold minRows
  refine (runs_mapM (c := fun _ => lam * 4 + (lam - 1)) _ fun p _ => ?_).congr rfl
    (by simp)
  exact Runs.bind' (runs_mapM (c := fun _ => 4) _ fun ρ _ => hK _ p)
    (runs_scan (F := min) (fun a b => runs_min cat a b) _) rfl
    (by simp)

/-- The value of `patterns`. -/
def patternsV (n ρq lam : ℕ) (kq : Q) (kl : List Q) (kp : List (List Q)) : List (List Bool) :=
  (List.range (2 ^ (n - 1))).map fun pat =>
    if ρq ≠ lam ∧ (List.range (n - 1)).filter pat.testBit = [] then [] else
      if (List.range (n - 1)).filter (fun p => !pat.testBit p) = [] then
        [decide (0 < (((List.range (n - 1)).filter pat.testBit).foldl
          (fun s p => (⟨s.val + (kl.getD p ⟨0⟩).val⟩ : Q)) kq).val)]
      else (List.range lam).map fun ρ =>
        decide (0 < (((List.range (n - 1)).filter fun p => !pat.testBit p).foldl
          (fun s p => (⟨s.val + ((kp.getD p []).getD ρ ⟨0⟩).val⟩ : Q))
          (((List.range (n - 1)).filter pat.testBit).foldl
            (fun s p => (⟨s.val + (kl.getD p ⟨0⟩).val⟩ : Q)) kq)).val)

theorem runs_patterns (n ρq lam : ℕ) (kq : Q) (kl : List Q) (kp : List (List Q)) :
    Runs (patterns Interp.counting n ρq lam kq kl kp) env (patternsV n ρq lam kq kl kp)
      ((List.range (2 ^ (n - 1))).map (patCost n ρq lam)).sum := by
  unfold patterns patternsV
  rw [show Nat.pow 2 (n - 1) = 2 ^ (n - 1) from rfl]
  refine runs_mapM _ fun pat _ => ?_
  unfold patCost
  dsimp only
  simp only [List.isEmpty_iff]
  split
  · exact Runs.pure _
  · refine Runs.bind (runs_addFold _ _ _) ?_ |>.of_eq rfl
    split
    · exact Runs.bind' (runs_lt cat _ _) (Runs.pure _) (by simp) rfl
    · refine (runs_mapM (c := fun _ => _) _ fun ρ _ =>
        Runs.bind (runs_addFold _ _ _) (runs_lt cat _ _)).congr (by simp) ?_
      simp

theorem runs_block (mx : Bool) (V n : ℕ) (X : List (List (List (Q × Q)))) (Dd : List (List Q))
    (G : List (List (List Q))) (ρq lam : ℕ) :
    Runs (block Interp.counting mx V n X Dd G ρq lam) env
      (patternsV n ρq lam (kV X Dd G (tok mx V ρq) (tok mx V ρq) (n - 1) (tok mx V lam))
        ((List.range (n - 1)).map fun p => kV X Dd G (tok mx V ρq) (tok mx V lam) p (tok mx V lam))
        (if ρq = lam ∨ 3 ≤ n then (List.range (n - 1)).map fun p => scanVal min
          ((List.range lam).map fun ρ => kV X Dd G (tok mx V ρq) (tok mx V ρ) p (tok mx V lam))
          else []))
      (blockCost n ρq lam) := by
  unfold block blockCost
  dsimp only
  refine Runs.bind (runs_kterm _ _ _) (Runs.bind (runs_mapM (c := fun _ => 4) _ fun p _ =>
    runs_kterm _ _ _) (Runs.bind (?_ : Runs _ env _ (if ρq = lam ∨ 3 ≤ n then
      (n - 1) * (lam * 4 + (lam - 1)) else 0)) (runs_patterns _ _ _ _ _ _))) |>.of_eq ?_
  · split
    · exact runs_minRows mx V n lam fun t p => runs_kterm _ _ _
    · exact Runs.pure _
  · simp
    ring

/-- The value of `block`. -/
def blockVal (mx : Bool) (V n : ℕ) (X : List (List (List (Q × Q)))) (Dd : List (List Q))
    (G : List (List (List Q))) (ρq lam : ℕ) : List (List Bool) :=
  patternsV n ρq lam (kV X Dd G (tok mx V ρq) (tok mx V ρq) (n - 1) (tok mx V lam))
    ((List.range (n - 1)).map fun p => kV X Dd G (tok mx V ρq) (tok mx V lam) p (tok mx V lam))
    (if ρq = lam ∨ 3 ≤ n then (List.range (n - 1)).map fun p => scanVal min
      ((List.range lam).map fun ρ => kV X Dd G (tok mx V ρq) (tok mx V ρ) p (tok mx V lam))
      else [])

/-- The table of verdicts. -/
def vtV (mx : Bool) (V n : ℕ) (X : List (List (List (Q × Q)))) (Dd : List (List Q))
    (G : List (List (List Q))) : List (List (List (List Bool))) :=
  (List.range V).map fun ρq => (List.range V).map fun lam =>
    if ρq ≤ lam then blockVal mx V n X Dd G ρq lam else []

/-- The operations of the table of verdicts. -/
def vtCost (V n : ℕ) : ℕ :=
  ((List.range V).map fun ρq =>
    ((List.range V).map fun lam => if ρq ≤ lam then blockCost n ρq lam else 0).sum).sum

theorem runs_vt (mx : Bool) (V n : ℕ) (X : List (List (List (Q × Q)))) (Dd : List (List Q))
    (G : List (List (List Q))) :
    Runs ((List.range V).mapM fun ρq => (List.range V).mapM fun lam =>
        if ρq ≤ lam then block Interp.counting mx V n X Dd G ρq lam else pure []) env
      (vtV mx V n X Dd G) (vtCost V n) := by
  refine runs_mapM _ fun ρq _ => runs_mapM _ fun lam _ => ?_
  split
  · exact runs_block mx V n X Dd G ρq lam
  · exact Runs.pure _

end Block

end AttnClasses
