import CompactCheck.Json
import CompactCheck.Spec
import CompactCheck.CountedOps
import CompactCheck.Soundness
import CompactCheck.IntervalSound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Tools shared by the entries: finite sums, and runs of counted computations

Two kinds of facts used throughout the library.

* The evaluator of CompactCheck writes a sum as `((List.range n).map f).sum`; the algebra is easier
  with `∑ i ∈ Finset.range n, f i`. `sum_range_eq` converts.
* `Runs x env v n`: from any bill, the counted computation `x` succeeds with the value `v` and adds
  exactly `n` to the bill's total. Runs compose (`Runs.bind`), so the value and the cost of a whole
  checker come out of one induction per loop.

Every CompactCheck module the acceptance service trusts is imported here, before any proof: a proof
that unfolds a CompactCheck definition makes Lean generate its equation lemma in the current module
unless an imported module already has it, and the service refuses a candidate that redeclares a
constant of the trusted modules.
-/

namespace Common

open CompactCheck

/-! ## Sums -/

theorem sum_range_eq {M : Type} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A finite sum of multiples of list sums is the list sum of the finite sums. -/
theorem sum_mul_list_sum {α : Type} (s : Finset ℕ) (c : ℕ → ℚ) (f : ℕ → α → ℚ) (x : List α) :
    ∑ a ∈ s, c a * (x.map (f a)).sum = (x.map fun t => ∑ a ∈ s, c a * f a t).sum := by
  induction x with
  | nil => simp
  | cons t x ih => simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, ih]

/-- Summing over the positions of a list, by index, is summing over its entries. -/
theorem sum_getD_eq {M : Type} [AddCommMonoid M] (f : ℕ → M) :
    ∀ x : List ℕ, ∑ p ∈ Finset.range x.length, f (x.getD p 0) = (x.map f).sum
  | [] => by simp
  | t :: x => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, add_comm]
    simp only [List.getD_cons_succ, List.getD_cons_zero, sum_getD_eq f x]

/-- A sum of `k` terms, each at least `μ`, is at least `k μ`. -/
theorem list_sum_ge {α : Type} (x : List α) (f : α → ℚ) (μ : ℚ) (h : ∀ t ∈ x, μ ≤ f t) :
    (x.length : ℚ) * μ ≤ (x.map f).sum := by
  induction x with
  | nil => simp
  | cons t x ih =>
    simp only [List.length_cons, Nat.cast_succ, List.map_cons, List.sum_cons]
    have h1 := h t List.mem_cons_self
    have h2 := ih fun u hu => h u (List.mem_cons_of_mem _ hu)
    have h3 : ((x.length : ℚ) + 1) * μ = x.length * μ + μ := by ring
    linarith

/-! ## Bills -/

theorem Cost.total_add (c : Cost) (cat : String) (n : ℕ) : (c.add cat n).total = c.total + n := by
  induction c with
  | nil => simp [Cost.add, Cost.total]
  | cons p rest ih =>
    obtain ⟨k, m⟩ := p
    simp only [Cost.add]
    split
    · simp [Cost.total]; omega
    · simp only [Cost.total, List.map_cons, List.sum_cons] at ih ⊢; omega

/-! ## Runs -/

/-- From any bill, `x` succeeds with the value `v` and adds `n` to the bill's total. -/
def Runs {α : Type} (x : CostM α) (env : Env) (v : α) (n : ℕ) : Prop :=
  ∀ c : Cost, ∃ c' : Cost, x.run env c = some (v, c') ∧ c'.total = c.total + n

namespace Runs

variable {α β : Type} {env : Env}

theorem pure (v : α) : Runs (Pure.pure v : CostM α) env v 0 :=
  fun c => ⟨c, rfl, by simp⟩

theorem bind {x : CostM α} {f : α → CostM β} {a : α} {b : β} {n m : ℕ}
    (hx : Runs x env a n) (hf : Runs (f a) env b m) : Runs (x >>= f) env b (n + m) := by
  intro c
  obtain ⟨c1, h1, t1⟩ := hx c
  obtain ⟨c2, h2, t2⟩ := hf c1
  refine ⟨c2, ?_, by omega⟩
  rw [CostM.run_bind, h1]
  exact h2

/-- `bind`, with the value and the cost left to be matched: `refine Runs.bind' hx ?_ ?_ ?_`
    leaves the continuation's run, then the value and the cost as equations. -/
theorem bind' {x : CostM α} {f : α → CostM β} {a : α} {b b' : β} {n m k : ℕ}
    (hx : Runs x env a n) (hf : Runs (f a) env b m) (hb : b = b') (hk : n + m = k) :
    Runs (x >>= f) env b' k :=
  hb ▸ hk ▸ bind hx hf

/-- `bind` after a free step. -/
theorem bind0 {x : CostM α} {f : α → CostM β} {a : α} {b : β} {m : ℕ}
    (hx : Runs x env a 0) (hf : Runs (f a) env b m) : Runs (x >>= f) env b m :=
  Nat.zero_add m ▸ bind hx hf

theorem of_eq {x : CostM α} {v : α} {n m : ℕ} (h : Runs x env v n) (hnm : n = m) : Runs x env v m :=
  hnm ▸ h

theorem congr {x : CostM α} {v v' : α} {n n' : ℕ} (h : Runs x env v n) (hv : v = v') (hn : n = n') :
    Runs x env v' n' :=
  hv ▸ hn ▸ h

/-- A run that succeeds gives the value of `Runs`. -/
theorem det {x : CostM α} {v v' : α} {n : ℕ} {c c' : Cost} (h : Runs x env v n)
    (hr : x.run env c = some (v', c')) : v' = v ∧ c'.total = c.total + n := by
  obtain ⟨c'', h1, t1⟩ := h c
  rw [h1] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  obtain ⟨rfl, rfl⟩ := hr
  exact ⟨rfl, t1⟩

/-- A run of `x >>= f` that succeeds is a run of `x` followed by a run of `f`. -/
theorem bind_some {x : CostM α} {f : α → CostM β} {c c' : Cost} {b : β}
    (h : (x >>= f).run env c = some (b, c')) :
    ∃ a c1, x.run env c = some (a, c1) ∧ (f a).run env c1 = some (b, c') := by
  rw [CostM.run_bind] at h
  match hx : x.run env c with
  | some (a, c1) => rw [hx] at h; exact ⟨a, c1, rfl, h⟩
  | none => rw [hx] at h; cases h

/-- The bill of a whole computation, from the empty bill. -/
theorem billed {x : CostM α} {v : α} {n : ℕ} (h : Runs x env v n) :
    CostM.billed x env = some (v, n) := by
  obtain ⟨c', h1, t1⟩ := h []
  simp only [Cost.total, List.map_nil, List.sum_nil, zero_add] at t1
  simp only [CostM.billed, CostM.exec, h1, Option.map_some, Cost.total, t1]

end Runs

/-! ## The counting interpreter's operations, as runs -/

section Ops

variable {env : Env}

theorem runs_weight {name : String} {t : Tensor ℚ} {i : ℕ}
    (h : List.lookup name env.weights = some t) (hi : i < t.data.size) :
    Runs (CostM.weight name i) env ⟨t.get i⟩ 0 := by
  intro c
  refine ⟨c, ?_, by simp⟩
  -- CompactCheck at eab37d3 reads weights through a balanced tree (policy v10); its lemma gives the read.
  rw [CostM.weight_run_of_lookup c h hi]
  simp [Tensor.get, Array.getD, hi]

theorem runs_weightShape {name : String} {t : Tensor ℚ}
    (h : List.lookup name env.weights = some t) :
    Runs (CostM.weightShape name) env t.shape 0 := by
  intro c
  exact ⟨c, by simp [CostM.weightShape, h], by simp⟩

theorem runs_weightSize {name : String} {t : Tensor ℚ}
    (h : List.lookup name env.weights = some t) :
    Runs (CostM.weightSize name) env t.data.size 0 := by
  intro c
  exact ⟨c, by simp [CostM.weightSize, h], by simp⟩

theorem weightSize_some {name : String} {n : ℕ} {c c' : Cost}
    (h : (CostM.weightSize name).run env c = some (n, c')) :
    ∃ t, List.lookup name env.weights = some t ∧ t.data.size = n := by
  obtain ⟨t, ht, hn, -⟩ := CostM.weightSize_spec h
  exact ⟨t, ht, hn⟩

theorem weightShape_some {name : String} {s : List ℕ} {c c' : Cost}
    (h : (CostM.weightShape name).run env c = some (s, c')) :
    ∃ t, List.lookup name env.weights = some t ∧ t.shape = s := by
  simp only [CostM.weightShape] at h
  split at h
  · rename_i t ht
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨t, ht, h.1⟩
  · cases h

theorem single_some {g : Graph} {task : Task} {x : Input} {b : Bool} {c c' : Cost}
    (h : (CostM.single g task x).run env c = some (b, c')) :
    ∃ sc, singleCost g env.weights = some sc := by
  simp only [CostM.single] at h
  split at h
  · rename_i sc hsc; exact ⟨sc, hsc⟩
  · cases h

theorem runs_muladd (cat : String) (acc a b : Q) :
    Runs (CostM.qmuladd cat acc a b) env ⟨acc.val + a.val * b.val⟩ 1 :=
  fun c => ⟨c.add cat 1, rfl, Cost.total_add _ _ _⟩

theorem runs_add (cat : String) (a b : Q) : Runs (CostM.qadd cat a b) env ⟨a.val + b.val⟩ 1 :=
  fun c => ⟨c.add cat 1, rfl, Cost.total_add _ _ _⟩

theorem runs_sub (cat : String) (a b : Q) : Runs (CostM.qsub cat a b) env ⟨a.val - b.val⟩ 1 :=
  fun c => ⟨c.add cat 1, rfl, Cost.total_add _ _ _⟩

theorem runs_max (cat : String) (a b : Q) : Runs (CostM.qmax cat a b) env ⟨max a.val b.val⟩ 1 :=
  fun c => ⟨c.add cat 1, rfl, Cost.total_add _ _ _⟩

theorem runs_min (cat : String) (a b : Q) : Runs (CostM.qmin cat a b) env ⟨min a.val b.val⟩ 1 :=
  fun c => ⟨c.add cat 1, rfl, Cost.total_add _ _ _⟩

theorem runs_lt (cat : String) (a b : Q) :
    Runs (CostM.qlt cat a b) env (decide (a.val < b.val)) 1 :=
  fun c => ⟨c.add cat 1, rfl, Cost.total_add _ _ _⟩

theorem runs_lit (cat : String) (n : ℕ) : Runs (CostM.lit cat n) env ⟨(n : ℚ)⟩ 1 :=
  fun c => ⟨c.add cat 1, rfl, Cost.total_add _ _ _⟩

theorem runs_band (cat : String) (a b : Bool) :
    Runs (Interp.counting.band cat a b) env (a && b) 1 :=
  fun c => ⟨c.add cat 1, rfl, Cost.total_add _ _ _⟩

theorem runs_single {g : Graph} {task : Task} {x : Input} {sc : ℕ}
    (h : singleCost g env.weights = some sc) :
    Runs (CostM.single g task x) env (singleOk g env.weights task x) sc := by
  intro c
  refine ⟨c.add "single" sc, ?_, Cost.total_add _ _ _⟩
  simp [CostM.single, h]

end Ops

/-! ## Folds and maps of counted steps -/

section Folds

variable {env : Env} {α β : Type}

/-- A fold of counted steps: the steps' values folded, and their costs added. -/
theorem runs_foldlM {f : β → α → Interp.counting.M β} {g : β → α → β} {c : α → ℕ} :
    ∀ (l : List α) (b : β), (∀ b, ∀ a ∈ l, Runs (f b a) env (g b a) (c a)) →
      Runs (@List.foldlM Interp.counting.M (instMonadInterp Interp.counting) β α f b l) env
        (l.foldl g b) (l.map c).sum
  | [], b, _ => (Runs.pure b).congr rfl (by simp)
  | a :: l, b, h => by
    simp only [List.foldlM_cons, Interp.counting_bind]
    exact Runs.bind' (h b a List.mem_cons_self)
      (runs_foldlM l _ fun b' a' ha' => h b' a' (List.mem_cons_of_mem _ ha')) rfl (by simp)

theorem runs_mapM_loop {f : α → Interp.counting.M β} {g : α → β} {c : α → ℕ} :
    ∀ (l : List α) (bs : List β), (∀ a ∈ l, Runs (f a) env (g a) (c a)) →
      Runs (@List.mapM.loop Interp.counting.M (instMonadInterp Interp.counting) α β f l bs) env
        (bs.reverse ++ l.map g) (l.map c).sum
  | [], bs, _ => (Runs.pure _).congr (by simp) (by simp)
  | a :: l, bs, h => by
    simp only [List.mapM.loop, Interp.counting_bind]
    exact Runs.bind' (h a List.mem_cons_self)
      (runs_mapM_loop l _ fun a' ha' => h a' (List.mem_cons_of_mem _ ha')) (by simp) (by simp)

/-- A map of counted steps: their values, and their costs added. -/
theorem runs_mapM {f : α → Interp.counting.M β} {g : α → β} {c : α → ℕ} (l : List α)
    (h : ∀ a ∈ l, Runs (f a) env (g a) (c a)) :
    Runs (@List.mapM Interp.counting.M (instMonadInterp Interp.counting) α β f l) env (l.map g)
      (l.map c).sum :=
  (runs_mapM_loop l [] h).congr (by simp) rfl

end Folds

end Common
