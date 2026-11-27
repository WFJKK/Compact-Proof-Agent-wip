import Protected.N_attn_max4_v64_s0
import CompactCheck.Soundness
import CompactCheck.CountedOps
import CompactCheck.CountedGeneralSound
import CompactCheck.ExpSound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Counted-language loops and their specifications under the counting interpreter.

`Spec env m P`: whatever bill `m` runs from, if it returns `v` then `P v`. Partial correctness: a failing
run proves nothing, which is what soundness needs.
-/

namespace Candidate.Loops
open CompactCheck Finset

/-! ## The loops (usable inside a checker: only the interpreter's fields) -/

/-- acc + Σ_{k<n} a k * b k, via muladd (k from n-1 down to 0). -/
def dotM (I : Interp) (a b : Nat → I.M I.V) : Nat → I.V → I.M I.V
  | 0, acc => pure acc
  | k+1, acc => do
    let x ← a k
    let y ← b k
    let acc' ← I.muladd "" acc x y
    dotM I a b k acc'

/-- The table f i, ..., f (i+n-1), pushed in order. -/
def tableM (I : Interp) (f : Nat → I.M I.V) : Nat → Nat → Array I.V → I.M (Array I.V)
  | 0, _, arr => pure arr
  | k+1, i, arr => do
    let v ← f i
    tableM I f k (i+1) (arr.push v)

def tableB (I : Interp) (f : Nat → I.M I.B) : Nat → Nat → Array I.B → I.M (Array I.B)
  | 0, _, arr => pure arr
  | k+1, i, arr => do
    let v ← f i
    tableB I f k (i+1) (arr.push v)

/-- max(acc, f 0, ..., f (n-1)). -/
def maxM (I : Interp) (f : Nat → I.V) : Nat → I.V → I.M I.V
  | 0, acc => pure acc
  | k+1, acc => do
    let acc' ← I.max "" acc (f k)
    maxM I f k acc'

/-- min(acc, f 0, ..., f (n-1)). -/
def minM (I : Interp) (f : Nat → I.V) : Nat → I.V → I.M I.V
  | 0, acc => pure acc
  | k+1, acc => do
    let acc' ← I.min "" acc (f k)
    minM I f k acc'

/-! ## Specifications -/

/-- Partial correctness of a counted computation: a returned value satisfies `P`. -/
def Spec (env : Env) {α : Type} (m : CostM α) (P : α → Prop) : Prop :=
  ∀ c v c', m.run env c = some (v, c') → P v

section
variable {env : Env} {α β : Type}

theorem spec_pure {a : α} {P : α → Prop} (h : P a) : Spec env (pure a) P := by
  intro c v c' hr
  simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
  rw [← hr.1]; exact h

theorem spec_bind {m : CostM α} {f : α → CostM β} {P : α → Prop} {Q : β → Prop}
    (hm : Spec env m P) (hf : ∀ a, P a → Spec env (f a) Q) : Spec env (m >>= f) Q := by
  intro c v c' hr
  rw [CostM.run_bind] at hr
  split at hr
  · rename_i a c1 ha
    exact hf a (hm c a c1 ha) c1 v c' hr
  · cases hr

theorem spec_mono {m : CostM α} {P Q : α → Prop} (h : ∀ a, P a → Q a) (hm : Spec env m P) : Spec env m Q :=
  fun c v c' hr => h v (hm c v c' hr)

theorem spec_muladd (cat : String) (acc x y : Q) :
    Spec env (CostM.qmuladd cat acc x y) fun v => v.val = acc.val + x.val * y.val := by
  intro c v c' hr
  simp only [CostM.qmuladd, Option.some.injEq, Prod.mk.injEq] at hr
  rw [← hr.1]

theorem spec_add (cat : String) (x y : Q) : Spec env (CostM.qadd cat x y) fun v => v.val = x.val + y.val := by
  intro c v c' hr
  simp only [CostM.qadd, Option.some.injEq, Prod.mk.injEq] at hr
  rw [← hr.1]

theorem spec_sub (cat : String) (x y : Q) : Spec env (CostM.qsub cat x y) fun v => v.val = x.val - y.val := by
  intro c v c' hr
  simp only [CostM.qsub, Option.some.injEq, Prod.mk.injEq] at hr
  rw [← hr.1]

theorem spec_neg (cat : String) (x : Q) : Spec env (CostM.qneg cat x) fun v => v.val = -x.val := by
  intro c v c' hr
  simp only [CostM.qneg, Option.some.injEq, Prod.mk.injEq] at hr
  rw [← hr.1]

theorem spec_min (cat : String) (x y : Q) : Spec env (CostM.qmin cat x y) fun v => v.val = min x.val y.val := by
  intro c v c' hr
  simp only [CostM.qmin, Option.some.injEq, Prod.mk.injEq] at hr
  rw [← hr.1]

theorem spec_max (cat : String) (x y : Q) : Spec env (CostM.qmax cat x y) fun v => v.val = max x.val y.val := by
  intro c v c' hr
  simp only [CostM.qmax, Option.some.injEq, Prod.mk.injEq] at hr
  rw [← hr.1]

theorem spec_lt (cat : String) (x y : Q) : Spec env (CostM.qlt cat x y) fun b => b = decide (x.val < y.val) := by
  intro c v c' hr
  simp only [CostM.qlt, Option.some.injEq, Prod.mk.injEq] at hr
  rw [← hr.1]

theorem spec_le (cat : String) (x y : Q) : Spec env (CostM.qle cat x y) fun b => b = decide (x.val ≤ y.val) := by
  intro c v c' hr
  simp only [CostM.qle, Option.some.injEq, Prod.mk.injEq] at hr
  rw [← hr.1]

theorem spec_lit (cat : String) (n : Nat) : Spec env (CostM.lit cat n) fun v => v.val = (n : ℚ) := by
  intro c v c' hr
  simp only [CostM.lit, Option.some.injEq, Prod.mk.injEq] at hr
  rw [← hr.1]

theorem spec_weight {name : String} {t : Tensor ℚ} (ht : List.lookup name env.weights = some t) (i : Nat) :
    Spec env (CostM.weight name i) fun v => v.val = t.get i :=
  fun _ _ _ hr => (CostM.weight_run_get ht hr).1

theorem spec_cert (i : Nat) : Spec env (CostM.cert i) fun v => v.val = env.cert[i]! :=
  fun _ _ _ hr => (CostM.cert_run_get hr).1

theorem spec_exp (cat : String) (a : Q) :
    Spec env (CostM.qexp cat a) fun p => (p.1.val : ℝ) ≤ Real.exp a.val ∧ Real.exp a.val ≤ p.2.val := by
  intro c v c' hr
  simp only [CostM.qexp] at hr
  split at hr
  · rename_i lo hi h
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    rw [← hr.1]
    exact expInterval_spec h
  · cases hr

theorem spec_selectV (cat : String) (b : Bool) (x y : Q) :
    Spec env (Interp.counting.selectV cat b x y) fun v => v = cond b x y := by
  intro c v c' hr
  rw [Interp.counting_selectV_run] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  exact hr.1.symm

theorem spec_band (cat : String) (a b : Bool) :
    Spec env (Interp.counting.band cat a b) fun v => v = (a && b) := by
  intro c v c' hr
  rw [Interp.counting_band_run] at hr
  simp only [Option.some.injEq, Prod.mk.injEq] at hr
  exact hr.1.symm

/-! ## Loop specifications -/

theorem spec_dotM {a b : Nat → CostM Q} {fa fb : Nat → ℚ} :
    ∀ (n : Nat) (acc : Q), (∀ k < n, Spec env (a k) fun x => x.val = fa k) →
      (∀ k < n, Spec env (b k) fun y => y.val = fb k) →
      Spec env (dotM Interp.counting a b n acc) fun v => v.val = acc.val + ∑ k ∈ range n, fa k * fb k
  | 0, acc, _, _ => by
    simp only [dotM, range_zero, sum_empty, add_zero]
    exact spec_pure rfl
  | n+1, acc, ha, hb => by
    show Spec env (a n >>= fun x => b n >>= fun y => CostM.qmuladd "" acc x y >>= fun acc' =>
      dotM Interp.counting a b n acc') _
    refine spec_bind (ha n (Nat.lt_succ_self n)) fun x hx => ?_
    refine spec_bind (hb n (Nat.lt_succ_self n)) fun y hy => ?_
    refine spec_bind (spec_muladd "" acc x y) fun acc' hacc => ?_
    refine spec_mono ?_ (spec_dotM n acc' (fun k hk => ha k (by omega)) (fun k hk => hb k (by omega)))
    intro v hv
    rw [hv, hacc, hx, hy, sum_range_succ]
    ring

theorem spec_maxM (f : Nat → Q) :
    ∀ (n : Nat) (acc : Q),
      Spec env (maxM Interp.counting f n acc) fun v => acc.val ≤ v.val ∧ ∀ k < n, (f k).val ≤ v.val
  | 0, acc => by
    simp only [maxM]
    exact spec_pure ⟨le_refl _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n+1, acc => by
    show Spec env (CostM.qmax "" acc (f n) >>= fun acc' => maxM Interp.counting f n acc') _
    refine spec_bind (spec_max "" acc (f n)) fun acc' hacc => ?_
    refine spec_mono ?_ (spec_maxM f n acc')
    intro v ⟨h1, h2⟩
    rw [hacc] at h1
    refine ⟨le_trans (le_max_left _ _) h1, fun k hk => ?_⟩
    by_cases hkn : k = n
    · subst hkn; exact le_trans (le_max_right _ _) h1
    · exact h2 k (by omega)

theorem spec_minM (f : Nat → Q) :
    ∀ (n : Nat) (acc : Q),
      Spec env (minM Interp.counting f n acc) fun v => v.val ≤ acc.val ∧ ∀ k < n, v.val ≤ (f k).val
  | 0, acc => by
    simp only [minM]
    exact spec_pure ⟨le_refl _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n+1, acc => by
    show Spec env (CostM.qmin "" acc (f n) >>= fun acc' => minM Interp.counting f n acc') _
    refine spec_bind (spec_min "" acc (f n)) fun acc' hacc => ?_
    refine spec_mono ?_ (spec_minM f n acc')
    intro v ⟨h1, h2⟩
    rw [hacc] at h1
    refine ⟨le_trans h1 (min_le_left _ _), fun k hk => ?_⟩
    by_cases hkn : k = n
    · subst hkn; exact le_trans h1 (min_le_right _ _)
    · exact h2 k (by omega)

theorem spec_tableM {f : Nat → CostM Q} {g : Nat → ℚ} (hf : ∀ i, Spec env (f i) fun v => v.val = g i) :
    ∀ (n i : Nat) (arr : Array Q),
      Spec env (tableM Interp.counting f n i arr) fun arr' =>
        arr'.toList.map Q.val = arr.toList.map Q.val ++ (List.range n).map fun k => g (i + k)
  | 0, i, arr => by
    simp only [tableM, List.range_zero, List.map_nil, List.append_nil]
    exact spec_pure rfl
  | n+1, i, arr => by
    show Spec env (f i >>= fun v => tableM Interp.counting f n (i+1) (arr.push v)) _
    refine spec_bind (hf i) fun v hv => ?_
    refine spec_mono ?_ (spec_tableM hf n (i+1) (arr.push v))
    intro arr' h
    rw [h, Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.range_succ_eq_map,
      List.map_cons, List.map_map, List.append_assoc, List.singleton_append, hv]
    congr 3
    funext k
    simp only [Function.comp, Nat.add_assoc, Nat.add_comm 1 k]

theorem spec_tableB {f : Nat → CostM Bool} {g : Nat → Bool} (hf : ∀ i, Spec env (f i) fun v => v = g i) :
    ∀ (n i : Nat) (arr : Array Bool),
      Spec env (tableB Interp.counting f n i arr) fun arr' =>
        arr'.toList = arr.toList ++ (List.range n).map fun k => g (i + k)
  | 0, i, arr => by
    simp only [tableB, List.range_zero, List.map_nil, List.append_nil]
    exact spec_pure rfl
  | n+1, i, arr => by
    show Spec env (f i >>= fun v => tableB Interp.counting f n (i+1) (arr.push v)) _
    refine spec_bind (hf i) fun v hv => ?_
    refine spec_mono ?_ (spec_tableB hf n (i+1) (arr.push v))
    intro arr' h
    rw [h, Array.toList_push, List.range_succ_eq_map, List.map_cons, List.map_map, List.append_assoc,
      List.singleton_append, hv]
    congr 3
    funext k
    simp only [Function.comp, Nat.add_assoc, Nat.add_comm 1 k]

/-- `tableB` with a predicate per entry (for entries whose value is only characterized, like the flags). -/
theorem spec_tableB' {f : Nat → CostM Bool} {P : Nat → Bool → Prop} (hf : ∀ i, Spec env (f i) (P i)) :
    ∀ (n i : Nat) (arr : Array Bool),
      Spec env (tableB Interp.counting f n i arr) fun arr' =>
        ∃ l : List Bool, arr'.toList = arr.toList ++ l ∧ l.length = n ∧ ∀ k (hk : k < l.length), P (i + k) l[k]
  | 0, i, arr => by
    simp only [tableB]
    exact spec_pure ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n+1, i, arr => by
    show Spec env (f i >>= fun v => tableB Interp.counting f n (i+1) (arr.push v)) _
    refine spec_bind (hf i) fun v hv => ?_
    refine spec_mono ?_ (spec_tableB' hf n (i+1) (arr.push v))
    intro arr' ⟨l, hl, hlen, hP⟩
    refine ⟨v :: l, ?_, by simp [hlen], ?_⟩
    · rw [hl, Array.toList_push, List.append_assoc, List.singleton_append]
    · intro k hk
      cases k with
      | zero => simpa using hv
      | succ k =>
        have := hP k (by simpa using hk)
        simp only [List.getElem_cons_succ]
        rw [show i + (k + 1) = i + 1 + k by omega]
        exact this

/-- Reading a table entry built by `tableB'`: `arr.getD g false` is `l[g]` when `arr.toList = l`. -/
theorem getD_of_toList {arr : Array Bool} {l : List Bool} (h : arr.toList = l) {g : Nat} (hg : g < l.length) :
    arr.getD g false = l[g] := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h, List.getElem?_eq_getElem hg]
  rfl

end

end Candidate.Loops
