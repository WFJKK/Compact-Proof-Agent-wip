import Candidate.Far

/-! # Run lemmas: the values a successful run of each helper computes, as rational models. -/

namespace Candidate.FarRun
open CompactCheck Candidate.Far

def dotQ : List ℚ → List ℚ → ℚ → ℚ
  | x :: xs, y :: ys, acc => dotQ xs ys (acc + x * y)
  | _, _, acc => acc

def fetchQ (t : Tensor ℚ) (base stride : Nat) (ts : List Nat) : List ℚ :=
  ts.map fun i => t.get (base + i * stride)
def matVecQ (t : Tensor ℚ) (ncols : Nat) (v : List ℚ) (js : List Nat) : List ℚ :=
  js.map fun j => dotQ v (fetchQ t j ncols (List.range v.length)) 0
def matVecTQ (t : Tensor ℚ) (ncols : Nat) (v : List ℚ) (ts : List Nat) : List ℚ :=
  ts.map fun i => dotQ (fetchQ t (i * ncols) 1 (List.range v.length)) v 0

theorem weight_run {name : String} {env : Env} {t : Tensor ℚ} {i : Nat} {c c' : Cost} {v : Q}
    (h : List.lookup name env.weights = some t) (hr : (CostM.weight name i).run env c = some (v, c')) :
    v.val = t.get i ∧ c' = c := CostM.weight_run_get h hr

theorem cert_run {env : Env} {i : Nat} {c c' : Cost} {v : Q}
    (hr : (CostM.cert i).run env c = some (v, c')) : v.val = env.cert[i]! ∧ c' = c := CostM.cert_run_get hr

theorem qmuladd_run (cat : String) (acc a b : Q) (env : Env) (c : Cost) :
    (CostM.qmuladd cat acc a b).run env c = some (⟨acc.val + a.val * b.val⟩, c.add cat 1) := rfl
theorem qadd_run (cat : String) (a b : Q) (env : Env) (c : Cost) :
    (CostM.qadd cat a b).run env c = some (⟨a.val + b.val⟩, c.add cat 1) := rfl
theorem qsub_run (cat : String) (a b : Q) (env : Env) (c : Cost) :
    (CostM.qsub cat a b).run env c = some (⟨a.val - b.val⟩, c.add cat 1) := rfl
theorem qmax_run (cat : String) (a b : Q) (env : Env) (c : Cost) :
    (CostM.qmax cat a b).run env c = some (⟨max a.val b.val⟩, c.add cat 1) := rfl
theorem qlt_run (cat : String) (a b : Q) (env : Env) (c : Cost) :
    (CostM.qlt cat a b).run env c = some (decide (a.val < b.val), c.add cat 1) := rfl
theorem qle_run (cat : String) (a b : Q) (env : Env) (c : Cost) :
    (CostM.qle cat a b).run env c = some (decide (a.val ≤ b.val), c.add cat 1) := rfl

theorem fetch_run {name : String} {env : Env} {t : Tensor ℚ} (h : List.lookup name env.weights = some t)
    (base stride : Nat) : ∀ (ts : List Nat) (c c' : Cost) (L : List Q),
    (fetch Interp.counting name base stride ts).run env c = some (L, c') →
    L.map Q.val = fetchQ t base stride ts
  | [], c, c', L, hr => by
    simp only [fetch, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr; rfl
  | i :: ts, c, c', L, hr => by
    simp only [fetch, Interp.counting_bind, Interp.counting_pure, Interp.counting_weight, CostM.run_bind] at hr
    split at hr
    · rename_i x c1 hx
      obtain ⟨hxv, rfl⟩ := weight_run h hx
      split at hr
      · rename_i rest c2 hrest
        have hrv := fetch_run h base stride ts _ _ rest hrest
        simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        simp only [List.map_cons, fetchQ, hxv]
        rw [fetchQ] at hrv; rw [hrv]
      · cases hr
    · cases hr

theorem dotL_run (env : Env) : ∀ (xs ys : List Q) (acc : Q) (c c' : Cost) (v : Q),
    (dotL Interp.counting xs ys acc).run env c = some (v, c') →
    v.val = dotQ (xs.map Q.val) (ys.map Q.val) acc.val
  | x :: xs, y :: ys, acc, c, c', v, hr => by
    simp only [dotL, Interp.counting_bind, Interp.counting_muladd, CostM.run_bind, qmuladd_run] at hr
    have := dotL_run env xs ys _ _ _ _ hr
    simpa [dotQ] using this
  | [], ys, acc, c, c', v, hr => by
    simp only [dotL, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr; simp [dotQ]
  | x :: xs, [], acc, c, c', v, hr => by
    simp only [dotL, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr; simp [dotQ]

theorem addL_run (env : Env) : ∀ (xs ys : List Q) (c c' : Cost) (v : List Q),
    (addL Interp.counting xs ys).run env c = some (v, c') →
    v.map Q.val = List.zipWith (· + ·) (xs.map Q.val) (ys.map Q.val)
  | x :: xs, y :: ys, c, c', v, hr => by
    simp only [addL, Interp.counting_bind, Interp.counting_pure, Interp.counting_add, CostM.run_bind, qadd_run] at hr
    split at hr
    · rename_i rest c2 hrest
      have hrv := addL_run env xs ys _ _ _ hrest
      simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      simp [hrv]
    · cases hr
  | [], ys, c, c', v, hr => by
    simp only [addL, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr; simp
  | x :: xs, [], c, c', v, hr => by
    simp only [addL, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr; simp

theorem matVec_run {name : String} {env : Env} {t : Tensor ℚ} (h : List.lookup name env.weights = some t)
    (ncols : Nat) (xs : List Q) : ∀ (js : List Nat) (c c' : Cost) (v : List Q),
    (Far.matVec Interp.counting name ncols xs js).run env c = some (v, c') →
    v.map Q.val = matVecQ t ncols (xs.map Q.val) js
  | [], c, c', v, hr => by
    simp only [Far.matVec, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr; rfl
  | j :: js, c, c', v, hr => by
    simp only [Far.matVec, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at hr
    split at hr
    · rename_i col c1 hcol
      have hcv := fetch_run h j ncols _ _ _ _ hcol
      split at hr
      · rename_i s c2 hs
        have hsv := dotL_run env _ _ _ _ _ _ hs
        split at hr
        · rename_i rest c3 hrest
          have hrv := matVec_run h ncols xs js _ _ _ hrest
          simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          simp only [List.map_cons, matVecQ, hsv, hcv, Interp.counting_zero, List.length_map]
          rw [matVecQ, List.length_map] at hrv; rw [hrv]
        · cases hr
      · cases hr
    · cases hr

theorem matVecT_run {name : String} {env : Env} {t : Tensor ℚ} (h : List.lookup name env.weights = some t)
    (ncols : Nat) (xs : List Q) : ∀ (ts : List Nat) (c c' : Cost) (v : List Q),
    (matVecT Interp.counting name ncols xs ts).run env c = some (v, c') →
    v.map Q.val = matVecTQ t ncols (xs.map Q.val) ts
  | [], c, c', v, hr => by
    simp only [matVecT, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr; rfl
  | j :: js, c, c', v, hr => by
    simp only [matVecT, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at hr
    split at hr
    · rename_i col c1 hcol
      have hcv := fetch_run h (j * ncols) 1 _ _ _ _ hcol
      split at hr
      · rename_i s c2 hs
        have hsv := dotL_run env _ _ _ _ _ _ hs
        split at hr
        · rename_i rest c3 hrest
          have hrv := matVecT_run h ncols xs js _ _ _ hrest
          simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          simp only [List.map_cons, matVecTQ, hsv, hcv, Interp.counting_zero, List.length_map]
          rw [matVecTQ, List.length_map] at hrv; rw [hrv]
        · cases hr
      · cases hr
    · cases hr

theorem scaleL_run (env : Env) (cq : Q) : ∀ (xs : List Q) (c c' : Cost) (v : List Q),
    (scaleL Interp.counting cq xs).run env c = some (v, c') →
    v.map Q.val = (xs.map Q.val).map fun x => 0 + x * cq.val
  | [], c, c', v, hr => by
    simp only [scaleL, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr; rfl
  | x :: xs, c, c', v, hr => by
    simp only [scaleL, Interp.counting_bind, Interp.counting_pure, Interp.counting_muladd, Interp.counting_zero,
      CostM.run_bind, qmuladd_run] at hr
    split at hr
    · rename_i rest c2 hrest
      have hrv := scaleL_run env cq xs _ _ _ hrest
      simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      simp [hrv]
    · cases hr

theorem maxS_run {env : Env} {tE : Tensor ℚ} (hE : List.lookup "E" env.weights = some tE) (kq : List Q) (c0 : Q) :
    ∀ (as : List Nat) (acc : Q) (c c' : Cost) (v : Q),
    (maxS Interp.counting kq c0 as acc).run env c = some (v, c') →
    acc.val ≤ v.val ∧ ∀ a ∈ as, dotQ (fetchQ tE (a * 8) 1 (List.range 8)) (kq.map Q.val) c0.val ≤ v.val
  | [], acc, c, c', v, hr => by
    simp only [maxS, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr; exact ⟨le_refl _, by simp⟩
  | a :: as, acc, c, c', v, hr => by
    simp only [maxS, Interp.counting_bind, Interp.counting_max, CostM.run_bind] at hr
    split at hr
    · rename_i ea c1 hea
      have hev := fetch_run hE (a * 8) 1 _ _ _ _ hea
      split at hr
      · rename_i s c2 hs
        have hsv := dotL_run env _ _ _ _ _ _ hs
        rw [qmax_run] at hr
        obtain ⟨h1, h2⟩ := maxS_run hE kq c0 as _ _ _ _ hr
        refine ⟨le_trans (le_max_left _ _) h1, ?_⟩
        intro a' ha'
        simp only [List.mem_cons] at ha'
        rcases ha' with rfl | ha'
        · rw [← hev, ← hsv]; exact le_trans (le_max_right _ _) h1
        · exact h2 a' ha'
      · cases hr
    · cases hr

theorem allIn_run (env : Env) (lo hi : Q) : ∀ (xs : List Q) (c c' : Cost),
    (allIn Interp.counting lo hi xs).run env c = some (true, c') →
    ∀ x ∈ xs, lo.val ≤ x.val ∧ x.val ≤ hi.val
  | [], c, c', hr => by simp
  | x :: xs, c, c', hr => by
    simp only [allIn, Interp.counting_bind, Interp.counting_le, CostM.run_bind] at hr
    split at hr
    · rename_i rest c1 hrest
      simp only [qle_run, Interp.counting_band_run, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨hb, -⟩ := hr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      obtain ⟨⟨h1, h2⟩, h3⟩ := hb
      intro y hy
      simp only [List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨h1, h2⟩
      · exact allIn_run env lo hi xs c c1 (by rw [hrest, h3]) y hy
    · cases hr

theorem checkJ_run (env : Env) (lo1 hi0 Xb base : Q) (b : Nat) :
    ∀ (xs ds : List Q) (j0 : Nat) (c c' : Cost),
    (checkJ Interp.counting lo1 hi0 Xb base b xs ds j0).run env c = some (true, c') →
    ∀ i, i < xs.length → i < ds.length → j0 + i ≠ b →
      0 < Xb.val - (xs.getD i ⟨0⟩).val ∧
      0 < lo1.val * (Xb.val - (xs.getD i ⟨0⟩).val) + hi0.val * (base.val - (ds.getD i ⟨0⟩).val)
  | x :: xs, d :: ds, j0, c, c', hr => by
    simp only [checkJ, Interp.counting_bind, Interp.counting_pure, Interp.counting_sub, Interp.counting_lt,
      Interp.counting_muladd, Interp.counting_zero, CostM.run_bind] at hr
    split at hr
    · rename_i rest c1 hrest
      intro i hi hd hne
      cases i with
      | zero =>
        split at hr
        · omega
        · simp only [Interp.counting_bind, Interp.counting_pure, CostM.run_bind, qsub_run, qlt_run, qmuladd_run,
            Interp.counting_band_run, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨hb, -⟩ := hr
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
          obtain ⟨⟨h1, h2⟩, -⟩ := hb
          simp only [List.getD_cons_zero]
          refine ⟨h1, ?_⟩
          simpa using h2
      | succ i =>
        have hrest' : (checkJ Interp.counting lo1 hi0 Xb base b xs ds (j0 + 1)).run env c = some (true, c1) := by
          split at hr
          · simp only [Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at hr; rw [hrest, hr.1]
          · simp only [Interp.counting_bind, Interp.counting_pure, CostM.run_bind, qsub_run, qlt_run, qmuladd_run,
              Interp.counting_band_run, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨hb, -⟩ := hr
            simp only [Bool.and_eq_true] at hb
            rw [hrest, hb.2]
        have := checkJ_run env lo1 hi0 Xb base b xs ds (j0 + 1) c c1 hrest' i (by simpa using hi) (by simpa using hd)
          (by omega)
        rw [List.getD_cons_succ, List.getD_cons_succ]
        exact this
    · cases hr
  | [], ds, j0, c, c', hr => by intro i hi; simp at hi
  | x :: xs, [], j0, c, c', hr => by intro i hi hd; simp at hd

end Candidate.FarRun
