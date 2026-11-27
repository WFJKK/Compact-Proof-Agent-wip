import Candidate.LibCubicChecker
import Candidate.LibAttnSound

/-!
# What the checker of entry 7 computes, and what it costs

Each function of the checker, run by the counting interpreter, as a `Runs`: its value (a function
of the values it is given) and its exact number of operations. The values are stated as plainly as
the checker computes them; the inequalities they satisfy are in `Sound.lean`.
-/

namespace GrossCubic

open CompactCheck Common AttnClasses Finset

variable {env : Env}

/-! ## Single operations -/

theorem runs_le (cat : String) (a b : Q) :
    Runs (CostM.qle cat a b) env (decide (a.val ≤ b.val)) 1 :=
  fun c => ⟨c.add cat 1, rfl, CompactCheck.Cost.total_add _ _ _⟩

theorem runs_selectV (cat : String) (b : Bool) (x y : Q) :
    Runs (Interp.counting.selectV cat b x y) env (cond b x y) 1 :=
  fun c => ⟨c.add cat 1, rfl, CompactCheck.Cost.total_add _ _ _⟩

/-! ## Largest entries and sums -/

/-- The value of `maxL`. -/
def maxLV : List Q → Q
  | [] => ⟨0⟩
  | a :: rs => ⟨rs.foldl (fun s v => max s v.val) a.val⟩

/-- The value of `sumL`. -/
def sumLV : List Q → Q
  | [] => ⟨0⟩
  | a :: rs => ⟨rs.foldl (fun s v => s + v.val) a.val⟩

theorem foldl_Q (F : ℚ → ℚ → ℚ) : ∀ (rs : List Q) (a : Q),
    rs.foldl (fun s v => (⟨F s.val v.val⟩ : Q)) a = ⟨rs.foldl (fun s v => F s v.val) a.val⟩
  | [], _ => rfl
  | r :: rs, a => by simp only [List.foldl_cons]; exact foldl_Q F rs _

theorem runs_maxL (l : List Q) :
    Runs (maxL Interp.counting l) env (maxLV l) (l.length - 1) := by
  cases l with
  | nil => exact Runs.pure _
  | cons a rs =>
    unfold maxL maxLV
    refine (runs_foldlM (g := fun s v => (⟨max s.val v.val⟩ : Q)) (c := fun _ => 1) rs a
      fun s v _ => runs_max cat s v).congr (foldl_Q _ rs a) ?_
    simp

theorem runs_sumL (l : List Q) :
    Runs (sumL Interp.counting l) env (sumLV l) (l.length - 1) := by
  cases l with
  | nil => exact Runs.pure _
  | cons a rs =>
    unfold sumL sumLV
    refine (runs_foldlM (g := fun s v => (⟨s.val + v.val⟩ : Q)) (c := fun _ => 1) rs a
      fun s v _ => runs_add cat s v).congr (foldl_Q _ rs a) ?_
    simp

theorem le_foldl_max : ∀ (rs : List Q) (a : ℚ), a ≤ rs.foldl (fun s v => max s v.val) a
  | [], _ => le_rfl
  | r :: rs, a => le_trans (le_max_left a r.val) (le_foldl_max rs _)

theorem mem_le_foldl_max : ∀ (rs : List Q) (a : ℚ) {v : Q}, v ∈ rs →
    v.val ≤ rs.foldl (fun s v => max s v.val) a
  | r :: rs, a, v, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right _ _) (le_foldl_max rs _)
    · exact mem_le_foldl_max rs _ h

/-- Every entry is at most `maxL`'s value. -/
theorem le_maxLV : ∀ {l : List Q} {v : Q}, v ∈ l → v.val ≤ (maxLV l).val
  | a :: rs, v, h => by
    unfold maxLV
    rcases List.mem_cons.mp h with rfl | h
    · exact le_foldl_max rs _
    · exact mem_le_foldl_max rs _ h

theorem foldl_add_val : ∀ (rs : List Q) (a : ℚ),
    rs.foldl (fun s v => s + v.val) a = a + (rs.map (·.val)).sum
  | [], a => by simp
  | r :: rs, a => by
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add_val rs]
    ring

/-- `sumL` adds up its list. -/
theorem sumLV_val (l : List Q) : (sumLV l).val = (l.map (·.val)).sum := by
  cases l with
  | nil => rfl
  | cons a rs => simp [sumLV, foldl_add_val]

/-! ## Bounds on products -/

/-- The value of `kup`. -/
def kupV (b : Q × Q) (y : Q) : Q := ⟨max (0 + b.1.val * y.val) (0 + b.2.val * y.val)⟩

theorem runs_kup (b : Q × Q) (y : Q) : Runs (kup Interp.counting b y) env (kupV b y) 3 := by
  unfold kup
  simp only [Interp.counting_bind]
  exact Runs.bind' (runs_muladd cat _ _ _) (Runs.bind' (runs_muladd cat _ _ _)
    (runs_max cat _ _) rfl rfl) rfl rfl

/-- `kup` bounds `e y` for every `e` between the bounds. -/
theorem kupV_ge {b : Q × Q} {y : Q} {e : ℝ} (hlo : (b.1.val : ℝ) ≤ e) (hhi : e ≤ b.2.val) :
    e * y.val ≤ ((kupV b y).val : ℝ) := by
  unfold kupV
  push_cast
  simp only [zero_add]
  rcases le_or_gt 0 (y.val : ℝ) with hy | hy
  · exact le_trans (mul_le_mul_of_nonneg_right hhi hy) (le_max_right _ _)
  · exact le_trans (mul_le_mul_of_nonpos_right hlo hy.le) (le_max_left _ _)

/-- The value of `prodB`. -/
def prodBV (a b : Q × Q) : Q × Q :=
  (⟨0 + max 0 a.1.val * max 0 b.1.val⟩, ⟨0 + a.2.val * b.2.val⟩)

theorem runs_prodB (a b : Q × Q) : Runs (prodB Interp.counting a b) env (prodBV a b) 4 := by
  unfold prodB
  simp only [Interp.counting_bind]
  exact Runs.bind' (runs_max cat _ _) (Runs.bind' (runs_max cat _ _)
    (Runs.bind' (runs_muladd cat _ _ _) (Runs.bind' (runs_muladd cat _ _ _) (Runs.pure _)
      rfl rfl) rfl rfl) rfl rfl) (by simp [prodBV]) rfl

/-- `prodB` bounds the product of two positive numbers from bounds on each. -/
theorem prodBV_bounds {a b : Q × Q} {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hax : (a.1.val : ℝ) ≤ x) (hxa : x ≤ a.2.val) (hby : (b.1.val : ℝ) ≤ y) (hyb : y ≤ b.2.val) :
    ((prodBV a b).1.val : ℝ) ≤ x * y ∧ x * y ≤ (prodBV a b).2.val := by
  unfold prodBV
  push_cast
  simp only [zero_add]
  constructor
  · exact mul_le_mul (max_le hx.le hax) (max_le hy.le hby) (le_max_left _ _) hx.le
  · exact mul_le_mul hxa hyb hy.le (hx.le.trans hxa)

/-- The value of `term`. -/
def termV (w : Q × Q) (a v c : Q) : Q := kupV w ⟨a.val + v.val - c.val⟩

theorem runs_term (w : Q × Q) (a v c : Q) :
    Runs (term Interp.counting w a v c) env (termV w a v c) 5 := by
  unfold term
  simp only [Interp.counting_bind]
  exact Runs.bind' (runs_add cat _ _) (Runs.bind' (runs_sub cat _ _) (runs_kup _ _) rfl rfl)
    rfl rfl


/-! ## The outputs other than the largest token -/

theorem mem_others {V m j : ℕ} : j ∈ others V m ↔ j < V ∧ j ≠ m := by
  simp [others, List.mem_filter]

theorem length_others {V m : ℕ} (hm : m < V) : (others V m).length = V - 1 := by
  unfold others
  have h := List.length_eq_length_filter_add (l := List.range V) (fun j => j != m)
  have h1 : ((List.range V).filter fun j => !(j != m)).length = 1 := by
    have e : ((List.range V).filter fun j => !(j != m)) = (List.range V).filter (· == m) := by
      congr 1; funext j; simp [bne]
    rw [e, ← List.count_eq_length_filter]
    exact List.count_eq_one_of_mem (List.nodup_range) (List.mem_range.mpr hm)
  simp only [List.length_range] at h
  omega

/-! ## The positional path, pessimised -/

/-- The value of `ppess`. -/
def ppessV (V n m : ℕ) (PV : List (List Q)) : List Q :=
  (List.range V).map fun j => maxLV ((List.range n).map fun p =>
    (⟨(at2 Interp.counting PV p j).val - (at2 Interp.counting PV p m).val⟩ : Q))

theorem runs_ppess (V n m : ℕ) (PV : List (List Q)) :
    Runs (ppess Interp.counting V n m PV) env (ppessV V n m PV) (V * (n + (n - 1))) := by
  unfold ppess ppessV
  refine (runs_mapM (c := fun _ => n + (n - 1)) _ fun j _ => ?_).congr rfl (by simp)
  simp only [Interp.counting_bind]
  exact Runs.bind' (runs_mapM (c := fun _ => 1) _ fun p _ => runs_sub cat _ _) (runs_maxL _)
    rfl (by simp)

/-! ## The direct path's and the keys' bounds -/

/-- The value of `dirU`. -/
def dirUV (V m t : ℕ) (EU : List (List Q)) : Q :=
  ⟨(maxLV ((others V m).map fun j => at2 Interp.counting EU t j)).val -
    (at2 Interp.counting EU t m).val⟩

theorem runs_dirU (V m t : ℕ) (EU : List (List Q)) :
    Runs (dirU Interp.counting V m t EU) env (dirUV V m t EU)
      ((others V m).length - 1 + 1) := by
  unfold dirU
  simp only [Interp.counting_bind]
  exact Runs.bind' (runs_maxL _) (runs_sub cat _ _) rfl (by simp)

/-- The value of `keyE`. -/
def keyEV (V m t : ℕ) (EV : List (List Q)) (Pp : List Q) : Q :=
  ⟨(maxLV ((others V m).map fun j =>
    (⟨(at2 Interp.counting EV t j).val + (Pp.getD j ⟨0⟩).val⟩ : Q))).val -
    (at2 Interp.counting EV t m).val⟩

theorem runs_keyE (V m t : ℕ) (EV : List (List Q)) (Pp : List Q) :
    Runs (keyE Interp.counting V m t EV Pp) env (keyEV V m t EV Pp)
      ((others V m).length + ((others V m).length - 1) + 1) := by
  unfold keyE
  simp only [Interp.counting_bind]
  exact Runs.bind' (runs_mapM (c := fun _ => 1) _ fun j _ => runs_add cat _ _)
    (Runs.bind' (runs_maxL _) (runs_sub cat _ _) rfl rfl) rfl (by simp; omega)

/-! ## The inputs without a non-maximal token -/

/-- The value of `onlyMax`. -/
def onlyMaxV (V m : ℕ) (EU EV : List (List Q)) (Pp : List Q) : Bool :=
  decide ((maxLV ((others V m).map fun j =>
      (⟨(at2 Interp.counting EU m j).val + (at2 Interp.counting EV m j).val +
        (Pp.getD j ⟨0⟩).val⟩ : Q))).val <
    (at2 Interp.counting EU m m).val + (at2 Interp.counting EV m m).val)

theorem runs_onlyMax (V m : ℕ) (EU EV : List (List Q)) (Pp : List Q) :
    Runs (onlyMax Interp.counting V m EU EV Pp) env (onlyMaxV V m EU EV Pp)
      (2 * (others V m).length + ((others V m).length - 1) + 2) := by
  unfold onlyMax
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_mapM (c := fun _ => 2) _ fun j _ =>
    Runs.bind' (runs_add cat _ _) (runs_add cat _ _) rfl rfl)
    (Runs.bind' (runs_maxL _) (Runs.bind' (runs_add cat _ _) (runs_lt cat _ _) rfl rfl) rfl rfl)
    ?_ (by simp; ring)
  simp [onlyMaxV]

/-- The value of `queryOnly`. -/
def queryOnlyV (V n m q : ℕ) (EU EV : List (List Q)) (Pp : List Q)
    (XE XP : List (List (Q × Q))) : Bool :=
  let slo := sumLV ((List.range (n - 1)).map fun p => (bt2 Interp.counting XP q p).1)
  let shi := sumLV ((List.range (n - 1)).map fun p => (bt2 Interp.counting XP q p).2)
  let wm := prodBV (bt2 Interp.counting XE q m) (slo, shi)
  let wq := prodBV (bt2 Interp.counting XE q q) (bt2 Interp.counting XP q (n - 1))
  let c1 : Q := ⟨(at2 Interp.counting EU q m).val + (at2 Interp.counting EV m m).val⟩
  let c2 : Q := ⟨(at2 Interp.counting EU q m).val + (at2 Interp.counting EV q m).val⟩
  decide ((maxLV ((others V m).map fun j =>
    (⟨(termV wm ⟨(at2 Interp.counting EU q j).val + (Pp.getD j ⟨0⟩).val⟩
        (at2 Interp.counting EV m j) c1).val +
      (termV wq ⟨(at2 Interp.counting EU q j).val + (Pp.getD j ⟨0⟩).val⟩
        (at2 Interp.counting EV q j) c2).val⟩ : Q))).val < 0)

/-- The cost of `queryOnly`. -/
def queryOnlyCost (V n : ℕ) : ℕ :=
  2 * (n - 1 - 1) + 4 + 4 + 2 + 12 * (V - 1) + (V - 1 - 1) + 1

theorem runs_queryOnly {V n m q : ℕ} (hm : m < V) (EU EV : List (List Q)) (Pp : List Q)
    (XE XP : List (List (Q × Q))) :
    Runs (queryOnly Interp.counting V n m q EU EV Pp XE XP) env
      (queryOnlyV V n m q EU EV Pp XE XP) (queryOnlyCost V n) := by
  unfold queryOnly
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_sumL _) (Runs.bind' (runs_sumL _) (Runs.bind' (runs_prodB _ _)
    (Runs.bind' (runs_prodB _ _) (Runs.bind' (runs_add cat _ _) (Runs.bind' (runs_add cat _ _)
    (Runs.bind' (runs_mapM (c := fun _ => 12) _ fun j _ =>
      Runs.bind' (runs_add cat _ _) (Runs.bind' (runs_term _ _ _ _)
        (Runs.bind' (runs_term _ _ _ _) (runs_add cat _ _) rfl rfl) rfl rfl) rfl rfl)
    (Runs.bind' (runs_maxL _) (runs_lt cat _ _) rfl rfl) rfl rfl) rfl rfl) rfl rfl) rfl rfl)
    rfl rfl) rfl rfl) rfl ?_
  simp only [List.length_map, List.length_range, sum_map_const', length_others hm, queryOnlyCost]
  omega

/-! ## The inputs with non-maximal tokens -/

/-- The patterns of `c` bits among `L`. -/
def patsOf (L c : ℕ) : List ℕ :=
  (List.range (Nat.pow 2 L)).filter fun pat => (inPat L pat).length == c

/-- The value of `kverd`. -/
def kverdV (n : ℕ) (qb : Q) (pk pm : List Q) (ncs : ℕ) : List Bool :=
  (List.range ncs).map fun c' => decide (qb.val + (maxLV ((patsOf (n - 1) (c' + 1)).map fun pat =>
    sumLV ((inPat (n - 1) pat).map fun p =>
      (((List.range (n - 1)).map fun p =>
        (⟨(pk.getD p ⟨0⟩).val - (pm.getD p ⟨0⟩).val⟩ : Q)).getD p ⟨0⟩)))).val < 0)

/-- The cost of `kverd`. -/
def kverdCost (n ncs : ℕ) : ℕ :=
  (n - 1) + ((List.range (Nat.pow 2 (n - 1))).map fun pat => (inPat (n - 1) pat).length - 1).sum +
    ((List.range ncs).map fun c' => (patsOf (n - 1) (c' + 1)).length - 1 + 2).sum

theorem runs_kverd (n : ℕ) (qb : Q) (pk pm : List Q) (ncs : ℕ) :
    Runs (kverd Interp.counting n qb pk pm ncs) env (kverdV n qb pk pm ncs) (kverdCost n ncs) := by
  unfold kverd
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_mapM (c := fun _ => 1) _ fun p _ => runs_sub cat _ _)
    (Runs.bind' (runs_mapM _ fun pat _ => runs_sumL _)
      (runs_mapM (c := fun c' => (patsOf (n - 1) (c' + 1)).length - 1 + 2) _ fun c' _ =>
        Runs.bind' (runs_maxL _) (Runs.bind' (runs_add cat _ _) (runs_lt cat _ _) rfl rfl) rfl
          (by simp [patsOf])) rfl rfl) ?_ ?_
  · unfold kverdV patsOf
    refine List.map_congr_left fun c' _ => ?_
    refine congrArg (fun L : List Q => decide (qb.val + (maxLV L).val < 0)) ?_
    refine List.map_congr_left fun pat hpat => ?_
    have hp : pat < 2 ^ (n - 1) := List.mem_range.mp (List.mem_filter.mp hpat).1
    simp [List.getD_eq_getElem?_getD, hp]
  · simp only [kverdCost, sum_map_const', List.length_range, List.length_map]
    omega

/-- The value of `patCount`. -/
def patCountV (lam c' : ℕ) (vs : List Bool) (one : Q) (js : List Q) : ℕ :=
  if c' = 0 then vs.foldl (fun a b => a + cond b 1 0) 0
  else (List.range lam).foldl (fun a i => a + cond
    ((((List.range lam).map fun i => decide ((js.getD i ⟨0⟩).val ≤
      (sumLV (vs.map fun b => cond b one ⟨0⟩)).val)).getD i false))
    (Nat.pow (i + 1) (c' + 1) - Nat.pow i (c' + 1)) 0) 0

/-- The cost of `patCount`. -/
def patCountCost (lam c' L : ℕ) : ℕ := if c' = 0 then 0 else L + (L - 1) + lam

theorem runs_patCount (lam c' : ℕ) (vs : List Bool) (one : Q) (js : List Q) :
    Runs (patCount Interp.counting lam c' vs one js) env (patCountV lam c' vs one js)
      (patCountCost lam c' vs.length) := by
  unfold patCount patCountV patCountCost
  by_cases h : c' = 0
  · simp only [h, ↓reduceIte]
    exact (Runs.pure _).congr rfl rfl
  · simp only [h, ↓reduceIte, Interp.counting_bind]
    refine Runs.bind' (runs_mapM (c := fun _ => 1) _ fun b _ => runs_selectV cat _ _ _)
      (Runs.bind' (runs_sumL _) (Runs.bind' (runs_mapM (c := fun _ => 1) _ fun i _ =>
        runs_le cat _ _) (Runs.pure _) rfl rfl) rfl rfl) rfl ?_
    simp
    omega

/-- The values `φ` of `withNonmax`, one per rank up to `lam`. -/
def phisV (mx : Bool) (V lam rq : ℕ) (us ks : List Q) (XE : List (List (Q × Q))) : List Q :=
  (List.range (lam + 1)).map fun r =>
    kupV (bt2 Interp.counting XE (tok mx V rq) (tok mx V r))
      ⟨(ks.getD r ⟨0⟩).val + (us.getD rq ⟨0⟩).val⟩

/-- The values `ψ` of `withNonmax`, per rank up to `lam` and position other than the query's. -/
def psisV (mx : Bool) (V n lam rq : ℕ) (us ks : List Q) (XE XP : List (List (Q × Q))) :
    List (List Q) :=
  (List.range (lam + 1)).map fun r => (List.range (n - 1)).map fun p =>
    kupV (bt2 Interp.counting XP (tok mx V rq) p) ((phisV mx V lam rq us ks XE).getD r ⟨0⟩)

/-- The query's term, `ψ` of its rank at its position. -/
def psiqV (mx : Bool) (V n lam rq : ℕ) (us ks : List Q) (XE XP : List (List (Q × Q))) : Q :=
  kupV (bt2 Interp.counting XP (tok mx V rq) (n - 1)) ((phisV mx V lam rq us ks XE).getD rq ⟨0⟩)

/-- `qb`: the largest token's terms at the positions other than the query's, and the query's. -/
def qbV (mx : Bool) (V n lam rq : ℕ) (us ks : List Q) (XE XP : List (List (Q × Q))) : Q :=
  ⟨(sumLV ((psisV mx V n lam rq us ks XE XP).getD lam [])).val +
    (psiqV mx V n lam rq us ks XE XP).val⟩

/-- The largest number of positions, other than the query's, that can hold a non-maximal token. -/
def ncsOf (n lam rq : ℕ) : ℕ := if rq = lam then n - 1 else n - 2

/-- The verdicts of `withNonmax`, per non-maximal rank. -/
def verdV (mx : Bool) (V n lam rq : ℕ) (us ks : List Q) (XE XP : List (List (Q × Q))) :
    List (List Bool) :=
  (List.range lam).map fun kappa => kverdV n (qbV mx V n lam rq us ks XE XP)
    ((psisV mx V n lam rq us ks XE XP).getD kappa [])
    ((psisV mx V n lam rq us ks XE XP).getD lam []) (ncsOf n lam rq)

/-- The counts of `withNonmax`, per number of positions holding a non-maximal token. -/
def cntsV (mx : Bool) (V n lam rq : ℕ) (us ks : List Q) (XE XP : List (List (Q × Q)))
    (one : Q) (js : List Q) : List ℕ :=
  (List.range (ncsOf n lam rq)).map fun c' =>
    patCountV lam c' ((verdV mx V n lam rq us ks XE XP).map fun l => l.getD c' false) one js

/-- The value of `withNonmax`. -/
def withNonmaxV (mx : Bool) (V n lam rq : ℕ) (us ks : List Q) (XE XP : List (List (Q × Q)))
    (one : Q) (js : List Q) : ℕ :=
  (List.range (Nat.pow 2 (n - 1))).foldl (fun a pat =>
    a + (0 :: cntsV mx V n lam rq us ks XE XP one js).getD (inPat (n - 1) pat).length 0) 0

/-- The cost of `withNonmax`. -/
def withNonmaxCost (n lam ncs : ℕ) : ℕ :=
  (lam + 1) * 4 + (lam + 1) * ((n - 1) * 3) + 3 + (n - 1 - 1) + 1 + lam * kverdCost n ncs +
    ((List.range ncs).map fun c' => patCountCost lam c' lam).sum

theorem runs_withNonmax (mx : Bool) (V n lam rq : ℕ) (us ks : List Q)
    (XE XP : List (List (Q × Q))) (one : Q) (js : List Q) :
    Runs (withNonmax Interp.counting mx V n lam rq us ks XE XP one js) env
      (withNonmaxV mx V n lam rq us ks XE XP one js) (withNonmaxCost n lam (ncsOf n lam rq)) := by
  unfold withNonmax
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_mapM (c := fun _ => 4) _ fun r _ =>
      Runs.bind' (runs_add cat _ _) (runs_kup _ _) rfl rfl)
    (Runs.bind' (runs_mapM (c := fun _ => (n - 1) * 3) _ fun r _ =>
        (runs_mapM (c := fun _ => 3) _ fun p _ => runs_kup _ _).congr rfl (by simp))
      (Runs.bind' (runs_kup _ _) (Runs.bind' (runs_sumL _) (Runs.bind' (runs_add cat _ _)
        (Runs.bind' (runs_mapM (c := fun _ => kverdCost n (ncsOf n lam rq)) _ fun kappa _ =>
            runs_kverd _ _ _ _ _)
          (Runs.bind' (runs_mapM _ fun c' _ => runs_patCount _ _ _ _ _) (Runs.pure _) rfl rfl)
          rfl rfl) rfl rfl) rfl rfl) rfl rfl) rfl rfl) ?_ ?_
  · rfl
  · simp [List.getD_eq_getElem?_getD, withNonmaxCost, ncsOf]
    ring

/-! ## A block: the inputs of one largest token -/

/-- The value of `block`. -/
def blockV (mx : Bool) (V n : ℕ) (EU EV PV : List (List Q)) (XE XP : List (List (Q × Q)))
    (one : Q) (js : List Q) (lam : ℕ) : ℕ :=
  ((List.range (lam + 1)).map fun rq => withNonmaxV mx V n lam rq
      ((List.range (lam + 1)).map fun r => dirUV V (tok mx V lam) (tok mx V r) EU)
      ((List.range (lam + 1)).map fun r =>
        keyEV V (tok mx V lam) (tok mx V r) EV (ppessV V n (tok mx V lam) PV))
      XE XP one js).foldl Nat.add
    (((List.range lam).map fun rq => queryOnlyV V n (tok mx V lam) (tok mx V rq) EU EV
        (ppessV V n (tok mx V lam) PV) XE XP).foldl (fun a b => a + cond b 1 0)
      (cond (onlyMaxV V (tok mx V lam) EU EV (ppessV V n (tok mx V lam) PV)) 1 0))

/-- The cost of `block`. -/
def blockCost (V n lam : ℕ) : ℕ :=
  V * (n + (n - 1)) + (lam + 1) * (V - 1 - 1 + 1) + (lam + 1) * (V - 1 + (V - 1 - 1) + 1) +
    (2 * (V - 1) + (V - 1 - 1) + 2) + lam * queryOnlyCost V n +
    ((List.range (lam + 1)).map fun rq => withNonmaxCost n lam (ncsOf n lam rq)).sum

theorem runs_block (mx : Bool) {V : ℕ} (n : ℕ) (EU EV PV : List (List Q))
    (XE XP : List (List (Q × Q))) (one : Q) (js : List Q) {lam : ℕ} (hlam : lam < V) :
    Runs (block Interp.counting mx V n EU EV PV XE XP one js lam) env
      (blockV mx V n EU EV PV XE XP one js lam) (blockCost V n lam) := by
  have hm : tok mx V lam < V := tok_lt hlam
  unfold block
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_ppess _ _ _ _) (Runs.bind' (runs_mapM _ fun r _ => runs_dirU _ _ _ _)
    (Runs.bind' (runs_mapM _ fun r _ => runs_keyE _ _ _ _ _)
      (Runs.bind' (runs_onlyMax _ _ _ _ _)
        (Runs.bind' (runs_mapM (c := fun _ => queryOnlyCost V n) _ fun rq _ =>
            runs_queryOnly hm _ _ _ _ _)
          (Runs.bind' (runs_mapM _ fun rq _ => runs_withNonmax _ _ _ _ _ _ _ _ _ _ _)
            (Runs.pure _) rfl rfl) rfl rfl) rfl rfl) rfl rfl) rfl rfl) rfl ?_
  simp only [List.length_range, sum_map_const', length_others hm, blockCost]
  ring

/-! ## Bounds on `exp` -/

/-- The bounds `exp` gives on every entry of the table `mat m k f` (zero where it refuses). -/
def expMat (m k : ℕ) (f : ℕ → ℕ → ℚ) : List (List (Q × Q)) :=
  (List.range m).map fun i => (List.range k).map fun j => expPair (f i j)

theorem runs_exp1 {s : Q} (h : (expInterval s.val).isSome) :
    Runs (Interp.counting.exp cat s) env (expPair s.val) 3 := by
  obtain ⟨⟨lo, hi⟩, hlh⟩ := Option.isSome_iff_exists.mp h
  intro c
  refine ⟨c.add cat 3, ?_, CompactCheck.Cost.total_add _ _ _⟩
  simp [CostM.qexp, hlh, expPair]

theorem sat_exp1 (s : Q) :
    Sat (Interp.counting.exp cat s) env (fun b => expInterval s.val = some (b.1.val, b.2.val)) := by
  intro c b c' hr
  simp only [CostM.qexp] at hr
  split at hr
  · rename_i lo hi hlh
    simp only [Option.some.injEq, Prod.mk.injEq] at hr
    rw [← hr.1]
    exact hlh
  · cases hr

theorem runs_expT (m k : ℕ) (f : ℕ → ℕ → ℚ) (h : ∀ i < m, ∀ j < k, (expInterval (f i j)).isSome) :
    Runs (expT Interp.counting (mat m k f)) env (expMat m k f) (m * (k * 3)) := by
  unfold expT mat
  refine (runs_mapM (g := fun r => r.map fun s => expPair s.val) (c := fun _ => k * 3) _
    fun r hr => ?_).congr ?_ (by simp [Function.comp_def])
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    refine (runs_mapM (c := fun _ => 3) _ fun s hs => ?_).congr rfl (by simp [Function.comp_def])
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
    exact runs_exp1 (h i (List.mem_range.mp hi) j (List.mem_range.mp hj))
  · simp [expMat, Function.comp_def]

/-- What a run of `expT` that succeeds returns: at `(i, j)`, the bounds `exp` gives on `f i j`. -/
theorem sat_expT (m k : ℕ) (f : ℕ → ℕ → ℚ) :
    Sat (expT Interp.counting (mat m k f)) env (fun X => ∀ i < m, ∀ j < k,
      expInterval (f i j) =
        some ((bt2 Interp.counting X i j).1.val, (bt2 Interp.counting X i j).2.val)) := by
  unfold expT mat
  refine (sat_mapM _ fun r _ => sat_mapM _ fun s _ => sat_exp1 s).mono ?_
  intro X hX i hi j hj
  obtain ⟨hl1, hg1⟩ := AttnClasses.forall₂_get hX
  have hi1 : i < X.length := by rw [hl1]; simpa using hi
  have h1 := hg1 i (by simpa using hi) hi1
  simp only [List.getElem_map, List.getElem_range] at h1
  obtain ⟨hl2, hg2⟩ := AttnClasses.forall₂_get h1
  have hj2 : j < X[i].length := by rw [hl2]; simpa using hj
  have h2 := hg2 j (by simpa using hj) hj2
  simp only [List.getElem_map, List.getElem_range] at h2
  unfold bt2
  rw [getD_of_lt hi1, getD_of_lt hj2]
  exact h2

end GrossCubic
