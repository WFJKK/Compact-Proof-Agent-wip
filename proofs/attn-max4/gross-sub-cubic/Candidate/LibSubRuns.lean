import Candidate.LibSubChecker
import Candidate.LibSubPsd
import Candidate.LibSubSort
import Candidate.LibCubicRuns

/-!
# What the checker of entry 9 computes, and what it costs

Each function of the checker, run by the counting interpreter, as a `Runs`: its value, as a
matrix `mat m k f` or vector `vec k f` of a closed form, and its exact number of operations. The
facts the values satisfy are in `Lin.lean`, `Psd.lean`, `Sort.lean` and `Sound.lean`.
-/

namespace GrossSub

open CompactCheck Common AttnClasses GrossCubic Finset

variable {env : Env}

/-! ## Single operations -/

theorem runs_neg (cat : String) (a : Q) : Runs (CostM.qneg cat a) env ⟨-a.val⟩ 1 :=
  fun c => ⟨c.add cat 1, rfl, CompactCheck.Cost.total_add _ _ _⟩

theorem runs_bor (cat : String) (a b : Bool) :
    Runs (Interp.counting.bor cat a b) env (a || b) 1 :=
  fun c => ⟨c.add cat 1, rfl, CompactCheck.Cost.total_add _ _ _⟩

/-- The certificate's number `i`, zero past its end. -/
def certAt (env : Env) (i : ℕ) : ℚ := env.cert.getD i 0

theorem runs_cert {i : ℕ} (h : i < env.cert.size) : Runs (CostM.cert i) env ⟨certAt env i⟩ 0 := by
  intro c
  refine ⟨c, ?_, by simp⟩
  -- CompactCheck at eab37d3 reads the certificate through a balanced tree (policy v10); its lemma gives the read.
  rw [CostM.cert_run_of_lt c h]
  simp [certAt, Array.getD, h]

theorem runs_certSize : Runs (CostM.certSize) env env.cert.size 0 := fun c => ⟨c, rfl, by simp⟩

/-! ## Vectors and matrices -/

theorem getD_vec' {k : ℕ} {f : ℕ → ℚ} {a : ℕ} (ha : a < k) :
    (vec k f).getD a (⟨0⟩ : Q) = ⟨f a⟩ := getD_vec ha _

theorem at1_vec {k : ℕ} {f : ℕ → ℚ} {a : ℕ} (ha : a < k) :
    at1 Interp.counting (vec k f) a = ⟨f a⟩ := getD_vec ha _

theorem at2_mat' {m k : ℕ} {f : ℕ → ℕ → ℚ} {i j : ℕ} (hi : i < m) (hj : j < k) :
    at2 Interp.counting (mat m k f) i j = ⟨f i j⟩ := by
  -- by `change`, not by unfolding: `at2`'s equation lemma belongs to entry 7's modules
  change ((mat m k f).getD i []).getD j ⟨0⟩ = ⟨f i j⟩
  simp [mat, List.getD_eq_getElem?_getD, hi, hj]

/-- The transpose of a matrix of closed form. -/
theorem tr_mat (rows cols : ℕ) (f : ℕ → ℕ → ℚ) :
    tr Interp.counting cols (mat rows cols f) = mat cols rows fun j i => f i j := by
  unfold tr mat
  refine List.map_congr_left fun j hj => ?_
  rw [List.map_map]
  refine List.map_congr_left fun i _ => ?_
  simp only [Function.comp_apply]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (List.mem_range.mp hj)]
  rfl

theorem runs_certVec (off k : ℕ) (h : off + k ≤ env.cert.size) :
    Runs (certVec Interp.counting off k) env (vec k fun i => certAt env (off + i)) 0 := by
  unfold certVec
  exact (runs_mapM (c := fun _ => 0) _ fun i hi =>
    runs_cert (by have := List.mem_range.mp hi; omega)).congr rfl (by simp)

theorem runs_certMat (off rows cols : ℕ) (h : off + rows * cols ≤ env.cert.size) :
    Runs (certMat Interp.counting off rows cols) env
      (mat rows cols fun i j => certAt env (off + i * cols + j)) 0 := by
  unfold certMat
  refine (runs_mapM (c := fun _ => 0) _ fun i hi => runs_certVec _ _ ?_).congr ?_ (by simp)
  · have hi' := List.mem_range.mp hi
    have : i * cols + cols ≤ rows * cols := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hi'
    omega
  · rfl

/-! ## Smallest entries and spreads -/

/-- The value of `minL`. -/
def minLV : List Q → Q
  | [] => ⟨0⟩
  | a :: rs => ⟨rs.foldl (fun s v => min s v.val) a.val⟩

theorem runs_minL (l : List Q) :
    Runs (minL Interp.counting l) env (minLV l) (l.length - 1) := by
  cases l with
  | nil => exact Runs.pure _
  | cons a rs =>
    unfold minL minLV
    refine (runs_foldlM (g := fun s v => (⟨min s.val v.val⟩ : Q)) (c := fun _ => 1) rs a
      fun s v _ => runs_min cat s v).congr (foldl_Q _ rs a) ?_
    simp

theorem foldl_min_le : ∀ (rs : List Q) (a : ℚ), rs.foldl (fun s v => min s v.val) a ≤ a
  | [], _ => le_rfl
  | r :: rs, a => le_trans (foldl_min_le rs _) (min_le_left a r.val)

theorem foldl_min_le_mem : ∀ (rs : List Q) (a : ℚ) {v : Q}, v ∈ rs →
    rs.foldl (fun s v => min s v.val) a ≤ v.val
  | r :: rs, a, v, h => by
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (foldl_min_le rs _) (min_le_right _ _)
    · exact foldl_min_le_mem rs _ h

/-- `minL`'s value is at most every entry. -/
theorem minLV_le : ∀ {l : List Q} {v : Q}, v ∈ l → (minLV l).val ≤ v.val
  | a :: rs, v, h => by
    unfold minLV
    rcases List.mem_cons.mp h with rfl | h
    · exact foldl_min_le rs _
    · exact foldl_min_le_mem rs _ h

/-- The spread of `f` over `[0, k)`, as the checker computes it. -/
def spreadV (k : ℕ) (f : ℕ → ℚ) : ℚ := (maxLV (vec k f)).val - (minLV (vec k f)).val

theorem runs_spread (k : ℕ) (f : ℕ → ℚ) :
    Runs (spread Interp.counting (vec k f)) env ⟨spreadV k f⟩ (2 * (k - 1) + 1) := by
  unfold spread
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_maxL _) (Runs.bind' (runs_minL _) (runs_sub cat _ _) rfl rfl) rfl ?_
  simp only [length_vec]
  omega

theorem spreadV_ge (k : ℕ) (f : ℕ → ℚ) {i j : ℕ} (hi : i < k) (hj : j < k) :
    f i - f j ≤ spreadV k f := by
  unfold spreadV
  have h1 := le_maxLV (l := vec k f) (v := ⟨f i⟩) (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  have h2 := minLV_le (l := vec k f) (v := ⟨f j⟩) (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  simp only at h1 h2
  linarith

theorem runs_absV (x : Q) : Runs (absV Interp.counting x) env ⟨|x.val|⟩ 2 := by
  unfold absV
  simp only [Interp.counting_bind]
  exact Runs.bind' (runs_neg cat x) (runs_max cat _ _) (by rw [abs_eq_max_neg]) rfl

/-! ## Maps over the rows of a matrix -/

theorem runs_mapM_loop_map {α β γ : Type} {f : γ → Interp.counting.M β} {h : α → γ} {g : α → β}
    {c : α → ℕ} : ∀ (l : List α) (bs : List β), (∀ a ∈ l, Runs (f (h a)) env (g a) (c a)) →
      Runs (@List.mapM.loop Interp.counting.M (instMonadInterp Interp.counting) γ β f (l.map h) bs)
        env (bs.reverse ++ l.map g) (l.map c).sum
  | [], bs, _ => (Runs.pure _).congr (by simp) (by simp)
  | a :: l, bs, hh => by
    simp only [List.map_cons, List.mapM.loop, Interp.counting_bind]
    exact Runs.bind' (hh a List.mem_cons_self)
      (runs_mapM_loop_map l _ fun a' ha' => hh a' (List.mem_cons_of_mem _ ha')) (by simp) (by simp)

/-- A map over a mapped list: the steps' values and costs, by the original entries. -/
theorem runs_mapM_map {α β γ : Type} {f : γ → Interp.counting.M β} {h : α → γ} {g : α → β}
    {c : α → ℕ} (l : List α) (hh : ∀ a ∈ l, Runs (f (h a)) env (g a) (c a)) :
    Runs (@List.mapM Interp.counting.M (instMonadInterp Interp.counting) γ β f (l.map h)) env
      (l.map g) (l.map c).sum :=
  (runs_mapM_loop_map l [] hh).congr (by simp) rfl

/-- A map over the rows of a matrix, each step of cost `c`. -/
theorem runs_mapM_mat {β : Type} {f : List Q → Interp.counting.M β} {g : ℕ → β} {c : ℕ}
    (m k : ℕ) (F : ℕ → ℕ → ℚ) (hh : ∀ i < m, Runs (f (vec k (F i))) env (g i) c) :
    Runs (@List.mapM Interp.counting.M (instMonadInterp Interp.counting) (List Q) β f
      (mat m k F)) env ((List.range m).map g) (m * c) := by
  rw [mat_eq]
  exact (runs_mapM_map (c := fun _ => c) _ fun i hi => hh i (List.mem_range.mp hi)).congr rfl
    (by rw [sum_map_const', List.length_range])

/-- A map over `[0, m)`, each step of cost `c`. -/
theorem runs_mapM_range {β : Type} {f : ℕ → Interp.counting.M β} {g : ℕ → β} {c : ℕ}
    (m : ℕ) (hh : ∀ i < m, Runs (f i) env (g i) c) :
    Runs (@List.mapM Interp.counting.M (instMonadInterp Interp.counting) ℕ β f
      (List.range m)) env ((List.range m).map g) (m * c) :=
  (runs_mapM (c := fun _ => c) _ fun i hi => hh i (List.mem_range.mp hi)).congr rfl
    (by rw [sum_map_const', List.length_range])

/-! ## Products with vectors -/

theorem runs_subOuter (rows cols : ℕ) (A : List (List Q)) (u w : List Q) :
    Runs (subOuter Interp.counting rows cols A u w) env
      (mat rows cols fun i k => (at2 Interp.counting A i k).val -
        (at1 Interp.counting u i).val * (at1 Interp.counting w k).val) (rows * (1 + cols)) := by
  unfold subOuter
  rw [mat_eq]
  refine runs_mapM_range rows fun i _ => ?_
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_neg cat _) ?_ rfl rfl
  refine (runs_mapM_range cols fun k _ => (runs_muladd cat _ _ _)).congr ?_ (by ring)
  simp only [vec]
  refine List.map_congr_left fun k _ => ?_
  congr 1; ring

theorem runs_vecMat (rows cols : ℕ) (u : ℕ → ℚ) (A : ℕ → ℕ → ℚ) :
    Runs (vecMat Interp.counting cols (vec rows u) (mat rows cols A)) env
      (vec cols fun k => ∑ s ∈ range rows, u s * A s k) (cols * rows) := by
  unfold vecMat
  rw [tr_mat]
  exact (runs_mapM_mat cols rows _ fun k _ => runs_dot_vec rows u (fun s => A s k)).congr rfl rfl

theorem runs_matVec (rows k : ℕ) (A : ℕ → ℕ → ℚ) (v : ℕ → ℚ) :
    Runs (matVec Interp.counting (mat rows k A) (vec k v)) env
      (vec rows fun i => ∑ a ∈ range k, A i a * v a) (rows * k) := by
  unfold matVec
  exact (runs_mapM_mat rows k _ fun i _ => runs_dot_vec k (A i) v).congr rfl rfl

theorem runs_absDot (l a s : List Q) (k : ℕ) :
    Runs (absDot Interp.counting l a s k) env
      ⟨∑ i ∈ range k, |(at1 Interp.counting l i).val - (at1 Interp.counting a i).val| *
        (at1 Interp.counting s i).val⟩ (k * 4) := by
  unfold absDot
  refine (runs_foldlM (g := fun acc i => (⟨acc.val +
    |(at1 Interp.counting l i).val - (at1 Interp.counting a i).val| *
      (at1 Interp.counting s i).val⟩ : Q)) (c := fun _ => 4) _ _ fun acc i _ => ?_).congr ?_ ?_
  · simp only [Interp.counting_bind]
    exact Runs.bind' (runs_sub cat _ _) (Runs.bind' (runs_absV _) (runs_muladd cat _ _ _)
      rfl rfl) rfl rfl
  · apply Q_ext
    rw [foldl_acc, zero_add, sum_range_eq]
  · rw [sum_map_const', List.length_range]

/-- `absDot` on vectors. -/
theorem runs_absDot_vec (k : ℕ) (l a s : ℕ → ℚ) :
    Runs (absDot Interp.counting (vec k l) (vec k a) (vec k s) k) env
      ⟨∑ i ∈ range k, |l i - a i| * s i⟩ (k * 4) := by
  refine (runs_absDot _ _ _ k).congr ?_ rfl
  congr 1
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' := mem_range.mp hi
  rw [at1_vec hi', at1_vec hi', at1_vec hi']

/-- The cost of `rowBound`. -/
def rowBoundCost (rows k cols : ℕ) : ℕ :=
  k * (2 * (cols - 1) + 1) + (cols * k + ((2 * (cols - 1) + 1) + rows * (k * 4 + 1)))

theorem runs_rowBound (rows k cols : ℕ) (l r : ℕ → ℕ → ℚ) (a : ℕ → ℚ) :
    Runs (rowBound Interp.counting k cols (mat rows k l) (mat k cols r) (vec k a)) env
      (vec rows fun i => spreadV cols (fun t => ∑ b ∈ range k, a b * r b t) +
        ∑ b ∈ range k, |l i b - a b| * spreadV cols (r b)) (rowBoundCost rows k cols) := by
  unfold rowBound rowBoundCost
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_mapM_mat k cols r fun b _ => runs_spread cols (r b)) ?_ rfl rfl
  refine Runs.bind' (runs_vecMat k cols a r) ?_ rfl rfl
  refine Runs.bind' (runs_spread cols _) ?_ rfl rfl
  refine (runs_mapM_mat rows k l fun i _ => ?_).congr rfl rfl
  have e : (List.range k).map (fun b => (⟨spreadV cols (r b)⟩ : Q)) =
      vec k fun b => spreadV cols (r b) := rfl
  rw [e]
  exact Runs.bind' (runs_absDot_vec k (l i) a _) (runs_add cat _ _) (by simp) rfl

/-! ## Equal closed forms -/

theorem vec_congr {k : ℕ} {f g : ℕ → ℚ} (h : ∀ i < k, f i = g i) : vec k f = vec k g :=
  List.map_congr_left fun i hi => by rw [h i (List.mem_range.mp hi)]

theorem mat_congr {m k : ℕ} {f g : ℕ → ℕ → ℚ} (h : ∀ i < m, ∀ j < k, f i j = g i j) :
    mat m k f = mat m k g :=
  List.map_congr_left fun i hi => vec_congr fun j hj => h i (List.mem_range.mp hi) j hj

theorem runs_subOuter_mat (rows cols : ℕ) (A : ℕ → ℕ → ℚ) (u w : ℕ → ℚ) :
    Runs (subOuter Interp.counting rows cols (mat rows cols A) (vec rows u) (vec cols w)) env
      (mat rows cols fun i k => A i k - u i * w k) (rows * (1 + cols)) :=
  (runs_subOuter rows cols _ _ _).congr (mat_congr fun i hi k hk => by
    rw [at2_mat' hi hk, at1_vec hi, at1_vec hk]) rfl

/-! ## Their `split_SVD` -/

/-- `uᵀ A`. -/
def sUA (V : ℕ) (u : ℕ → ℚ) (A : ℕ → ℕ → ℚ) (k : ℕ) : ℚ := ∑ s ∈ range V, u s * A s k

/-- `A - u uᵀ A`. -/
def sAr (V : ℕ) (u : ℕ → ℚ) (A : ℕ → ℕ → ℚ) (q k : ℕ) : ℚ := A q k - u q * sUA V u A k

/-- `B v`. -/
def sBv (V : ℕ) (B : ℕ → ℕ → ℚ) (v : ℕ → ℚ) (k : ℕ) : ℚ := ∑ t ∈ range V, B k t * v t

/-- `B - B v vᵀ`. -/
def sBr (V : ℕ) (B : ℕ → ℕ → ℚ) (v : ℕ → ℚ) (k t : ℕ) : ℚ := B k t - sBv V B v k * v t

/-- `Ê = u (uᵀ A B) + (Ar B v) vᵀ`. -/
def sEh (V r : ℕ) (A B : ℕ → ℕ → ℚ) (u v : ℕ → ℚ) (q t : ℕ) : ℚ :=
  0 + u q * (∑ k ∈ range r, sUA V u A k * B k t) +
    (∑ k ∈ range r, sAr V u A q k * sBv V B v k) * v t

/-- The cost of `svdSplit`. -/
def svdSplitCost (V r : ℕ) : ℕ :=
  r * V + (V * (1 + r) + (r * V + (r * (1 + V) + (V * r + (V * r + V * (V * 2))))))

theorem runs_svdSplit (V r : ℕ) (A B : ℕ → ℕ → ℚ) (u v : ℕ → ℚ) :
    Runs (svdSplit Interp.counting V r (mat V r A) (mat r V B) (vec V u) (vec V v)) env
      (mat V V (sEh V r A B u v), mat V r (sAr V u A), mat r V (sBr V B v))
      (svdSplitCost V r) := by
  unfold svdSplit svdSplitCost
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_vecMat V r u A) ?_ rfl rfl
  refine Runs.bind' (runs_subOuter_mat V r A u _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec r V B v) ?_ rfl rfl
  refine Runs.bind' (runs_subOuter_mat r V B _ v) ?_ rfl rfl
  refine Runs.bind' (runs_vecMat r V _ B) ?_ rfl rfl
  refine Runs.bind' (runs_matVec V r _ _) ?_ rfl rfl
  refine Runs.bind' (runs_mapM_range V fun q hq => runs_mapM_range V fun t ht =>
    Runs.bind' (runs_muladd cat _ _ _) (runs_muladd cat _ _ _) rfl rfl) (Runs.pure _) ?_ (by ring)
  congr 1
  refine List.map_congr_left fun q hq => List.map_congr_left fun t ht => ?_
  have hq' := List.mem_range.mp hq
  have ht' := List.mem_range.mp ht
  rw [at1_vec hq', at1_vec ht', at1_vec hq', at1_vec ht']
  rfl

/-! ## The certified `svd` bound -/

/-- A sum over the entries of `[0, r)` that pass a test. -/
theorem sum_filter_range (p : ℕ → Bool) (g : ℕ → ℚ) : ∀ r : ℕ,
    (((List.range r).filter p).map g).sum = ∑ j ∈ range r, (if p j then g j else 0)
  | 0 => by simp
  | r + 1 => by
    rw [List.range_succ, List.filter_append, List.map_append, List.sum_append,
      sum_filter_range p g r, Finset.sum_range_succ]
    by_cases hp : p r <;> simp [hp]

theorem length_filter_ne {r i : ℕ} (hi : i < r) :
    ((List.range r).filter fun j => j != i).length = r - 1 := by
  have e : ((List.range r).filter fun j => j != i) = (List.range r).erase i := by
    rw [(List.nodup_range).erase_eq_filter]
  rw [e, List.length_erase_of_mem (List.mem_range.mpr hi), List.length_range]

/-- The remainder `X - F Fᵀ`. -/
def psdD (r : ℕ) (X F : ℕ → ℕ → ℚ) (i j : ℕ) : ℚ := X i j - ∑ l ∈ range r, F i l * F j l

/-- The off-diagonal row and column of the remainder, in absolute value. -/
def psdOff (r : ℕ) (X F : ℕ → ℕ → ℚ) (i : ℕ) : ℚ :=
  ∑ j ∈ range r, (if j = i then 0 else |psdD r X F i j| + |psdD r X F j i|)

/-- The value of `psdOk`. -/
def psdV (r : ℕ) (X F : ℕ → ℕ → ℚ) : Bool :=
  (List.range r).foldl (fun a i =>
    a && decide (psdOff r X F i ≤ psdD r X F i i + psdD r X F i i)) true

/-- The cost of `psdOk`. -/
def psdCost (r : ℕ) : ℕ := r * r * r + (r * (r * 1) + (r * (6 * (r - 1) + 2) + r))

theorem foldl_band_cost : ∀ (l : List Bool) (b : Bool),
    Runs (@List.foldlM Interp.counting.M (instMonadInterp Interp.counting) Bool Bool
      (fun a b => Interp.counting.band cat a b) b l) env (l.foldl (· && ·) b) l.length
  | [], b => (Runs.pure _).congr rfl rfl
  | x :: l, b => by
    simp only [List.foldlM_cons, Interp.counting_bind, List.foldl_cons, List.length_cons]
    exact Runs.bind' (runs_band cat b x) (foldl_band_cost l _) rfl (by ring)

theorem foldl_and_map (f : ℕ → Bool) : ∀ (l : List ℕ) (b : Bool),
    (l.map f).foldl (· && ·) b = l.foldl (fun a i => a && f i) b
  | [], _ => rfl
  | i :: l, b => by simp only [List.map_cons, List.foldl_cons]; exact foldl_and_map f l _

theorem runs_psdOk (r : ℕ) (X F : ℕ → ℕ → ℚ) :
    Runs (psdOk Interp.counting r (mat r r X) (mat r r F)) env (psdV r X F) (psdCost r) := by
  unfold psdOk psdCost
  simp only [Interp.counting_bind]
  refine Runs.bind' (runs_mm r r r F F) ?_ rfl rfl
  refine Runs.bind' (runs_mapM_range r fun i _ => runs_mapM_range r fun j _ =>
    runs_sub cat _ _) ?_ rfl rfl
  have hD : ((List.range r).map fun i => (List.range r).map fun j =>
      (⟨(at2 Interp.counting (mat r r X) i j).val -
        (at2 Interp.counting (mat r r fun i j => ∑ a ∈ range r, F i a * F j a) i j).val⟩ : Q)) =
      mat r r (psdD r X F) :=
    mat_congr fun i hi j hj => by rw [at2_mat' hi hj, at2_mat' hi hj]; rfl
  rw [hD]
  refine Runs.bind' (runs_mapM_range r (c := 6 * (r - 1) + 2)
    (g := fun i => decide (psdOff r X F i ≤ psdD r X F i i + psdD r X F i i)) fun i hi => ?_)
    ?_ rfl rfl
  · refine Runs.bind' (m := 2) (runs_foldlM (c := fun _ => 6)
      (g := fun acc j => (⟨acc.val + (|psdD r X F i j| + |psdD r X F j i|)⟩ : Q)) _ _
      fun acc j hj => ?_) ?_ rfl ?_
    · have hj' := List.mem_range.mp (List.mem_filter.mp hj).1
      rw [at2_mat' hi hj', at2_mat' hj' hi]
      exact Runs.bind' (runs_absV _) (Runs.bind' (runs_absV _) (Runs.bind' (runs_add cat _ _)
        (runs_add cat _ _) rfl rfl) rfl rfl) (by congr 1; ring) rfl
    · rw [at2_mat' hi hi]
      refine Runs.bind' (runs_add cat _ _) (runs_le cat _ _) ?_ rfl
      rw [foldl_acc, zero_add, sum_filter_range]
      unfold psdOff
      congr 2
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases h : j = i <;> simp [h]
    · rw [sum_map_const', length_filter_ne hi]; ring
  · refine (foldl_band_cost _ _).congr ?_ (by simp)
    exact foldl_and_map _ _ _

/-- `psdOk` passing: the dominance `qf_nonneg` needs. -/
theorem psdV_dom {r : ℕ} {X F : ℕ → ℕ → ℚ} (h : psdV r X F = true) :
    ∀ i < r, ∑ j ∈ range r, (if j = i then 0 else
        |X i j - ∑ l ∈ range r, F i l * F j l| + |X j i - ∑ l ∈ range r, F j l * F i l|) ≤
      (X i i - ∑ l ∈ range r, F i l * F i l) + (X i i - ∑ l ∈ range r, F i l * F i l) := by
  have key : ∀ (l : List ℕ) (b : Bool), l.foldl (fun a i =>
      a && decide (psdOff r X F i ≤ psdD r X F i i + psdD r X F i i)) b = true →
      b = true ∧ ∀ i ∈ l, psdOff r X F i ≤ psdD r X F i i + psdD r X F i i := by
    intro l
    induction l with
    | nil => intro b hb; exact ⟨hb, by simp⟩
    | cons a l ih =>
      intro b hb
      simp only [List.foldl_cons] at hb
      obtain ⟨h1, h2⟩ := ih _ hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
      exact ⟨h1.1, fun i hi => by
        rcases List.mem_cons.mp hi with rfl | hi
        · exact h1.2
        · exact h2 i hi⟩
  intro i hi
  exact (key _ _ h).2 i (List.mem_range.mpr hi)

/-- The certificate's `T`, `F₁`, `F₂` and `ε` of the `svd` bound, from `off`. -/
def cT (env : Env) (r off : ℕ) (i j : ℕ) : ℚ := certAt env (off + i * r + j)

def cF1 (env : Env) (r off : ℕ) (i j : ℕ) : ℚ := certAt env (off + r * r + i * r + j)

def cF2 (env : Env) (r off : ℕ) (i j : ℕ) : ℚ := certAt env (off + 2 * (r * r) + i * r + j)

def cE (env : Env) (r off : ℕ) : ℚ := certAt env (off + 3 * (r * r))

/-- `T Tᵀ - Arᵀ Ar`. -/
def svdX1 (V r : ℕ) (Ar T : ℕ → ℕ → ℚ) (i j : ℕ) : ℚ :=
  (∑ l ∈ range r, T i l * T j l) - ∑ q ∈ range V, Ar q i * Ar q j

/-- `Tᵀ (Br Brᵀ) T`. -/
def svdTGT (V r : ℕ) (Br T : ℕ → ℕ → ℚ) (i j : ℕ) : ℚ :=
  ∑ a ∈ range r, T a i * ∑ b ∈ range r, (∑ t ∈ range V, Br a t * Br b t) * T b j

/-- `ε² I - 2 Tᵀ (Br Brᵀ) T`. -/
def svdX2 (V r : ℕ) (Br T : ℕ → ℕ → ℚ) (e : ℚ) (i j : ℕ) : ℚ :=
  (if i = j then 0 + e * e else 0) - (svdTGT V r Br T i j + svdTGT V r Br T i j)

/-- The cost of `svdBound`. -/
def svdBoundCost (V r : ℕ) : ℕ :=
  r * r * V + (r * r * V + (r * r * r + (r * (r * 1) + (psdCost r + (r * r * r + (r * r * r +
    (1 + (r * (r * 2) + (psdCost r + (1 + (1 + 1)))))))))))

theorem runs_svdBound (V r off : ℕ) (Ar Br : ℕ → ℕ → ℚ)
    (h : off + 3 * (r * r) + 1 ≤ env.cert.size) :
    Runs (svdBound Interp.counting r off (mat V r Ar) (mat r V Br)) env
      (⟨cE env r off⟩, psdV r (svdX1 V r Ar (cT env r off)) (cF1 env r off) &&
        psdV r (svdX2 V r Br (cT env r off) (cE env r off)) (cF2 env r off) &&
        decide (0 ≤ cE env r off))
      (svdBoundCost V r) := by
  unfold svdBound svdBoundCost
  simp only [Interp.counting_bind]
  refine Runs.bind0 (runs_certMat off r r (by nlinarith)) ?_
  refine Runs.bind0 (runs_certMat (off + r * r) r r (by nlinarith)) ?_
  refine Runs.bind0 (runs_certMat (off + 2 * (r * r)) r r (by nlinarith)) ?_
  refine Runs.bind0 (runs_cert (by omega)) ?_
  rw [tr_mat]
  refine Runs.bind' (runs_mm r r V (fun k q => Ar q k) (fun k q => Ar q k)) ?_ rfl rfl
  refine Runs.bind' (runs_mm r r V Br Br) ?_ rfl rfl
  refine Runs.bind' (runs_mm r r r _ _) ?_ rfl rfl
  refine Runs.bind' (runs_mapM_range r fun i _ => runs_mapM_range r fun j _ =>
    runs_sub cat _ _) ?_ rfl rfl
  have hX1 : ((List.range r).map fun i => (List.range r).map fun j =>
      (⟨(at2 Interp.counting (mat r r fun i j =>
          ∑ a ∈ range r, certAt env (off + i * r + a) * certAt env (off + j * r + a)) i j).val -
        (at2 Interp.counting (mat r r fun i j => ∑ a ∈ range V, Ar a i * Ar a j) i j).val⟩ :
        Q)) = mat r r (svdX1 V r Ar (cT env r off)) :=
    mat_congr fun i hi j hj => by rw [at2_mat' hi hj, at2_mat' hi hj]; rfl
  rw [hX1]
  refine Runs.bind' (runs_psdOk r _ _) ?_ rfl rfl
  rw [tr_mat]
  refine Runs.bind' (runs_mm r r r _ _) ?_ rfl rfl
  rw [tr_mat]
  refine Runs.bind' (runs_mm r r r _ _) ?_ rfl rfl
  refine Runs.bind' (runs_muladd cat _ _ _) ?_ rfl rfl
  refine Runs.bind' (runs_mapM_range r fun i _ => runs_mapM_range r fun j _ =>
    Runs.bind' (runs_add cat _ _) (runs_sub cat _ _) rfl rfl) ?_ rfl rfl
  have hX2 : ((List.range r).map fun i => (List.range r).map fun j =>
      (⟨(if i = j then (⟨0 + certAt env (off + 3 * (r * r)) *
          certAt env (off + 3 * (r * r))⟩ : Q) else ⟨0⟩).val -
        ((at2 Interp.counting (mat r r fun i j => ∑ a ∈ range r, certAt env (off + a * r + i) *
          ∑ b ∈ range r, (∑ t ∈ range V, Br a t * Br b t) * certAt env (off + b * r + j)) i j).val +
         (at2 Interp.counting (mat r r fun i j => ∑ a ∈ range r, certAt env (off + a * r + i) *
          ∑ b ∈ range r, (∑ t ∈ range V, Br a t * Br b t) *
            certAt env (off + b * r + j)) i j).val)⟩ :
        Q)) = mat r r (svdX2 V r Br (cT env r off) (cE env r off)) := by
    refine mat_congr fun i hi j hj => ?_
    rw [at2_mat' hi hj]
    unfold svdX2 svdTGT cT cE
    split <;> rfl
  rw [hX2]
  refine Runs.bind' (runs_psdOk r _ _) ?_ rfl rfl
  refine Runs.bind' (runs_le cat _ _) ?_ rfl rfl
  refine Runs.bind' (runs_band cat _ _) ?_ rfl rfl
  exact Runs.bind' (runs_band cat _ _) (Runs.pure _) rfl rfl

/-! ## Their subproduct decomposition -/

/-- `A - u wᵀ`. -/
def rem (A : ℕ → ℕ → ℚ) (u w : ℕ → ℚ) (i k : ℕ) : ℚ := A i k - u i * w k

/-- `A v`, over `k` coordinates. -/
def mv (k : ℕ) (A : ℕ → ℕ → ℚ) (v : ℕ → ℚ) (i : ℕ) : ℚ := ∑ a ∈ range k, A i a * v a

/-- The remainders of the keys and queries after one and two rank-one parts, and of `W_Q`, `W_K`. -/
def subKe (V : ℕ) (Ek : ℕ → ℕ → ℚ) (kd : ℕ → ℚ) : ℕ → ℕ → ℚ := rem Ek kd (sUA V kd Ek)

def subQe (V : ℕ) (Eq : ℕ → ℕ → ℚ) (qd : ℕ → ℚ) : ℕ → ℕ → ℚ := rem Eq qd (sUA V qd Eq)

def subKe2 (V : ℕ) (Ek : ℕ → ℕ → ℚ) (kd skd : ℕ → ℚ) : ℕ → ℕ → ℚ :=
  rem (subKe V Ek kd) skd (sUA V skd (subKe V Ek kd))

def subQe2 (V : ℕ) (Eq : ℕ → ℕ → ℚ) (qd sqd : ℕ → ℚ) : ℕ → ℕ → ℚ :=
  rem (subQe V Eq qd) sqd (sUA V sqd (subQe V Eq qd))

def subWqe (d : ℕ) (Wq : ℕ → ℕ → ℚ) (qu : ℕ → ℚ) : ℕ → ℕ → ℚ := rem Wq qu (sUA d qu Wq)

def subWke (d : ℕ) (Wk : ℕ → ℕ → ℚ) (ku : ℕ → ℚ) : ℕ → ℕ → ℚ := rem Wk ku (sUA d ku Wk)

/-- The six rank-one terms of `Ê`, as the checker adds them up. -/
def subEh (V d h : ℕ) (Eq Ek Wq Wk Mqk : ℕ → ℕ → ℚ) (kd qd skd sqd qu ku : ℕ → ℚ)
    (q t : ℕ) : ℚ :=
  0 + qd q * mv d Ek (sUA d (sUA V qd Eq) Mqk) t +
    mv d (subQe V Eq qd) (mv d Mqk (sUA V kd Ek)) q * kd t +
    sqd q * mv d (subKe V Ek kd) (sUA d (sUA V sqd (subQe V Eq qd)) Mqk) t +
    mv d (subQe2 V Eq qd sqd) (mv d Mqk (sUA V skd (subKe V Ek kd))) q * skd t +
    mv d (subQe2 V Eq qd sqd) qu q * mv d (subKe2 V Ek kd skd) (mv h Wk (sUA d qu Wq)) t +
    mv d (subQe2 V Eq qd sqd) (mv h (subWqe d Wq qu) (sUA d ku Wk)) q *
      mv d (subKe2 V Ek kd skd) ku t

/-- The directions of the certificate, from `off`. -/
def cDir (env : Env) (off : ℕ) (i : ℕ) : ℚ := certAt env (off + i)

/-- The cost of `subDecomp`. -/
def subCost (V d h : ℕ) : ℕ :=
  d * V + (V * (1 + d) + (d * V + (V * (1 + d) + (d * V + (V * (1 + d) + (d * V + (V * (1 + d) +
    (h * d + (d * (1 + h) + (h * d + (d * (1 + h) + (d * d + (V * d + (d * d + (V * d + (d * d + (V
    * d + (d * d + (V * d + (d * h + (V * d + (V * d + (d * h + (V * d + (V * d + (V * (V *
    6)))))))))))))))))))))))))))

theorem runs_subDecomp (V d h off : ℕ) (Eq Ek Wq Wk Mqk : ℕ → ℕ → ℚ)
    (hc : off + 4 * V + d + d ≤ env.cert.size) :
    Runs (subDecomp Interp.counting V d h off (mat V d Eq) (mat V d Ek) (mat d h Wq)
      (mat d h Wk) (mat d d Mqk)) env
      (mat V V (subEh V d h Eq Ek Wq Wk Mqk (cDir env off) (cDir env (off + V))
          (cDir env (off + 2 * V)) (cDir env (off + 3 * V)) (cDir env (off + 4 * V))
          (cDir env (off + 4 * V + d))),
        mat V d (subQe2 V Eq (cDir env (off + V)) (cDir env (off + 3 * V))),
        mat d h (subWqe d Wq (cDir env (off + 4 * V))),
        mat d h (subWke d Wk (cDir env (off + 4 * V + d))),
        mat V d (subKe2 V Ek (cDir env off) (cDir env (off + 2 * V))))
      (subCost V d h) := by
  unfold subDecomp subCost
  simp only [Interp.counting_bind]
  refine Runs.bind0 (runs_certVec off V (by omega)) ?_
  refine Runs.bind0 (runs_certVec (off + V) V (by omega)) ?_
  refine Runs.bind0 (runs_certVec (off + 2 * V) V (by omega)) ?_
  refine Runs.bind0 (runs_certVec (off + 3 * V) V (by omega)) ?_
  refine Runs.bind0 (runs_certVec (off + 4 * V) d (by omega)) ?_
  refine Runs.bind0 (runs_certVec (off + 4 * V + d) d (by omega)) ?_
  refine Runs.bind' (runs_vecMat V d _ Ek) ?_ rfl rfl
  refine Runs.bind' (runs_subOuter_mat V d Ek _ _) ?_ rfl rfl
  refine Runs.bind' (runs_vecMat V d _ Eq) ?_ rfl rfl
  refine Runs.bind' (runs_subOuter_mat V d Eq _ _) ?_ rfl rfl
  refine Runs.bind' (runs_vecMat V d _ _) ?_ rfl rfl
  refine Runs.bind' (runs_subOuter_mat V d _ _ _) ?_ rfl rfl
  refine Runs.bind' (runs_vecMat V d _ _) ?_ rfl rfl
  refine Runs.bind' (runs_subOuter_mat V d _ _ _) ?_ rfl rfl
  refine Runs.bind' (runs_vecMat d h _ Wq) ?_ rfl rfl
  refine Runs.bind' (runs_subOuter_mat d h Wq _ _) ?_ rfl rfl
  refine Runs.bind' (runs_vecMat d h _ Wk) ?_ rfl rfl
  refine Runs.bind' (runs_subOuter_mat d h Wk _ _) ?_ rfl rfl
  refine Runs.bind' (runs_vecMat d d _ Mqk) ?_ rfl rfl
  refine Runs.bind' (runs_matVec V d Ek _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec d d Mqk _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec V d _ _) ?_ rfl rfl
  refine Runs.bind' (runs_vecMat d d _ Mqk) ?_ rfl rfl
  refine Runs.bind' (runs_matVec V d _ _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec d d Mqk _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec V d _ _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec d h Wk _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec V d _ _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec V d _ _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec d h _ _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec V d _ _) ?_ rfl rfl
  refine Runs.bind' (runs_matVec V d _ _) ?_ rfl rfl
  refine Runs.bind' (runs_mapM_range V fun q hq => runs_mapM_range V fun t ht =>
    Runs.bind' (runs_muladd cat _ _ _) (Runs.bind' (runs_muladd cat _ _ _)
      (Runs.bind' (runs_muladd cat _ _ _) (Runs.bind' (runs_muladd cat _ _ _)
        (Runs.bind' (runs_muladd cat _ _ _) (runs_muladd cat _ _ _) rfl rfl) rfl rfl) rfl rfl)
      rfl rfl) rfl rfl) (Runs.pure _) ?_ (by ring)
  congr 1
  refine List.map_congr_left fun q hq => List.map_congr_left fun t ht => ?_
  have hq' := List.mem_range.mp hq
  have ht' := List.mem_range.mp ht
  simp only [at1_vec hq', at1_vec ht']
  rfl

end GrossSub
