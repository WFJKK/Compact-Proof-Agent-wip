import Protected.N_max2_v64_s0
import CompactCheck.Soundness
import CompactCheck.CountedOps

/-!
# max2: the direct check on the token-logit matrix

The network is linear in the summed one-hot input: logits([a, b]) = M[:, a] + M[:, b] where
M = U · L · E (d_vocab × d_vocab). The checker computes M once (v·d·(d + v) muladds), then for every
unordered pair a ≤ m tests that the logit at m is the strict maximum of M[:, a] + M[:, m]
(v adds, v − 2 maxes, one comparison), which certifies both inputs [a, m] and [m, a].
-/

namespace Candidate.MaxDirect

open CompactCheck Protected.N_max2_v64_s0

/-! ## The checker -/

/-- Entries `0, …, n-1` of a weight (free reads). -/
def readList (I : Interp) (name : String) : Nat → I.M (List I.V)
  | 0 => pure []
  | n+1 => do
    let xs ← readList I name n
    let x ← I.weight name n
    pure (xs ++ [x])

/-- `acc + Σ_{k<n} xs[o1 + k·s1] · ys[o2 + k·s2]`, one `muladd` per term. -/
def dotM (I : Interp) (xs ys : List I.V) (o1 s1 o2 s2 : Nat) : Nat → I.V → I.M I.V
  | 0, acc => pure acc
  | k+1, acc => do
    let acc' ← I.muladd "a" acc (xs.getD (o1 + k*s1) I.zero) (ys.getD (o2 + k*s2) I.zero)
    dotM I xs ys o1 s1 o2 s2 k acc'

/-- `[f i, f (i+1), …, f (i+n-1)]`, in order. -/
def buildM {α : Type} (I : Interp) (f : Nat → I.M α) : Nat → Nat → I.M (List α)
  | _, 0 => pure []
  | i, n+1 => do
    let x ← f i
    let xs ← buildM I f (i+1) n
    pure (x :: xs)

/-- Column `a` of `M = U · L · E`: first `F[:, a] = L · E[:, a]`, then `U · F[:, a]`. -/
def computeCol (I : Interp) (E L U : List I.V) (d v a : Nat) : I.M (List I.V) := do
  let F ← buildM I (fun i => dotM I L E (i*d) 1 a v d I.zero) 0 d
  buildM I (fun j => dotM I U F (j*d) 1 0 1 d I.zero) 0 v

def computeCols (I : Interp) (E L U : List I.V) (d v : Nat) :
    List Nat → List (List I.V) → I.M (List (List I.V))
  | [], acc => pure acc
  | a :: as, acc => do
    let col ← computeCol I E L U d v a
    computeCols I E L U d v as (acc ++ [col])

/-- Running max of `f j` over `j = i, …, i+n-1`, skipping `j = m`. -/
def maxExcept (I : Interp) (f : Nat → I.M I.V) (m : Nat) : Nat → Nat → I.V → I.M I.V
  | _, 0, mx => pure mx
  | i, n+1, mx => do
    let mx' ← if i = m then pure mx else do
      let s ← f i
      I.max "a" mx s
    maxExcept I f m (i+1) n mx'

/-- Is `f m` strictly above every `f j`, `j < v`, `j ≠ m`? (`v ≥ 2`.) -/
def strictMaxM (I : Interp) (f : Nat → I.M I.V) (m v : Nat) : I.M I.B := do
  let lm ← f m
  let j0 := if m = 0 then 1 else 0
  let s0 ← f j0
  let mx ← maxExcept I f m (j0+1) (v - (j0+1)) s0
  I.lt "a" mx lm

def diagOk (I : Interp) (cm : List I.V) (m v : Nat) : I.M I.B :=
  strictMaxM I (fun j => pure (cm.getD j I.zero)) m v

def pairOk (I : Interp) (ca cm : List I.V) (m v : Nat) : I.M I.B :=
  strictMaxM I (fun j => I.add "a" (ca.getD j I.zero) (cm.getD j I.zero)) m v

/-- Row `m` of verdicts: `ok(a, m)` for `a < m`, then the diagonal `ok(m, m)`. -/
def rowOks (I : Interp) (cols : List (List I.V)) (v m : Nat) : I.M (List I.B) := do
  let cm := cols.getD m []
  let ps ← buildM I (fun a => pairOk I (cols.getD a []) cm m v) 0 m
  let dg ← diagOk I cm m v
  pure (ps ++ [dg])

def oksFor (I : Interp) (cols : List (List I.V)) (v : Nat) : List Nat → I.M (List (List I.B))
  | [] => pure []
  | m :: ms => do
    let r ← rowOks I cols v m
    let rs ← oksFor I cols v ms
    pure (r :: rs)

def okOf (I : Interp) (oks : List (List I.B)) : Input → I.B
  | [t, s] => (oks.getD (max t s) []).getD (min t s) I.bfalse
  | _ => I.bfalse

def tally (I : Interp) (oks : List (List I.B)) : List Input → I.N
  | [] => I.nzero
  | x :: xs => I.nadd (I.countB (okOf I oks x)) (tally I oks xs)

def body (I : Interp) (d v : Nat) : I.M I.N := do
  let E ← readList I "embedding.weight" (d*v)
  let L ← readList I "linear.weight" (d*d)
  let U ← readList I "unembedding.weight" (v*d)
  let cols ← computeCols I E L U d v (List.range v) []
  let oks ← oksFor I cols v (List.range v)
  pure (tally I oks (allInputs task.space))

def D : Checker := fun I => do
  let shE ← I.weightShape "embedding.weight"
  let shL ← I.weightShape "linear.weight"
  let shU ← I.weightShape "unembedding.weight"
  let szE ← I.weightSize "embedding.weight"
  let szL ← I.weightSize "linear.weight"
  let szU ← I.weightSize "unembedding.weight"
  match shE with
  | [d, v] =>
    if shL = [d, d] ∧ shU = [v, d] ∧ szE = d * v ∧ szL = d * d ∧ szU = v * d ∧
        v = graph.values ∧ 2 ≤ v then
      body I d v
    else pure I.nzero
  | _ => pure I.nzero

/-! ## Run lemmas (counting interpreter) -/

def qget (xs : List Q) (i : Nat) : ℚ := (xs.getD i ⟨0⟩).val

def readPure (t : Tensor ℚ) (n : Nat) : List Q := (List.range n).map fun i => ⟨t.get i⟩

theorem qget_map_range (g : Nat → ℚ) (n i : Nat) (hi : i < n) :
    qget ((List.range n).map fun i => (⟨g i⟩ : Q)) i = g i := by
  simp [qget, List.getD_eq_getElem?_getD, hi]

theorem qget_readPure (t : Tensor ℚ) (n i : Nat) (hi : i < n) : qget (readPure t n) i = t.get i :=
  qget_map_range (fun i => t.get i) n i hi

theorem readList_run (env : Env) (name : String) (t : Tensor ℚ)
    (ht : List.lookup name env.weights = some t) :
    ∀ (n : Nat), n ≤ t.data.size → ∀ (c : Cost),
      (readList Interp.counting name n).run env c = some (readPure t n, c)
  | 0, _, c => by
    simp [readList, readPure, CostM.run_pure]
  | n+1, hn, c => by
    have ih := readList_run env name t ht n (by omega) c
    have hlt : n < t.data.size := by omega
    simp only [readList, Interp.counting_bind, Interp.counting_pure, CostM.run_bind, ih,
      CostM.weight_run_of_lookup (ht := ht) (hi := hlt), CostM.run_pure]
    simp [readPure, List.range_succ, Tensor.get, Array.getD_eq_getD_getElem?,
      Array.getElem?_eq_getElem hlt]

theorem dotM_run (env : Env) (xs ys : List Q) (o1 s1 o2 s2 : Nat) :
    ∀ (n : Nat) (acc : Q) (c : Cost), ∃ c',
      (dotM Interp.counting xs ys o1 s1 o2 s2 n acc).run env c =
        some (⟨acc.val + ∑ k ∈ Finset.range n, qget xs (o1 + k*s1) * qget ys (o2 + k*s2)⟩, c')
  | 0, acc, c => ⟨c, by simp [dotM, CostM.run_pure]⟩
  | n+1, acc, c => by
    obtain ⟨c', ih⟩ := dotM_run env xs ys o1 s1 o2 s2 n
      ⟨acc.val + qget xs (o1 + n*s1) * qget ys (o2 + n*s2)⟩ (c.add "a" 1)
    refine ⟨c', ?_⟩
    simp only [dotM, Interp.counting_bind, CostM.run_bind, CostM.qmuladd]
    rw [show (⟨acc.val + (xs.getD (o1 + n*s1) ⟨0⟩).val * (ys.getD (o2 + n*s2) ⟨0⟩).val⟩ : Q) =
      ⟨acc.val + qget xs (o1 + n*s1) * qget ys (o2 + n*s2)⟩ from rfl, ih]
    simp only [Finset.sum_range_succ, Option.some.injEq, Prod.mk.injEq, Q.mk.injEq, and_true]
    ring

theorem buildM_run {α : Type} (env : Env) (f : Nat → CostM α) (g : Nat → α)
    (hf : ∀ j c, ∃ c', (f j).run env c = some (g j, c')) :
    ∀ (n i : Nat) (c : Cost), ∃ c',
      (buildM Interp.counting f i n).run env c = some ((List.range' i n).map g, c')
  | 0, i, c => ⟨c, by simp [buildM, CostM.run_pure]⟩
  | n+1, i, c => by
    obtain ⟨c1, h1⟩ := hf i c
    obtain ⟨c2, h2⟩ := buildM_run env f g hf n (i+1) c1
    refine ⟨c2, ?_⟩
    simp only [buildM, Interp.counting_bind, Interp.counting_pure, CostM.run_bind, h1, h2,
      CostM.run_pure, List.range'_succ, List.map_cons]

/-- `buildM` in specification form: each entry satisfies what its computation certifies. -/
theorem buildM_spec {α : Type} (env : Env) (f : Nat → CostM α) (P : Nat → α → Prop)
    (hf : ∀ j c r c', (f j).run env c = some (r, c') → P j r) (dflt : α) :
    ∀ (n i : Nat) (c : Cost) (xs : List α) (c' : Cost),
      (buildM Interp.counting f i n).run env c = some (xs, c') →
      xs.length = n ∧ ∀ k < n, P (i + k) (xs.getD k dflt)
  | 0, i, c, xs, c', h => by
    simp only [buildM, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | n+1, i, c, xs, c', h => by
    simp only [buildM, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at h
    split at h
    · rename_i r c1 h1
      split at h
      · rename_i ys c2 h2
        simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        obtain ⟨hlen, hall⟩ := buildM_spec env f P hf dflt n (i+1) c1 ys c2 h2
        refine ⟨by simp [hlen], fun k hk => ?_⟩
        cases k with
        | zero => simpa using hf i c r c1 h1
        | succ k =>
          have := hall k (by omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using this
      · cases h
    · cases h

theorem maxExcept_spec (env : Env) (f : Nat → CostM Q) (g : Nat → ℚ)
    (hf : ∀ j c, ∃ r c', (f j).run env c = some (r, c') ∧ r.val = g j) (m : Nat) :
    ∀ (n i : Nat) (mx : Q) (c : Cost) (r : Q) (c' : Cost),
      (maxExcept Interp.counting f m i n mx).run env c = some (r, c') →
      mx.val ≤ r.val ∧ ∀ j, i ≤ j → j < i + n → j ≠ m → g j ≤ r.val
  | 0, i, mx, c, r, c', h => by
    simp only [maxExcept, Interp.counting_pure, CostM.run_pure, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨le_refl _, fun j h1 h2 _ => absurd h2 (by omega)⟩
  | n+1, i, mx, c, r, c', h => by
    simp only [maxExcept, Interp.counting_bind, Interp.counting_pure] at h
    by_cases hi : i = m
    · subst hi
      simp only [↓reduceIte, CostM.run_bind, CostM.run_pure] at h
      obtain ⟨h1, h2⟩ := maxExcept_spec env f g hf i n (i+1) mx c r c' h
      refine ⟨h1, fun j hj1 hj2 hjm => ?_⟩
      have : i + 1 ≤ j := by
        rcases Nat.eq_or_lt_of_le hj1 with h | h
        · exact absurd h.symm hjm
        · omega
      exact h2 j this (by omega) hjm
    · obtain ⟨s, c1, hs, hsv⟩ := hf i c
      simp only [hi, ↓reduceIte, CostM.run_bind, hs, CostM.qmax] at h
      obtain ⟨h1, h2⟩ := maxExcept_spec env f g hf m n (i+1) ⟨max mx.val s.val⟩ _ r c' h
      refine ⟨le_trans (le_max_left _ _) h1, fun j hj1 hj2 hjm => ?_⟩
      rcases Nat.eq_or_lt_of_le hj1 with h | h
      · subst h
        exact hsv ▸ le_trans (le_max_right _ _) h1
      · exact h2 j h (by omega) hjm

theorem strictMaxM_spec (env : Env) (f : Nat → CostM Q) (g : Nat → ℚ)
    (hf : ∀ j c, ∃ r c', (f j).run env c = some (r, c') ∧ r.val = g j) (m v : Nat)
    (hv : 2 ≤ v) (hm : m < v) (c c' : Cost)
    (h : (strictMaxM Interp.counting f m v).run env c = some (true, c')) :
    ∀ j < v, j ≠ m → g j < g m := by
  obtain ⟨lm, c1, hlm, hlmv⟩ := hf m c
  simp only [strictMaxM, Interp.counting_bind, CostM.run_bind, hlm] at h
  by_cases hm0 : m = 0
  · subst hm0
    simp only [↓reduceIte] at h
    obtain ⟨s0, c2, hs0, hs0v⟩ := hf 1 c1
    simp only [hs0] at h
    split at h
    · rename_i mx c3 hmx
      obtain ⟨h1, h2⟩ := maxExcept_spec env f g hf 0 _ _ _ _ _ _ hmx
      simp only [CostM.qlt, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at h
      intro j hj hjm
      rw [← hlmv]
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · have : j = 1 := by omega
        subst this
        exact lt_of_le_of_lt (hs0v ▸ h1) h.1
      · exact lt_of_le_of_lt (h2 j hj2 (by omega) hjm) h.1
    · cases h
  · simp only [hm0, ↓reduceIte] at h
    obtain ⟨s0, c2, hs0, hs0v⟩ := hf 0 c1
    simp only [hs0] at h
    split at h
    · rename_i mx c3 hmx
      obtain ⟨h1, h2⟩ := maxExcept_spec env f g hf m _ _ _ _ _ _ hmx
      simp only [CostM.qlt, Option.some.injEq, Prod.mk.injEq, decide_eq_true_eq] at h
      intro j hj hjm
      rw [← hlmv]
      rcases Nat.lt_or_ge j 1 with hj1 | hj1
      · have : j = 0 := by omega
        subst this
        exact lt_of_le_of_lt (hs0v ▸ h1) h.1
      · exact lt_of_le_of_lt (h2 j hj1 (by omega) hjm) h.1
    · cases h

open Classical in
theorem tally_le (w : Weights ℚ) (oks : List (List Bool)) :
    ∀ xs : List Input, (∀ x ∈ xs, okOf Interp.counting oks x = true → Correct graph w task x) →
      ∀ k : Nat, tally Interp.counting oks xs = k →
      k ≤ xs.countP (fun x => decide (Correct graph w task x))
  | [], _, k, hk => by
    simp only [tally] at hk
    omega
  | x :: xs, h, k, hk => by
    obtain ⟨k', hk'⟩ : ∃ k' : Nat, tally Interp.counting oks xs = k' := ⟨_, rfl⟩
    have ih := tally_le w oks xs (fun y hy => h y (List.mem_cons_of_mem x hy)) k' hk'
    simp only [tally, hk', Nat.add_eq] at hk
    rw [List.countP_cons]
    cases hx : okOf Interp.counting oks x with
    | false => simp only [hx, Bool.cond_false] at hk; omega
    | true =>
      have hc := h x (List.mem_cons_self) hx
      simp only [hx, Bool.cond_true] at hk
      simp only [hc, decide_true, ite_true]
      omega

/-! ## The columns of `M` -/

def fEntry (E L : List Q) (d v a i : Nat) : ℚ :=
  ∑ k ∈ Finset.range d, qget L (i*d + k) * qget E (a + k*v)

def mEntry (E L U : List Q) (d v a j : Nat) : ℚ :=
  ∑ i ∈ Finset.range d, qget U (j*d + i) * fEntry E L d v a i

def colPure (E L U : List Q) (d v a : Nat) : List Q :=
  (List.range v).map fun j => ⟨mEntry E L U d v a j⟩

theorem computeCol_run (env : Env) (E L U : List Q) (d v a : Nat) (c : Cost) : ∃ c',
    (computeCol Interp.counting E L U d v a).run env c = some (colPure E L U d v a, c') := by
  have hF : ∀ i c, ∃ c', (dotM Interp.counting L E (i*d) 1 a v d Interp.counting.zero).run env c =
      some ((⟨fEntry E L d v a i⟩ : Q), c') := by
    intro i c
    obtain ⟨c', h⟩ := dotM_run env L E (i*d) 1 a v d ⟨0⟩ c
    exact ⟨c', by rw [Interp.counting_zero, h]; simp [fEntry]⟩
  obtain ⟨c1, h1⟩ := buildM_run env _ (fun i => (⟨fEntry E L d v a i⟩ : Q)) hF d 0 c
  have hM : ∀ j c, ∃ c', (dotM Interp.counting U ((List.range' 0 d).map fun i => (⟨fEntry E L d v a i⟩ : Q))
      (j*d) 1 0 1 d Interp.counting.zero).run env c = some ((⟨mEntry E L U d v a j⟩ : Q), c') := by
    intro j c
    obtain ⟨c', h⟩ := dotM_run env U ((List.range' 0 d).map fun i => (⟨fEntry E L d v a i⟩ : Q))
      (j*d) 1 0 1 d ⟨0⟩ c
    refine ⟨c', ?_⟩
    rw [Interp.counting_zero, h]
    simp only [Option.some.injEq, Prod.mk.injEq, Q.mk.injEq, and_true, mEntry, zero_add,
      Nat.mul_one]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [← List.range_eq_range', qget_map_range _ _ _ hi]
  obtain ⟨c2, h2⟩ := buildM_run env _ (fun j => (⟨mEntry E L U d v a j⟩ : Q)) hM v 0 c1
  refine ⟨c2, ?_⟩
  simp only [computeCol, Interp.counting_bind, CostM.run_bind, h1, h2, colPure, List.range_eq_range']

theorem computeCols_run (env : Env) (E L U : List Q) (d v : Nat) :
    ∀ (as : List Nat) (acc : List (List Q)) (c : Cost), ∃ c',
      (computeCols Interp.counting E L U d v as acc).run env c =
        some (acc ++ as.map (colPure E L U d v), c')
  | [], acc, c => ⟨c, by simp [computeCols, CostM.run_pure]⟩
  | a :: as, acc, c => by
    obtain ⟨c1, h1⟩ := computeCol_run env E L U d v a c
    obtain ⟨c2, h2⟩ := computeCols_run env E L U d v as (acc ++ [colPure E L U d v a]) c1
    exact ⟨c2, by simp [computeCols, CostM.run_bind, h1, h2]⟩

/-! ## The verdicts -/

def Strict (cols : List (List Q)) (v a m : Nat) : Prop :=
  ∀ j < v, j ≠ m → qget (cols.getD a []) j + qget (cols.getD m []) j <
    qget (cols.getD a []) m + qget (cols.getD m []) m

def RowSpec (cols : List (List Q)) (v m : Nat) (row : List Bool) : Prop :=
  ∀ a, row.getD a false = true → a ≤ m ∧ Strict cols v a m

theorem pairOk_spec (env : Env) (ca cm : List Q) (m v : Nat) (hv : 2 ≤ v) (hm : m < v)
    (c c' : Cost) (h : (pairOk Interp.counting ca cm m v).run env c = some (true, c')) :
    ∀ j < v, j ≠ m → qget ca j + qget cm j < qget ca m + qget cm m := by
  refine strictMaxM_spec env _ (fun j => qget ca j + qget cm j) ?_ m v hv hm c c' h
  intro j c
  exact ⟨_, _, rfl, rfl⟩

theorem diagOk_spec (env : Env) (cm : List Q) (m v : Nat) (hv : 2 ≤ v) (hm : m < v)
    (c c' : Cost) (h : (diagOk Interp.counting cm m v).run env c = some (true, c')) :
    ∀ j < v, j ≠ m → qget cm j < qget cm m := by
  refine strictMaxM_spec env _ (fun j => qget cm j) ?_ m v hv hm c c' h
  intro j c
  exact ⟨_, _, rfl, rfl⟩

theorem rowOks_spec (env : Env) (cols : List (List Q)) (v m : Nat) (hv : 2 ≤ v) (hm : m < v)
    (c : Cost) (row : List Bool) (c' : Cost)
    (h : (rowOks Interp.counting cols v m).run env c = some (row, c')) : RowSpec cols v m row := by
  simp only [rowOks, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at h
  split at h
  · rename_i ps c1 hps
    split at h
    · rename_i dg c2 hdg
      simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      obtain ⟨hlen, hall⟩ := buildM_spec env _ (fun a r => r = true → Strict cols v a m)
        (fun a c r c' hr ht => by
          subst ht
          intro j hj hjm
          exact pairOk_spec env _ _ m v hv hm c c' hr j hj hjm) false m 0 c ps c1 hps
      intro a ha
      rcases Nat.lt_trichotomy a m with hlt | heq | hgt
      · rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega),
          ← List.getD_eq_getElem?_getD] at ha
        have := hall a hlt
        simp only [Nat.zero_add] at this
        exact ⟨le_of_lt hlt, this ha⟩
      · subst heq
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega), hlen,
          Nat.sub_self] at ha
        simp only [List.getElem?_cons_zero, Option.getD_some] at ha
        subst ha
        have hd := diagOk_spec env _ a v hv hm c1 c2 hdg
        refine ⟨le_refl _, fun j hj hja => ?_⟩
        have := hd j hj hja
        linarith
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)] at ha
        simp at ha
    · cases h
  · cases h

theorem oksFor_spec (env : Env) (cols : List (List Q)) (v : Nat) (hv : 2 ≤ v) :
    ∀ (ms : List Nat) (c : Cost) (oks : List (List Bool)) (c' : Cost),
      (oksFor Interp.counting cols v ms).run env c = some (oks, c') → (∀ m ∈ ms, m < v) →
      oks.length = ms.length ∧ ∀ k < ms.length, RowSpec cols v (ms.getD k 0) (oks.getD k [])
  | [], c, oks, c', h, _ => by
    simp only [oksFor, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact ⟨rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | m :: ms, c, oks, c', h, hms => by
    simp only [oksFor, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at h
    split at h
    · rename_i r c1 hr
      split at h
      · rename_i rs c2 hrs
        simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, _⟩ := h
        have hm : m < v := hms m (List.mem_cons_self)
        obtain ⟨hlen, hall⟩ := oksFor_spec env cols v hv ms c1 rs c2 hrs
          (fun x hx => hms x (List.mem_cons_of_mem m hx))
        refine ⟨by simp [hlen], fun k hk => ?_⟩
        cases k with
        | zero => simpa using rowOks_spec env cols v m hv hm c r c1 hr
        | succ k => simpa using hall k (by simpa using hk)
      · cases h
    · cases h

/-! ## The network's output, entry by entry -/

theorem sum_range_list (f : Nat → ℚ) : ∀ n, ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i
  | 0 => by simp
  | n+1 => by simp [List.range_succ, Finset.sum_range_succ, sum_range_list f n]

theorem get_map_range (sh : List Nat) (n : Nat) (f : Nat → ℚ) (i : Nat) (hi : i < n) :
    Tensor.get ⟨sh, (Array.range n).map f⟩ i = f i := by
  simp [Tensor.get, Array.getD_eq_getD_getElem?, hi]

theorem linearOp_vec (W t : Tensor ℚ) (out inn : Nat) (hW : W.shape = [out, inn])
    (hWs : W.data.size = out * inn) (ht : t.shape = [1, inn]) (hts : t.data.size = inn) :
    ∃ r : Tensor ℚ, linearOp W none t = some r ∧ r.shape = [1, out] ∧ r.data.size = out ∧
      ∀ o < out, r.get o = ∑ i ∈ Finset.range inn, W.get (o * inn + i) * t.get i := by
  refine ⟨⟨[1, out], (Array.range out).map fun o =>
      ∑ i ∈ Finset.range inn, W.get (o * inn + i) * t.get i⟩, ?_, rfl, by simp,
      fun o ho => get_map_range _ _ _ _ ho⟩
  simp only [linearOp, hW, ht, hWs, hts]
  simp [shapeSize]
  intro j hj
  rw [Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj, sum_range_list]
  simp

theorem onehotSum_vec (v t s : Nat) (ht : t < v) (hs : s < v) :
    ∃ t0 t1 : Tensor ℚ, oneHotInput 2 v [t, s] = some t0 ∧ sumOp 1 t0 = some t1 ∧
      t1.shape = [1, v] ∧ t1.data.size = v ∧
      ∀ l < v, t1.get l = (if t = l then (1:ℚ) else 0) + (if s = l then 1 else 0) := by
  refine ⟨⟨[1, 2, v], (Array.range (2 * v)).map fun j =>
    if [t, s].getD (j / v) 0 = j % v then 1 else 0⟩, ⟨[1, v], (Array.range v).map fun l =>
        (if t = l then (1:ℚ) else 0) + (if s = l then 1 else 0)⟩, ?_, ?_, rfl, by simp,
        fun l hl => get_map_range _ _ _ _ hl⟩
  · simp [oneHotInput, ht, hs]
  · have hv : 0 < v := by omega
    simp [sumOp, normDim, shapeSize]
    intro j hj
    have h1 : (v + j) / v = 1 := by
      rw [Nat.add_comm, Nat.add_div_right _ hv, Nat.div_eq_of_lt hj]
    have h2 : (v + j) % v = j := by
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt hj]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.singleton_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.div_eq_of_lt hj,
      Nat.mod_eq_of_lt hj, Nat.zero_mul, Nat.zero_add, Nat.one_mul, add_zero]
    rw [get_map_range _ _ _ _ (by omega), get_map_range _ _ _ _ (by omega)]
    simp [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, h1, h2]

theorem sum_onehot (f : Nat → ℚ) (v t s : Nat) (ht : t < v) (hs : s < v) :
    ∑ l ∈ Finset.range v, f l * ((if t = l then (1:ℚ) else 0) + (if s = l then 1 else 0)) =
      f t + f s := by
  simp [mul_add, Finset.sum_add_distrib, mul_ite, Finset.sum_ite_eq, ht, hs]

/-- The logit of input `[t, s]` at `j`, from the weight tensors. -/
def logitT (tE tL tU : Tensor ℚ) (d v t s j : Nat) : ℚ :=
  ∑ i ∈ Finset.range d, tU.get (j*d + i) * ∑ k ∈ Finset.range d, tL.get (i*d + k) *
    (tE.get (k*v + t) + tE.get (k*v + s))

theorem evalGraph_formula (w : Weights ℚ) (tE tL tU : Tensor ℚ) (d v : Nat)
    (hE : List.lookup "embedding.weight" w = some tE)
    (hL : List.lookup "linear.weight" w = some tL)
    (hU : List.lookup "unembedding.weight" w = some tU)
    (hEs : tE.shape = [d, v]) (hEz : tE.data.size = d * v)
    (hLs : tL.shape = [d, d]) (hLz : tL.data.size = d * d)
    (hUs : tU.shape = [v, d]) (hUz : tU.data.size = v * d) (hv : v = 64)
    (t s : Nat) (ht : t < v) (hs : s < v) :
    ∃ out : Tensor ℚ, evalGraph graph w [t, s] = some out ∧ out.shape = [1, v] ∧
      out.data.size = v ∧ ∀ j < v, out.get j = logitT tE tL tU d v t s j := by
  subst hv
  obtain ⟨t0, t1, h0, h1, h1s, h1z, h1g⟩ := onehotSum_vec 64 t s ht hs
  obtain ⟨t2, h2, h2s, h2z, h2g⟩ := linearOp_vec tE t1 d 64 hEs hEz h1s h1z
  obtain ⟨t3, h3, h3s, h3z, h3g⟩ := linearOp_vec tL t2 d d hLs hLz h2s h2z
  obtain ⟨t4, h4, h4s, h4z, h4g⟩ := linearOp_vec tU t3 64 d hUs hUz h3s h3z
  refine ⟨t4, ?_, h4s, h4z, fun j hj => ?_⟩
  · simp [evalGraph, graph, evalOps, evalOp, h0, h1, hE, hL, hU, h2, h3, h4]
  · rw [h4g j hj]
    unfold logitT
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_range] at hi
    rw [h3g i hi]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_range] at hk
    rw [h2g k hk]
    congr 1
    rw [← sum_onehot (fun l => tE.get (k*64 + l)) 64 t s ht hs]
    apply Finset.sum_congr rfl
    intro l hl
    rw [h1g l (Finset.mem_range.mp hl)]

theorem mEntry_eq (tE tL tU : Tensor ℚ) (d v a j : Nat) (ha : a < v) (hj : j < v) :
    mEntry (readPure tE (d*v)) (readPure tL (d*d)) (readPure tU (v*d)) d v a j =
      ∑ i ∈ Finset.range d, tU.get (j*d + i) * ∑ k ∈ Finset.range d, tL.get (i*d + k) * tE.get (k*v + a) := by
  unfold mEntry fEntry
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_range] at hi
  have h1 : j*d + i < v*d := by
    calc j*d + i < j*d + d := by omega
      _ = (j+1)*d := by ring
      _ ≤ v*d := Nat.mul_le_mul_right d hj
  rw [qget_readPure _ _ _ h1]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  have h2 : i*d + k < d*d := by
    calc i*d + k < i*d + d := by omega
      _ = (i+1)*d := by ring
      _ ≤ d*d := Nat.mul_le_mul_right d hi
  have h3 : a + k*v < d*v := by
    calc a + k*v < v + k*v := by omega
      _ = (k+1)*v := by ring
      _ ≤ d*v := Nat.mul_le_mul_right v hk
  rw [qget_readPure _ _ _ h2, qget_readPure _ _ _ h3, Nat.add_comm a]

theorem logitT_eq (tE tL tU : Tensor ℚ) (d v t s j : Nat) (ht : t < v) (hs : s < v) (hj : j < v) :
    logitT tE tL tU d v t s j =
      mEntry (readPure tE (d*v)) (readPure tL (d*d)) (readPure tU (v*d)) d v t j +
      mEntry (readPure tE (d*v)) (readPure tL (d*d)) (readPure tU (v*d)) d v s j := by
  rw [mEntry_eq _ _ _ _ _ _ _ ht hj, mEntry_eq _ _ _ _ _ _ _ hs hj]
  simp only [logitT, mul_add, Finset.sum_add_distrib, Finset.mul_sum]

theorem mem_allInputs_two (v : Nat) (x : Input) (hx : x ∈ allInputs [v, v]) :
    ∃ t s, x = [t, s] ∧ t < v ∧ s < v := by
  simp only [allInputs, List.mem_flatMap, List.mem_map, List.mem_range, List.map_cons, List.map_nil,
    List.mem_singleton] at hx
  obtain ⟨t, ht, y, ⟨s, hs, rfl⟩, rfl⟩ := hx
  exact ⟨t, s, rfl, ht, hs⟩

/-! ## Soundness -/

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  simp only [D, CostM.exec, Interp.counting_bind, CostM.run_bind] at h
  rcases hE : List.lookup "embedding.weight" w with _ | tE
  · simp [CostM.weightShape, hE] at h
  rcases hL : List.lookup "linear.weight" w with _ | tL
  · simp [CostM.weightShape, hE, hL] at h
  rcases hU : List.lookup "unembedding.weight" w with _ | tU
  · simp [CostM.weightShape, hE, hL, hU] at h
  simp only [CostM.weightShape, CostM.weightSize, hE, hL, hU] at h
  match hsh : tE.shape with
  | [] =>
    simp only [hsh, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact Nat.zero_le _
  | [_] =>
    simp only [hsh, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact Nat.zero_le _
  | _ :: _ :: _ :: _ =>
    simp only [hsh, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    exact Nat.zero_le _
  | [d, v] =>
    simp only [hsh] at h
    split_ifs at h with hc
    · obtain ⟨hLs, hUs, hEz, hLz, hUz, hv, hv2⟩ := hc
      have hv' : v = 64 := hv
      simp only [body, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at h
      have hrE := readList_run ⟨w, c⟩ _ tE hE (d*v) (by omega) []
      have hrL := readList_run ⟨w, c⟩ _ tL hL (d*d) (by omega) []
      have hrU := readList_run ⟨w, c⟩ _ tU hU (v*d) (by omega) []
      simp only [hrE, hrL, hrU] at h
      obtain ⟨c4, h4⟩ := computeCols_run ⟨w, c⟩ (readPure tE (d*v)) (readPure tL (d*d))
        (readPure tU (v*d)) d v (List.range v) [] []
      simp only [h4, List.nil_append] at h
      rcases h5 : (oksFor Interp.counting ((List.range v).map
          (colPure (readPure tE (d*v)) (readPure tL (d*d)) (readPure tU (v*d)) d v)) v
          (List.range v)).run ⟨w, c⟩ c4 with _ | ⟨oks, c5⟩
      · simp [h5] at h
      simp only [h5, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hn, _⟩ := h
      obtain ⟨hlen, hspec⟩ := oksFor_spec ⟨w, c⟩ _ v hv2 (List.range v) c4 oks c5 h5
        (fun m hm => List.mem_range.mp hm)
      unfold numCorrect
      refine tally_le w oks _ ?_ n hn
      intro x hx hok
      have hx' : x ∈ allInputs [64, 64] := hx
      obtain ⟨t, s, rfl, ht, hs⟩ := mem_allInputs_two 64 x hx'
      -- the verdict
      have hmax : max t s < v := by omega
      have hrow := hspec (max t s) (by simp; omega)
      have hk : (List.range v).getD (max t s) 0 = max t s := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_range hmax]
      rw [hk] at hrow
      simp only [okOf] at hok
      obtain ⟨_, hstrict⟩ := hrow (min t s) hok
      -- the columns
      have hcol : ∀ a < v, ((List.range v).map (colPure (readPure tE (d*v)) (readPure tL (d*d))
          (readPure tU (v*d)) d v)).getD a [] = colPure (readPure tE (d*v)) (readPure tL (d*d))
          (readPure tU (v*d)) d v a := by
        intro a ha
        simp [List.getD_eq_getElem?_getD, ha]
      have hq : ∀ a < v, ∀ j < v, qget (colPure (readPure tE (d*v)) (readPure tL (d*d))
          (readPure tU (v*d)) d v a) j = mEntry (readPure tE (d*v)) (readPure tL (d*d))
          (readPure tU (v*d)) d v a j := by
        intro a ha j hj
        exact qget_map_range _ v j hj
      obtain ⟨out, hout, hos, hoz, hog⟩ :=
        evalGraph_formula w tE tL tU d v hE hL hU hsh hEz hLs hLz hUs hUz hv' t s (by omega) (by omega)
      have hlabel : task.label [t, s] = max t s := by
        show List.foldl max 0 [t, s] = max t s
        simp
      have hmin : min t s < v := by omega
      refine ⟨_, realOutput_of_evalGraph hout, ?_, ?_, ?_⟩
      · simp [hos, hoz]
      · simp [hlabel, hoz]; omega
      · intro j hj hne
        simp only [Tensor.map_data_size, hoz] at hj
        rw [hlabel] at hne ⊢
        rw [Tensor.get_map_cast, Tensor.get_map_cast, hog j hj, hog _ hmax]
        have key := hstrict j hj hne
        rw [hcol (min t s) hmin, hcol (max t s) hmax, hq (min t s) hmin j hj, hq (max t s) hmax j hj,
          hq (min t s) hmin (max t s) hmax, hq (max t s) hmax (max t s) hmax] at key
        rw [logitT_eq tE tL tU d v t s j (by omega) (by omega) hj,
          logitT_eq tE tL tU d v t s (max t s) (by omega) (by omega) hmax]
        have hcast : ∀ x y : ℚ, x < y → ((x : ℚ) : ℝ) < ((y : ℚ) : ℝ) :=
          fun x y h => by exact_mod_cast h
        apply hcast
        rcases le_total t s with hts | hts
        · rw [min_eq_left hts, max_eq_right hts] at key
          rw [max_eq_right hts]
          exact key
        · rw [min_eq_right hts, max_eq_left hts] at key
          rw [max_eq_left hts]
          linarith
    · simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, _⟩ := h
      exact Nat.zero_le _

/-! ## Glue for the instance: the run of a loop is the runs of its parts -/

/-- The prelude of `D` on weights of the right shapes: its run is the body's run. -/
theorem D_run_eq (env : Env) (tE tL tU : Tensor ℚ) (d v : Nat)
    (hE : List.lookup "embedding.weight" env.weights = some tE)
    (hL : List.lookup "linear.weight" env.weights = some tL)
    (hU : List.lookup "unembedding.weight" env.weights = some tU)
    (hEs : tE.shape = [d, v]) (hLs : tL.shape = [d, d]) (hUs : tU.shape = [v, d])
    (hEz : tE.data.size = d * v) (hLz : tL.data.size = d * d) (hUz : tU.data.size = v * d)
    (hv : v = graph.values) (hv2 : 2 ≤ v) (c : Cost) :
    (D Interp.counting).run env c = (body Interp.counting d v).run env c := by
  simp only [D, Interp.counting_bind, CostM.run_bind, CostM.weightShape, CostM.weightSize,
    hE, hL, hU, hEs]
  rw [if_pos ⟨hLs, hUs, hEz, hLz, hUz, hv, hv2⟩]

theorem computeCols_run_of (env : Env) (E L U : List Q) (d v : Nat) (cst : Nat → Cost)
    (col : Nat → List Q) :
    ∀ (n a0 : Nat) (acc : List (List Q)),
      (∀ a, a0 ≤ a → a < a0 + n →
        (computeCol Interp.counting E L U d v a).run env (cst a) = some (col a, cst (a+1))) →
      (computeCols Interp.counting E L U d v (List.range' a0 n) acc).run env (cst a0) =
        some (acc ++ (List.range' a0 n).map col, cst (a0 + n))
  | 0, a0, acc, _ => by simp [computeCols, CostM.run_pure]
  | n+1, a0, acc, hf => by
    have h0 := hf a0 (le_refl _) (by omega)
    have ih := computeCols_run_of env E L U d v cst col n (a0+1) (acc ++ [col a0])
      (fun a h1 h2 => hf a (by omega) (by omega))
    simp only [List.range'_succ, computeCols, Interp.counting_bind, CostM.run_bind, h0, ih,
      List.map_cons, List.append_assoc, List.singleton_append]
    rw [show a0 + 1 + n = a0 + (n+1) by omega]

theorem oksFor_run_append (env : Env) (cols : List (List Q)) (v : Nat) :
    ∀ (l1 l2 : List Nat) (c : Cost) (r1 : List (List Bool)) (c1 : Cost) (r2 : List (List Bool))
      (c2 : Cost),
      (oksFor Interp.counting cols v l1).run env c = some (r1, c1) →
      (oksFor Interp.counting cols v l2).run env c1 = some (r2, c2) →
      (oksFor Interp.counting cols v (l1 ++ l2)).run env c = some (r1 ++ r2, c2)
  | [], l2, c, r1, c1, r2, c2, h1, h2 => by
    simp only [oksFor, Interp.counting_pure, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    simpa using h2
  | m :: l1, l2, c, r1, c1, r2, c2, h1, h2 => by
    simp only [oksFor, Interp.counting_bind, Interp.counting_pure, CostM.run_bind] at h1
    split at h1
    · rename_i r c' hr
      split at h1
      · rename_i rs c'' hrs
        simp only [CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨rfl, rfl⟩ := h1
        rw [List.cons_append, oksFor]
        simp only [Interp.counting_bind, Interp.counting_pure, CostM.run_bind, hr,
          oksFor_run_append env cols v l1 l2 c' rs c'' r2 c2 hrs h2, CostM.run_pure, List.cons_append]
      · cases h1
    · cases h1

end Candidate.MaxDirect
