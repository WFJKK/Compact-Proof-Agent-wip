import Candidate.Sound3

/-!
# Checker4: Checker3 with the flag test as one comparison of `theta` against the minimum over `j ≠ m` of `L_j`
(a min per `j` instead of a comparison and a gate per `j`), with its soundness.
-/

namespace Candidate.Checker4
open CompactCheck Candidate.Loops Candidate.Tables Candidate.Formula Candidate.Checker Candidate.Checker2
  Candidate.Checker3 Finset

/-- `min(acc, f k : k < n, k ≠ m)`. -/
def minExM (I : Interp) (f : Nat → I.V) (m : Nat) : Nat → I.V → I.M I.V
  | 0, acc => pure acc
  | k+1, acc => if k = m then minExM I f m k acc else do
      let acc' ← I.min "" acc (f k)
      minExM I f m k acc'

/-- `theta < min_{j ≠ m} L_j`. -/
def okOfM3 (I : Interp) (term Fm Fm1 fx3 : Array I.V) (theta : I.V) (m istar : Nat) : I.M I.B := do
  let L ← tableM I (fun j =>
    if j = m then pure I.zero else do
      let L0 ← I.add "" (fx3.getD j I.zero) (cSel I term Fm Fm1 istar 0 j)
      let L1 ← I.add "" L0 (cSel I term Fm Fm1 istar 1 j)
      I.add "" L1 (cSel I term Fm Fm1 istar 2 j)) 64 0 (E0 I)
  let mn ← minExM I (fun j => L.getD j I.zero) m 64 (L.getD (if m = 0 then 1 else 0) I.zero)
  I.lt "" theta mn

def groupFlagsK (I : Interp) (tabs : Tabs I) (dov n1 : Array I.V) (H4 : I.V) (t3 m : Nat) (K : I.V) (a : Nat) :
    I.M (List I.B) := do
  let cpr ← tableM I (fun j => I.sub "" (tabs.dm.getD (t3*64+j) I.zero) (tabs.dm.getD (t3*64+m) I.zero)) 64 0 (E0 I)
  let exlo ← tableM I (fun k =>
    if a + k%3 ≤ m then do
      let p ← expAt I tabs K t3 (k/3) (a + k%3)
      pure p.1
    else pure I.zero) 9 0 (E0 I)
  let exhi ← tableM I (fun k =>
    if a + k%3 ≤ m then do
      let p ← expAt I tabs K t3 (k/3) (a + k%3)
      pure p.2
    else pure I.zero) 9 0 (E0 I)
  let e3 ← expAt I tabs K t3 3 t3
  let negEfar ← tableM I (fun i =>
    if a = 0 then pure I.zero else do
      let d ← I.sub "" (tabs.spre.getD ((t3*3+i)*65+a) I.zero) K
      let p ← I.exp "" d
      I.neg "" p.2) 3 0 (E0 I)
  let dtab ← tableM I (fun k => I.sub "" (exhi.getD k I.zero) (exlo.getD k I.zero)) 9 0 (E0 I)
  let d3 ← I.sub "" e3.2 e3.1
  let dmax ← maxM I (fun k => dtab.getD k I.zero) 9 d3
  let theta ← I.muladd "" I.zero dmax H4
  let term ← tableM I (fun k => do
    let h ← hD I dov cpr m a (k/64) m (k%64)
    loProdM I (exlo.getD (k/64*3 + (m-a)) I.zero) h) 192 0 (E0 I)
  let Fm ← tableM I (fun k => do
    let near ← minRangeM I (fun t => do
      let h ← hD I dov cpr m a (k/64) t (k%64)
      loProdM I (exlo.getD (k/64*3 + (t-a)) I.zero) h) a (m - a)
    if a = 0 then pure near else do
      let n2 ← I.add "" (cpr.getD (k%64) I.zero) (n1.getD ((k/64*64 + k%64)*64 + m) I.zero)
      let n3 ← I.max "" I.zero n2
      let far ← I.muladd "" I.zero (negEfar.getD (k/64) I.zero) n3
      I.min "" near far) 192 0 (E0 I)
  let Fm1 ← tableM I (fun k => I.min "" (Fm.getD k I.zero) (term.getD k I.zero)) 192 0 (E0 I)
  let fx3 ← tableM I (fun j => do
    let h ← hM I tabs cpr m 3 t3 j
    loProdM I e3.1 h) 64 0 (E0 I)
  if t3 = m then do
    let ok3 ← okOfM3 I term Fm Fm1 fx3 theta m 3
    pure [I.bfalse, I.bfalse, I.bfalse, ok3]
  else do
    let ok0 ← okOfM3 I term Fm Fm1 fx3 theta m 0
    let ok1 ← okOfM3 I term Fm Fm1 fx3 theta m 1
    let ok2 ← okOfM3 I term Fm Fm1 fx3 theta m 2
    pure [ok0, ok1, ok2, I.bfalse]

def stepFlags (I : Interp) (tabs : Tabs I) (dov n1 : Array I.V) (H4 : I.V) (plan : List Nat) (lo hi g2 : Nat) :
    I.M (List I.B) :=
  if g2 / 64 ≤ g2 % 64 && g2 % 64 ≠ 0 && lo ≤ g2 / 64 && g2 / 64 < hi then
    groupFlagsK I tabs dov n1 H4 (g2 / 64) (g2 % 64) (tabs.kk.getD (g2 / 64 * 64 + g2 % 64) I.zero) (aOf plan (g2 % 64))
  else pure [I.bfalse, I.bfalse, I.bfalse, I.bfalse]

def groupsM (I : Interp) (tabs : Tabs I) (dov n1 : Array I.V) (H4 : I.V) (plan : List Nat) (lo hi : Nat) :
    Nat → Nat → Array I.B → I.M (Array I.B)
  | 0, _, arr => pure arr
  | k+1, g2, arr => do
    let fl ← stepFlags I tabs dov n1 H4 plan lo hi g2
    groupsM I tabs dov n1 H4 plan lo hi k (g2+1)
      ((((arr.push (fl.getD 0 I.bfalse)).push (fl.getD 1 I.bfalse)).push (fl.getD 2 I.bfalse)).push (fl.getD 3 I.bfalse))

def D (plan : List Nat) : Checker := fun I => do
  let ok ← shapesOk I
  if !ok then pure I.nzero else do
    let tabs ← buildTabs I
    let H4 ← boundH I tabs
    let dov ← buildDov I tabs plan
    let n1 ← buildN1 I tabs plan
    let flags ← groupsM I tabs dov n1 H4 plan (plan.getD 0 0) (plan.getD 1 64) 4096 0 (Array.mk [])
    pure (sumInputs I [64, 64, 64, 64] (fun x => I.countB (flags.getD (gidx x) I.bfalse)))

section
variable {env : Env} {E P WQ WK WV WO U C : Tensor ℚ} {tabs : Tabs Interp.counting}

theorem spec_minExM (f : Nat → Q) (m : Nat) : ∀ (n : Nat) (acc : Q),
    Spec env (minExM Interp.counting f m n acc) fun v => v.val ≤ acc.val ∧ ∀ k < n, k ≠ m → v.val ≤ (f k).val
  | 0, acc => by
    simp only [minExM]
    exact spec_pure ⟨le_refl _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n+1, acc => by
    show Spec env (if n = m then minExM Interp.counting f m n acc else
      (CostM.qmin "" acc (f n) >>= fun acc' => minExM Interp.counting f m n acc')) _
    by_cases hnm : n = m
    · rw [if_pos hnm]
      refine spec_mono ?_ (spec_minExM f m n acc)
      intro v ⟨h1, h2⟩
      exact ⟨h1, fun k hk hkm => h2 k (by omega) hkm⟩
    · rw [if_neg hnm]
      refine spec_bind (spec_min "" acc (f n)) fun acc' hacc => ?_
      refine spec_mono ?_ (spec_minExM f m n acc')
      intro v ⟨h1, h2⟩
      rw [hacc] at h1
      refine ⟨le_trans h1 (min_le_left _ _), fun k hk hkm => ?_⟩
      by_cases hkn : k = n
      · subst hkn; exact le_trans h1 (min_le_right _ _)
      · exact h2 k (by omega) hkm

theorem spec_okOfM3 {term Fm Fm1 fx3 : Array Q} {t3 m : Nat} {K : ℚ} {sl : ℝ} (istar : Nat) (theta : Q)
    (htheta : 4 * sl ≤ (theta.val : ℝ))
    (hterm : ∀ i j, i < 3 → j < 64 → ((term.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i m j + sl)
    (hFm : ∀ i j, i < 3 → j < 64 → ∀ t < m, ((Fm.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i t j + sl)
    (hFm1 : ∀ i j, i < 3 → j < 64 → ∀ t ≤ m, ((Fm1.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K i t j + sl)
    (hfx3 : ∀ j < 64, ((fx3.getD j ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K 3 t3 j + sl) :
    Spec env (okOfM3 Interp.counting term Fm Fm1 fx3 theta m istar) fun b => b = true →
      ∀ j < 64, j ≠ m → ∀ t0 t1 t2, InRange m istar 0 t0 → InRange m istar 1 t1 → InRange m istar 2 t2 →
        0 < T E P WQ WK WV WO U C t3 m K 0 t0 j + T E P WQ WK WV WO U C t3 m K 1 t1 j +
          T E P WQ WK WV WO U C t3 m K 2 t2 j + T E P WQ WK WV WO U C t3 m K 3 t3 j := by
  unfold okOfM3
  refine spec_bind (spec_table0 (P := fun j v => j ≠ m → j < 64 → ∀ t0 t1 t2,
      InRange m istar 0 t0 → InRange m istar 1 t1 → InRange m istar 2 t2 →
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K 0 t0 j + T E P WQ WK WV WO U C t3 m K 1 t1 j +
        T E P WQ WK WV WO U C t3 m K 2 t2 j + T E P WQ WK WV WO U C t3 m K 3 t3 j + 4 * sl) ?_ 64) fun L hL => ?_
  · intro j
    by_cases hjm : j = m
    · rw [if_pos hjm]
      exact spec_pure fun h => absurd hjm h
    · rw [if_neg hjm]
      refine spec_bind (spec_add "" _ _) fun L0 hL0 => ?_
      refine spec_bind (spec_add "" L0 _) fun L1 hL1 => ?_
      refine spec_mono ?_ (spec_add "" L1 _)
      intro v hv _ hj t0 t1 t2 h0 h1 h2
      rw [hv, hL1, hL0]
      push_cast
      have c0 := cSel_le' (g := fun i t => T E P WQ WK WV WO U C t3 m K i t j + sl)
        (hterm 0 j (by omega) hj) (hFm 0 j (by omega) hj) (hFm1 0 j (by omega) hj) h0
      have c1 := cSel_le' (g := fun i t => T E P WQ WK WV WO U C t3 m K i t j + sl)
        (hterm 1 j (by omega) hj) (hFm 1 j (by omega) hj) (hFm1 1 j (by omega) hj) h1
      have c2 := cSel_le' (g := fun i t => T E P WQ WK WV WO U C t3 m K i t j + sl)
        (hterm 2 j (by omega) hj) (hFm 2 j (by omega) hj) (hFm1 2 j (by omega) hj) h2
      have c3 := hfx3 j hj
      linarith
  refine spec_bind (spec_minExM _ m 64 _) fun mn hmn => ?_
  refine spec_mono ?_ (spec_lt "" theta mn)
  intro b hb htrue j hj hjm t0 t1 t2 h0 h1 h2
  rw [hb] at htrue
  have hpos : theta.val < mn.val := by simpa using htrue
  have hle : mn.val ≤ (L.getD j ⟨0⟩).val := hmn.2 j hj hjm
  have hLj := hL j hj hjm hj t0 t1 t2 h0 h1 h2
  have hpos' : (theta.val : ℝ) < ((L.getD j ⟨0⟩).val : ℝ) := by exact_mod_cast lt_of_lt_of_le hpos hle
  linarith

theorem spec_groupFlagsK4 (hT : TabsOk E P WQ WK WV WO U C tabs) (dov n1 : Array Q) (H4 : Q) (Hb : ℚ)
    (hH4 : H4.val = 4 * Hb) (t3 m : Nat) (K : Q) (a : Nat)
    (hH : ∀ i t j, i < 4 → t < 64 → j < 64 →
      |(DmQ E P U t3 m + OVQ E P WV WO U i t m) - (DmQ E P U t3 j + OVQ E P WV WO U i t j)| ≤ Hb)
    (hdov : ∀ i t j, i < 3 → a ≤ t → t ≤ m → j < 64 →
      (dov.getD ((i*3 + (t-a))*4096 + m*64 + j) ⟨0⟩).val =
        (tabs.ov.getD ((i*64+t)*64+m) ⟨0⟩).val - (tabs.ov.getD ((i*64+t)*64+j) ⟨0⟩).val)
    (hn1 : ∀ i j, i < 3 → j < 64 → (n1.getD ((i*64+j)*64 + m) ⟨0⟩).val =
      (tabs.ovmax.getD ((i*64+j)*65 + a) ⟨0⟩).val - (tabs.ovmin.getD ((i*64+m)*65 + a) ⟨0⟩).val)
    (h3 : t3 < 64) (hm : m < 64) (ham : a + 1 ≤ m) (ha2 : m ≤ a + 2) :
    Spec env (groupFlagsK Interp.counting tabs dov n1 H4 t3 m K a) fun l =>
      l.length = 4 ∧ ∀ istar, istar < 4 → l.getD istar false = true →
        ∀ j < 64, j ≠ m → ∀ t0 t1 t2, InRange m istar 0 t0 → InRange m istar 1 t1 → InRange m istar 2 t2 →
          0 < T E P WQ WK WV WO U C t3 m K.val 0 t0 j + T E P WQ WK WV WO U C t3 m K.val 1 t1 j +
            T E P WQ WK WV WO U C t3 m K.val 2 t2 j + T E P WQ WK WV WO U C t3 m K.val 3 t3 j := by
  unfold groupFlagsK
  refine spec_bind (spec_table0 (P := fun j v => v.val = (tabs.dm.getD (t3 * 64 + j) ⟨0⟩).val - (tabs.dm.getD (t3 * 64 + m) ⟨0⟩).val)
    (fun j => spec_sub "" _ _) 64) fun cpr hcpr0 => ?_
  have hcpr : ∀ j < 64, (cpr.getD j ⟨0⟩).val = DmQ E P U t3 j - DmQ E P U t3 m := by
    intro j hj
    rw [hcpr0 j hj, hT.dm t3 j h3 hj, hT.dm t3 m h3 hm]
  refine spec_bind (spec_table0 (P := fun k v => a + k % 3 ≤ m →
      (v.val : ℝ) ≤ Real.exp (((tabs.s.getD ((t3 * 4 + k / 3) * 64 + (a + k % 3)) ⟨0⟩).val - K.val : ℚ))) ?_ 9)
      fun exlo hP1 => ?_
  · intro k
    by_cases hk : a + k % 3 ≤ m
    · rw [if_pos hk]
      exact spec_bind (spec_expAt tabs K t3 (k / 3) (a + k % 3)) fun p hp => spec_pure fun _ => hp.1
    · rw [if_neg hk]
      exact spec_pure fun h => absurd h hk
  have hexlo : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      ((exlo.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ) ≤ Real.exp ((SQ E P WQ WK C t3 i t - K.val : ℚ) : ℝ) := by
    intro i t hi hat htm
    have := hP1 (i * 3 + (t - a)) (by omega)
    have e1 : (i * 3 + (t - a)) / 3 = i := by omega
    have e2 : a + (i * 3 + (t - a)) % 3 = t := by omega
    rw [e1, e2, hT.s t3 i t h3 (by omega) (by omega)] at this
    exact this htm
  refine spec_bind (spec_table0 (P := fun k v => a + k % 3 ≤ m →
      Real.exp (((tabs.s.getD ((t3 * 4 + k / 3) * 64 + (a + k % 3)) ⟨0⟩).val - K.val : ℚ)) ≤ (v.val : ℝ)) ?_ 9)
      fun exhi hP2 => ?_
  · intro k
    by_cases hk : a + k % 3 ≤ m
    · rw [if_pos hk]
      exact spec_bind (spec_expAt tabs K t3 (k / 3) (a + k % 3)) fun p hp => spec_pure fun _ => hp.2
    · rw [if_neg hk]
      exact spec_pure fun h => absurd h hk
  have hexhi : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      Real.exp ((SQ E P WQ WK C t3 i t - K.val : ℚ) : ℝ) ≤ ((exhi.getD (i * 3 + (t - a)) ⟨0⟩).val : ℝ) := by
    intro i t hi hat htm
    have := hP2 (i * 3 + (t - a)) (by omega)
    have e1 : (i * 3 + (t - a)) / 3 = i := by omega
    have e2 : a + (i * 3 + (t - a)) % 3 = t := by omega
    rw [e1, e2, hT.s t3 i t h3 (by omega) (by omega)] at this
    exact this htm
  refine spec_bind (spec_expAt tabs K t3 3 t3) fun e3 he3 => ?_
  refine spec_bind (spec_table0 (P := fun i v => a ≠ 0 → ∃ hi : ℚ, v.val = -hi ∧
      Real.exp (((tabs.spre.getD ((t3 * 3 + i) * 65 + a) ⟨0⟩).val - K.val : ℚ) : ℝ) ≤ hi) ?_ 3)
      fun negEfar hP3 => ?_
  · intro i
    by_cases ha0 : a = 0
    · rw [if_pos ha0]
      exact spec_pure fun h => absurd ha0 h
    · rw [if_neg ha0]
      refine spec_bind (spec_sub "" _ K) fun d hd => ?_
      refine spec_bind (spec_exp "" d) fun p hp => ?_
      refine spec_mono ?_ (spec_neg "" p.2)
      intro v hv _
      refine ⟨p.2.val, hv, ?_⟩
      rw [hd] at hp
      exact hp.2
  have hneg : ∀ i < 3, a ≠ 0 → ∃ hi : ℚ, (negEfar.getD i ⟨0⟩).val = -hi ∧
      Real.exp (((tabs.spre.getD ((t3 * 3 + i) * 65 + a) ⟨0⟩).val - K.val : ℚ) : ℝ) ≤ hi := by
    intro i hi
    exact hP3 i hi
  refine spec_bind (spec_table0 (P := fun k v => v.val = (exhi.getD k ⟨0⟩).val - (exlo.getD k ⟨0⟩).val)
    (fun k => spec_sub "" _ _) 9) fun dtab hdtab => ?_
  refine spec_bind (spec_sub "" e3.2 e3.1) fun d3 hd3 => ?_
  refine spec_bind (spec_maxM _ 9 d3) fun dmax hdmax => ?_
  refine spec_bind (spec_muladd "" _ dmax H4) fun theta htheta => ?_
  have hd : ∀ i t, i < 3 → a ≤ t → t ≤ m →
      (exhi.getD (i * 3 + (t - a)) ⟨0⟩).val - (exlo.getD (i * 3 + (t - a)) ⟨0⟩).val ≤ dmax.val := by
    intro i t hi hat htm
    have h1 : (dtab.getD (i * 3 + (t - a)) ⟨0⟩).val ≤ dmax.val := hdmax.2 _ (by omega)
    rw [hdtab _ (by omega)] at h1
    exact h1
  have hd3' : e3.2.val - e3.1.val ≤ dmax.val := by
    rw [← hd3]
    exact hdmax.1
  have hsl : 0 ≤ dmax.val * Hb := by
    apply mul_nonneg
    · have h1 : (e3.1.val : ℝ) ≤ e3.2.val := le_trans he3.1 he3.2
      have h2 : e3.1.val ≤ e3.2.val := by exact_mod_cast h1
      linarith
    · have := hH 0 0 0 (by omega) (by omega) (by omega)
      exact le_trans (abs_nonneg _) this
  have hth : 4 * ((dmax.val * Hb : ℚ) : ℝ) ≤ (theta.val : ℝ) := by
    rw [htheta, hH4]
    show 4 * ((dmax.val * Hb : ℚ) : ℝ) ≤ (((0 : ℚ) + dmax.val * (4 * Hb) : ℚ) : ℝ)
    exact le_of_eq (by push_cast; ring)
  refine spec_bind (spec_table0 (P := fun k v => k < 192 →
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) m (k % 64) + ((dmax.val * Hb : ℚ) : ℝ))
      (fun k => spec_termEntry3 hT hm hcpr hexlo hexhi hd hH hdov k m (by omega) le_rfl) 192)
      fun term hP4 => ?_
  have htermk : ∀ k < 192, ((term.getD k ⟨0⟩).val : ℝ) ≤
      T E P WQ WK WV WO U C t3 m K.val (k / 64) m (k % 64) + ((dmax.val * Hb : ℚ) : ℝ) :=
    fun k hk => hP4 k hk hk
  have hterm : ∀ i j, i < 3 → j < 64 → ((term.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤
      T E P WQ WK WV WO U C t3 m K.val i m j + ((dmax.val * Hb : ℚ) : ℝ) := by
    intro i j hi hj
    have := htermk (i * 64 + j) (by omega)
    have e1 : (i * 64 + j) / 64 = i := by omega
    have e2 : (i * 64 + j) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  refine spec_bind (spec_table0 (P := fun k v => k < 192 → ∀ t < m,
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) t (k % 64) + ((dmax.val * Hb : ℚ) : ℝ))
      (fun k => spec_FmEntry3 hT h3 hm ham hsl hcpr hexlo hexhi hd hH hdov hn1 hneg k) 192)
      fun Fm hP5 => ?_
  have hFmk : ∀ k < 192, ∀ t < m, ((Fm.getD k ⟨0⟩).val : ℝ) ≤
      T E P WQ WK WV WO U C t3 m K.val (k / 64) t (k % 64) + ((dmax.val * Hb : ℚ) : ℝ) :=
    fun k hk => hP5 k hk hk
  have hFm : ∀ i j, i < 3 → j < 64 → ∀ t < m,
      ((Fm.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val i t j + ((dmax.val * Hb : ℚ) : ℝ) := by
    intro i j hi hj
    have := hFmk (i * 64 + j) (by omega)
    have e1 : (i * 64 + j) / 64 = i := by omega
    have e2 : (i * 64 + j) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  refine spec_bind (spec_table0 (P := fun k v => k < 192 → ∀ t ≤ m,
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val (k / 64) t (k % 64) + ((dmax.val * Hb : ℚ) : ℝ)) ?_ 192)
      fun Fm1 hP6 => ?_
  · intro k
    refine spec_mono ?_ (spec_min "" _ _)
    intro v hv hk t ht
    rw [hv, Rat.cast_min]
    by_cases htm : t < m
    · exact le_trans (min_le_left _ _) (hFmk k hk t htm)
    · have : t = m := by omega
      subst this
      exact le_trans (min_le_right _ _) (htermk k hk)
  have hFm1 : ∀ i j, i < 3 → j < 64 → ∀ t ≤ m,
      ((Fm1.getD (i * 64 + j) ⟨0⟩).val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val i t j + ((dmax.val * Hb : ℚ) : ℝ) := by
    intro i j hi hj
    have := hP6 (i * 64 + j) (by omega) (by omega)
    have e1 : (i * 64 + j) / 64 = i := by omega
    have e2 : (i * 64 + j) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  refine spec_bind (spec_table0 (P := fun j v => j < 64 →
      (v.val : ℝ) ≤ T E P WQ WK WV WO U C t3 m K.val 3 t3 j + ((dmax.val * Hb : ℚ) : ℝ))
      (fun j => spec_fx3Entry2 hT h3 hm hcpr he3 hd3' hH j) 64) fun fx3 hP7 => ?_
  have hfx3 : ∀ j < 64, ((fx3.getD j ⟨0⟩).val : ℝ) ≤
      T E P WQ WK WV WO U C t3 m K.val 3 t3 j + ((dmax.val * Hb : ℚ) : ℝ) :=
    fun j hj => hP7 j hj hj
  by_cases h3m : t3 = m
  · rw [if_pos h3m]
    refine spec_bind (spec_okOfM3 3 theta hth hterm hFm hFm1 hfx3) fun ok3 hok3 => ?_
    refine spec_pure ⟨rfl, ?_⟩
    intro istar hi htrue
    match istar with
    | 0 => simp at htrue
    | 1 => simp at htrue
    | 2 => simp at htrue
    | 3 => exact hok3 (by simpa using htrue)
  · rw [if_neg h3m]
    refine spec_bind (spec_okOfM3 0 theta hth hterm hFm hFm1 hfx3) fun ok0 hok0 => ?_
    refine spec_bind (spec_okOfM3 1 theta hth hterm hFm hFm1 hfx3) fun ok1 hok1 => ?_
    refine spec_bind (spec_okOfM3 2 theta hth hterm hFm hFm1 hfx3) fun ok2 hok2 => ?_
    refine spec_pure ⟨rfl, ?_⟩
    intro istar hi htrue
    match istar with
    | 0 => exact hok0 (by simpa using htrue)
    | 1 => exact hok1 (by simpa using htrue)
    | 2 => exact hok2 (by simpa using htrue)
    | 3 => simp at htrue

theorem spec_groupStep4 (hT : TabsOk E P WQ WK WV WO U C tabs) (dov n1 : Array Q) (plan : List Nat)
    (hdovG : ∀ i r m j, i < 3 → r < 3 → m < 64 → j < 64 → aOf plan m + r ≤ m →
      (dov.getD ((i*3+r)*4096 + m*64 + j) ⟨0⟩).val =
        (tabs.ov.getD ((i*64 + (aOf plan m + r))*64 + m) ⟨0⟩).val -
          (tabs.ov.getD ((i*64 + (aOf plan m + r))*64 + j) ⟨0⟩).val)
    (hn1G : ∀ i j m, i < 3 → j < 64 → m < 64 →
      (n1.getD ((i*64+j)*64 + m) ⟨0⟩).val =
        (tabs.ovmax.getD ((i*64+j)*65 + aOf plan m) ⟨0⟩).val - (tabs.ovmin.getD ((i*64+m)*65 + aOf plan m) ⟨0⟩).val)
    (H4 : Q) (Hb : ℚ) (hH4 : H4.val = 4 * Hb)
    (hH : ∀ t3 m i t j, t3 < 64 → m < 64 → i < 4 → t < 64 → j < 64 →
      |(DmQ E P U t3 m + OVQ E P WV WO U i t m) - (DmQ E P U t3 j + OVQ E P WV WO U i t j)| ≤ Hb)
    (lo hi g2 : Nat) :
    Spec env (stepFlags Interp.counting tabs dov n1 H4 plan lo hi g2)
      fun fl => ∀ istar < 4, fl.getD istar false = true → GroupOk E P WQ WK WV WO U C tabs g2 istar := by
  unfold stepFlags
  by_cases hc : (g2 / 64 ≤ g2 % 64 && g2 % 64 ≠ 0 && lo ≤ g2 / 64 && g2 / 64 < hi) = true
  · rw [if_pos hc]
    simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq] at hc
    intro c v c' hr istar hi hfl h3
    have hm : g2 % 64 < 64 := Nat.mod_lt _ (by omega)
    have ha1 : aOf plan (g2 % 64) + 1 ≤ g2 % 64 := by unfold aOf; split_ifs <;> omega
    have ha2 : g2 % 64 ≤ aOf plan (g2 % 64) + 2 := by unfold aOf; split_ifs <;> omega
    have hdov : ∀ i t j, i < 3 → aOf plan (g2 % 64) ≤ t → t ≤ g2 % 64 → j < 64 →
        (dov.getD ((i*3 + (t - aOf plan (g2 % 64)))*4096 + g2 % 64*64 + j) ⟨0⟩).val =
          (tabs.ov.getD ((i*64+t)*64+g2 % 64) ⟨0⟩).val - (tabs.ov.getD ((i*64+t)*64+j) ⟨0⟩).val := by
      intro i t j hi hat htm hj
      have := hdovG i (t - aOf plan (g2 % 64)) (g2 % 64) j hi (by omega) hm hj (by omega)
      rw [show aOf plan (g2 % 64) + (t - aOf plan (g2 % 64)) = t by omega] at this
      exact this
    have := spec_groupFlagsK4 hT dov n1 H4 Hb hH4 (g2 / 64) (g2 % 64) _ (aOf plan (g2 % 64))
      (fun i t j hi ht hj => hH (g2 / 64) (g2 % 64) i t j h3 hm hi ht hj) hdov
      (fun i j hi hj => hn1G i j (g2 % 64) hi hj hm) h3 hm ha1 ha2 c v c' hr
    exact this.2 istar hi hfl
  · rw [if_neg hc]
    refine spec_pure fun istar hi hfl => ?_
    exfalso
    match istar with
    | 0 => simp at hfl
    | 1 => simp at hfl
    | 2 => simp at hfl
    | 3 => simp at hfl

theorem spec_groupsM4 (hT : TabsOk E P WQ WK WV WO U C tabs) (dov n1 : Array Q) (plan : List Nat)
    (hdovG : ∀ i r m j, i < 3 → r < 3 → m < 64 → j < 64 → aOf plan m + r ≤ m →
      (dov.getD ((i*3+r)*4096 + m*64 + j) ⟨0⟩).val =
        (tabs.ov.getD ((i*64 + (aOf plan m + r))*64 + m) ⟨0⟩).val -
          (tabs.ov.getD ((i*64 + (aOf plan m + r))*64 + j) ⟨0⟩).val)
    (hn1G : ∀ i j m, i < 3 → j < 64 → m < 64 →
      (n1.getD ((i*64+j)*64 + m) ⟨0⟩).val =
        (tabs.ovmax.getD ((i*64+j)*65 + aOf plan m) ⟨0⟩).val - (tabs.ovmin.getD ((i*64+m)*65 + aOf plan m) ⟨0⟩).val)
    (H4 : Q) (Hb : ℚ) (hH4 : H4.val = 4 * Hb)
    (hH : ∀ t3 m i t j, t3 < 64 → m < 64 → i < 4 → t < 64 → j < 64 →
      |(DmQ E P U t3 m + OVQ E P WV WO U i t m) - (DmQ E P U t3 j + OVQ E P WV WO U i t j)| ≤ Hb)
    (lo hi : Nat) :
    ∀ (n g2 : Nat) (arr : Array Bool),
    Spec env (groupsM Interp.counting tabs dov n1 H4 plan lo hi n g2 arr) fun arr' =>
      ∃ l : List Bool, arr'.toList = arr.toList ++ l ∧ l.length = 4 * n ∧
        ∀ k (hk : k < l.length), l[k] = true → GroupOk E P WQ WK WV WO U C tabs (g2 + k / 4) (k % 4)
  | 0, g2, arr => by
    simp only [groupsM]
    exact spec_pure ⟨[], by simp, rfl, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n+1, g2, arr => by
    unfold groupsM
    refine spec_bind (spec_groupStep4 hT dov n1 plan hdovG hn1G H4 Hb hH4 hH lo hi g2) fun fl hfl => ?_
    refine spec_mono ?_ (spec_groupsM4 hT dov n1 plan hdovG hn1G H4 Hb hH4 hH lo hi n (g2+1) _)
    intro arr' ⟨l, hl, hlen, hP⟩
    refine ⟨[fl.getD 0 false, fl.getD 1 false, fl.getD 2 false, fl.getD 3 false] ++ l, ?_, ?_, ?_⟩
    · rw [hl]
      simp [Array.toList_push]
    · simp [hlen]; ring
    · intro k hk htrue
      by_cases hk4 : k < 4
      · rw [List.getElem_append_left (by simpa using hk4)] at htrue
        have e1 : g2 + k / 4 = g2 := by omega
        rw [e1]
        match k, hk4 with
        | 0, _ => exact hfl 0 (by omega) (by simpa using htrue)
        | 1, _ => exact hfl 1 (by omega) (by simpa using htrue)
        | 2, _ => exact hfl 2 (by omega) (by simpa using htrue)
        | 3, _ => exact hfl 3 (by omega) (by simpa using htrue)
      · have hge : [fl.getD 0 false, fl.getD 1 false, fl.getD 2 false, fl.getD 3 false].length ≤ k := by
          simp; omega
        rw [List.getElem_append_right hge] at htrue
        have hk' : k - 4 < l.length := by
          simp only [List.length_append] at hk
          simp at hk
          omega
        have := hP (k - 4) (by simpa using hk') (by simpa using htrue)
        have e1 : g2 + 1 + (k - 4) / 4 = g2 + k / 4 := by omega
        have e2 : (k - 4) % 4 = k % 4 := by omega
        rw [e1, e2] at this
        exact this

end

open Classical Protected.N_attn_max4_v64_s0 in
theorem D_sound : ∀ (p : List Nat) (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D p Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro p w c n cost h
  unfold numCorrect
  suffices hS : Spec ⟨w, c⟩ (D p Interp.counting) fun n =>
      n ≤ (allInputs task.space).countP fun x => decide (Correct graph w task x) from hS [] n cost h
  unfold D
  refine spec_bind spec_shapesOk fun ok hok => ?_
  by_cases hok' : ok = true
  swap
  · have hf : (!ok) = true := by simp [hok']
    rw [if_pos hf]
    exact spec_pure (Nat.zero_le _)
  · have hf : ¬ ((!ok) = true) := by simp [hok']
    rw [if_neg hf]
    obtain ⟨⟨E, hE, hEs, hEn⟩, ⟨P, hP, hPs, hPn⟩, ⟨WQ, hWQ, hWQs, hWQn⟩, ⟨WK, hWK, hWKs, hWKn⟩,
      ⟨WV, hWV, hWVs, hWVn⟩, ⟨WO, hWO, hWOs, hWOn⟩, ⟨U, hU, hUs, hUn⟩, ⟨C, hC, hCs, hCn⟩⟩ := hok hok'
    refine spec_bind (spec_buildTabs hE hP hWQ hC hWK hWV hWO hU) fun tabs hT => ?_
    refine spec_bind (spec_boundH hT) fun H4 ⟨Hb, hH4, hH⟩ => ?_
    refine spec_bind (spec_buildDov tabs p) fun dov hdovG => ?_
    refine spec_bind (spec_buildN1 tabs p) fun n1 hn1G => ?_
    refine spec_bind (spec_groupsM4 hT dov n1 p hdovG hn1G H4 Hb hH4 hH (p.getD 0 0) (p.getD 1 64) 4096 0 (Array.mk []))
      fun flags ⟨l, hl, hlen, hPl⟩ => ?_
    refine spec_pure ?_
    rw [sumInputs_eq, space_eq]
    apply sum_le_countP'
    intro x hx
    obtain ⟨t0, t1, t2, t3, rfl, h0, h1, h2, h3⟩ := mem_space hx
    simp only [Interp.counting_countB]
    have hl' : flags.toList = l := by simpa using hl
    by_cases hf : flags.getD (gidx [t0, t1, t2, t3]) false = true
    · rw [hf]
      have hg : gidx [t0, t1, t2, t3] < l.length := by
        rw [hlen, gidx_eq]
        simp only
        split_ifs <;> omega
      rw [getD_of_toList hl' hg] at hf
      have hG := hPl _ hg hf
      rw [Nat.zero_add] at hG
      have hc := correct_of_flag (c := c) hE hEs hEn hP hPs hPn hWQ hWQs hWQn hC hCs hCn hWK hWKs hWKn
        hWV hWVs hWVn hWO hWOs hWOn hU hUs hUn t0 t1 t2 t3 h0 h1 h2 h3 hG
      simp [hc]
    · simp only [Bool.not_eq_true] at hf
      rw [hf]
      exact Nat.zero_le _

end Candidate.Checker4