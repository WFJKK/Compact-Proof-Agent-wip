import Candidate.ScanSpec

/-!
# Specifications of the tables of `buildTabs` (general lemmas; the OV chain).
-/

namespace Candidate.Tables
open CompactCheck Candidate.Loops Candidate.Formula Finset

section
variable {env : Env}

/-- Reading a table whose values are known: entry `k` is `g k` below `n`, and 0 beyond. -/
theorem getD_val_of_map {arr : Array Q} {n : Nat} {g : Nat → ℚ}
    (h : arr.toList.map Q.val = (List.range n).map g) (k : Nat) :
    (arr.getD k ⟨0⟩).val = if k < n then g k else 0 := by
  have h1 : (arr.toList.map Q.val)[k]? = ((List.range n).map g)[k]? := by rw [h]
  rw [List.getElem?_map, List.getElem?_map] at h1
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList]
  by_cases hk : k < n
  · rw [List.getElem?_range hk] at h1
    simp only [Option.map_some] at h1
    cases hl : arr.toList[k]? with
    | none => rw [hl] at h1; cases h1
    | some v =>
      rw [hl] at h1
      simp only [Option.map_some, Option.some.injEq] at h1
      simp [hl, h1, hk]
  · have hlen : arr.toList.length = n := by
      have := congrArg List.length h
      simpa using this
    rw [List.getElem?_eq_none (by omega : arr.toList.length ≤ k)]
    simp [hk]

theorem getD_val_lt {arr : Array Q} {n : Nat} {g : Nat → ℚ}
    (h : arr.toList.map Q.val = (List.range n).map g) {k : Nat} (hk : k < n) :
    (arr.getD k ⟨0⟩).val = g k := by
  rw [getD_val_of_map h k, if_pos hk]

/-- A table of 32-term dot products from two sources with known values. -/
theorem spec_dotTable {a b : Nat → Nat → CostM Q} {fa fb : Nat → Nat → ℚ} (cnt : Nat)
    (ha : ∀ k d, Spec env (a k d) fun x => x.val = fa k d)
    (hb : ∀ k d, Spec env (b k d) fun y => y.val = fb k d) :
    Spec env (tableM Interp.counting (fun k => dotM Interp.counting (a k) (b k) 32 Interp.counting.zero)
        cnt 0 (E0 Interp.counting))
      fun arr => arr.toList.map Q.val = (List.range cnt).map fun k => ∑ d ∈ range 32, fa k d * fb k d := by
  have h := spec_tableM (env := env) (g := fun k => ∑ d ∈ range 32, fa k d * fb k d)
    (f := fun k => dotM Interp.counting (a k) (b k) 32 Interp.counting.zero) ?_ cnt 0 (E0 Interp.counting)
  · refine spec_mono ?_ h
    intro arr harr
    rw [harr]
    simp [E0]
  · intro k
    refine spec_mono ?_ (spec_dotM (fa := fa k) (fb := fb k) 32 Interp.counting.zero
      (fun d _ => ha k d) (fun d _ => hb k d))
    intro v hv
    rw [hv]
    show (0 : ℚ) + _ = _
    rw [zero_add]

/-- A table of sums of two known tables. -/
theorem spec_addTable {ia ib : Nat → Nat} {A B : Array Q} {fa fb : Nat → ℚ} (cnt : Nat)
    (ha : ∀ k, (A.getD (ia k) ⟨0⟩).val = fa k) (hb : ∀ k, (B.getD (ib k) ⟨0⟩).val = fb k) :
    Spec env (tableM Interp.counting (fun k =>
        Interp.counting.add "" (A.getD (ia k) Interp.counting.zero) (B.getD (ib k) Interp.counting.zero))
        cnt 0 (E0 Interp.counting))
      fun arr => arr.toList.map Q.val = (List.range cnt).map fun k => fa k + fb k := by
  have h := spec_tableM (env := env) (g := fun k => fa k + fb k)
    (f := fun k => Interp.counting.add "" (A.getD (ia k) Interp.counting.zero) (B.getD (ib k) Interp.counting.zero))
    ?_ cnt 0 (E0 Interp.counting)
  · refine spec_mono ?_ h
    intro arr harr
    rw [harr]
    simp [E0]
  · intro k
    refine spec_mono ?_ (spec_add "" _ _)
    intro v hv
    rw [hv, ha, hb]

variable {E P WQ WK WV WO U C : Tensor ℚ}

/-- The OV chain of `buildTabs`: from `vwo` to `ov`, as one specification. -/
theorem ov_formula (vwo wov ove ovp ov : Array Q)
    (hvwo : vwo.toList.map Q.val = (List.range 1024).map fun k =>
      ∑ d' ∈ range 32, WV.get (k / 32 * 32 + d') * WO.get (d' * 32 + k % 32))
    (hwov : wov.toList.map Q.val = (List.range 2048).map fun k =>
      ∑ d2 ∈ range 32, (vwo.getD (k / 64 * 32 + d2) ⟨0⟩).val * U.get (d2 * 64 + k % 64))
    (hove : ove.toList.map Q.val = (List.range 4096).map fun k =>
      ∑ d ∈ range 32, E.get (k / 64 * 32 + d) * (wov.getD (d * 64 + k % 64) ⟨0⟩).val)
    (hovp : ovp.toList.map Q.val = (List.range 256).map fun k =>
      ∑ d ∈ range 32, P.get (k / 64 * 32 + d) * (wov.getD (d * 64 + k % 64) ⟨0⟩).val)
    (hov : ov.toList.map Q.val = (List.range 16384).map fun k =>
      (ove.getD (k % 4096) ⟨0⟩).val + (ovp.getD (k / 4096 * 64 + k % 64) ⟨0⟩).val)
    (i t j : Nat) (hi : i < 4) (ht : t < 64) (hj : j < 64) :
    (ov.getD ((i * 64 + t) * 64 + j) ⟨0⟩).val = OVQ E P WV WO U i t j := by
  rw [getD_val_lt hov (by omega)]
  have e1 : ((i * 64 + t) * 64 + j) % 4096 = t * 64 + j := by omega
  have e2 : ((i * 64 + t) * 64 + j) / 4096 * 64 + ((i * 64 + t) * 64 + j) % 64 = i * 64 + j := by omega
  rw [e1, e2, getD_val_lt hove (by omega), getD_val_lt hovp (by omega)]
  have e3 : (t * 64 + j) / 64 * 32 = t * 32 := by omega
  have e4 : (t * 64 + j) % 64 = j := by omega
  have e5 : (i * 64 + j) / 64 * 32 = i * 32 := by omega
  have e6 : (i * 64 + j) % 64 = j := by omega
  simp only [e3, e4, e5, e6]
  have hw : ∀ d, d < 32 → (wov.getD (d * 64 + j) ⟨0⟩).val = WovQ WV WO U d j := by
    intro d hd
    rw [getD_val_lt hwov (by omega)]
    have e7 : (d * 64 + j) / 64 * 32 = d * 32 := by omega
    have e8 : (d * 64 + j) % 64 = j := by omega
    simp only [e7, e8]
    unfold WovQ WOUQ
    have hv : ∀ d2, d2 < 32 → (vwo.getD (d * 32 + d2) ⟨0⟩).val =
        ∑ d' ∈ range 32, WV.get (d * 32 + d') * WO.get (d' * 32 + d2) := by
      intro d2 hd2
      rw [getD_val_lt hvwo (by omega)]
      have e9 : (d * 32 + d2) / 32 * 32 = d * 32 := by omega
      have e10 : (d * 32 + d2) % 32 = d2 := by omega
      simp only [e9, e10]
    rw [sum_congr rfl fun d2 hd2 => by rw [hv d2 (mem_range.mp hd2)]]
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun d' _ => sum_congr rfl fun d2 _ => ?_
    ring
  have h1 : ∑ d ∈ range 32, E.get (t * 32 + d) * (wov.getD (d * 64 + j) ⟨0⟩).val =
      ∑ d ∈ range 32, E.get (t * 32 + d) * WovQ WV WO U d j :=
    sum_congr rfl fun d hd => by rw [hw d (mem_range.mp hd)]
  have h2 : ∑ d ∈ range 32, P.get (i * 32 + d) * (wov.getD (d * 64 + j) ⟨0⟩).val =
      ∑ d ∈ range 32, P.get (i * 32 + d) * WovQ WV WO U d j :=
    sum_congr rfl fun d hd => by rw [hw d (mem_range.mp hd)]
  rw [h1, h2]
  unfold OVQ resQ
  rw [← sum_add_distrib]
  refine sum_congr rfl fun d _ => ?_
  ring

/-- The `dm` table from `last`. -/
theorem dm_formula (last dm : Array Q)
    (hlast : last.toList.map Q.val = (List.range 2048).map fun k => E.get k + P.get (96 + k % 32))
    (hdm : dm.toList.map Q.val = (List.range 4096).map fun k =>
      ∑ d ∈ range 32, (last.getD (k / 64 * 32 + d) ⟨0⟩).val * U.get (d * 64 + k % 64))
    (t3 j : Nat) (h3 : t3 < 64) (hj : j < 64) :
    (dm.getD (t3 * 64 + j) ⟨0⟩).val = DmQ E P U t3 j := by
  rw [getD_val_lt hdm (by omega)]
  have e1 : (t3 * 64 + j) / 64 * 32 = t3 * 32 := by omega
  have e2 : (t3 * 64 + j) % 64 = j := by omega
  simp only [e1, e2]
  unfold DmQ resQ
  refine sum_congr rfl fun d hd => ?_
  have hd' := mem_range.mp hd
  rw [getD_val_lt hlast (by omega)]
  have e3 : (t3 * 32 + d) % 32 = d := by omega
  rw [e3]

/-- The score chain: `s[(t3*4+i)*64+t] = SQ t3 i t`. -/
theorem s_formula (sc : Q) (hsc : sc.val = C.get 0) (last qm ek pk sqe sqp s : Array Q)
    (hlast : last.toList.map Q.val = (List.range 2048).map fun k => E.get k + P.get (96 + k % 32))
    (hqm : qm.toList.map Q.val = (List.range 2048).map fun k =>
      0 + (∑ d ∈ range 32, (last.getD (k / 32 * 32 + d) ⟨0⟩).val * WQ.get (d * 32 + k % 32)) * sc.val)
    (hek : ek.toList.map Q.val = (List.range 2048).map fun k =>
      ∑ d ∈ range 32, E.get (k / 32 * 32 + d) * WK.get (d * 32 + k % 32))
    (hpk : pk.toList.map Q.val = (List.range 128).map fun k =>
      ∑ d ∈ range 32, P.get (k / 32 * 32 + d) * WK.get (d * 32 + k % 32))
    (hsqe : sqe.toList.map Q.val = (List.range 4096).map fun k =>
      ∑ d' ∈ range 32, (qm.getD (k / 64 * 32 + d') ⟨0⟩).val * (ek.getD (k % 64 * 32 + d') ⟨0⟩).val)
    (hsqp : sqp.toList.map Q.val = (List.range 256).map fun k =>
      ∑ d' ∈ range 32, (qm.getD (k / 4 * 32 + d') ⟨0⟩).val * (pk.getD (k % 4 * 32 + d') ⟨0⟩).val)
    (hs : s.toList.map Q.val = (List.range 16384).map fun k =>
      (sqe.getD (k / 256 * 64 + k % 64) ⟨0⟩).val + (sqp.getD (k / 64) ⟨0⟩).val)
    (t3 i t : Nat) (h3 : t3 < 64) (hi : i < 4) (ht : t < 64) :
    (s.getD ((t3 * 4 + i) * 64 + t) ⟨0⟩).val = SQ E P WQ WK C t3 i t := by
  rw [getD_val_lt hs (by omega)]
  have e1 : ((t3 * 4 + i) * 64 + t) / 256 * 64 + ((t3 * 4 + i) * 64 + t) % 64 = t3 * 64 + t := by omega
  have e2 : ((t3 * 4 + i) * 64 + t) / 64 = t3 * 4 + i := by omega
  rw [e1, e2, getD_val_lt hsqe (by omega), getD_val_lt hsqp (by omega)]
  have e3 : (t3 * 64 + t) / 64 * 32 = t3 * 32 := by omega
  have e4 : (t3 * 64 + t) % 64 * 32 = t * 32 := by omega
  have e5 : (t3 * 4 + i) / 4 * 32 = t3 * 32 := by omega
  have e6 : (t3 * 4 + i) % 4 * 32 = i * 32 := by omega
  simp only [e3, e4, e5, e6]
  have hq : ∀ d', d' < 32 → (qm.getD (t3 * 32 + d') ⟨0⟩).val = qQ E P WQ C t3 d' := by
    intro d' hd'
    rw [getD_val_lt hqm (by omega)]
    have e7 : (t3 * 32 + d') / 32 * 32 = t3 * 32 := by omega
    have e8 : (t3 * 32 + d') % 32 = d' := by omega
    simp only [e7, e8, zero_add, hsc]
    unfold qQ resQ
    congr 1
    refine sum_congr rfl fun d hd => ?_
    have hd2 := mem_range.mp hd
    rw [getD_val_lt hlast (by omega)]
    have e9 : (t3 * 32 + d) % 32 = d := by omega
    rw [e9]
  have he : ∀ d', d' < 32 → (ek.getD (t * 32 + d') ⟨0⟩).val =
      ∑ d ∈ range 32, E.get (t * 32 + d) * WK.get (d * 32 + d') := by
    intro d' hd'
    rw [getD_val_lt hek (by omega)]
    have e7 : (t * 32 + d') / 32 * 32 = t * 32 := by omega
    have e8 : (t * 32 + d') % 32 = d' := by omega
    simp only [e7, e8]
  have hp : ∀ d', d' < 32 → (pk.getD (i * 32 + d') ⟨0⟩).val =
      ∑ d ∈ range 32, P.get (i * 32 + d) * WK.get (d * 32 + d') := by
    intro d' hd'
    rw [getD_val_lt hpk (by omega)]
    have e7 : (i * 32 + d') / 32 * 32 = i * 32 := by omega
    have e8 : (i * 32 + d') % 32 = d' := by omega
    simp only [e7, e8]
  have h1 : ∑ d' ∈ range 32, (qm.getD (t3 * 32 + d') ⟨0⟩).val * (ek.getD (t * 32 + d') ⟨0⟩).val =
      ∑ d' ∈ range 32, qQ E P WQ C t3 d' * ∑ d ∈ range 32, E.get (t * 32 + d) * WK.get (d * 32 + d') :=
    sum_congr rfl fun d' hd' => by rw [hq d' (mem_range.mp hd'), he d' (mem_range.mp hd')]
  have h2 : ∑ d' ∈ range 32, (qm.getD (t3 * 32 + d') ⟨0⟩).val * (pk.getD (i * 32 + d') ⟨0⟩).val =
      ∑ d' ∈ range 32, qQ E P WQ C t3 d' * ∑ d ∈ range 32, P.get (i * 32 + d) * WK.get (d * 32 + d') :=
    sum_congr rfl fun d' hd' => by rw [hq d' (mem_range.mp hd'), hp d' (mem_range.mp hd')]
  rw [h1, h2]
  unfold SQ keyQ resQ
  rw [← sum_add_distrib]
  refine sum_congr rfl fun d' _ => ?_
  rw [← mul_add, ← sum_add_distrib]
  rw [mul_comm]
  congr 1
  refine sum_congr rfl fun d _ => ?_
  ring

theorem getD_val_of_list {arr : Array Q} {l : List Q} (h : arr.toList = l) {g : Nat} (hg : g < l.length) :
    arr.getD g ⟨0⟩ = l[g] := by
  rw [Array.getD_eq_getD_getElem?, ← Array.getElem?_toList, h, List.getElem?_eq_getElem hg]
  rfl

/-- A table of `(Σ_d a k d * b k d) * sc` (through `muladd zero v sc`). -/
theorem spec_qmTable {a b : Nat → Nat → CostM Q} {fa fb : Nat → Nat → ℚ} (cnt : Nat) (sc : Q)
    (ha : ∀ k d, Spec env (a k d) fun x => x.val = fa k d)
    (hb : ∀ k d, Spec env (b k d) fun y => y.val = fb k d) :
    Spec env (tableM Interp.counting (fun k => do
        let v ← dotM Interp.counting (a k) (b k) 32 Interp.counting.zero
        Interp.counting.muladd "" Interp.counting.zero v sc) cnt 0 (E0 Interp.counting))
      fun arr => arr.toList.map Q.val = (List.range cnt).map fun k =>
        0 + (∑ d ∈ range 32, fa k d * fb k d) * sc.val := by
  have h := spec_tableM (env := env) (g := fun k => 0 + (∑ d ∈ range 32, fa k d * fb k d) * sc.val)
    (f := fun k => do
        let v ← dotM Interp.counting (a k) (b k) 32 Interp.counting.zero
        Interp.counting.muladd "" Interp.counting.zero v sc) ?_ cnt 0 (E0 Interp.counting)
  · refine spec_mono ?_ h
    intro arr harr
    rw [harr]
    simp [E0]
  · intro k
    refine spec_bind (spec_dotM (fa := fa k) (fb := fb k) 32 Interp.counting.zero
      (fun d _ => ha k d) (fun d _ => hb k d)) fun v hv => ?_
    refine spec_mono ?_ (spec_muladd "" _ v sc)
    intro r hr
    rw [hr, hv]
    show (0 : ℚ) + ((0 : ℚ) + _) * _ = _
    ring

/-- What the checker knows about its tables. -/
structure TabsOk (E P WQ WK WV WO U C : Tensor ℚ) (tabs : Tabs Interp.counting) : Prop where
  dm : ∀ t3 j, t3 < 64 → j < 64 → (tabs.dm.getD (t3 * 64 + j) ⟨0⟩).val = DmQ E P U t3 j
  ov : ∀ i t j, i < 4 → t < 64 → j < 64 → (tabs.ov.getD ((i * 64 + t) * 64 + j) ⟨0⟩).val = OVQ E P WV WO U i t j
  s : ∀ t3 i t, t3 < 64 → i < 4 → t < 64 → (tabs.s.getD ((t3 * 4 + i) * 64 + t) ⟨0⟩).val = SQ E P WQ WK C t3 i t
  ovmax : ∀ i j a t, i < 3 → j < 64 → a ≤ 64 → t < a →
    (tabs.ov.getD ((i * 64 + t) * 64 + j) ⟨0⟩).val ≤ (tabs.ovmax.getD ((i * 64 + j) * 65 + a) ⟨0⟩).val
  ovmin : ∀ i j a t, i < 3 → j < 64 → a ≤ 64 → t < a →
    (tabs.ovmin.getD ((i * 64 + j) * 65 + a) ⟨0⟩).val ≤ (tabs.ov.getD ((i * 64 + t) * 64 + j) ⟨0⟩).val
  spre : ∀ t3 i a t, t3 < 64 → i < 3 → a ≤ 64 → t < a →
    (tabs.s.getD ((t3 * 4 + i) * 64 + t) ⟨0⟩).val ≤ (tabs.spre.getD ((t3 * 3 + i) * 65 + a) ⟨0⟩).val

/-- The specification of `buildTabs`. -/
theorem spec_buildTabs
    (hE : List.lookup "E" env.weights = some E) (hP : List.lookup "P" env.weights = some P)
    (hWQ : List.lookup "WQ" env.weights = some WQ) (hC : List.lookup "#const0" env.weights = some C)
    (hWK : List.lookup "WK" env.weights = some WK) (hWV : List.lookup "WV" env.weights = some WV)
    (hWO : List.lookup "WO" env.weights = some WO) (hU : List.lookup "U" env.weights = some U) :
    Spec env (buildTabs Interp.counting) (TabsOk E P WQ WK WV WO U C) := by
  unfold buildTabs
  refine spec_bind (spec_weight hC 0) fun sc hsc => ?_
  refine spec_bind (spec_last hE hP) fun last hlast => ?_
  refine spec_bind (spec_dm hU last (fun k => (last.getD k ⟨0⟩).val) (fun k => rfl)) fun dm hdm => ?_
  refine spec_bind (spec_dotTable (fa := fun k d' => WV.get (k / 32 * 32 + d')) (fb := fun k d' => WO.get (d' * 32 + k % 32))
    1024 (fun k d => spec_weight hWV _) (fun k d => spec_weight hWO _)) fun vwo hvwo => ?_
  refine spec_bind (spec_dotTable (fa := fun k d2 => (vwo.getD (k / 64 * 32 + d2) ⟨0⟩).val)
    (fb := fun k d2 => U.get (d2 * 64 + k % 64))
    2048 (fun k d => spec_pure rfl) (fun k d => spec_weight hU _)) fun wov hwov => ?_
  refine spec_bind (spec_dotTable (fa := fun k d => E.get (k / 64 * 32 + d))
    (fb := fun k d => (wov.getD (d * 64 + k % 64) ⟨0⟩).val)
    4096 (fun k d => spec_weight hE _) (fun k d => spec_pure rfl)) fun ove hove => ?_
  refine spec_bind (spec_dotTable (fa := fun k d => P.get (k / 64 * 32 + d))
    (fb := fun k d => (wov.getD (d * 64 + k % 64) ⟨0⟩).val)
    256 (fun k d => spec_weight hP _) (fun k d => spec_pure rfl)) fun ovp hovp => ?_
  refine spec_bind (spec_addTable (ia := fun k => k % 4096) (ib := fun k => k / 4096 * 64 + k % 64)
    (fa := fun k => (ove.getD (k % 4096) ⟨0⟩).val) (fb := fun k => (ovp.getD (k / 4096 * 64 + k % 64) ⟨0⟩).val)
    16384 (fun k => rfl) (fun k => rfl)) fun ov hov => ?_
  refine spec_bind (spec_qmTable (fa := fun k d => (last.getD (k / 32 * 32 + d) ⟨0⟩).val)
    (fb := fun k d => WQ.get (d * 32 + k % 32)) 2048 sc (fun k d => spec_pure rfl) (fun k d => spec_weight hWQ _))
    fun qm hqm => ?_
  refine spec_bind (spec_dotTable (fa := fun k d => E.get (k / 32 * 32 + d)) (fb := fun k d => WK.get (d * 32 + k % 32))
    2048 (fun k d => spec_weight hE _) (fun k d => spec_weight hWK _)) fun ek hek => ?_
  refine spec_bind (spec_dotTable (fa := fun k d => P.get (k / 32 * 32 + d)) (fb := fun k d => WK.get (d * 32 + k % 32))
    128 (fun k d => spec_weight hP _) (fun k d => spec_weight hWK _)) fun pk hpk => ?_
  refine spec_bind (spec_dotTable (fa := fun k d' => (qm.getD (k / 64 * 32 + d') ⟨0⟩).val)
    (fb := fun k d' => (ek.getD (k % 64 * 32 + d') ⟨0⟩).val)
    4096 (fun k d => spec_pure rfl) (fun k d => spec_pure rfl)) fun sqe hsqe => ?_
  refine spec_bind (spec_dotTable (fa := fun k d' => (qm.getD (k / 4 * 32 + d') ⟨0⟩).val)
    (fb := fun k d' => (pk.getD (k % 4 * 32 + d') ⟨0⟩).val)
    256 (fun k d => spec_pure rfl) (fun k d => spec_pure rfl)) fun sqp hsqp => ?_
  refine spec_bind (spec_addTable (ia := fun k => k / 256 * 64 + k % 64) (ib := fun k => k / 64)
    (fa := fun k => (sqe.getD (k / 256 * 64 + k % 64) ⟨0⟩).val) (fb := fun k => (sqp.getD (k / 64) ⟨0⟩).val)
    16384 (fun k => rfl) (fun k => rfl)) fun s hs => ?_
  refine spec_bind (fun _ _ _ _ => trivial : Spec env _ fun _ => True) fun kk0 _ => ?_
  refine spec_bind (fun _ _ _ _ => trivial : Spec env _ fun _ => True) fun kk _ => ?_
  refine spec_bind (spec_scansMaxM (fun o t => ov.getD ((o / 64 * 64 + t) * 64 + o % 64) ⟨0⟩) 64 192 0 _)
    fun ovmax ⟨l1, hl1, hlen1, hP1⟩ => ?_
  refine spec_bind (spec_scansMinM (fun o t => ov.getD ((o / 64 * 64 + t) * 64 + o % 64) ⟨0⟩) 64 192 0 _)
    fun ovmin ⟨l2, hl2, hlen2, hP2⟩ => ?_
  refine spec_bind (spec_scansMaxM (fun o t => s.getD ((o / 3 * 4 + o % 3) * 64 + t) ⟨0⟩) 64 192 0 _)
    fun spre ⟨l3, hl3, hlen3, hP3⟩ => ?_
  refine spec_pure ?_
  simp only [E0, List.nil_append] at hl1 hl2 hl3
  refine ⟨fun t3 j h3 hj => dm_formula last dm hlast hdm t3 j h3 hj,
    fun i t j hi ht hj => ov_formula vwo wov ove ovp ov hvwo hwov hove hovp hov i t j hi ht hj,
    fun t3 i t h3 hi ht => s_formula sc hsc last qm ek pk sqe sqp s hlast hqm hek hpk hsqe hsqp hs t3 i t h3 hi ht,
    ?_, ?_, ?_⟩
  · intro i j a t hi hj ha ht
    have hlt : (i * 64 + j) * (64 + 1) + a < l1.length := by rw [hlen1]; omega
    have := hP1 (i * 64 + j) a hlt (by omega) ha t ht
    rw [show (i * 64 + j) * 65 + a = (i * 64 + j) * (64 + 1) + a by ring, getD_val_of_list hl1 hlt]
    have e1 : (0 + (i * 64 + j)) / 64 * 64 = i * 64 := by omega
    have e2 : (0 + (i * 64 + j)) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  · intro i j a t hi hj ha ht
    have hlt : (i * 64 + j) * (64 + 1) + a < l2.length := by rw [hlen2]; omega
    have := hP2 (i * 64 + j) a hlt (by omega) ha t ht
    rw [show (i * 64 + j) * 65 + a = (i * 64 + j) * (64 + 1) + a by ring, getD_val_of_list hl2 hlt]
    have e1 : (0 + (i * 64 + j)) / 64 * 64 = i * 64 := by omega
    have e2 : (0 + (i * 64 + j)) % 64 = j := by omega
    rw [e1, e2] at this
    exact this
  · intro t3 i a t h3 hi ha ht
    have hlt : (t3 * 3 + i) * (64 + 1) + a < l3.length := by rw [hlen3]; omega
    have := hP3 (t3 * 3 + i) a hlt (by omega) ha t ht
    rw [show (t3 * 3 + i) * 65 + a = (t3 * 3 + i) * (64 + 1) + a by ring, getD_val_of_list hl3 hlt]
    have e1 : (0 + (t3 * 3 + i)) / 3 * 4 + (0 + (t3 * 3 + i)) % 3 = t3 * 4 + i := by omega
    rw [e1] at this
    exact this

end

end Candidate.Tables
