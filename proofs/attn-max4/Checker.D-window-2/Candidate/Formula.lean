import Protected.N_attn_max4_v64_s0
import CompactCheck.Soundness
import CompactCheck.CountedOps
import CompactCheck.CountedGeneralSound

/-!
# Formula lemma infrastructure: tensors as functions of multi-indices.
-/

namespace Candidate.Formula
open CompactCheck

/-- A valid multi-index of a shape: one index per dimension, each below its size. -/
abbrev Valid (s i : List Nat) : Prop := List.Forall₂ (fun a d => a < d) i s

/-- `t` has shape `s`, is well formed, and its entry at every valid multi-index `i` is `f i`. -/
structure Rep (t : Tensor ℝ) (s : List Nat) (f : List Nat → ℝ) : Prop where
  shape : t.shape = s
  size : t.data.size = shapeSize s
  entry : ∀ i, Valid s i → t.entry i = f i

theorem shapeSize_cons (d : Nat) (s : List Nat) : shapeSize (d :: s) = d * shapeSize s := rfl

theorem ravel_cons (d : Nat) (s : List Nat) (a : Nat) (i : List Nat) :
    ravel (d :: s) (a :: i) = shapeSize s * a + ravel s i := by
  simp [ravel, strides]

theorem unravel_cons (d : Nat) (s : List Nat) (j : Nat) :
    unravel (d :: s) j = (j / shapeSize s % d) :: unravel s j := by
  simp [unravel, strides]

theorem ravel_lt {s i : List Nat} (h : Valid s i) : ravel s i < shapeSize s := by
  induction h with
  | nil => simp [ravel, shapeSize]
  | @cons a d i s ha hi ih =>
    rw [ravel_cons, shapeSize_cons]
    have h1 : shapeSize s * a + ravel s i < shapeSize s * (a + 1) := by
      rw [Nat.mul_succ]; omega
    have h2 : shapeSize s * (a + 1) ≤ shapeSize s * d := Nat.mul_le_mul_left _ ha
    rw [Nat.mul_comm d]; omega

theorem shapeSize_pos {s i : List Nat} (h : Valid s i) : 0 < shapeSize s :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (ravel_lt h)

theorem unravel_ravel' {s i : List Nat} (h : Valid s i) :
    ∀ c, unravel s (c * shapeSize s + ravel s i) = i := by
  induction h with
  | nil => intro c; simp [unravel, strides]
  | @cons a d i s ha hi ih =>
    intro c
    rw [unravel_cons, ravel_cons, shapeSize_cons]
    have hpos := shapeSize_pos hi
    have hlt := ravel_lt hi
    have e : c * (d * shapeSize s) + (shapeSize s * a + ravel s i)
        = (c * d + a) * shapeSize s + ravel s i := by ring
    rw [e]
    have hdiv : ((c * d + a) * shapeSize s + ravel s i) / shapeSize s = c * d + a := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpos, Nat.div_eq_of_lt hlt, Nat.zero_add]
    rw [hdiv, ih (c * d + a)]
    congr 1
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt ha]

theorem unravel_ravel {s i : List Nat} (h : Valid s i) : unravel s (ravel s i) = i := by
  have := unravel_ravel' h 0
  simpa using this

theorem get_rangeMap {s : List Nat} (n : Nat) (g : Nat → ℝ) {j : Nat} (hj : j < n) :
    (⟨s, (Array.range n).map g⟩ : Tensor ℝ).get j = g j := by
  simp [Tensor.get, Array.getD, hj]

theorem ofFn_get (s : List Nat) (f : List Nat → ℝ) {j : Nat} (hj : j < shapeSize s) :
    (Tensor.ofFn s f).get j = f (unravel s j) := by
  unfold Tensor.ofFn
  exact get_rangeMap _ _ hj

theorem ofFn_rep (s : List Nat) (f : List Nat → ℝ) : Rep (Tensor.ofFn s f) s f where
  shape := rfl
  size := by simp [Tensor.ofFn]
  entry := by
    intro i hi
    rw [Tensor.entry, show (Tensor.ofFn s f).shape = s from rfl]
    rw [ofFn_get s f (ravel_lt hi), unravel_ravel hi]

theorem rep_of_ofFn {s : List Nat} {f g : List Nat → ℝ} (h : ∀ i, Valid s i → f i = g i) :
    Rep (Tensor.ofFn s f) s g :=
  ⟨rfl, (ofFn_rep s f).size, fun i hi => by rw [(ofFn_rep s f).entry i hi, h i hi]⟩

theorem param_rep {t : Tensor ℝ} {s : List Nat} (hs : t.shape = s) (hn : t.data.size = shapeSize s) :
    Rep t s fun i => t.entry i := ⟨hs, hn, fun _ _ => rfl⟩

theorem Rep.wellFormed {t : Tensor ℝ} {s f} (h : Rep t s f) : t.wellFormed = true := by
  simp [Tensor.wellFormed, h.size, h.shape]

theorem Rep.eta {t : Tensor ℝ} {s f} (h : Rep t s f) : (⟨s, t.data⟩ : Tensor ℝ) = t := by
  cases t; simp [← h.shape]

theorem valid3 {d0 d1 d2 : Nat} {i : List Nat} (h : Valid [d0, d1, d2] i) :
    ∃ a b c, i = [a, b, c] ∧ a < d0 ∧ b < d1 ∧ c < d2 := by
  rcases h with _ | ⟨ha, _ | ⟨hb, _ | ⟨hc, _ | _⟩⟩⟩
  exact ⟨_, _, _, rfl, ha, hb, hc⟩

theorem valid2 {d0 d1 : Nat} {i : List Nat} (h : Valid [d0, d1] i) :
    ∃ a b, i = [a, b] ∧ a < d0 ∧ b < d1 := by
  rcases h with _ | ⟨ha, _ | ⟨hb, _ | _⟩⟩
  exact ⟨_, _, rfl, ha, hb⟩

theorem valid0 {i : List Nat} (h : Valid [] i) : i = [] := by
  rcases h with _ | _
  rfl

theorem valid3_of {d0 d1 d2 a b c : Nat} (ha : a < d0) (hb : b < d1) (hc : c < d2) :
    Valid [d0, d1, d2] [a, b, c] :=
  List.Forall₂.cons ha (List.Forall₂.cons hb (List.Forall₂.cons hc List.Forall₂.nil))

theorem valid2_of {d0 d1 a b : Nat} (ha : a < d0) (hb : b < d1) : Valid [d0, d1] [a, b] :=
  List.Forall₂.cons ha (List.Forall₂.cons hb List.Forall₂.nil)

theorem ravel3 (d0 d1 d2 a b c : Nat) : ravel [d0, d1, d2] [a, b, c] = (a * d1 + b) * d2 + c := by
  simp [ravel, strides, shapeSize]; ring

theorem ravel2 (d0 d1 a b : Nat) : ravel [d0, d1] [a, b] = a * d1 + b := by
  simp [ravel, strides, shapeSize]; ring

/-! ## Generic op lemmas -/

theorem semOps_cons_some {g : Graph} {w : Weights ℝ} {x : Input} {op : Op} {ops : List Op}
    {vals : Array (Tensor ℝ)} {v : Tensor ℝ} (h : semOp g w x vals op = some v) :
    semOps g w x (op :: ops) vals = semOps g w x ops (vals.push v) := by
  simp [semOps, h]

theorem broadcastOp_some (op : ℝ → ℝ → ℝ) {a b : Tensor ℝ} {sa sb s : List Nat} {fa fb}
    (ha : Rep a sa fa) (hb : Rep b sb fb) (hs : broadcastShape sa sb = some s) :
    broadcastOp op a b = some (Tensor.ofFn s fun i =>
      op (a.entry (broadcastIndex sa i)) (b.entry (broadcastIndex sb i))) := by
  simp [broadcastOp, ha.wellFormed, hb.wellFormed, ha.shape, hb.shape, hs]

theorem matmulOp_some {a b : Tensor ℝ} {sa sb : List Nat} {fa fb} {p : MatmulShape}
    (ha : Rep a sa fa) (hb : Rep b sb fb) (hp : matmulShape sa sb = some p)
    (hout : p.out = p.batch ++ [p.m, p.n]) :
    matmulOp a b = some (Tensor.ofFn (p.batch ++ [p.m, p.n]) fun i =>
      let bi := i.take p.batch.length
      ((List.range p.k).map fun t =>
        (⟨p.sa, a.data⟩ : Tensor ℝ).entry (broadcastIndex p.ba bi ++ [i.getD p.batch.length 0, t]) *
        (⟨p.sb, b.data⟩ : Tensor ℝ).entry (broadcastIndex p.bb bi ++ [t, i.getD (p.batch.length + 1) 0])).sum) := by
  simp [matmulOp, ha.wellFormed, hb.wellFormed, ha.shape, hb.shape, hp]
  rw [hout]
  rfl

/-! ## Concrete nodes -/

theorem oneHot_rep {x : Input} (hx : x.length = 4) (hall : x.all (· < 64) = true) :
    ∃ v, (oneHotInput 4 64 x : Option (Tensor ℝ)) = some v ∧
      Rep v [1, 4, 64] fun i => if x.getD (i.getD 1 0) 0 = i.getD 2 0 then 1 else 0 := by
  refine ⟨⟨[1, 4, 64], (Array.range (4 * 64)).map fun j => if x.getD (j / 64) 0 = j % 64 then 1 else 0⟩, ?_, ?_⟩
  · unfold oneHotInput
    rw [hx, hall]
    rfl
  refine ⟨rfl, by simp [shapeSize], ?_⟩
  intro i hi
  obtain ⟨a, b, c, rfl, ha, hb, hc⟩ := valid3 hi
  simp only [Tensor.entry, ravel3]
  rw [get_rangeMap _ _ (by omega)]
  have e1 : ((a * 4 + b) * 64 + c) / 64 = b := by omega
  have e2 : ((a * 4 + b) * 64 + c) % 64 = c := by omega
  simp [e1, e2]

/-- matmul `[1,4,k] × [k,n]` (the shape computation is a hypothesis, `rfl` at concrete sizes). -/
theorem matmul_1_4_rep {k n : Nat} {a b : Tensor ℝ} {fa fb} (ha : Rep a [1, 4, k] fa) (hb : Rep b [k, n] fb)
    (hp : matmulShape [1, 4, k] [k, n] = some ⟨[1, 4, k], [k, n], 4, k, n, [1], [], [1], [1, 4, n]⟩) :
    ∃ c, matmulOp a b = some c ∧
      Rep c [1, 4, n] fun i => ((List.range k).map fun t => fa [0, i.getD 1 0, t] * fb [t, i.getD 2 0]).sum := by
  refine ⟨_, matmulOp_some ha hb hp rfl, ?_⟩
  dsimp only [List.cons_append, List.nil_append]
  apply rep_of_ofFn
  intro i hi
  obtain ⟨a0, b0, c0, rfl, ha0, hb0, hc0⟩ := valid3 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp (config := { decide := true }) only [ha.eta, hb.eta, List.take, broadcastIndex, List.getD_cons_zero,
    List.getD_cons_succ, List.length_cons, List.length_nil, List.zipWith, List.drop, Nat.sub_self,
    ite_true, ite_false, List.cons_append, List.nil_append]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  rw [ha.entry _ (valid3_of ha0 hb0 ht), hb.entry _ (valid2_of ht hc0)]

/-- matmul `[1,32] × [32,n]`. -/
theorem matmul_1_32_rep {n : Nat} {a b : Tensor ℝ} {fa fb} (ha : Rep a [1, 32] fa) (hb : Rep b [32, n] fb)
    (hp : matmulShape [1, 32] [32, n] = some ⟨[1, 32], [32, n], 1, 32, n, [], [], [], [1, n]⟩) :
    ∃ c, matmulOp a b = some c ∧
      Rep c [1, n] fun i => ((List.range 32).map fun t => fa [0, t] * fb [t, i.getD 1 0]).sum := by
  refine ⟨_, matmulOp_some ha hb hp rfl, ?_⟩
  dsimp only [List.cons_append, List.nil_append]
  apply rep_of_ofFn
  intro i hi
  obtain ⟨a0, b0, rfl, ha0, hb0⟩ := valid2 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp (config := { decide := true }) only [ha.eta, hb.eta, List.take, broadcastIndex, List.getD_cons_zero,
    List.getD_cons_succ, List.length_cons, List.length_nil, List.zipWith, List.drop, Nat.sub_self,
    ite_true, ite_false, List.cons_append, List.nil_append]
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [List.mem_range] at ht
  rw [ha.entry _ (valid2_of ha0 ht), hb.entry _ (valid2_of ht hb0)]

/-- binary op on `[1,32]` and a scalar `[]`. -/
theorem bin_1_32_scalar_rep (op : BinOp) {a b : Tensor ℝ} {fa fb} (ha : Rep a [1, 32] fa) (hb : Rep b [] fb) :
    ∃ c, broadcastOp op.apply a b = some c ∧
      Rep c [1, 32] fun i => op.apply (fa [0, i.getD 1 0]) (fb []) := by
  have hs : broadcastShape [1, 32] [] = some [1, 32] := by rfl
  refine ⟨_, broadcastOp_some _ ha hb hs, ?_⟩
  apply rep_of_ofFn
  intro i hi
  obtain ⟨a0, b0, rfl, ha0, hb0⟩ := valid2 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp (config := { decide := true }) only [broadcastIndex, List.length_cons, List.length_nil, List.zipWith,
    List.drop, Nat.sub_self, List.getD_cons_zero, List.getD_cons_succ, ite_true, ite_false]
  rw [ha.entry _ (valid2_of ha0 hb0), hb.entry _ List.Forall₂.nil]

/-- binary op on `[1,32]` and `[1,32]`. -/
theorem bin_1_32_rep (op : BinOp) {a b : Tensor ℝ} {fa fb} (ha : Rep a [1, 32] fa) (hb : Rep b [1, 32] fb) :
    ∃ c, broadcastOp op.apply a b = some c ∧
      Rep c [1, 32] fun i => op.apply (fa [0, i.getD 1 0]) (fb [0, i.getD 1 0]) := by
  have hs : broadcastShape [1, 32] [1, 32] = some [1, 32] := by rfl
  refine ⟨_, broadcastOp_some _ ha hb hs, ?_⟩
  apply rep_of_ofFn
  intro i hi
  obtain ⟨a0, b0, rfl, ha0, hb0⟩ := valid2 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp (config := { decide := true }) only [broadcastIndex, List.length_cons, List.length_nil, List.zipWith,
    List.drop, Nat.sub_self, List.getD_cons_zero, List.getD_cons_succ, ite_true, ite_false]
  rw [ha.entry _ (valid2_of ha0 hb0), hb.entry _ (valid2_of ha0 hb0)]

/-- binary op on `[1,4,32]` and `[1,1,32]`. -/
theorem bin_1_4_32_1_1_32_rep (op : BinOp) {a b : Tensor ℝ} {fa fb} (ha : Rep a [1, 4, 32] fa)
    (hb : Rep b [1, 1, 32] fb) :
    ∃ c, broadcastOp op.apply a b = some c ∧
      Rep c [1, 4, 32] fun i => op.apply (fa [0, i.getD 1 0, i.getD 2 0]) (fb [0, 0, i.getD 2 0]) := by
  have hs : broadcastShape [1, 4, 32] [1, 1, 32] = some [1, 4, 32] := by rfl
  refine ⟨_, broadcastOp_some _ ha hb hs, ?_⟩
  apply rep_of_ofFn
  intro i hi
  obtain ⟨a0, b0, c0, rfl, ha0, hb0, hc0⟩ := valid3 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp (config := { decide := true }) only [broadcastIndex, List.length_cons, List.length_nil, List.zipWith,
    List.drop, Nat.sub_self, List.getD_cons_zero, List.getD_cons_succ, ite_true, ite_false]
  rw [ha.entry _ (valid3_of ha0 hb0 hc0), hb.entry _ (valid3_of ha0 ha0 hc0)]

/-- binary op on `[1,4,1]` and `[1,4,32]`. -/
theorem bin_1_4_1_1_4_32_rep (op : BinOp) {a b : Tensor ℝ} {fa fb} (ha : Rep a [1, 4, 1] fa)
    (hb : Rep b [1, 4, 32] fb) :
    ∃ c, broadcastOp op.apply a b = some c ∧
      Rep c [1, 4, 32] fun i => op.apply (fa [0, i.getD 1 0, 0]) (fb [0, i.getD 1 0, i.getD 2 0]) := by
  have hs : broadcastShape [1, 4, 1] [1, 4, 32] = some [1, 4, 32] := by rfl
  refine ⟨_, broadcastOp_some _ ha hb hs, ?_⟩
  apply rep_of_ofFn
  intro i hi
  obtain ⟨a0, b0, c0, rfl, ha0, hb0, hc0⟩ := valid3 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp (config := { decide := true }) only [broadcastIndex, List.length_cons, List.length_nil, List.zipWith,
    List.drop, Nat.sub_self, List.getD_cons_zero, List.getD_cons_succ, ite_true, ite_false]
  rw [ha.entry _ (valid3_of ha0 hb0 ha0), hb.entry _ (valid3_of ha0 hb0 hc0)]

/-- unsqueeze `[1,32]` at 1: `[1,1,32]`. -/
theorem unsq1_rep {t : Tensor ℝ} {f} (h : Rep t [1, 32] f) :
    ∃ c, unsqueezeOp t 1 = some c ∧ Rep c [1, 1, 32] fun i => f [0, i.getD 2 0] := by
  refine ⟨⟨[1, 1, 32], t.data⟩, ?_, ?_⟩
  · unfold unsqueezeOp
    rw [h.shape]
    rfl
  refine ⟨rfl, by rw [h.size]; rfl, ?_⟩
  intro i hi
  obtain ⟨a0, b0, c0, rfl, ha0, hb0, hc0⟩ := valid3 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  have hb0' : b0 = 0 := by omega
  subst hb0'
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [← h.entry _ (valid2_of ha0 hc0)]
  simp only [Tensor.entry, Tensor.get, h.shape, ravel3, ravel2]

/-- unsqueeze `[1,4]` at 2: `[1,4,1]`. -/
theorem unsq2_rep {t : Tensor ℝ} {f} (h : Rep t [1, 4] f) :
    ∃ c, unsqueezeOp t 2 = some c ∧ Rep c [1, 4, 1] fun i => f [0, i.getD 1 0] := by
  refine ⟨⟨[1, 4, 1], t.data⟩, ?_, ?_⟩
  · unfold unsqueezeOp
    rw [h.shape]
    rfl
  refine ⟨rfl, by rw [h.size]; rfl, ?_⟩
  intro i hi
  obtain ⟨a0, b0, c0, rfl, ha0, hb0, hc0⟩ := valid3 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  have hc0' : c0 = 0 := by omega
  subst hc0'
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [← h.entry _ (valid2_of ha0 hb0)]
  simp only [Tensor.entry, Tensor.get, h.shape, ravel3, ravel2]
  congr 1
  omega

/-- sum over dim 2 of `[1,4,32]`: `[1,4]`. -/
theorem sum2_rep {t : Tensor ℝ} {f} (h : Rep t [1, 4, 32] f) :
    ∃ c, sumOp 2 t = some c ∧ Rep c [1, 4] fun i => ((List.range 32).map fun k => f [0, i.getD 1 0, k]).sum := by
  refine ⟨⟨[1, 4], (Array.range (4 * 1)).map fun j =>
    ((List.range 32).map fun k => t.get ((j / 1 * 32 + k) * 1 + j % 1)).sum⟩, ?_, ?_⟩
  · unfold sumOp
    rw [h.shape, h.size]
    rfl
  refine ⟨rfl, by simp [shapeSize], ?_⟩
  intro i hi
  obtain ⟨a0, b0, rfl, ha0, hb0⟩ := valid2 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp only [Tensor.entry, ravel2, List.getD_cons_zero, List.getD_cons_succ]
  rw [get_rangeMap _ _ (by omega)]
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [← h.entry _ (valid3_of ha0 hb0 hk)]
  simp only [Tensor.entry, Tensor.get, h.shape, ravel3]
  congr 1
  omega

/-- sum over dim 1 of `[1,4,32]`: `[1,32]`. -/
theorem sum1_rep {t : Tensor ℝ} {f} (h : Rep t [1, 4, 32] f) :
    ∃ c, sumOp 1 t = some c ∧ Rep c [1, 32] fun i => ((List.range 4).map fun k => f [0, k, i.getD 1 0]).sum := by
  refine ⟨⟨[1, 32], (Array.range (1 * 32)).map fun j =>
    ((List.range 4).map fun k => t.get ((j / 32 * 4 + k) * 32 + j % 32)).sum⟩, ?_, ?_⟩
  · unfold sumOp
    rw [h.shape, h.size]
    rfl
  refine ⟨rfl, by simp [shapeSize], ?_⟩
  intro i hi
  obtain ⟨a0, b0, rfl, ha0, hb0⟩ := valid2 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp only [Tensor.entry, ravel2, List.getD_cons_zero, List.getD_cons_succ]
  rw [get_rangeMap _ _ (by omega)]
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [List.mem_range] at hk
  rw [← h.entry _ (valid3_of ha0 hk hb0)]
  simp only [Tensor.entry, Tensor.get, h.shape, ravel3]
  congr 1
  omega

/-- softmax over dim 1 of `[1,4]`. -/
theorem softmax_rep {t : Tensor ℝ} {f} (h : Rep t [1, 4] f) :
    ∃ c, softmaxOp t 1 = some c ∧ Rep c [1, 4] fun i =>
      Real.exp (f [0, i.getD 1 0]) / ((List.range 4).map fun k => Real.exp (f [0, k])).sum := by
  refine ⟨Tensor.ofFn [1, 4] (fun i => ExpDiv.div (ExpDiv.exp (t.entry i))
    ((List.range 4).map fun k => ExpDiv.exp (t.entry (i.set 1 k))).sum), ?_, ?_⟩
  · unfold softmaxOp
    rw [h.shape, h.wellFormed]
    rfl
  apply rep_of_ofFn
  intro i hi
  obtain ⟨a0, b0, rfl, ha0, hb0⟩ := valid2 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp only [List.set_cons_succ, List.set_cons_zero, List.getD_cons_zero, List.getD_cons_succ]
  rw [h.entry _ (valid2_of ha0 hb0)]
  have hs : ((List.range 4).map fun k => ExpDiv.exp (t.entry [0, k])).sum =
      ((List.range 4).map fun k => Real.exp (f [0, k])).sum := by
    congr 1
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    show Real.exp _ = _
    rw [h.entry _ (valid2_of ha0 hk)]
  rw [hs]
  rfl

/-- binary add `[1,4,32] + [4,32]`. -/
theorem add_1_4_32_rep {a b : Tensor ℝ} {fa fb} (ha : Rep a [1, 4, 32] fa) (hb : Rep b [4, 32] fb) :
    ∃ c, broadcastOp BinOp.add.apply a b = some c ∧
      Rep c [1, 4, 32] fun i => fa [0, i.getD 1 0, i.getD 2 0] + fb [i.getD 1 0, i.getD 2 0] := by
  have hs : broadcastShape [1, 4, 32] [4, 32] = some [1, 4, 32] := by rfl
  refine ⟨_, broadcastOp_some _ ha hb hs, ?_⟩
  apply rep_of_ofFn
  intro i hi
  obtain ⟨a0, b0, c0, rfl, ha0, hb0, hc0⟩ := valid3 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp (config := { decide := true }) only [broadcastIndex, List.length_cons, List.length_nil, List.zipWith,
    List.drop, Nat.sub_self, List.getD_cons_zero, List.getD_cons_succ, BinOp.apply, ite_true, ite_false]
  rw [ha.entry _ (valid3_of ha0 hb0 hc0), hb.entry _ (valid2_of hb0 hc0)]

/-- index `[all, one 3]` on `[1,4,32]`. -/
theorem index_rep {t : Tensor ℝ} {f} (h : Rep t [1, 4, 32] f) :
    ∃ c, indexOp t [.all, .one 3] = some c ∧ Rep c [1, 32] fun i => f [0, 3, i.getD 1 0] := by
  refine ⟨Tensor.ofFn [1, 32] (fun i => t.entry (sourceIndex [.all, .one 3] i)), ?_, ?_⟩
  · unfold indexOp
    rw [h.shape, h.wellFormed]
    rfl
  apply rep_of_ofFn
  intro i hi
  obtain ⟨a0, b0, rfl, ha0, hb0⟩ := valid2 hi
  have ha0' : a0 = 0 := by omega
  subst ha0'
  simp only [sourceIndex, List.headD_cons, List.tail_cons, List.getD_cons_zero, List.getD_cons_succ]
  rw [h.entry _ (valid3_of ha0 (by omega) hb0)]

/-! ## Steps of `semOp` -/

theorem Rep.congr {t : Tensor ℝ} {s : List Nat} {f g : List Nat → ℝ} (h : ∀ i, Valid s i → f i = g i)
    (r : Rep t s f) : Rep t s g :=
  ⟨r.shape, r.size, fun i hi => (r.entry i hi).trans (h i hi)⟩

section steps
variable {g : Graph} {w : Weights ℝ} {x : Input} {vals : Array (Tensor ℝ)}

theorem semOp_param {n : String} {t : Tensor ℝ} (h : List.lookup n w = some t) :
    semOp g w x vals (.param n) = some t := h

theorem semOp_input {v : Tensor ℝ} (h : oneHotInput g.positions g.values x = some v) :
    semOp g w x vals .input = some v := h

theorem semOp_matmul {a b : Nat} {ta tb r : Tensor ℝ} (ha : vals[a]? = some ta) (hb : vals[b]? = some tb)
    (h : matmulOp ta tb = some r) : semOp g w x vals (.matmul a b) = some r := by
  simp only [semOp, ha, hb, h]

theorem semOp_binary {f : BinOp} {a b : Nat} {ta tb r : Tensor ℝ} (ha : vals[a]? = some ta)
    (hb : vals[b]? = some tb) (h : broadcastOp f.apply ta tb = some r) :
    semOp g w x vals (.binary f a b) = some r := by
  simp only [semOp, ha, hb, h]

theorem semOp_index {a : Nat} {items : List IndexItem} {ta r : Tensor ℝ} (ha : vals[a]? = some ta)
    (h : indexOp ta items = some r) : semOp g w x vals (.index a items) = some r := by
  simp only [semOp, ha, Option.bind_some, h]

theorem semOp_unsqueeze {a : Nat} {d : Int} {ta r : Tensor ℝ} (ha : vals[a]? = some ta)
    (h : unsqueezeOp ta d = some r) : semOp g w x vals (.unsqueeze a d) = some r := by
  simp only [semOp, ha, Option.bind_some, h]

theorem semOp_softmax {a : Nat} {d : Int} {ta r : Tensor ℝ} (ha : vals[a]? = some ta)
    (h : softmaxOp ta d = some r) : semOp g w x vals (.softmax a d) = some r := by
  simp only [semOp, ha, Option.bind_some, h]

theorem semOp_sum {a : Nat} {d : Int} {ta r : Tensor ℝ} (ha : vals[a]? = some ta)
    (h : sumOp d ta = some r) : semOp g w x vals (.sum a d) = some r := by
  show evalOp g w x vals (.sum a d) = some r
  simp only [evalOp, ha, h]

theorem semOps_cons_some' {op : Op} {ops : List Op} {vals' : Array (Tensor ℝ)} {v : Tensor ℝ}
    (h : semOp g w x vals op = some v) (hv : vals.push v = vals') :
    semOps g w x (op :: ops) vals = semOps g w x ops vals' := by
  rw [← hv]; simp [semOps, h]

end steps

/-! ## The closed form -/

noncomputable section

def resF (x : Input) (E P : Tensor ℝ) (p d : Nat) : ℝ :=
  ((List.range 64).map fun v => (if x.getD p 0 = v then (1 : ℝ) else 0) * E.entry [v, d]).sum + P.entry [p, d]

def lastF (x : Input) (E P : Tensor ℝ) (d : Nat) : ℝ := resF x E P 3 d

def qF (x : Input) (E P WQ C : Tensor ℝ) (d' : Nat) : ℝ :=
  ((List.range 32).map fun d => lastF x E P d * WQ.entry [d, d']).sum * C.entry []

def keyF (x : Input) (E P WK : Tensor ℝ) (p d' : Nat) : ℝ :=
  ((List.range 32).map fun d => resF x E P p d * WK.entry [d, d']).sum

def scoreF (x : Input) (E P WQ WK C : Tensor ℝ) (p : Nat) : ℝ :=
  ((List.range 32).map fun d' => keyF x E P WK p d' * qF x E P WQ C d').sum

def wF (x : Input) (E P WQ WK C : Tensor ℝ) (p : Nat) : ℝ :=
  Real.exp (scoreF x E P WQ WK C p) / ((List.range 4).map fun k => Real.exp (scoreF x E P WQ WK C k)).sum

def headF (x : Input) (E P WQ WK WV C : Tensor ℝ) (d' : Nat) : ℝ :=
  ((List.range 4).map fun k => wF x E P WQ WK C k * keyF x E P WV k d').sum

def outF (x : Input) (E P WQ WK WV WO C : Tensor ℝ) (d : Nat) : ℝ :=
  lastF x E P d + ((List.range 32).map fun d' => headF x E P WQ WK WV C d' * WO.entry [d', d]).sum

def logitF (x : Input) (E P WQ WK WV WO U C : Tensor ℝ) (j : Nat) : ℝ :=
  ((List.range 32).map fun d => outF x E P WQ WK WV WO C d * U.entry [d, j]).sum

end

open Protected.N_attn_max4_v64_s0 in
theorem formula {w : Weights ℝ} {E P WQ WK WV WO U C : Tensor ℝ} {x : Input}
    (hE : List.lookup "E" w = some E) (hEs : E.shape = [64, 32]) (hEn : E.data.size = 2048)
    (hP : List.lookup "P" w = some P) (hPs : P.shape = [4, 32]) (hPn : P.data.size = 128)
    (hWQ : List.lookup "WQ" w = some WQ) (hWQs : WQ.shape = [32, 32]) (hWQn : WQ.data.size = 1024)
    (hC : List.lookup "#const0" w = some C) (hCs : C.shape = []) (hCn : C.data.size = 1)
    (hWK : List.lookup "WK" w = some WK) (hWKs : WK.shape = [32, 32]) (hWKn : WK.data.size = 1024)
    (hWV : List.lookup "WV" w = some WV) (hWVs : WV.shape = [32, 32]) (hWVn : WV.data.size = 1024)
    (hWO : List.lookup "WO" w = some WO) (hWOs : WO.shape = [32, 32]) (hWOn : WO.data.size = 1024)
    (hU : List.lookup "U" w = some U) (hUs : U.shape = [32, 64]) (hUn : U.data.size = 2048)
    (hx : x.length = 4) (hall : x.all (· < 64) = true) :
    ∃ out, semGraph graph w x = some out ∧
      Rep out [1, 64] fun i => logitF x E P WQ WK WV WO U C (i.getD 1 0) := by
  obtain ⟨v0, hv0, r0⟩ := oneHot_rep hx hall
  have rE := param_rep hEs (by rw [hEn]; rfl)
  obtain ⟨v2, hv2, r2⟩ := matmul_1_4_rep r0 rE rfl
  have rP := param_rep hPs (by rw [hPn]; rfl)
  obtain ⟨v4, hv4, r4⟩ := add_1_4_32_rep r2 rP
  obtain ⟨v5, hv5, r5⟩ := index_rep r4
  have rWQ := param_rep hWQs (by rw [hWQn]; rfl)
  obtain ⟨v7, hv7, r7⟩ := matmul_1_32_rep r5 rWQ rfl
  have rC := param_rep hCs (by rw [hCn]; rfl)
  obtain ⟨v9, hv9, r9⟩ := bin_1_32_scalar_rep .mul r7 rC
  have rWK := param_rep hWKs (by rw [hWKn]; rfl)
  obtain ⟨v11, hv11, r11⟩ := matmul_1_4_rep r4 rWK rfl
  have rWV := param_rep hWVs (by rw [hWVn]; rfl)
  obtain ⟨v13, hv13, r13⟩ := matmul_1_4_rep r4 rWV rfl
  obtain ⟨v14, hv14, r14⟩ := unsq1_rep r9
  obtain ⟨v15, hv15, r15⟩ := bin_1_4_32_1_1_32_rep .mul r11 r14
  obtain ⟨v16, hv16, r16⟩ := sum2_rep r15
  obtain ⟨v17, hv17, r17⟩ := softmax_rep r16
  obtain ⟨v18, hv18, r18⟩ := unsq2_rep r17
  obtain ⟨v19, hv19, r19⟩ := bin_1_4_1_1_4_32_rep .mul r18 r13
  obtain ⟨v20, hv20, r20⟩ := sum1_rep r19
  have rWO := param_rep hWOs (by rw [hWOn]; rfl)
  obtain ⟨v22, hv22, r22⟩ := matmul_1_32_rep r20 rWO rfl
  obtain ⟨v23, hv23, r23⟩ := bin_1_32_rep .add r5 r22
  have rU := param_rep hUs (by rw [hUn]; rfl)
  obtain ⟨v25, hv25, r25⟩ := matmul_1_32_rep r23 rU rfl
  refine ⟨v25, ?_, ?_⟩
  · unfold semGraph
    rw [show graph.nodes = [Op.input, Op.param "E", Op.matmul 0 1, Op.param "P", Op.binary .add 2 3,
      Op.index 4 [.all, .one 3], Op.param "WQ", Op.matmul 5 6, Op.param "#const0", Op.binary .mul 7 8,
      Op.param "WK", Op.matmul 4 10, Op.param "WV", Op.matmul 4 12, Op.unsqueeze 9 1, Op.binary .mul 11 14,
      Op.sum 15 2, Op.softmax 16 1, Op.unsqueeze 17 2, Op.binary .mul 18 13, Op.sum 19 1, Op.param "WO",
      Op.matmul 20 21, Op.binary .add 5 22, Op.param "U", Op.matmul 23 24] from rfl]
    rw [semOps_cons_some' (semOp_input (g := graph) (vals := #[]) hv0) (vals' := #[v0]) rfl]
    rw [semOps_cons_some' (semOp_param (vals := #[v0]) hE) (vals' := #[v0, E]) rfl]
    rw [semOps_cons_some' (semOp_matmul (vals := #[v0, E]) rfl rfl hv2) (vals' := #[v0, E, v2]) rfl]
    rw [semOps_cons_some' (semOp_param (vals := #[v0, E, v2]) hP) (vals' := #[v0, E, v2, P]) rfl]
    rw [semOps_cons_some' (semOp_binary (vals := #[v0, E, v2, P]) rfl rfl hv4) (vals' := #[v0, E, v2, P, v4]) rfl]
    rw [semOps_cons_some' (semOp_index (vals := #[v0, E, v2, P, v4]) rfl hv5) (vals' := #[v0, E, v2, P, v4, v5]) rfl]
    rw [semOps_cons_some' (semOp_param (vals := #[v0, E, v2, P, v4, v5]) hWQ) (vals' := #[v0, E, v2, P, v4, v5, WQ]) rfl]
    rw [semOps_cons_some' (semOp_matmul (vals := #[v0, E, v2, P, v4, v5, WQ]) rfl rfl hv7)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7]) rfl]
    rw [semOps_cons_some' (semOp_param (vals := #[v0, E, v2, P, v4, v5, WQ, v7]) hC)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C]) rfl]
    rw [semOps_cons_some' (semOp_binary (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C]) rfl rfl hv9)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9]) rfl]
    rw [semOps_cons_some' (semOp_param (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9]) hWK)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK]) rfl]
    rw [semOps_cons_some' (semOp_matmul (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK]) rfl rfl hv11)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11]) rfl]
    rw [semOps_cons_some' (semOp_param (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11]) hWV)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV]) rfl]
    rw [semOps_cons_some' (semOp_matmul (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV]) rfl rfl hv13)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13]) rfl]
    rw [semOps_cons_some' (semOp_unsqueeze (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13]) rfl hv14)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14]) rfl]
    rw [semOps_cons_some' (semOp_binary (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14]) rfl rfl hv15)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15]) rfl]
    rw [semOps_cons_some' (semOp_sum (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15]) rfl hv16)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16]) rfl]
    rw [semOps_cons_some' (semOp_softmax (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16]) rfl hv17)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17]) rfl]
    rw [semOps_cons_some' (semOp_unsqueeze (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17]) rfl hv18)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18]) rfl]
    rw [semOps_cons_some' (semOp_binary (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18]) rfl rfl hv19)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19]) rfl]
    rw [semOps_cons_some' (semOp_sum (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19]) rfl hv20)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20]) rfl]
    rw [semOps_cons_some' (semOp_param (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20]) hWO)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20, WO]) rfl]
    rw [semOps_cons_some' (semOp_matmul (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20, WO]) rfl rfl hv22)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20, WO, v22]) rfl]
    rw [semOps_cons_some' (semOp_binary (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20, WO, v22]) rfl rfl hv23)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20, WO, v22, v23]) rfl]
    rw [semOps_cons_some' (semOp_param (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20, WO, v22, v23]) hU)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20, WO, v22, v23, U]) rfl]
    rw [semOps_cons_some' (semOp_matmul (vals := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20, WO, v22, v23, U]) rfl rfl hv25)
      (vals' := #[v0, E, v2, P, v4, v5, WQ, v7, C, v9, WK, v11, WV, v13, v14, v15, v16, v17, v18, v19, v20, WO, v22, v23, U, v25]) rfl]
    rfl
  · refine Rep.congr ?_ r25
    intro i hi
    obtain ⟨a0, b0, rfl, ha0, hb0⟩ := valid2 hi
    simp only [logitF, outF, headF, wF, scoreF, keyF, qF, lastF, resF, BinOp.apply,
      List.getD_cons_zero, List.getD_cons_succ]

end Candidate.Formula
