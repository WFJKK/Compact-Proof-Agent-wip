import Candidate.LibAttnOps
import Candidate.LibAttnChecker
import Mathlib.Data.Rat.BigOperators

/-!
# The family: one-layer, one-head, attention-only transformers

The pipeline's `models/attn-max2/model.py` (the same for max and min of 2 and 4 tokens, at every
size): one-hot tokens at `n` positions, the token embedding `E` (`V × d`) and the positional one
`P` (`n × d`) added, the last position's query `c · r_Q W_Q`, every position's key `r_p W_K` and
value `r_p W_V` (`d × h` each), the softmax of the scores, the head's output `W_O` (`h × d`) added
to the last position's residual, and the unembedding `U` (`d × V`). No biases.

`IsAttn` recognises the graph `scripts/export_network.py` writes for such a network, operation by
operation, and `Net.WF` says the weights have the shapes it needs. `eval_attn` follows the 26
operations over the reals and gives the logits as one formula, and `logit_eq` rewrites it as

    logit_j = D[q, j] + Σ_p α_p O[x_p, p, j],     α_p = exp S[q, x_p, p] / Σ_r exp S[q, x_r, r],

with the path tables `D`, `O`, `S` of `Net` (rationals: the weights are).
-/

namespace AttnClasses

open CompactCheck Common Finset

/-- The cast of the weights to the reals, as `realWeights` makes it. -/
local notation "toR" => (fun q : ℚ => (q : ℝ))

/-! ## The graph -/

/-- The 26 operations the exporter writes for the one-head model with last position `Q`. -/
def attnNodes (Q : ℕ) : List Op :=
  [.input, .param nE, .matmul 0 1, .param nP, .binary .add 2 3, .index 4 [.all, .one Q],
    .param nQ, .matmul 5 6, .param nC, .binary .mul 7 8, .param nK, .matmul 4 10,
    .param nV, .matmul 4 12, .unsqueeze 9 1, .binary .mul 11 14, .sum 15 2, .softmax 16 1,
    .unsqueeze 17 2, .binary .mul 18 13, .sum 19 1, .param nO, .matmul 20 21,
    .binary .add 5 22, .param nU, .matmul 23 24]

/-- The graph of the family, with at least one position and one token. -/
def IsAttn (g : Graph) : Prop :=
  g.nodes = attnNodes (g.positions - 1) ∧ g.output = 25 ∧ 0 < g.positions ∧ 0 < g.values

/-! ## The weights and the path tables -/

/-- A network of the family: its sizes and its eight weight tensors. -/
structure Net where
  V : ℕ
  n : ℕ
  d : ℕ
  h : ℕ
  E : Tensor ℚ
  P : Tensor ℚ
  WQ : Tensor ℚ
  WK : Tensor ℚ
  WV : Tensor ℚ
  WO : Tensor ℚ
  U : Tensor ℚ
  C : Tensor ℚ

namespace Net

variable (N : Net)

/-- The weights `w` are `N`'s, with the family's shapes. -/
structure WF (w : Weights ℚ) : Prop where
  hE : List.lookup nE w = some N.E
  hEs : N.E.shape = [N.V, N.d]
  hEn : N.E.data.size = N.V * N.d
  hP : List.lookup nP w = some N.P
  hPs : N.P.shape = [N.n, N.d]
  hPn : N.P.data.size = N.n * N.d
  hQ : List.lookup nQ w = some N.WQ
  hQs : N.WQ.shape = [N.d, N.h]
  hQn : N.WQ.data.size = N.d * N.h
  hK : List.lookup nK w = some N.WK
  hKs : N.WK.shape = [N.d, N.h]
  hKn : N.WK.data.size = N.d * N.h
  hV : List.lookup nV w = some N.WV
  hVs : N.WV.shape = [N.d, N.h]
  hVn : N.WV.data.size = N.d * N.h
  hO : List.lookup nO w = some N.WO
  hOs : N.WO.shape = [N.h, N.d]
  hOn : N.WO.data.size = N.h * N.d
  hU : List.lookup nU w = some N.U
  hUs : N.U.shape = [N.d, N.V]
  hUn : N.U.data.size = N.d * N.V
  hC : List.lookup nC w = some N.C
  hCs : N.C.shape = []
  hCn : N.C.data.size = 1

/-- The residual of token `t` at position `p`: `E_t + P_p`, coordinate `a`. -/
def r (t p a : ℕ) : ℚ := N.E.get (t * N.d + a) + N.P.get (p * N.d + a)

/-- The query of token `q` at the last position, coordinate `k`, scaled. -/
def qv (q k : ℕ) : ℚ :=
  (∑ a ∈ range N.d, N.r q (N.n - 1) a * N.WQ.get (a * N.h + k)) * N.C.get 0

/-- The key of token `t` at position `p`, coordinate `k`. -/
def key (t p k : ℕ) : ℚ := ∑ a ∈ range N.d, N.r t p a * N.WK.get (a * N.h + k)

/-- The value of token `t` at position `p`, coordinate `k`. -/
def val (t p k : ℕ) : ℚ := ∑ a ∈ range N.d, N.r t p a * N.WV.get (a * N.h + k)

/-- The score of token `t` at position `p` for the query token `q`. -/
def S (q t p : ℕ) : ℚ := ∑ k ∈ range N.h, N.key t p k * N.qv q k

/-- What token `t` at position `p` writes to logit `j` through the head. -/
def O (t p j : ℕ) : ℚ :=
  ∑ k ∈ range N.h, N.val t p k *
    ∑ a ∈ range N.d, N.WO.get (k * N.d + a) * N.U.get (a * N.V + j)

/-- The direct path: what the query token `q` writes to logit `j`. -/
def D (q j : ℕ) : ℚ := ∑ a ∈ range N.d, N.r q (N.n - 1) a * N.U.get (a * N.V + j)

/-- The token at position `p` of `x`. -/
abbrev tk (x : Input) (p : ℕ) : ℕ := x.getD p 0

/-- The attention weight of position `p` on input `x`. -/
noncomputable def α (x : Input) (p : ℕ) : ℝ :=
  Real.exp (N.S (tk x (N.n - 1)) (tk x p) p) /
    ∑ r ∈ range N.n, Real.exp (N.S (tk x (N.n - 1)) (tk x r) r)

/-- Logit `j` on input `x`, as the operations compute it. -/
noncomputable def logitF (x : Input) (j : ℕ) : ℝ :=
  ∑ a ∈ range N.d, ((N.r (tk x (N.n - 1)) (N.n - 1) a : ℝ) +
    ∑ k ∈ range N.h, (∑ p ∈ range N.n, N.α x p * (N.val (tk x p) p k : ℝ)) *
      (N.WO.get (k * N.d + a) : ℝ)) * (N.U.get (a * N.V + j) : ℝ)

end Net

/-! ## Following the operations -/

theorem semOps_cons_some {α : Type} [Zero α] [One α] [Add α] [Mul α] [Neg α] [ExpDiv α]
    {g : Graph} {w : Weights α} {x : Input} {vals : Array (Tensor α)} {op : Op} {ops : List Op}
    {v : Tensor α} (h : semOp g w x vals op = some v) :
    semOps g w x (op :: ops) vals = semOps g w x ops (vals.push v) := by
  simp [semOps, h]

theorem lookup_real {w : Weights ℚ} {nm : String} {t : Tensor ℚ}
    (h : List.lookup nm w = some t) :
    List.lookup nm (realWeights w) = some (t.map toR) := by
  rw [lookup_realWeights, h]
  rfl

theorem size_map_toR (t : Tensor ℚ) : (t.map toR).data.size = t.data.size := by
  simp [Tensor.map]

theorem tk_mem {x : Input} {p : ℕ} (hp : p < x.length) : Net.tk x p ∈ x := by
  rw [Net.tk, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  exact List.getElem_mem hp

theorem get_data (s : List ℕ) (t : Tensor ℝ) (i : ℕ) : (Tensor.mk s t.data).get i = t.get i :=
  rfl

/-- **The operations, followed.** On a network of the family and a valid input, the graph's real
    output is the vector of `logitF`. -/
theorem eval_attn {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) {x : Input} (hx : x.length = N.n)
    (hxV : ∀ t ∈ x, t < N.V) :
    ∃ out : Tensor ℝ, realOutput g w x = some out ∧ out.shape = [1, N.V] ∧
      out.data.size = N.V ∧ ∀ j < N.V, out.get j = N.logitF x j := by
  obtain ⟨hnodes, hout, hpos, -⟩ := hg
  have hQ : N.n - 1 < N.n := by omega
  -- the weights, over the reals
  have rE := lookup_real hw.hE
  have rP := lookup_real hw.hP
  have rQ := lookup_real hw.hQ
  have rK := lookup_real hw.hK
  have rV := lookup_real hw.hV
  have rO := lookup_real hw.hO
  have rU := lookup_real hw.hU
  have rC := lookup_real hw.hC
  -- the operations, one at a time
  obtain ⟨T0, h0, h0s, h0n, h0g⟩ := oneHot_get hx hxV
  obtain ⟨T2, h2, h2s, h2n, h2g⟩ := matmul_three h0s h0n (b := N.E.map toR) hw.hEs
    (by rw [size_map_toR, hw.hEn])
  obtain ⟨T4, h4, h4s, h4n, h4g⟩ := bcast_add_three h2s h2n (b := N.P.map toR) hw.hPs
    (by rw [size_map_toR, hw.hPn])
  obtain ⟨T5, h5, h5s, h5n, h5g⟩ := index_last h4s h4n hQ
  obtain ⟨T7, h7, h7s, h7n, h7g⟩ := matmul_two h5s h5n (b := N.WQ.map toR) hw.hQs
    (by rw [size_map_toR, hw.hQn])
  obtain ⟨T9, h9, h9s, h9n, h9g⟩ := bcast_mul_scalar h7s h7n (b := N.C.map toR) hw.hCs
    (by rw [size_map_toR, hw.hCn])
  obtain ⟨T11, h11, h11s, h11n, h11g⟩ := matmul_three h4s h4n (b := N.WK.map toR) hw.hKs
    (by rw [size_map_toR, hw.hKn])
  obtain ⟨T13, h13, h13s, h13n, h13g⟩ := matmul_three h4s h4n (b := N.WV.map toR) hw.hVs
    (by rw [size_map_toR, hw.hVn])
  have h14 := unsqueeze_mid h9s
  obtain ⟨T15, h15, h15s, h15n, h15g⟩ :=
    bcast_mul_mid h11s h11n (b := ⟨[1, 1, N.h], T9.data⟩)
    rfl h9n
  obtain ⟨T16, h16, h16s, h16n, h16g⟩ := sum_last h15s h15n
  obtain ⟨T17, h17, h17s, h17n, h17g⟩ := softmax_row h16s h16n
  have h18 := unsqueeze_last h17s
  obtain ⟨T19, h19, h19s, h19n, h19g⟩ :=
    bcast_mul_last (a := ⟨[1, N.n, 1], T17.data⟩) rfl h17n
    h13s h13n
  obtain ⟨T20, h20, h20s, h20n, h20g⟩ := sum_mid h19s h19n
  obtain ⟨T22, h22, h22s, h22n, h22g⟩ := matmul_two h20s h20n (b := N.WO.map toR) hw.hOs
    (by rw [size_map_toR, hw.hOn])
  obtain ⟨T23, h23, h23s, h23n, h23g⟩ := bcast_add_two h5s h5n h22s h22n
  obtain ⟨T25, h25, h25s, h25n, h25g⟩ := matmul_two h23s h23n (b := N.U.map toR) hw.hUs
    (by rw [size_map_toR, hw.hUn])
  refine ⟨T25, ?_, h25s, h25n, fun j hj => ?_⟩
  · unfold realOutput semGraph
    rw [hnodes, ← hn, attnNodes]
    simp [semOps, semOp, evalOp, ← hn, ← hV, h0, rE, h2, rP, h4, h5, rQ, h7, rC, h9, rK, h11,
      rV, h13, h14, h15, h16, h17, h18, h19, h20, rO, h22, h23, rU, h25,
      hout]
  · have e4 : ∀ p < N.n, ∀ a < N.d, T4.get (p * N.d + a) = (N.r (Net.tk x p) p a : ℝ) := by
      intro p hp a ha
      rw [h4g p hp a ha, h2g p hp a ha, Tensor.get_map_cast]
      have hxp : Net.tk x p < N.V := hxV _ (tk_mem (by omega))
      have : ((List.range N.V).map fun t => T0.get (p * N.V + t) *
          (N.E.map toR).get (t * N.d + a)).sum = (N.E.get (Net.tk x p * N.d + a) : ℝ) := by
        rw [← onehot_sum N.V (Net.tk x p) hxp (fun t => (N.E.get (t * N.d + a) : ℝ))]
        refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
        rw [h0g p hp t (List.mem_range.mp ht), Tensor.get_map_cast]
      rw [this, Net.r]
      push_cast
      ring
    have e5 : ∀ a < N.d, T5.get a = (N.r (Net.tk x (N.n - 1)) (N.n - 1) a : ℝ) := fun a ha => by
      rw [h5g a ha, e4 _ hQ a ha]
    have e9 : ∀ k < N.h, T9.get k = (N.qv (Net.tk x (N.n - 1)) k : ℝ) := by
      intro k hk
      rw [h9g k hk, h7g k hk, Tensor.get_map_cast, sum_range_eq, Net.qv]
      push_cast
      congr 1
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [e5 a (Finset.mem_range.mp ha), Tensor.get_map_cast]
    have e11 : ∀ p < N.n, ∀ k < N.h,
        T11.get (p * N.h + k) = (N.key (Net.tk x p) p k : ℝ) := by
      intro p hp k hk
      rw [h11g p hp k hk, sum_range_eq, Net.key]
      push_cast
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [e4 p hp a (Finset.mem_range.mp ha), Tensor.get_map_cast]
    have e13 : ∀ p < N.n, ∀ k < N.h,
        T13.get (p * N.h + k) = (N.val (Net.tk x p) p k : ℝ) := by
      intro p hp k hk
      rw [h13g p hp k hk, sum_range_eq, Net.val]
      push_cast
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [e4 p hp a (Finset.mem_range.mp ha), Tensor.get_map_cast]
    have e16 : ∀ p < N.n, T16.get p = (N.S (Net.tk x (N.n - 1)) (Net.tk x p) p : ℝ) := by
      intro p hp
      rw [h16g p hp, sum_range_eq, Net.S]
      push_cast
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' := Finset.mem_range.mp hk
      rw [h15g p hp k hk', get_data _ T9 k, e11 p hp k hk', e9 k hk']
    have e17 : ∀ p < N.n, T17.get p = N.α x p := by
      intro p hp
      rw [h17g p hp, e16 p hp, Net.α, sum_range_eq]
      congr 1
      exact Finset.sum_congr rfl fun r hr => by rw [e16 r (Finset.mem_range.mp hr)]
    have e20 : ∀ k < N.h, T20.get k =
        ∑ p ∈ range N.n, N.α x p * (N.val (Net.tk x p) p k : ℝ) := by
      intro k hk
      rw [h20g k hk, sum_range_eq]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp' := Finset.mem_range.mp hp
      rw [h19g p hp' k hk, get_data _ T17 p, e17 p hp', e13 p hp' k hk]
    have e23 : ∀ a < N.d, T23.get a = (N.r (Net.tk x (N.n - 1)) (N.n - 1) a : ℝ) +
        ∑ k ∈ range N.h, (∑ p ∈ range N.n, N.α x p * (N.val (Net.tk x p) p k : ℝ)) *
          (N.WO.get (k * N.d + a) : ℝ) := by
      intro a ha
      rw [h23g a ha, e5 a ha, h22g a ha, sum_range_eq]
      congr 1
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [e20 k (Finset.mem_range.mp hk), Tensor.get_map_cast]
    rw [h25g j hj, sum_range_eq, Net.logitF]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [e23 a (Finset.mem_range.mp ha), Tensor.get_map_cast]

/-! ## The logits through the path tables -/

/-- The logits are the direct path plus the attention-weighted paths through the head. -/
theorem logit_eq (N : Net) (x : Input) (j : ℕ) :
    N.logitF x j = (N.D (Net.tk x (N.n - 1)) j : ℝ) +
      ∑ p ∈ range N.n, N.α x p * (N.O (Net.tk x p) p j : ℝ) := by
  unfold Net.logitF Net.D Net.O
  push_cast
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum]
  congr 1
  -- Σ_a Σ_k Σ_p into Σ_p Σ_k Σ_a
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun a _ => ?_
  ring

/-- **The bound.** If `κ_p ≤ exp(s_p) (μ + G_p)` with `μ ≤ A` and `G_p ≤ B_p`, and the
    `κ_p` add up to a positive number, then so does `A + Σ_p α_p B_p`, `α` the softmax of
    `s`. -/
theorem margin_pos {n : ℕ} (hn : 0 < n) (s : ℕ → ℝ) {A μ : ℝ} {B G κ : ℕ → ℝ}
    (hA : μ ≤ A) (hB : ∀ p < n, G p ≤ B p)
    (hκ : ∀ p < n, κ p ≤ Real.exp (s p) * (μ + G p))
    (hpos : 0 < ∑ p ∈ range n, κ p) :
    0 < A + ∑ p ∈ range n, Real.exp (s p) / (∑ r ∈ range n, Real.exp (s r)) * B p := by
  set Z := ∑ r ∈ range n, Real.exp (s r) with hZ
  have hZpos : 0 < Z := Finset.sum_pos (fun r _ => Real.exp_pos _) ⟨0, Finset.mem_range.mpr hn⟩
  have key : Z * (A + ∑ p ∈ range n, Real.exp (s p) / Z * B p) =
      ∑ p ∈ range n, Real.exp (s p) * (A + B p) := by
    rw [mul_add, Finset.mul_sum, hZ, Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← hZ]
    field_simp
  have hge : ∑ p ∈ range n, κ p ≤ ∑ p ∈ range n, Real.exp (s p) * (A + B p) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hp' := Finset.mem_range.mp hp
    calc κ p ≤ Real.exp (s p) * (μ + G p) := hκ p hp'
      _ ≤ Real.exp (s p) * (A + B p) :=
        mul_le_mul_of_nonneg_left (by linarith [hB p hp']) (Real.exp_pos _).le
  have h1 : 0 < Z * (A + ∑ p ∈ range n, Real.exp (s p) / Z * B p) := by
    rw [key]; linarith
  exact pos_of_mul_pos_right h1 hZpos.le

/-- **Correct, from the tables.** On a network of the family and a valid input `x` with label
    `ℓ`: if `μ` bounds the direct path's margin of `ℓ` over every other output, `G p` the
    margin of the path of position `p`, and `κ p ≤ exp(S) (μ + G p)` add up to a positive
    number, then the network answers `x` correctly. -/
theorem correct_of_bound {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) {task : Task} {x : Input}
    (hx : x.length = N.n) (hxV : ∀ t ∈ x, t < N.V) (hl : task.label x < N.V) {μ : ℝ}
    {G κ : ℕ → ℝ}
    (hμ : ∀ j < N.V, j ≠ task.label x →
      μ ≤ (N.D (Net.tk x (N.n - 1)) (task.label x) : ℝ) - N.D (Net.tk x (N.n - 1)) j)
    (hG : ∀ p < N.n, ∀ j < N.V, j ≠ task.label x →
      G p ≤ (N.O (Net.tk x p) p (task.label x) : ℝ) - N.O (Net.tk x p) p j)
    (hκ : ∀ p < N.n, κ p ≤
      Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x p) p) * (μ + G p))
    (hpos : 0 < ∑ p ∈ range N.n, κ p) :
    Correct g w task x := by
  obtain ⟨out, hout, hs, hsz, hget⟩ := eval_attn hg hw hV hn hx hxV
  refine ⟨out, hout, by rw [hs, hsz], by rw [hsz]; exact hl, fun j hj hne => ?_⟩
  rw [hsz] at hj
  rw [hget j hj, hget _ hl, logit_eq, logit_eq]
  have hn0 : 0 < N.n := by have := hg.2.2.1; omega
  have := margin_pos hn0 (fun p => (N.S (Net.tk x (N.n - 1)) (Net.tk x p) p : ℝ))
    (A := (N.D (Net.tk x (N.n - 1)) (task.label x) : ℝ) - N.D (Net.tk x (N.n - 1)) j)
    (B := fun p => (N.O (Net.tk x p) p (task.label x) : ℝ) - N.O (Net.tk x p) p j)
    (hμ j hj hne) (fun p hp => hG p hp j hj hne) hκ hpos
  simp only [Net.α] at *
  have hsplit : ∀ p ∈ range N.n,
      Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x p) p) /
          (∑ r ∈ range N.n, Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x r) r)) *
        ((N.O (Net.tk x p) p (task.label x) : ℝ) - N.O (Net.tk x p) p j) =
      Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x p) p) /
          (∑ r ∈ range N.n, Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x r) r)) *
        (N.O (Net.tk x p) p (task.label x) : ℝ) -
      Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x p) p) /
          (∑ r ∈ range N.n, Real.exp (N.S (Net.tk x (N.n - 1)) (Net.tk x r) r)) *
        (N.O (Net.tk x p) p j : ℝ) := fun p _ => by ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib] at this
  linarith

end AttnClasses
