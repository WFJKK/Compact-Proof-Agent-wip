import Protected.N_max4_v64_s0
import CompactCheck.Soundness
import CompactCheck.CountedOps

/-!
# Infrastructure (P1): the exact evaluator on the max4 graph is a composition of three
linear maps applied to the token-count vector. Generic over the weights.
-/

namespace Candidate.Linear

open CompactCheck Protected.N_max4_v64_s0

theorem graph_nodes : graph.nodes = [.input, .sum 0 1, .linear 1 "embedding.weight" none,
    .linear 2 "linear.weight" none, .linear 3 "unembedding.weight" none] := rfl
theorem graph_output : graph.output = 4 := rfl
theorem graph_positions : graph.positions = 4 := rfl
theorem graph_values : graph.values = 64 := rfl

/-- Entry `j` of a tensor built from `Array.range n` mapped by `f`. -/
theorem get_range_map (s : List Nat) (n : Nat) (f : Nat → ℚ) (j : Nat) (hj : j < n) :
    Tensor.get ⟨s, (Array.range n).map f⟩ j = f j := by
  simp [Tensor.get, Array.getD_eq_getD_getElem?, Array.getElem?_map, hj]

theorem get_range_map_ge (s : List Nat) (n : Nat) (f : Nat → ℚ) (j : Nat) (hj : n ≤ j) :
    Tensor.get ⟨s, (Array.range n).map f⟩ j = 0 := by
  simp [Tensor.get, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_range,
    Nat.not_lt.mpr hj]

/-- `linearOp` without bias on a row vector `[1, inn]`. -/
theorem linearOp_row (W t : Tensor ℚ) (out inn : Nat) (hW : W.shape = [out, inn])
    (hWs : W.data.size = out * inn) (ht : t.shape = [1, inn]) (hts : t.data.size = inn) :
    ∃ r : Tensor ℚ, linearOp W none t = some r ∧ r.shape = [1, out] ∧ r.data.size = out ∧
      ∀ o < out, r.get o = ((List.range inn).map fun i => W.get (o * inn + i) * t.get i).sum := by
  have hdl : (([1, inn] : List Nat).dropLast) = [1] := rfl
  have hpre : shapeSize ([1] : List Nat) = 1 := rfl
  have hlast : (([1, inn] : List Nat).getLast?) = some inn := rfl
  simp only [linearOp, hW, ht, hWs, hts, hdl, hpre, hlast, List.getD_cons_zero, List.getD_cons_succ,
    Nat.one_mul, beq_self_eq_true, Bool.and_self, Bool.and_true, Bool.true_and, ite_true]
  refine ⟨_, rfl, by simp, by simp, fun o ho => ?_⟩
  rw [get_range_map _ _ _ o ho]
  simp [Nat.div_eq_of_lt ho, Nat.mod_eq_of_lt ho]

/-- `sumOp 1` on a tensor of shape `[1, P, V]`. -/
theorem sumOp_dim1 (t : Tensor ℚ) (P V : Nat) (ht : t.shape = [1, P, V]) (hts : t.data.size = P * V) :
    ∃ r : Tensor ℚ, sumOp 1 t = some r ∧ r.shape = [1, V] ∧ r.data.size = V ∧
      ∀ v < V, r.get v = ((List.range P).map fun k => t.get (k * V + v)).sum := by
  have hn : normDim 1 ([1, P, V] : List Nat).length = some 1 := rfl
  have htk : List.take 1 ([1, P, V] : List Nat) = [1] := rfl
  have hdr : List.drop 2 ([1, P, V] : List Nat) = [V] := rfl
  have hgd : ([1, P, V] : List Nat).getD 1 0 = P := rfl
  have her : ([1, P, V] : List Nat).eraseIdx 1 = [1, V] := rfl
  have hs1 : shapeSize ([1] : List Nat) = 1 := rfl
  have hsV : shapeSize ([V] : List Nat) = V := by simp [shapeSize]
  simp only [sumOp, ht, hts, hn, htk, hdr, hgd, her, hs1, hsV, Nat.one_mul, beq_self_eq_true, ite_true]
  refine ⟨_, rfl, rfl, by simp, fun v hv => ?_⟩
  rw [get_range_map _ _ _ v hv]
  simp [Nat.div_eq_of_lt hv, Nat.mod_eq_of_lt hv]

/-- The one-hot input. -/
theorem oneHotInput_spec (P V : Nat) (x : Input) (hx : x.length = P) (hall : ∀ a ∈ x, a < V) :
    ∃ r : Tensor ℚ, oneHotInput P V x = some r ∧ r.shape = [1, P, V] ∧ r.data.size = P * V ∧
      ∀ j < P * V, r.get j = if x.getD (j / V) 0 = j % V then 1 else 0 := by
  have hc : (x.length == P && x.all (· < V)) = true := by
    simp only [hx, beq_self_eq_true, Bool.true_and, List.all_eq_true, decide_eq_true_eq]
    exact hall
  simp only [oneHotInput, hc, ite_true]
  refine ⟨_, rfl, rfl, by simp, fun j hj => ?_⟩
  rw [get_range_map _ _ _ j hj]

/-- The number of positions (among `P`) of `x` holding token `t`, as a rational. -/
def cnt (P : Nat) (x : Input) (t : Nat) : ℚ :=
  ((List.range P).map fun p => if x.getD p 0 = t then (1 : ℚ) else 0).sum

/-- The first hidden layer: `E` applied to the count vector. -/
def hid1 (E : Tensor ℚ) (P V : Nat) (x : Input) (l : Nat) : ℚ :=
  ((List.range V).map fun t => E.get (l * V + t) * cnt P x t).sum

/-- The second hidden layer. -/
def hid2 (E L : Tensor ℚ) (d P V : Nat) (x : Input) (k : Nat) : ℚ :=
  ((List.range d).map fun l => L.get (k * d + l) * hid1 E P V x l).sum

/-- Logit `j`. -/
def logit (E L U : Tensor ℚ) (d P V : Nat) (x : Input) (j : Nat) : ℚ :=
  ((List.range d).map fun k => U.get (j * d + k) * hid2 E L d P V x k).sum

/-- (P1) The exact evaluator on the max4 graph, for any weights of the right shapes:
    the output is the vector of logits. -/
theorem evalGraph_max4 (w : Weights ℚ) (E L U : Tensor ℚ) (d P V : Nat)
    (hgP : graph.positions = P) (hgV : graph.values = V)
    (hE : List.lookup "embedding.weight" w = some E) (hEs : E.shape = [d, V])
    (hEsz : E.data.size = d * V)
    (hL : List.lookup "linear.weight" w = some L) (hLs : L.shape = [d, d])
    (hLsz : L.data.size = d * d)
    (hU : List.lookup "unembedding.weight" w = some U) (hUs : U.shape = [V, d])
    (hUsz : U.data.size = V * d)
    (x : Input) (hx : x.length = P) (hall : ∀ a ∈ x, a < V) :
    ∃ out : Tensor ℚ, evalGraph graph w x = some out ∧ out.shape = [1, V] ∧ out.data.size = V ∧
      ∀ j < V, out.get j = logit E L U d P V x j := by
  obtain ⟨r0, h0, s0, z0, g0⟩ := oneHotInput_spec P V x hx hall
  obtain ⟨r1, h1, s1, z1, g1⟩ := sumOp_dim1 r0 P V s0 z0
  obtain ⟨r2, h2, s2, z2, g2⟩ := linearOp_row E r1 d V hEs hEsz s1 z1
  obtain ⟨r3, h3, s3, z3, g3⟩ := linearOp_row L r2 d d hLs hLsz s2 z2
  obtain ⟨r4, h4, s4, z4, g4⟩ := linearOp_row U r3 V d hUs hUsz s3 z3
  refine ⟨r4, ?_, s4, z4, ?_⟩
  · unfold evalGraph
    rw [graph_nodes, graph_output]
    simp [evalOps, evalOp, hgP, hgV, h0, h1, h2, h3, h4, hE, hL, hU]
  · intro j hj
    have hV0 : 0 < V := by omega
    rw [g4 j hj]
    unfold logit
    congr 1
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    rw [g3 k hk]
    unfold hid2
    congr 1
    congr 1
    apply List.map_congr_left
    intro l hl
    rw [List.mem_range] at hl
    rw [g2 l hl]
    unfold hid1
    congr 1
    congr 1
    apply List.map_congr_left
    intro t ht
    rw [List.mem_range] at ht
    rw [g1 t ht]
    unfold cnt
    congr 1
    congr 1
    apply List.map_congr_left
    intro p hp
    rw [List.mem_range] at hp
    have hlt : p * V + t < P * V := by
      calc p * V + t < p * V + V := by omega
        _ = (p + 1) * V := by ring
        _ ≤ P * V := Nat.mul_le_mul_right V hp
    rw [g0 (p * V + t) hlt]
    rw [Nat.add_comm (p * V) t, Nat.add_mul_div_right t p hV0, Nat.add_mul_mod_self_right,
      Nat.div_eq_of_lt ht, Nat.mod_eq_of_lt ht, Nat.zero_add]

theorem task_label (x : Input) : task.label x = x.foldl max 0 := rfl
theorem task_space : task.space = [64, 64, 64, 64] := rfl

/-- An input is answered correctly when its label's logit beats every other logit, over ℚ. -/
theorem correct_of_logits (w : Weights ℚ) (E L U : Tensor ℚ) (d P V : Nat)
    (hgP : graph.positions = P) (hgV : graph.values = V)
    (hE : List.lookup "embedding.weight" w = some E) (hEs : E.shape = [d, V])
    (hEsz : E.data.size = d * V)
    (hL : List.lookup "linear.weight" w = some L) (hLs : L.shape = [d, d])
    (hLsz : L.data.size = d * d)
    (hU : List.lookup "unembedding.weight" w = some U) (hUs : U.shape = [V, d])
    (hUsz : U.data.size = V * d)
    (x : Input) (hx : x.length = P) (hall : ∀ a ∈ x, a < V)
    (hlab : task.label x < V)
    (hlt : ∀ j < V, j ≠ task.label x →
      logit E L U d P V x j < logit E L U d P V x (task.label x)) :
    Correct graph w task x := by
  obtain ⟨out, hout, hs, hz, hg⟩ :=
    evalGraph_max4 w E L U d P V hgP hgV hE hEs hEsz hL hLs hLsz hU hUs hUsz x hx hall
  have hr := realOutput_of_evalGraph hout
  refine ⟨_, hr, ?_, ?_, ?_⟩
  · rw [Tensor.map_shape', Tensor.map_data_size, hs, hz]
  · rw [Tensor.map_data_size, hz]; exact hlab
  · intro j hj hne
    rw [Tensor.map_data_size, hz] at hj
    rw [Tensor.get_map_cast, Tensor.get_map_cast, hg j hj, hg _ hlab]
    exact_mod_cast hlt j hj hne

end Candidate.Linear
