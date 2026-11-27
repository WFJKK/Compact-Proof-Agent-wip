import Candidate.LibCommonBasic
import CompactCheck.TokensIndex

/-!
# The operations of the attention graph, over the reals

What each of the operations the exporter writes for the one-head attention model computes, on
tensors of the shapes that model gives them, in the flat (row-major) indices of the result: a
product with a matrix, a broadcast sum or product, picking the last position, a new dimension of
size one, a sum over one dimension and a softmax. Each lemma states that the operation succeeds,
the shape and length of its result, and every entry.

These are CompactCheck's own definitions (`Semantics.lean`, `Eval.lean`), unchanged: the lemmas
only read them.
-/

namespace AttnClasses

open CompactCheck

/-! ## Indices -/

theorem unravel_one_three {n m p c : ℕ} (hp : p < n) (hc : c < m) :
    unravel [1, n, m] (p * m + c) = [0, p, c] := by
  have h := unravel_three_cons (P := n) (rest := [m]) hp (q := c) (by simpa [shapeSize] using hc)
  have hs : shapeSize [m] = m := by simp [shapeSize]
  rw [hs] at h
  rw [h]
  simp [unravel, strides, shapeSize, Nat.mod_eq_of_lt hc]

theorem unravel_one_two {m c : ℕ} (hc : c < m) : unravel [1, m] c = [0, c] := by
  simp [unravel, strides, shapeSize, Nat.mod_eq_of_lt hc, Nat.div_eq_of_lt hc]

theorem ravel_one_two (m c : ℕ) : ravel [1, m] [0, c] = c := by
  simp [ravel, strides, shapeSize]

theorem ravel_one_three (n m p c : ℕ) : ravel [1, n, m] [0, p, c] = p * m + c := by
  simp [ravel, strides, shapeSize]
  ring

theorem shapeSize_three (n m : ℕ) : shapeSize [1, n, m] = n * m := by
  simp [shapeSize]

theorem shapeSize_two (m : ℕ) : shapeSize [1, m] = m := by
  simp [shapeSize]

theorem shapeSize_pair (a b : ℕ) : shapeSize [a, b] = a * b := by
  simp [shapeSize]

theorem wf_iff {α : Type} (t : Tensor α) :
    t.wellFormed = true ↔ t.data.size = shapeSize t.shape := by
  simp [Tensor.wellFormed]

/-- A dimension of size `n` keeps an index below `n`, also when `n = 1`. -/
theorem keep_index {n p : ℕ} (hp : p < n) : (if n = 1 then 0 else p) = p := by
  split <;> omega

/-! ## The one-hot input -/

theorem get_map_range {α : Type} [Zero α] {s : List ℕ} {f : ℕ → α} {n j : ℕ}
    (hj : j < n) :
    (Tensor.mk s ((Array.range n).map f)).get j = f j := by
  simp [Tensor.get, Array.getD, hj]

theorem oneHot_get {n V : ℕ} {x : Input} (hx : x.length = n) (hxV : ∀ t ∈ x, t < V) :
    ∃ oh : Tensor ℝ, oneHotInput n V x = some oh ∧ oh.shape = [1, n, V] ∧
      oh.data.size = n * V ∧
      ∀ p < n, ∀ t < V, oh.get (p * V + t) = if x.getD p 0 = t then 1 else 0 := by
  refine ⟨⟨[1, n, V], (Array.range (n * V)).map fun j =>
      if x.getD (j / V) 0 = j % V then 1 else 0⟩, ?_, rfl, by simp, fun p hp t ht => ?_⟩
  · unfold oneHotInput
    have hall : x.all (· < V) = true := List.all_eq_true.mpr fun t ht => decide_eq_true (hxV t ht)
    simp [hx, hall]
  · have hj : p * V + t < n * V := lt_mul_of_row hp ht
    rw [get_map_range hj, div_aux (by omega) ht, mod_aux ht]

/-! ## Products with a matrix -/

/-- `[1, n, K] × [K, M]`. -/
theorem matmul_three {a b : Tensor ℝ} {n K M : ℕ} (ha : a.shape = [1, n, K])
    (han : a.data.size = n * K) (hb : b.shape = [K, M]) (hbn : b.data.size = K * M) :
    ∃ r, matmulOp a b = some r ∧ r.shape = [1, n, M] ∧ r.data.size = n * M ∧
      ∀ p < n, ∀ c < M, r.get (p * M + c) =
        ((List.range K).map fun t => a.get (p * K + t) * b.get (t * M + c)).sum := by
  have hwa : a.wellFormed = true := by rw [wf_iff, ha, han, shapeSize_three]
  have hwb : b.wellFormed = true := by rw [wf_iff, hb, hbn, shapeSize_pair]
  unfold matmulOp
  simp only [hwa, hwb, Bool.not_true, Bool.or_self, Bool.false_eq_true, ↓reduceIte, ha, hb,
    matmulShape_lookup, Option.map_some]
  refine ⟨_, rfl, rfl, by simp [Tensor.ofFn_data_size, shapeSize], fun p hp c hc => ?_⟩
  have hj : p * M + c < shapeSize ([1] ++ [n, M]) := by
    simp only [List.singleton_append, shapeSize_three]
    exact lt_mul_of_row hp hc
  rw [Tensor.get_mk_ofFn _ _ _ hj]
  simp only [List.singleton_append]
  rw [unravel_one_three hp hc]
  have hbi : broadcastIndex [1] (List.take [1].length [0, p, c]) = [0] := by
    simp [broadcastIndex]
  have hbj : broadcastIndex [] (List.take [1].length [0, p, c]) = [] := by
    simp [broadcastIndex]
  rw [hbi, hbj]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Tensor.entry, List.singleton_append, List.nil_append, List.getD_cons_zero,
    List.getD_cons_succ, List.length_singleton]
  rw [ravel_one_three, ravel_pair]
  rfl

/-- `[1, K] × [K, M]`. -/
theorem matmul_two {a b : Tensor ℝ} {K M : ℕ} (ha : a.shape = [1, K]) (han : a.data.size = K)
    (hb : b.shape = [K, M]) (hbn : b.data.size = K * M) :
    ∃ r, matmulOp a b = some r ∧ r.shape = [1, M] ∧ r.data.size = M ∧
      ∀ c < M, r.get c = ((List.range K).map fun t => a.get t * b.get (t * M + c)).sum := by
  have hwa : a.wellFormed = true := by rw [wf_iff, ha, han, shapeSize_two]
  have hwb : b.wellFormed = true := by rw [wf_iff, hb, hbn, shapeSize_pair]
  obtain ⟨r, hr, hrs, hrn, hget⟩ := matmulOp_two ha hb hwa hwb
  refine ⟨r, hr, hrs, by rw [hrn, Nat.one_mul], fun c hc => ?_⟩
  have := hget 0 Nat.one_pos c hc
  simpa using this

/-! ## Entrywise operations with broadcasting -/

theorem broadcastShape_three_two (n d : ℕ) :
    broadcastShape [1, n, d] [n, d] = some [1, n, d] := by
  simp [broadcastShape]

theorem broadcastShape_two_scalar (h : ℕ) : broadcastShape [1, h] [] = some [1, h] := by
  by_cases h2 : h = 1
  · subst h2; simp [broadcastShape]
  · simp [broadcastShape, h2]

theorem broadcastShape_bcast_mid (n h : ℕ) :
    broadcastShape [1, n, h] [1, 1, h] = some [1, n, h] := by
  by_cases h1 : n = 1
  · subst h1; simp [broadcastShape]
  · simp [broadcastShape, h1]

theorem broadcastShape_bcast_last (n h : ℕ) :
    broadcastShape [1, n, 1] [1, n, h] = some [1, n, h] := by
  by_cases h2 : h = 1
  · subst h2; simp [broadcastShape]
  · have h3 : ¬ (1 = h) := fun e => h2 e.symm
    simp [broadcastShape, h3]

theorem bI_three_self {n d p c : ℕ} (hp : p < n) (hc : c < d) :
    broadcastIndex [1, n, d] [0, p, c] = [0, p, c] := by
  simp [broadcastIndex, keep_index hp, keep_index hc]

theorem bI_three_two {n d p c : ℕ} (hp : p < n) (hc : c < d) :
    broadcastIndex [n, d] [0, p, c] = [p, c] := by
  simp [broadcastIndex, keep_index hp, keep_index hc]

theorem bI_two_self {h k : ℕ} (hk : k < h) : broadcastIndex [1, h] [0, k] = [0, k] := by
  simp [broadcastIndex, keep_index hk]

theorem bI_scalar (i : List ℕ) : broadcastIndex [] i = [] := by
  simp [broadcastIndex]

theorem bI_mid {h p k : ℕ} (hk : k < h) : broadcastIndex [1, 1, h] [0, p, k] = [0, 0, k] := by
  simp [broadcastIndex, keep_index hk]

theorem bI_last {n p k : ℕ} (hp : p < n) : broadcastIndex [1, n, 1] [0, p, k] = [0, p, 0] := by
  simp [broadcastIndex, keep_index hp]

theorem entry_eq_get {t : Tensor ℝ} {s : List ℕ} (hs : t.shape = s) (i : List ℕ) :
    t.entry i = t.get (ravel s i) := by
  rw [Tensor.entry_eq, hs]

/-- `[1, n, d] + [n, d]`: the positional embedding added to every position. -/
theorem bcast_add_three {a b : Tensor ℝ} {n d : ℕ} (ha : a.shape = [1, n, d])
    (han : a.data.size = n * d) (hb : b.shape = [n, d]) (hbn : b.data.size = n * d) :
    ∃ r, broadcastOp BinOp.add.apply a b = some r ∧ r.shape = [1, n, d] ∧
      r.data.size = n * d ∧
      ∀ p < n, ∀ c < d, r.get (p * d + c) = a.get (p * d + c) + b.get (p * d + c) := by
  have hwa : a.wellFormed = true := by rw [wf_iff, ha, han, shapeSize_three]
  have hwb : b.wellFormed = true := by rw [wf_iff, hb, hbn, shapeSize_pair]
  rw [broadcastOp_eq _ hwa hwb (by rw [ha, hb]; exact broadcastShape_three_two n d)]
  refine ⟨_, rfl, rfl, by simp [Tensor.ofFn_data_size, shapeSize], fun p hp c hc => ?_⟩
  have hj : p * d + c < shapeSize [1, n, d] := by rw [shapeSize_three]; exact lt_mul_of_row hp hc
  rw [Tensor.ofFn_get _ _ hj, unravel_one_three hp hc, ha, hb, bI_three_self hp hc,
    bI_three_two hp hc, entry_eq_get ha, entry_eq_get hb, ravel_one_three, ravel_pair]
  rfl

/-- `[1, h] * []`: a vector times a number. -/
theorem bcast_mul_scalar {a b : Tensor ℝ} {h : ℕ} (ha : a.shape = [1, h])
    (han : a.data.size = h)
    (hb : b.shape = []) (hbn : b.data.size = 1) :
    ∃ r, broadcastOp BinOp.mul.apply a b = some r ∧ r.shape = [1, h] ∧ r.data.size = h ∧
      ∀ k < h, r.get k = a.get k * b.get 0 := by
  have hwa : a.wellFormed = true := by rw [wf_iff, ha, han, shapeSize_two]
  have hwb : b.wellFormed = true := by rw [wf_iff, hb, hbn]; rfl
  rw [broadcastOp_eq _ hwa hwb (by rw [ha, hb]; exact broadcastShape_two_scalar h)]
  refine ⟨_, rfl, rfl, by simp [Tensor.ofFn_data_size, shapeSize], fun k hk => ?_⟩
  have hj : k < shapeSize [1, h] := by rw [shapeSize_two]; exact hk
  rw [Tensor.ofFn_get _ _ hj, unravel_one_two hk, ha, hb, bI_two_self hk, bI_scalar,
    entry_eq_get ha, entry_eq_get hb, ravel_one_two]
  rfl

/-- `[1, n, h] * [1, 1, h]`: every position's key times the query. -/
theorem bcast_mul_mid {a b : Tensor ℝ} {n h : ℕ} (ha : a.shape = [1, n, h])
    (han : a.data.size = n * h) (hb : b.shape = [1, 1, h]) (hbn : b.data.size = h) :
    ∃ r, broadcastOp BinOp.mul.apply a b = some r ∧ r.shape = [1, n, h] ∧
      r.data.size = n * h ∧
      ∀ p < n, ∀ k < h, r.get (p * h + k) = a.get (p * h + k) * b.get k := by
  have hwa : a.wellFormed = true := by rw [wf_iff, ha, han, shapeSize_three]
  have hwb : b.wellFormed = true := by rw [wf_iff, hb, hbn, shapeSize_three, Nat.one_mul]
  rw [broadcastOp_eq _ hwa hwb (by rw [ha, hb]; exact broadcastShape_bcast_mid n h)]
  refine ⟨_, rfl, rfl, by simp [Tensor.ofFn_data_size, shapeSize], fun p hp k hk => ?_⟩
  have hj : p * h + k < shapeSize [1, n, h] := by rw [shapeSize_three]; exact lt_mul_of_row hp hk
  rw [Tensor.ofFn_get _ _ hj, unravel_one_three hp hk, ha, hb, bI_three_self hp hk, bI_mid hk,
    entry_eq_get ha, entry_eq_get hb, ravel_one_three, ravel_one_three, Nat.zero_mul,
    Nat.zero_add]
  rfl

/-- `[1, n, 1] * [1, n, h]`: every position's value times its attention weight. -/
theorem bcast_mul_last {a b : Tensor ℝ} {n h : ℕ} (ha : a.shape = [1, n, 1])
    (han : a.data.size = n) (hb : b.shape = [1, n, h]) (hbn : b.data.size = n * h) :
    ∃ r, broadcastOp BinOp.mul.apply a b = some r ∧ r.shape = [1, n, h] ∧
      r.data.size = n * h ∧
      ∀ p < n, ∀ k < h, r.get (p * h + k) = a.get p * b.get (p * h + k) := by
  have hwa : a.wellFormed = true := by rw [wf_iff, ha, han, shapeSize_three, Nat.mul_one]
  have hwb : b.wellFormed = true := by rw [wf_iff, hb, hbn, shapeSize_three]
  rw [broadcastOp_eq _ hwa hwb (by rw [ha, hb]; exact broadcastShape_bcast_last n h)]
  refine ⟨_, rfl, rfl, by simp [Tensor.ofFn_data_size, shapeSize], fun p hp k hk => ?_⟩
  have hj : p * h + k < shapeSize [1, n, h] := by rw [shapeSize_three]; exact lt_mul_of_row hp hk
  rw [Tensor.ofFn_get _ _ hj, unravel_one_three hp hk, ha, hb, bI_last hp, bI_three_self hp hk,
    entry_eq_get ha, entry_eq_get hb, ravel_one_three, ravel_one_three, Nat.mul_one,
    Nat.add_zero]
  rfl

/-- `[1, d] + [1, d]`. -/
theorem bcast_add_two {a b : Tensor ℝ} {d : ℕ} (ha : a.shape = [1, d]) (han : a.data.size = d)
    (hb : b.shape = [1, d]) (hbn : b.data.size = d) :
    ∃ r, broadcastOp BinOp.add.apply a b = some r ∧ r.shape = [1, d] ∧ r.data.size = d ∧
      ∀ c < d, r.get c = a.get c + b.get c := by
  have hwa : a.wellFormed = true := by rw [wf_iff, ha, han, shapeSize_two]
  have hwb : b.wellFormed = true := by rw [wf_iff, hb, hbn, shapeSize_two]
  rw [broadcastOp_eq _ hwa hwb (by rw [ha, hb]; exact broadcastShape_self _)]
  refine ⟨_, rfl, rfl, by simp [Tensor.ofFn_data_size, shapeSize], fun c hc => ?_⟩
  have hj : c < shapeSize [1, d] := by rw [shapeSize_two]; exact hc
  rw [Tensor.ofFn_get _ _ hj, unravel_one_two hc, ha, hb, bI_two_self hc, entry_eq_get ha,
    entry_eq_get hb, ravel_one_two]
  rfl

/-! ## Indexing, new dimensions, sums, softmax -/

/-- `t[:, Q]` of a tensor `[1, n, d]`. -/
theorem index_last {t : Tensor ℝ} {n d Q : ℕ} (ht : t.shape = [1, n, d])
    (htn : t.data.size = n * d)
    (hQ : Q < n) :
    ∃ r, indexOp t [.all, .one Q] = some r ∧ r.shape = [1, d] ∧ r.data.size = d ∧
      ∀ c < d, r.get c = t.get (Q * d + c) := by
  have hw : t.wellFormed = true := by rw [wf_iff, ht, htn, shapeSize_three]
  obtain ⟨r, hr, hrs, hrn, hget⟩ := indexOp_getitem (rest := [d]) ht hw hQ
  have hs : shapeSize [d] = d := by simp [shapeSize]
  refine ⟨r, hr, hrs, by rw [hrn, hs], fun c hc => ?_⟩
  rw [hget c (by rw [hs]; exact hc), hs]

theorem unsqueeze_mid {t : Tensor ℝ} {h : ℕ} (ht : t.shape = [1, h]) :
    unsqueezeOp t 1 = some ⟨[1, 1, h], t.data⟩ := by
  simp [unsqueezeOp, normDim, ht]

theorem unsqueeze_last {t : Tensor ℝ} {n : ℕ} (ht : t.shape = [1, n]) :
    unsqueezeOp t 2 = some ⟨[1, n, 1], t.data⟩ := by
  simp [unsqueezeOp, normDim, ht]

/-- The sum over the last dimension of `[1, n, h]`. -/
theorem sum_last {t : Tensor ℝ} {n h : ℕ} (ht : t.shape = [1, n, h])
    (htn : t.data.size = n * h) :
    ∃ r, sumOp 2 t = some r ∧ r.shape = [1, n] ∧ r.data.size = n ∧
      ∀ p < n, r.get p = ((List.range h).map fun k => t.get (p * h + k)).sum := by
  refine ⟨⟨[1, n], (Array.range (n * 1)).map fun j =>
      ((List.range h).map fun k => t.get ((j / 1 * h + k) * 1 + j % 1)).sum⟩, ?_, rfl,
    by simp, fun p hp => ?_⟩
  · unfold sumOp
    simp [normDim, ht, htn, shapeSize]
  · rw [get_map_range (show p < n * 1 by omega)]
    simp only [Nat.div_one, Nat.mod_one, Nat.mul_one, Nat.add_zero]

/-- The sum over the middle dimension of `[1, n, h]`. -/
theorem sum_mid {t : Tensor ℝ} {n h : ℕ} (ht : t.shape = [1, n, h])
    (htn : t.data.size = n * h) :
    ∃ r, sumOp 1 t = some r ∧ r.shape = [1, h] ∧ r.data.size = h ∧
      ∀ k < h, r.get k = ((List.range n).map fun p => t.get (p * h + k)).sum := by
  refine ⟨⟨[1, h], (Array.range (1 * h)).map fun j =>
      ((List.range n).map fun p => t.get ((j / h * n + p) * h + j % h)).sum⟩, ?_, rfl,
    by simp, fun k hk => ?_⟩
  · unfold sumOp
    simp [normDim, ht, htn, shapeSize, Nat.mul_comm]
  · rw [get_map_range (show k < 1 * h by omega), Nat.div_eq_of_lt hk, Nat.mod_eq_of_lt hk]
    simp only [Nat.zero_mul, Nat.zero_add]

/-- The softmax of `[1, n]` along its positions. -/
theorem softmax_row {t : Tensor ℝ} {n : ℕ} (ht : t.shape = [1, n]) (htn : t.data.size = n) :
    ∃ r, softmaxOp t 1 = some r ∧ r.shape = [1, n] ∧ r.data.size = n ∧
      ∀ p < n, r.get p =
        Real.exp (t.get p) / ((List.range n).map fun k => Real.exp (t.get k)).sum := by
  have hw : t.wellFormed = true := by rw [wf_iff, ht, htn, shapeSize_two]
  have hnd : normDim 1 t.shape.length = some 1 := by rw [ht]; rfl
  unfold softmaxOp
  rw [hnd]
  simp only [hw, ↓reduceIte]
  refine ⟨_, rfl, by simp [ht], by simp [Tensor.ofFn_data_size, ht, shapeSize], fun p hp => ?_⟩
  have hj : p < shapeSize t.shape := by rw [ht, shapeSize_two]; exact hp
  rw [Tensor.ofFn_get _ _ hj]
  simp only [ht, unravel_one_two hp, List.getD_cons_succ, List.getD_cons_zero, List.set_cons_succ,
    List.set_cons_zero]
  rw [entry_eq_get ht, ravel_one_two]
  congr 1
  refine congrArg List.sum (List.map_congr_left fun k _ => ?_)
  rw [entry_eq_get ht, ravel_one_two]
  rfl

end AttnClasses
