import Candidate.Formula

/-!
# Corollaries of the formula lemma: `Correct` from the logit formula, one-hot collapse, real weights.
-/

namespace Candidate.Formula
open CompactCheck Protected.N_attn_max4_v64_s0

/-- The real cast of a rational tensor, as the spec reads the weights. -/
noncomputable def rc (t : Tensor ℚ) : Tensor ℝ := t.map fun q : ℚ => (q : ℝ)

theorem lookup_realWeights (n : String) : ∀ (w : Weights ℚ),
    List.lookup n (realWeights w) = (List.lookup n w).map rc
  | [] => rfl
  | (k, t) :: rest => by
    have ih := lookup_realWeights n rest
    show List.lookup n ((k, rc t) :: realWeights rest) = _
    simp only [List.lookup]
    rcases hnk : (n == k) with _ | _
    · exact ih
    · rfl

theorem rc_shape (t : Tensor ℚ) : (rc t).shape = t.shape := rfl

theorem rc_size (t : Tensor ℚ) : (rc t).data.size = t.data.size := by
  simp [rc, Tensor.map]

theorem rc_get (t : Tensor ℚ) (k : Nat) : (rc t).get k = ((t.get k : ℚ) : ℝ) := by
  simp only [rc, Tensor.map, Tensor.get, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases t.data[k]? <;> simp

theorem rc_entry (t : Tensor ℚ) (i : List Nat) : (rc t).entry i = ((t.entry i : ℚ) : ℝ) := by
  simp only [Tensor.entry, rc_shape]
  exact rc_get t _

theorem onehot_sum' (f : Nat → ℝ) (t : Nat) : ∀ n, t < n →
    ((List.range n).map fun v => (if t = v then (1 : ℝ) else 0) * f v).sum = f t
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.sum_append]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    by_cases ht : t = n
    · subst ht
      rw [if_pos rfl, one_mul]
      have hz : ((List.range t).map fun v => (if t = v then (1 : ℝ) else 0) * f v).sum = 0 := by
        apply List.sum_eq_zero
        intro y hy
        rw [List.mem_map] at hy
        obtain ⟨v, hv, rfl⟩ := hy
        rw [List.mem_range] at hv
        rw [if_neg (by omega), zero_mul]
      rw [hz, zero_add]
    · rw [if_neg ht, zero_mul, add_zero]
      exact onehot_sum' f t n (by omega)

/-- The one-hot matmul collapses: the residual is the token's embedding plus the position's. -/
theorem resF_eq {x : Input} {E P : Tensor ℝ} {p d : Nat} (h : x.getD p 0 < 64) :
    resF x E P p d = E.entry [x.getD p 0, d] + P.entry [p, d] := by
  unfold resF
  exact congrArg (· + P.entry [p, d]) (onehot_sum' (fun v => E.entry [v, d]) (x.getD p 0) 64 h)

/-- `Correct` follows from strict logit comparisons in the closed form, for rational weights of the
    checked shapes. -/
theorem correct_of_logit {w : Weights ℚ} {E P WQ WK WV WO U C : Tensor ℚ} {x : Input}
    (hE : List.lookup "E" w = some E) (hEs : E.shape = [64, 32]) (hEn : E.data.size = 2048)
    (hP : List.lookup "P" w = some P) (hPs : P.shape = [4, 32]) (hPn : P.data.size = 128)
    (hWQ : List.lookup "WQ" w = some WQ) (hWQs : WQ.shape = [32, 32]) (hWQn : WQ.data.size = 1024)
    (hC : List.lookup "#const0" w = some C) (hCs : C.shape = []) (hCn : C.data.size = 1)
    (hWK : List.lookup "WK" w = some WK) (hWKs : WK.shape = [32, 32]) (hWKn : WK.data.size = 1024)
    (hWV : List.lookup "WV" w = some WV) (hWVs : WV.shape = [32, 32]) (hWVn : WV.data.size = 1024)
    (hWO : List.lookup "WO" w = some WO) (hWOs : WO.shape = [32, 32]) (hWOn : WO.data.size = 1024)
    (hU : List.lookup "U" w = some U) (hUs : U.shape = [32, 64]) (hUn : U.data.size = 2048)
    (hx : x.length = 4) (hall : x.all (· < 64) = true) (hlab : task.label x < 64)
    (h : ∀ j < 64, j ≠ task.label x →
      logitF x (rc E) (rc P) (rc WQ) (rc WK) (rc WV) (rc WO) (rc U) (rc C) j <
      logitF x (rc E) (rc P) (rc WQ) (rc WK) (rc WV) (rc WO) (rc U) (rc C) (task.label x)) :
    Correct graph w task x := by
  obtain ⟨out, hout, r⟩ := formula (w := realWeights w)
    (by rw [lookup_realWeights, hE]; rfl) hEs (by rw [rc_size, hEn])
    (by rw [lookup_realWeights, hP]; rfl) hPs (by rw [rc_size, hPn])
    (by rw [lookup_realWeights, hWQ]; rfl) hWQs (by rw [rc_size, hWQn])
    (by rw [lookup_realWeights, hC]; rfl) hCs (by rw [rc_size, hCn])
    (by rw [lookup_realWeights, hWK]; rfl) hWKs (by rw [rc_size, hWKn])
    (by rw [lookup_realWeights, hWV]; rfl) hWVs (by rw [rc_size, hWVn])
    (by rw [lookup_realWeights, hWO]; rfl) hWOs (by rw [rc_size, hWOn])
    (by rw [lookup_realWeights, hU]; rfl) hUs (by rw [rc_size, hUn])
    hx hall
  have hget : ∀ j, j < 64 → out.get j =
      logitF x (rc E) (rc P) (rc WQ) (rc WK) (rc WV) (rc WO) (rc U) (rc C) j := by
    intro j hj
    have := r.entry [0, j] (valid2_of (by omega) hj)
    rw [Tensor.entry, r.shape, ravel2] at this
    simpa using this
  refine ⟨out, hout, ?_, ?_, ?_⟩
  · rw [r.shape, r.size]; rfl
  · rw [r.size]; exact hlab
  · intro j hj hne
    rw [r.size] at hj
    rw [hget j hj, hget _ hlab]
    exact h j hj hne

end Candidate.Formula
