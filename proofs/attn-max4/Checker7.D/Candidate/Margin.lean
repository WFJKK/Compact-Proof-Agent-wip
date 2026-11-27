import Candidate.FormulaCor

/-!
# Lemma D: the logit as `Dm + Σ_k w_k OV`, and the margin as a ratio of shifted exponentials.
-/

namespace Candidate.Formula
open CompactCheck Protected.N_attn_max4_v64_s0 Finset

theorem lsum (f : ℕ → ℝ) (n : ℕ) : ((List.range n).map f).sum = ∑ i ∈ range n, f i := rfl

theorem sum_div' (s : Finset ℕ) (f : ℕ → ℝ) (a : ℝ) : (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by
  simp only [div_eq_mul_inv, sum_mul]

/-- `Σ_d (Σ_d' h d' * W d' d) * u d = Σ_d' h d' * Σ_d W d' d * u d`. -/
theorem swapB (n m : ℕ) (h : ℕ → ℝ) (W : ℕ → ℕ → ℝ) (u : ℕ → ℝ) :
    ∑ d ∈ range n, (∑ d' ∈ range m, h d' * W d' d) * u d =
      ∑ d' ∈ range m, h d' * ∑ d ∈ range n, W d' d * u d := by
  simp only [sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun d' _ => sum_congr rfl fun d _ => by ring

theorem addA (n : ℕ) (a b u : ℕ → ℝ) :
    ∑ d ∈ range n, (a d + b d) * u d = ∑ d ∈ range n, a d * u d + ∑ d ∈ range n, b d * u d := by
  simp only [add_mul, sum_add_distrib]

noncomputable section

/-- The residual of token `t` at position `p`. -/
def resT (E P : Tensor ℝ) (p t d : Nat) : ℝ := E.entry [t, d] + P.entry [p, d]
/-- Direct path: `Dm[t3][j]`. -/
def DmT (E P U : Tensor ℝ) (t3 j : Nat) : ℝ := ∑ d ∈ range 32, resT E P 3 t3 d * U.entry [d, j]
def WOU (WO U : Tensor ℝ) (d' j : Nat) : ℝ := ∑ d ∈ range 32, WO.entry [d', d] * U.entry [d, j]
def WovT (WV WO U : Tensor ℝ) (d j : Nat) : ℝ := ∑ d' ∈ range 32, WV.entry [d, d'] * WOU WO U d' j
/-- Attention path: `OV[p,t][j]`. -/
def OVT (E P WV WO U : Tensor ℝ) (p t j : Nat) : ℝ := ∑ d ∈ range 32, resT E P p t d * WovT WV WO U d j
def qT (E P WQ C : Tensor ℝ) (t3 d' : Nat) : ℝ :=
  (∑ d ∈ range 32, resT E P 3 t3 d * WQ.entry [d, d']) * C.entry []
def keyT (E P WK : Tensor ℝ) (p t d' : Nat) : ℝ := ∑ d ∈ range 32, resT E P p t d * WK.entry [d, d']
/-- The score `S[t3,p,t]`. -/
def ST (E P WQ WK C : Tensor ℝ) (t3 p t : Nat) : ℝ :=
  ∑ d' ∈ range 32, keyT E P WK p t d' * qT E P WQ C t3 d'
/-- The shifted attention weight numerator `exp(S - K)`. -/
def eT (E P WQ WK C : Tensor ℝ) (t3 p t : Nat) (K : ℝ) : ℝ := Real.exp (ST E P WQ WK C t3 p t - K)

end

section
variable {E P WQ WK WV WO U C : Tensor ℝ} {x : Input}

theorem resF_eq' (htok : ∀ p, x.getD p 0 < 64) (p d : Nat) :
    resF x E P p d = resT E P p (x.getD p 0) d := resF_eq (htok p)

theorem keyF_eq (htok : ∀ p, x.getD p 0 < 64) (p d' : Nat) :
    keyF x E P WK p d' = keyT E P WK p (x.getD p 0) d' := by
  unfold keyF keyT
  rw [lsum]
  simp only [resF_eq' htok]

theorem qF_eq (htok : ∀ p, x.getD p 0 < 64) (d' : Nat) :
    qF x E P WQ C d' = qT E P WQ C (x.getD 3 0) d' := by
  unfold qF qT lastF
  rw [lsum]
  simp only [resF_eq' htok]

theorem scoreF_eq (htok : ∀ p, x.getD p 0 < 64) (p : Nat) :
    scoreF x E P WQ WK C p = ST E P WQ WK C (x.getD 3 0) p (x.getD p 0) := by
  unfold scoreF ST
  rw [lsum]
  simp only [keyF_eq htok, qF_eq htok]

/-- The logit as the direct path plus the attention-weighted OV path. -/
theorem logit_decomp (htok : ∀ p, x.getD p 0 < 64) (j : Nat) :
    logitF x E P WQ WK WV WO U C j =
      DmT E P U (x.getD 3 0) j +
        ∑ k ∈ range 4, wF x E P WQ WK C k * OVT E P WV WO U k (x.getD k 0) j := by
  unfold logitF outF headF DmT OVT WovT WOU lastF
  simp only [lsum, resF_eq' htok, keyF_eq htok, keyT]
  rw [addA, swapB, swapB]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  congr 1
  rw [swapB]

theorem wF_shift (htok : ∀ p, x.getD p 0 < 64) (K : ℝ) (k : Nat) :
    wF x E P WQ WK C k =
      eT E P WQ WK C (x.getD 3 0) k (x.getD k 0) K /
        ∑ k' ∈ range 4, eT E P WQ WK C (x.getD 3 0) k' (x.getD k' 0) K := by
  unfold wF eT
  simp only [lsum, scoreF_eq htok, Real.exp_sub, ← sum_div']
  have hK : 0 < Real.exp K := Real.exp_pos K
  rw [div_div_div_cancel_right₀ hK.ne']

theorem Z_pos (t3 : Nat) (tok : Nat → Nat) (K : ℝ) :
    0 < ∑ k ∈ range 4, eT E P WQ WK C t3 k (tok k) K :=
  sum_pos (fun k _ => Real.exp_pos _) (Finset.nonempty_range_iff.mpr (by norm_num))

/-- Lemma D: the margin is a positive multiple of `Σ_k e_k h_kj`. -/
theorem margin (htok : ∀ p, x.getD p 0 < 64) (m j : Nat) (K : ℝ) :
    logitF x E P WQ WK WV WO U C m - logitF x E P WQ WK WV WO U C j =
      (∑ k ∈ range 4, eT E P WQ WK C (x.getD 3 0) k (x.getD k 0) K *
        ((DmT E P U (x.getD 3 0) m + OVT E P WV WO U k (x.getD k 0) m) -
          (DmT E P U (x.getD 3 0) j + OVT E P WV WO U k (x.getD k 0) j))) /
      ∑ k ∈ range 4, eT E P WQ WK C (x.getD 3 0) k (x.getD k 0) K := by
  rw [logit_decomp htok, logit_decomp htok]
  simp only [wF_shift htok K]
  have hZ := Z_pos (E := E) (P := P) (WQ := WQ) (WK := WK) (C := C) (x.getD 3 0) (fun k => x.getD k 0) K
  rw [eq_div_iff hZ.ne']
  simp only [div_mul_eq_mul_div, ← sum_div', mul_sub, mul_add, sum_add_distrib, sum_sub_distrib, ← sum_mul]
  field_simp

end

end Candidate.Formula
