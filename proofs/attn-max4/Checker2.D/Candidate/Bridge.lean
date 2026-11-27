import Candidate.Margin

/-!
# Bridge: `Correct` from positive shifted sums; rational tables (linear indices, as a checker reads
weights) cast to the real table quantities.
-/

namespace Candidate.Formula
open CompactCheck Protected.N_attn_max4_v64_s0 Finset

theorem tokens_lt {x : Input} (hall : x.all (· < 64) = true) : ∀ p, x.getD p 0 < 64 := by
  intro p
  rw [List.getD_eq_getElem?_getD]
  cases hp : x[p]? with
  | none => simp
  | some t =>
    simp only [Option.getD_some]
    have hmem : t ∈ x := List.mem_of_getElem? hp
    have := List.all_eq_true.mp hall t hmem
    simpa using this

/-- `Correct` from positivity of `Σ_k e_k h_kj` for every `j ≠ label`, for rational weights. -/
theorem correct_of_delta {w : Weights ℚ} {E P WQ WK WV WO U C : Tensor ℚ} {x : Input}
    (hE : List.lookup "E" w = some E) (hEs : E.shape = [64, 32]) (hEn : E.data.size = 2048)
    (hP : List.lookup "P" w = some P) (hPs : P.shape = [4, 32]) (hPn : P.data.size = 128)
    (hWQ : List.lookup "WQ" w = some WQ) (hWQs : WQ.shape = [32, 32]) (hWQn : WQ.data.size = 1024)
    (hC : List.lookup "#const0" w = some C) (hCs : C.shape = []) (hCn : C.data.size = 1)
    (hWK : List.lookup "WK" w = some WK) (hWKs : WK.shape = [32, 32]) (hWKn : WK.data.size = 1024)
    (hWV : List.lookup "WV" w = some WV) (hWVs : WV.shape = [32, 32]) (hWVn : WV.data.size = 1024)
    (hWO : List.lookup "WO" w = some WO) (hWOs : WO.shape = [32, 32]) (hWOn : WO.data.size = 1024)
    (hU : List.lookup "U" w = some U) (hUs : U.shape = [32, 64]) (hUn : U.data.size = 2048)
    (hx : x.length = 4) (hall : x.all (· < 64) = true) (hlab : task.label x < 64) (K : ℝ)
    (h : ∀ j < 64, j ≠ task.label x →
      0 < ∑ k ∈ range 4, eT (rc E) (rc P) (rc WQ) (rc WK) (rc C) (x.getD 3 0) k (x.getD k 0) K *
        ((DmT (rc E) (rc P) (rc U) (x.getD 3 0) (task.label x) +
            OVT (rc E) (rc P) (rc WV) (rc WO) (rc U) k (x.getD k 0) (task.label x)) -
          (DmT (rc E) (rc P) (rc U) (x.getD 3 0) j +
            OVT (rc E) (rc P) (rc WV) (rc WO) (rc U) k (x.getD k 0) j))) :
    Correct graph w task x := by
  have htok := tokens_lt hall
  apply correct_of_logit hE hEs hEn hP hPs hPn hWQ hWQs hWQn hC hCs hCn hWK hWKs hWKn hWV hWVs hWVn
    hWO hWOs hWOn hU hUs hUn hx hall hlab
  intro j hj hne
  have hm := margin (E := rc E) (P := rc P) (WQ := rc WQ) (WK := rc WK) (WV := rc WV) (WO := rc WO)
    (U := rc U) (C := rc C) htok (task.label x) j K
  rw [← sub_pos, hm]
  exact div_pos (h j hj hne) (Z_pos _ _ _)

/-! ## Rational tables at linear indices -/

def resQ (E P : Tensor ℚ) (p t d : Nat) : ℚ := E.get (t * 32 + d) + P.get (p * 32 + d)
def DmQ (E P U : Tensor ℚ) (t3 j : Nat) : ℚ := ∑ d ∈ range 32, resQ E P 3 t3 d * U.get (d * 64 + j)
def WOUQ (WO U : Tensor ℚ) (d' j : Nat) : ℚ := ∑ d ∈ range 32, WO.get (d' * 32 + d) * U.get (d * 64 + j)
def WovQ (WV WO U : Tensor ℚ) (d j : Nat) : ℚ := ∑ d' ∈ range 32, WV.get (d * 32 + d') * WOUQ WO U d' j
def OVQ (E P WV WO U : Tensor ℚ) (p t j : Nat) : ℚ := ∑ d ∈ range 32, resQ E P p t d * WovQ WV WO U d j
def qQ (E P WQ C : Tensor ℚ) (t3 d' : Nat) : ℚ :=
  (∑ d ∈ range 32, resQ E P 3 t3 d * WQ.get (d * 32 + d')) * C.get 0
def keyQ (E P WK : Tensor ℚ) (p t d' : Nat) : ℚ := ∑ d ∈ range 32, resQ E P p t d * WK.get (d * 32 + d')
def SQ (E P WQ WK C : Tensor ℚ) (t3 p t : Nat) : ℚ := ∑ d' ∈ range 32, keyQ E P WK p t d' * qQ E P WQ C t3 d'

section
variable {E P WQ WK WV WO U C : Tensor ℚ}

theorem rc_entry2 {t : Tensor ℚ} {d0 d1 : Nat} (hs : t.shape = [d0, d1]) (a b : Nat) :
    (rc t).entry [a, b] = ((t.get (a * d1 + b) : ℚ) : ℝ) := by
  rw [rc_entry, Tensor.entry, hs, ravel2]

theorem rc_entry0 {t : Tensor ℚ} (hs : t.shape = []) : (rc t).entry [] = ((t.get 0 : ℚ) : ℝ) := by
  rw [rc_entry, Tensor.entry, hs]
  rfl

theorem cast_sum' (s : Finset ℕ) (f : ℕ → ℚ) : ((∑ i ∈ s, f i : ℚ) : ℝ) = ∑ i ∈ s, (f i : ℝ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Rat.cast_add, ih]

theorem cast_resQ (hEs : E.shape = [64, 32]) (hPs : P.shape = [4, 32]) (p t d : Nat) :
    ((resQ E P p t d : ℚ) : ℝ) = resT (rc E) (rc P) p t d := by
  simp only [resQ, resT, rc_entry2 hEs, rc_entry2 hPs, Rat.cast_add]

theorem cast_DmQ (hEs : E.shape = [64, 32]) (hPs : P.shape = [4, 32]) (hUs : U.shape = [32, 64]) (t3 j : Nat) :
    ((DmQ E P U t3 j : ℚ) : ℝ) = DmT (rc E) (rc P) (rc U) t3 j := by
  simp only [DmQ, DmT, cast_sum', Rat.cast_mul, cast_resQ hEs hPs, rc_entry2 hUs]

theorem cast_OVQ (hEs : E.shape = [64, 32]) (hPs : P.shape = [4, 32]) (hWVs : WV.shape = [32, 32])
    (hWOs : WO.shape = [32, 32]) (hUs : U.shape = [32, 64]) (p t j : Nat) :
    ((OVQ E P WV WO U p t j : ℚ) : ℝ) = OVT (rc E) (rc P) (rc WV) (rc WO) (rc U) p t j := by
  simp only [OVQ, OVT, WovQ, WovT, WOUQ, WOU, cast_sum', Rat.cast_mul, cast_resQ hEs hPs, rc_entry2 hWVs,
    rc_entry2 hWOs, rc_entry2 hUs]

theorem cast_SQ (hEs : E.shape = [64, 32]) (hPs : P.shape = [4, 32]) (hWQs : WQ.shape = [32, 32])
    (hWKs : WK.shape = [32, 32]) (hCs : C.shape = []) (t3 p t : Nat) :
    ((SQ E P WQ WK C t3 p t : ℚ) : ℝ) = ST (rc E) (rc P) (rc WQ) (rc WK) (rc C) t3 p t := by
  simp only [SQ, ST, keyQ, keyT, qQ, qT, cast_sum', Rat.cast_mul, cast_resQ hEs hPs, rc_entry2 hWQs,
    rc_entry2 hWKs, rc_entry0 hCs]

/-- The shifted exponential of a rational score with a rational shift. -/
theorem eT_cast (hEs : E.shape = [64, 32]) (hPs : P.shape = [4, 32]) (hWQs : WQ.shape = [32, 32])
    (hWKs : WK.shape = [32, 32]) (hCs : C.shape = []) (t3 p t : Nat) (K : ℚ) :
    eT (rc E) (rc P) (rc WQ) (rc WK) (rc C) t3 p t (K : ℝ) = Real.exp ((SQ E P WQ WK C t3 p t - K : ℚ) : ℝ) := by
  rw [eT, Rat.cast_sub, cast_SQ hEs hPs hWQs hWKs hCs]

end

end Candidate.Formula
