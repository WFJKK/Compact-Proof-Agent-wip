import Candidate.Linear

/-!
# (P2) The logits as sums over positions of a single matrix `Mat = U·L·E`:
`logit j = Σ_p Mat[j, x_p]`.
-/

namespace Candidate.Linear

open CompactCheck Protected.N_max4_v64_s0

theorem sum_range_eq (n : Nat) (f : Nat → ℚ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [Finset.sum_eq_multiset_sum, Finset.range_val, Multiset.range, Multiset.map_coe,
    Multiset.sum_coe]

theorem getD_mem (x : List Nat) (p : Nat) (hp : p < x.length) : x.getD p 0 ∈ x := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  exact List.getElem_mem hp

/-- `(L·E)[k, t]`. -/
def LE (E L : Tensor ℚ) (d V : Nat) (k t : Nat) : ℚ :=
  ∑ l ∈ Finset.range d, L.get (k * d + l) * E.get (l * V + t)

/-- `(U·L·E)[j, t]`: the logit `j` contributed by one token `t`. -/
def Mat (E L U : Tensor ℚ) (d V : Nat) (j t : Nat) : ℚ :=
  ∑ k ∈ Finset.range d, U.get (j * d + k) * LE E L d V k t

theorem cnt_eq (P : Nat) (x : Input) (t : Nat) :
    cnt P x t = ∑ p ∈ Finset.range P, if x.getD p 0 = t then (1 : ℚ) else 0 :=
  sum_range_eq _ _

theorem hid1_eq (E : Tensor ℚ) (P V : Nat) (x : Input) (hx : x.length = P)
    (hall : ∀ a ∈ x, a < V) (l : Nat) :
    hid1 E P V x l = ∑ p ∈ Finset.range P, E.get (l * V + x.getD p 0) := by
  unfold hid1
  rw [sum_range_eq]
  simp_rw [cnt_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  have hm : x.getD p 0 ∈ Finset.range V :=
    Finset.mem_range.mpr (hall _ (getD_mem x p (by rw [hx]; exact Finset.mem_range.mp hp)))
  rw [if_pos hm]

theorem hid2_eq (E L : Tensor ℚ) (d P V : Nat) (x : Input) (hx : x.length = P)
    (hall : ∀ a ∈ x, a < V) (k : Nat) :
    hid2 E L d P V x k = ∑ p ∈ Finset.range P, LE E L d V k (x.getD p 0) := by
  unfold hid2
  rw [sum_range_eq]
  rw [Finset.sum_congr rfl (fun l _ => by rw [hid1_eq E P V x hx hall l])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

theorem logit_eq (E L U : Tensor ℚ) (d P V : Nat) (x : Input) (hx : x.length = P)
    (hall : ∀ a ∈ x, a < V) (j : Nat) :
    logit E L U d P V x j = ∑ p ∈ Finset.range P, Mat E L U d V j (x.getD p 0) := by
  unfold logit
  rw [sum_range_eq]
  rw [Finset.sum_congr rfl (fun k _ => by rw [hid2_eq E L d P V x hx hall k])]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  rfl

/-- The margin of label `m` over competitor `j` is a sum over positions of `Mat[m,·] - Mat[j,·]`. -/
theorem margin_eq (E L U : Tensor ℚ) (d P V : Nat) (x : Input) (hx : x.length = P)
    (hall : ∀ a ∈ x, a < V) (m j : Nat) :
    logit E L U d P V x m - logit E L U d P V x j =
      ∑ p ∈ Finset.range P, (Mat E L U d V m (x.getD p 0) - Mat E L U d V j (x.getD p 0)) := by
  rw [logit_eq E L U d P V x hx hall m, logit_eq E L U d P V x hx hall j, Finset.sum_sub_distrib]

end Candidate.Linear
