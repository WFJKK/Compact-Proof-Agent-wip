import Candidate.Tables

/-!
# Facts about the input space and the group index.
-/

namespace Candidate.Tables
open CompactCheck Protected.N_attn_max4_v64_s0

theorem mem_allInputs : ∀ (vs : List Nat) (x : Input), x ∈ allInputs vs →
    x.length = vs.length ∧ List.Forall₂ (· < ·) x vs
  | [], x, h => by
    simp [allInputs] at h
    subst h
    exact ⟨rfl, List.Forall₂.nil⟩
  | v :: vs, x, h => by
    simp only [allInputs, List.mem_flatMap, List.mem_map, List.mem_range] at h
    obtain ⟨t, ht, y, hy, rfl⟩ := h
    obtain ⟨h1, h2⟩ := mem_allInputs vs y hy
    exact ⟨by simp [h1], List.Forall₂.cons ht h2⟩

theorem mem_space {x : Input} (h : x ∈ allInputs [64, 64, 64, 64]) :
    ∃ t0 t1 t2 t3, x = [t0, t1, t2, t3] ∧ t0 < 64 ∧ t1 < 64 ∧ t2 < 64 ∧ t3 < 64 := by
  obtain ⟨_, h2⟩ := mem_allInputs _ x h
  rcases h2 with _ | ⟨h0, _ | ⟨h1, _ | ⟨h2, _ | ⟨h3, _ | _⟩⟩⟩⟩
  exact ⟨_, _, _, _, rfl, h0, h1, h2, h3⟩

theorem space_eq : task.space = [64, 64, 64, 64] := rfl

theorem label_eq (t0 t1 t2 t3 : Nat) : task.label [t0, t1, t2, t3] = max (max (max (max 0 t0) t1) t2) t3 := rfl

/-- The group index, explicitly. -/
theorem gidx_eq (t0 t1 t2 t3 : Nat) :
    gidx [t0, t1, t2, t3] =
      (t3 * 64 + max (max (max (max 0 t0) t1) t2) t3) * 4 +
        (let m := max (max (max (max 0 t0) t1) t2) t3
         if t3 = m then 3 else if t2 = m then 2 else if t1 = m then 1 else 0) := by
  simp only [gidx, List.foldl, List.getD_cons_zero, List.getD_cons_succ]
  rw [show List.range 4 = [0, 1, 2, 3] from rfl]
  simp only [List.foldl, List.getD_cons_zero, List.getD_cons_succ, ite_self]

/-- Decoding the group index. -/
theorem gidx_decode {t3 m istar : Nat} (h3 : t3 < 64) (hm : m < 64) (hi : istar < 4) :
    ((t3 * 64 + m) * 4 + istar) / 256 = t3 ∧ ((t3 * 64 + m) * 4 + istar) / 4 % 64 = m ∧
      ((t3 * 64 + m) * 4 + istar) % 4 = istar := by
  omega

/-- Where the maximum sits: the token at `istar` is the max; later tokens are smaller; all are at most the max. -/
theorem istar_facts (t0 t1 t2 t3 : Nat) :
    let m := max (max (max (max 0 t0) t1) t2) t3
    let istar := if t3 = m then 3 else if t2 = m then 2 else if t1 = m then 1 else 0
    [t0, t1, t2, t3].getD istar 0 = m ∧ (∀ i, istar < i → i < 4 → [t0, t1, t2, t3].getD i 0 < m) ∧
      (∀ i, [t0, t1, t2, t3].getD i 0 ≤ m) ∧ istar < 4 := by
  intro m istar
  have hm0 : t0 ≤ m := by simp [m]
  have hm1 : t1 ≤ m := by simp [m]
  have hm2 : t2 ≤ m := by simp [m]
  have hm3 : t3 ≤ m := by simp [m]
  have hmax : t0 = m ∨ t1 = m ∨ t2 = m ∨ t3 = m := by
    simp only [m]
    omega
  have hget : ∀ i, [t0, t1, t2, t3].getD i 0 ≤ m := by
    intro i
    match i with
    | 0 => exact hm0
    | 1 => exact hm1
    | 2 => exact hm2
    | 3 => exact hm3
    | n + 4 => simp
  refine ⟨?_, ?_, hget, ?_⟩
  · simp only [istar]
    split
    · simpa
    · split
      · simpa
      · split
        · simpa
        · simp only [List.getD_cons_zero]; omega
  · intro i hi hi4
    have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    simp only [istar] at hi
    rcases hcases with rfl | rfl | rfl | rfl <;> simp only [List.getD_cons_succ, List.getD_cons_zero] <;>
      split_ifs at hi <;> omega
  · show (if t3 = m then 3 else if t2 = m then 2 else if t1 = m then 1 else 0) < 4
    split_ifs <;> omega

end Candidate.Tables
