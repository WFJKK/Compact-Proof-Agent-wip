import Candidate.Boxes

/-!
# A certified product box: every input in it is answered correctly.
-/

namespace Candidate.Boxes

open CompactCheck Protected.N_max4_v64_s0 Candidate.Linear

open Classical in
theorem numCorrect_ge_countP (w : Weights ℚ) (S : Input → Bool)
    (hS : ∀ x ∈ allInputs task.space, S x = true → Correct graph w task x) :
    (allInputs task.space).countP S ≤ numCorrect graph w task := by
  unfold numCorrect
  apply List.countP_mono_left
  intro x hx h
  exact decide_eq_true (hS x hx h)

theorem inBox_length : ∀ (bs : List (Nat × Nat)) (x : Input), inBox bs x = true → x.length = bs.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [inBox] at h
  | _ :: _, [], h => by simp [inBox] at h
  | (lo, hi) :: bs, t :: x, h => by
    simp only [inBox, Bool.and_eq_true] at h
    simp [inBox_length bs x h.2]

theorem inBox_getD : ∀ (bs : List (Nat × Nat)) (x : Input), inBox bs x = true →
    ∀ p, (h : p < bs.length) → bs[p].1 ≤ x.getD p 0 ∧ x.getD p 0 < bs[p].2
  | [], [], _, p, h => by simp at h
  | [], _ :: _, h, _, _ => by simp [inBox] at h
  | _ :: _, [], h, _, _ => by simp [inBox] at h
  | (lo, hi) :: bs, t :: x, h, p, hp => by
    simp only [inBox, Bool.and_eq_true, decide_eq_true_eq] at h
    cases p with
    | zero => simpa using h.1
    | succ p =>
      simp only [List.getElem_cons_succ, List.getD_cons_succ]
      exact inBox_getD bs x h.2 p (by simpa using hp)

theorem inBox_mem : ∀ (bs : List (Nat × Nat)) (x : Input), inBox bs x = true →
    ∀ t ∈ x, ∃ b ∈ bs, b.1 ≤ t ∧ t < b.2
  | [], [], _, t, ht => by simp at ht
  | [], _ :: _, h, _, _ => by simp [inBox] at h
  | _ :: _, [], h, _, _ => by simp [inBox] at h
  | (lo, hi) :: bs, a :: x, h, t, ht => by
    simp only [inBox, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨(lo, hi), List.mem_cons_self, h.1⟩
    · obtain ⟨b, hb, hbt⟩ := inBox_mem bs x h.2 t ht
      exact ⟨b, List.mem_cons_of_mem _ hb, hbt⟩

theorem foldl_max_le (x : List Nat) (m : Nat) (hle : ∀ t ∈ x, t ≤ m) :
    ∀ a, a ≤ m → x.foldl max a ≤ m := by
  induction x with
  | nil => intro a ha; simpa using ha
  | cons t x ih =>
    intro a ha
    simp only [List.foldl_cons]
    apply ih (fun u hu => hle u (List.mem_cons_of_mem _ hu))
    exact max_le ha (hle t List.mem_cons_self)

theorem le_foldl_max (x : List Nat) (t : Nat) (ht : t ∈ x) : ∀ a, t ≤ x.foldl max a := by
  induction x with
  | nil => simp at ht
  | cons u x ih =>
    intro a
    simp only [List.foldl_cons]
    rw [List.mem_cons] at ht
    rcases ht with rfl | ht
    · have : ∀ b, b ≤ x.foldl max b := by
        intro b
        clear ih
        induction x generalizing b with
        | nil => simp
        | cons v x ih2 =>
          simp only [List.foldl_cons]
          exact le_trans (le_max_left b v) (ih2 _)
      exact le_trans (le_max_right a t) (this _)
    · exact ih ht _

theorem foldl_max_eq (x : List Nat) (m : Nat) (hle : ∀ t ∈ x, t ≤ m) (hmem : m ∈ x) :
    x.foldl max 0 = m :=
  le_antisymm (foldl_max_le x m hle 0 (Nat.zero_le m)) (le_foldl_max x m hmem 0)

/-- The label of an input of a box whose intervals all lie in `[0, m]` and one of which is
    `[m, m+1)`. -/
theorem label_of_box (bs : List (Nat × Nat)) (m : Nat) (hfit : ∀ b ∈ bs, b.2 ≤ m + 1)
    (hS : ∃ b ∈ bs, b.1 = m) (x : Input) (hx : inBox bs x = true) : task.label x = m := by
  rw [task_label]
  apply foldl_max_eq
  · intro t ht
    obtain ⟨b, hb, _, h2⟩ := inBox_mem bs x hx t ht
    have := hfit b hb
    omega
  · obtain ⟨b, hb, hb1⟩ := hS
    obtain ⟨p, hp, rfl⟩ := List.mem_iff_getElem.mp hb
    have h := inBox_getD bs x hx p hp
    have hf := hfit _ hb
    have hlen := inBox_length bs x hx
    have : x.getD p 0 = m := by omega
    rw [← this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _

/-- The main box theorem: a box with a known label `m`, fitting the vocabulary, each of whose
    competitors `j` has a per-position lower bound summing to a positive margin, holds only
    correctly answered inputs. -/
theorem correct_of_box (w : Weights ℚ) (E L U : Tensor ℚ) (d P V : Nat)
    (hgP : graph.positions = P) (hgV : graph.values = V)
    (hE : List.lookup "embedding.weight" w = some E) (hEs : E.shape = [d, V])
    (hEsz : E.data.size = d * V)
    (hL : List.lookup "linear.weight" w = some L) (hLs : L.shape = [d, d])
    (hLsz : L.data.size = d * d)
    (hU : List.lookup "unembedding.weight" w = some U) (hUs : U.shape = [V, d])
    (hUsz : U.data.size = V * d)
    (bs : List (Nat × Nat)) (hbs : bs.length = P) (m : Nat) (hm : m < V)
    (hfit : ∀ b ∈ bs, b.2 ≤ m + 1) (hS : ∃ b ∈ bs, b.1 = m)
    (hcomp : ∀ j < V, j ≠ m → ∃ lo : Nat → ℚ,
      (∀ p, (hp : p < bs.length) → ∀ t, bs[p].1 ≤ t → t < bs[p].2 →
        lo p ≤ Mat E L U d V m t - Mat E L U d V j t) ∧
      0 < ∑ p ∈ Finset.range P, lo p)
    (x : Input) (hx : inBox bs x = true) : Correct graph w task x := by
  have hlab := label_of_box bs m hfit hS x hx
  have hxl : x.length = P := by rw [inBox_length bs x hx, hbs]
  have hall : ∀ a ∈ x, a < V := by
    intro a ha
    obtain ⟨b, hb, _, h2⟩ := inBox_mem bs x hx a ha
    have := hfit b hb
    omega
  apply correct_of_logits w E L U d P V hgP hgV hE hEs hEsz hL hLs hLsz hU hUs hUsz x hxl hall
  · rw [hlab]; exact hm
  · intro j hj hne
    rw [hlab] at hne ⊢
    obtain ⟨lo, hlo, hsum⟩ := hcomp j hj hne
    apply logit_lt_of_lower E L U d P V x hxl hall m j lo _ hsum
    intro p hp
    have hp' : p < bs.length := by rw [hbs]; exact Finset.mem_range.mp hp
    obtain ⟨h1, h2⟩ := inBox_getD bs x hx p hp'
    exact hlo p hp' _ h1 h2

end Candidate.Boxes
