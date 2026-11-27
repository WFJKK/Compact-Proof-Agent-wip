import Candidate.CvxD
import Candidate.BoxCorrect

/-!
# Boxes with set-valued sides: membership, size, splits, and the box theorem
-/

namespace Candidate.Ref

open CompactCheck Protected.N_max4_v64_s0 Candidate.Linear Candidate.Boxes

/-- Membership in a box with set-valued sides. -/
def inS : Box → Input → Bool
  | [], [] => true
  | s :: c, t :: x => s.contains t && inS c x
  | _, _ => false

/-- A well-formed box: four sets without repetitions, of tokens below 64. -/
def WF (c : Box) : Prop := c.length = 4 ∧ ∀ s ∈ c, s.Nodup ∧ ∀ t ∈ s, t < 64

theorem countP_range_contains (v : Nat) (s : List Nat) (hs : s.Nodup) (hv : ∀ t ∈ s, t < v) :
    (List.range v).countP (fun t => s.contains t) = s.length := by
  rw [List.countP_eq_length_filter]
  apply List.Perm.length_eq
  rw [List.perm_ext_iff_of_nodup ((List.nodup_range).filter _) hs]
  intro a
  simp only [List.mem_filter, List.mem_range, List.contains_iff_mem]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨hv a h, h⟩

theorem countP_inS : ∀ (c : Box) (space : List Nat),
    List.Forall₂ (fun (s : List Nat) v => s.Nodup ∧ ∀ t ∈ s, t < v) c space →
    (allInputs space).countP (inS c) = bsz c
  | [], [], _ => by simp [allInputs, inS, bsz]
  | s :: c, v :: vs, h => by
    cases h with
    | cons hb hrest =>
      have ih := countP_inS c vs hrest
      simp only [allInputs]
      rw [countP_flatMap']
      simp only [List.countP_map]
      have : (fun t => (allInputs vs).countP (inS (s :: c) ∘ (t :: ·))) =
          fun t => (allInputs vs).countP (fun x => s.contains t && inS c x) := by
        funext t
        rfl
      rw [this, sum_map_countP, countP_range_contains v s hb.1 hb.2, ih]
      simp [bsz]

theorem inS_length : ∀ (c : Box) (x : Input), inS c x = true → x.length = c.length
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [inS] at h
  | _ :: _, [], h => by simp [inS] at h
  | s :: c, t :: x, h => by
    simp only [inS, Bool.and_eq_true] at h
    simp [inS_length c x h.2]

theorem inS_getD : ∀ (c : Box) (x : Input), inS c x = true →
    ∀ p, p < c.length → x.getD p 0 ∈ c.getD p []
  | [], [], _, p, h => by simp at h
  | [], _ :: _, h, _, _ => by simp [inS] at h
  | _ :: _, [], h, _, _ => by simp [inS] at h
  | s :: c, t :: x, h, p, hp => by
    simp only [inS, Bool.and_eq_true, List.contains_iff_mem] at h
    cases p with
    | zero => simpa using h.1
    | succ p =>
      simp only [List.getD_cons_succ]
      exact inS_getD c x h.2 p (by simpa using hp)

theorem inS_mem : ∀ (c : Box) (x : Input), inS c x = true → ∀ t ∈ x, ∃ s ∈ c, t ∈ s
  | [], [], _, t, ht => by simp at ht
  | [], _ :: _, h, _, _ => by simp [inS] at h
  | _ :: _, [], h, _, _ => by simp [inS] at h
  | s :: c, a :: x, h, t, ht => by
    simp only [inS, Bool.and_eq_true, List.contains_iff_mem] at h
    rw [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨s, List.mem_cons_self, h.1⟩
    · obtain ⟨s', hs', ht'⟩ := inS_mem c x h.2 t ht
      exact ⟨s', List.mem_cons_of_mem _ hs', ht'⟩

/-- A binary split of one side by a predicate: the two halves partition the box. -/
theorem inS_split : ∀ (c : Box) (p : Nat) (q : Nat → Bool) (x : Input), p < c.length →
    (inS c x = (inS (c.set p ((c.getD p []).filter q)) x || inS (c.set p ((c.getD p []).filter fun t => !q t)) x)) ∧
    ¬ (inS (c.set p ((c.getD p []).filter q)) x = true ∧
      inS (c.set p ((c.getD p []).filter fun t => !q t)) x = true)
  | [], p, q, x, hp => by simp at hp
  | s :: c, 0, q, x, _ => by
    cases x with
    | nil => simp [inS]
    | cons t x =>
      simp only [List.set_cons_zero, List.getD_cons_zero, inS]
      cases inS c x
      · simp
      · simp only [Bool.and_true, List.contains_iff_mem, List.mem_filter]
        cases hq : q t <;> simp [hq]
  | s :: c, p + 1, q, x, hp => by
    simp only [List.set_cons_succ, List.getD_cons_succ]
    cases x with
    | nil => simp [inS]
    | cons t x =>
      obtain ⟨ih1, ih2⟩ := inS_split c p q x (by simpa using hp)
      simp only [inS]
      cases s.contains t
      · simp
      · simp only [Bool.true_and]
        exact ⟨ih1, ih2⟩

theorem countP_split_or' {α : Type} (A A1 A2 C : α → Bool)
    (hA : ∀ x, A x = (A1 x || A2 x)) (hd : ∀ x, ¬ (A1 x = true ∧ A2 x = true)) :
    ∀ (l : List α), l.countP (fun x => A x && C x) =
      l.countP (fun x => A1 x && C x) + l.countP (fun x => A2 x && C x)
  | [] => by simp
  | x :: l => by
    simp only [List.countP_cons, countP_split_or' A A1 A2 C hA hd l, hA x]
    have := hd x
    cases h1 : A1 x <;> cases h2 : A2 x <;> cases hc : C x <;> simp_all <;> omega

/-- The count of a box, as a function of the box. -/
def cP (C : Input → Bool) (l : List Input) (c : Box) : Nat := l.countP fun x => inS c x && C x

theorem cP_split (C : Input → Bool) (l : List Input) (c : Box) (p : Nat) (q : Nat → Bool) (hp : p < c.length) :
    cP C l c = cP C l (c.set p ((c.getD p []).filter q)) + cP C l (c.set p ((c.getD p []).filter fun t => !q t)) :=
  countP_split_or' _ _ _ C (fun x => (inS_split c p q x hp).1) (fun x => (inS_split c p q x hp).2) l

theorem getD_set_self (c : Box) (p : Nat) (s : List Nat) (hp : p < c.length) : (c.set p s).getD p [] = s := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, hp]

theorem set_getD_self (c : Box) (p : Nat) : c.set p (c.getD p []) = c := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_set]
    split
    · subst_vars
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]
    · rfl

/-- The sum over the pieces of `splitAt` is the count of the box. -/
theorem splitAt_sum (C : Input → Bool) (l : List Input) (p : Nat) (c : Box) (hp : p < c.length) (B : List Nat) :
    ((splitAt p c B).map (cP C l)).sum = cP C l c := by
  have key : ∀ (B : List Nat) (s : List Nat) (acc : List Box),
      let r := B.foldl (fun st b => (st.1.filter (· != b), st.2 ++ [c.set p (st.1.filter (· == b))])) (s, acc)
      (r.2.map (cP C l)).sum + cP C l (c.set p r.1) = (acc.map (cP C l)).sum + cP C l (c.set p s) := by
    intro B
    induction B with
    | nil => intro s acc; rfl
    | cons b B ih =>
      intro s acc
      simp only [List.foldl_cons]
      rw [ih]
      have hp' : p < (c.set p s).length := by simpa using hp
      have h := cP_split C l (c.set p s) p (· == b) hp'
      rw [getD_set_self c p s hp, List.set_set, List.set_set] at h
      have hb : (fun t => !(t == b)) = (fun t => t != b) := rfl
      rw [hb] at h
      rw [List.map_append, List.sum_append, h]
      simp
      omega
  have := key B (c.getD p []) []
  simp only at this
  unfold splitAt
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Nat.add_zero]
  rw [this, set_getD_self]
  simp

/-- Every piece of `splitAt` is the box with side `p` replaced by a sublist of it. -/
theorem splitAt_shape (p : Nat) (c : Box) (B : List Nat) :
    ∀ d ∈ splitAt p c B, ∃ X : List Nat, X.Sublist (c.getD p []) ∧ d = c.set p X := by
  have key : ∀ (B : List Nat) (s : List Nat) (acc : List Box), s.Sublist (c.getD p []) →
      (∀ d ∈ acc, ∃ X : List Nat, X.Sublist (c.getD p []) ∧ d = c.set p X) →
      let r := B.foldl (fun st b => (st.1.filter (· != b), st.2 ++ [c.set p (st.1.filter (· == b))])) (s, acc)
      r.1.Sublist (c.getD p []) ∧ ∀ d ∈ r.2, ∃ X : List Nat, X.Sublist (c.getD p []) ∧ d = c.set p X := by
    intro B
    induction B with
    | nil => intro s acc hs hacc; exact ⟨hs, hacc⟩
    | cons b B ih =>
      intro s acc hs hacc
      simp only [List.foldl_cons]
      apply ih
      · exact (List.filter_sublist).trans hs
      · intro d hd
        rw [List.mem_append, List.mem_singleton] at hd
        rcases hd with hd | rfl
        · exact hacc d hd
        · exact ⟨_, (List.filter_sublist).trans hs, rfl⟩
  intro d hd
  unfold splitAt at hd
  have h := key B (c.getD p []) [] (List.Sublist.refl _) (by simp)
  simp only at h
  rw [List.mem_append, List.mem_singleton] at hd
  rcases hd with hd | rfl
  · exact h.2 d hd
  · exact ⟨_, h.1, rfl⟩

theorem WF_set (c : Box) (p : Nat) (X : List Nat) (hc : WF c) (hX : X.Sublist (c.getD p [])) : WF (c.set p X) := by
  refine ⟨by rw [List.length_set]; exact hc.1, fun s hs => ?_⟩
  rcases List.mem_or_eq_of_mem_set hs with hs | rfl
  · exact hc.2 s hs
  · by_cases hp : p < c.length
    · have hm : c.getD p [] ∈ c := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
        exact List.getElem_mem hp
      obtain ⟨h1, h2⟩ := hc.2 _ hm
      exact ⟨h1.sublist hX, fun t ht => h2 t (hX.subset ht)⟩
    · have : c.getD p [] = [] := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
        rfl
      rw [this] at hX
      rw [List.sublist_nil.mp hX]
      simp

theorem WF_splitAt (p : Nat) (c : Box) (B : List Nat) (hc : WF c) : ∀ d ∈ splitAt p c B, WF d := by
  intro d hd
  obtain ⟨X, hX, rfl⟩ := splitAt_shape p c B d hd
  exact WF_set c p X hc hX

theorem sum_flatMap {α : Type} (f : α → List α) (g : α → Nat) :
    ∀ (bs : List α), ((bs.flatMap f).map g).sum = (bs.map fun d => ((f d).map g).sum).sum
  | [] => by simp
  | d :: bs => by
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons]
    rw [sum_flatMap f g bs]

theorem refine_gen (C : Input → Bool) (l : List Input) (S B : List Nat) :
    ∀ (ps : List Nat) (bs : List Box), (∀ p ∈ ps, p < 4) → (∀ d ∈ bs, WF d) →
    let r := ps.foldl (fun bs p => bs.flatMap fun d => cond (d.getD p [] == S) (splitAt p d B) [d]) bs
    (∀ d ∈ r, WF d) ∧ (r.map (cP C l)).sum = (bs.map (cP C l)).sum := by
  intro ps
  induction ps with
  | nil => intro bs _ hbs; exact ⟨hbs, rfl⟩
  | cons p ps ih =>
    intro bs hps hbs
    simp only [List.foldl_cons]
    have h := ih (bs.flatMap fun d => cond (d.getD p [] == S) (splitAt p d B) [d])
      (fun q hq => hps q (List.mem_cons_of_mem _ hq)) ?_
    · refine ⟨h.1, ?_⟩
      rw [h.2, sum_flatMap]
      congr 1
      apply List.map_congr_left
      intro d hd
      have hp : p < d.length := by rw [(hbs d hd).1]; exact hps p List.mem_cons_self
      cases (d.getD p [] == S)
      · simp
      · exact splitAt_sum C l p d hp B
    · intro e he
      rw [List.mem_flatMap] at he
      obtain ⟨d, hd, he⟩ := he
      cases hq : (d.getD p [] == S)
      · rw [hq] at he
        simp only [Bool.cond_false, List.mem_singleton] at he
        rw [he]
        exact hbs d hd
      · rw [hq] at he
        exact WF_splitAt p d B (hbs d hd) e he

theorem refine_spec (C : Input → Bool) (l : List Input) (c : Box) (S B : List Nat) (hc : WF c) :
    (∀ d ∈ refine c S B, WF d) ∧ ((refine c S B).map (cP C l)).sum = cP C l c := by
  have h := refine_gen C l S B (List.range 4) [c] (fun p hp => List.mem_range.mp hp) (by simpa using hc)
  simp only at h
  unfold refine
  refine ⟨h.1, ?_⟩
  rw [h.2]
  simp

/-- A box is a permutation of itself with one side moved to the end. -/
theorem perm_eraseIdx (c : Box) (p : Nat) (hp : p < c.length) : c.Perm (c.eraseIdx p ++ [c.getD p []]) := by
  rw [List.eraseIdx_eq_take_drop_succ]
  have h1 : c = c.take p ++ c[p] :: c.drop (p + 1) := by
    conv_lhs => rw [← List.take_append_drop p c]
    rw [List.drop_eq_getElem_cons hp]
  have h2 : c.getD p [] = c[p] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  rw [h2]
  conv_lhs => rw [h1]
  exact List.perm_middle.trans (List.perm_append_comm (l₁ := [c[p]]))

theorem srt_perm (c : Box) : (srt c).Perm c := List.mergeSort_perm c _

theorem count_map_ite {α : Type} [BEq α] [LawfulBEq α] (a : α) (x y : ℚ) :
    ∀ (l : List α), (l.map fun s => if s == a then x else y).sum =
      (l.count a : ℚ) * x + ((l.length : ℚ) - (l.count a : ℚ)) * y
  | [] => by simp
  | s :: l => by
    rw [List.map_cons, List.sum_cons, count_map_ite a x y l, List.count_cons, List.length_cons]
    by_cases h : s = a
    · subst h
      simp only [beq_self_eq_true, ite_true]
      push_cast
      ring
    · have hb : (s == a) = false := by simpa using h
      simp only [hb, Bool.false_eq_true, ite_false]
      push_cast
      ring

/-- What a verdict stands for: a key of four sets with label `m`, and for every competitor a lower bound per set
    whose sum is positive. -/
def Passes (E L U : Tensor ℚ) (d V m : Nat) (key : Box) : Prop :=
  key.length = 4 ∧ [m] ∈ key ∧ (∀ s ∈ key, ∀ t ∈ s, t ≤ m) ∧
  ∀ j < V, j ≠ m → ∃ lo : List Nat → ℚ,
    (∀ s ∈ key, ∀ t ∈ s, lo s ≤ Mat E L U d V m t - Mat E L U d V j t) ∧ 0 < (key.map lo).sum

theorem sum_map_eq_range {β : Type} (lo : β → ℚ) (dflt : β) : ∀ (c : List β),
    (c.map lo).sum = ∑ p ∈ Finset.range c.length, lo (c.getD p dflt)
  | [] => by simp
  | s :: c => by
    rw [List.map_cons, List.sum_cons, List.length_cons, Finset.sum_range_succ', sum_map_eq_range lo dflt c]
    simp [List.getD_cons_succ, List.getD_cons_zero, add_comm]

theorem getD_mem_box (c : Box) (p : Nat) (hp : p < c.length) : c.getD p [] ∈ c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  exact List.getElem_mem hp

/-- The box theorem: every input of a box that is a permutation of a passing key is answered correctly. -/
theorem correct_of_passes (w : Weights ℚ) (E L U : Tensor ℚ) (d P V : Nat)
    (hgP : graph.positions = P) (hgV : graph.values = V)
    (hE : List.lookup "embedding.weight" w = some E) (hEs : E.shape = [d, V])
    (hEsz : E.data.size = d * V)
    (hL : List.lookup "linear.weight" w = some L) (hLs : L.shape = [d, d])
    (hLsz : L.data.size = d * d)
    (hU : List.lookup "unembedding.weight" w = some U) (hUs : U.shape = [V, d])
    (hUsz : U.data.size = V * d) (hP4 : P = 4)
    (key c : Box) (m : Nat) (hm : m < V) (hpass : Passes E L U d V m key) (hperm : c.Perm key)
    (x : Input) (hx : inS c x = true) : Correct graph w task x := by
  obtain ⟨hlen, hmem, hle, hj⟩ := hpass
  have hcl : c.length = 4 := by rw [hperm.length_eq, hlen]
  have hxl : x.length = P := by rw [inS_length c x hx, hcl, hP4]
  have hall : ∀ t ∈ x, t ≤ m := by
    intro t ht
    obtain ⟨s, hs, hts⟩ := inS_mem c x hx t ht
    exact hle s (hperm.subset hs) t hts
  have hmx : m ∈ x := by
    have hmc : [m] ∈ c := hperm.symm.subset hmem
    obtain ⟨p, hp, hcp⟩ := List.mem_iff_getElem.mp hmc
    have h1 := inS_getD c x hx p hp
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some, hcp] at h1
    have hxp : x.getD p 0 = m := List.mem_singleton.mp h1
    rw [← hxp]
    exact getD_mem x p (by rw [inS_length c x hx]; exact hp)
  have hlab : task.label x = m := by rw [task_label]; exact foldl_max_eq x m hall hmx
  have hVall : ∀ a ∈ x, a < V := fun a ha => lt_of_le_of_lt (hall a ha) hm
  apply correct_of_logits w E L U d P V hgP hgV hE hEs hEsz hL hLs hLsz hU hUs hUsz x hxl hVall
  · rw [hlab]; exact hm
  · intro j hjV hne
    rw [hlab] at hne ⊢
    obtain ⟨lo, hlo, hsum⟩ := hj j hjV hne
    apply logit_lt_of_lower E L U d P V x hxl hVall m j (fun p => lo (c.getD p []))
    · intro p hp
      have hp' : p < c.length := by rw [hcl, ← hP4]; exact Finset.mem_range.mp hp
      exact hlo _ (hperm.subset (getD_mem_box c p hp')) _ (inS_getD c x hx p hp')
    · have h1 : (c.map lo).sum = (key.map lo).sum := (hperm.map lo).sum_eq
      rw [sum_map_eq_range lo [] c, hcl, ← hP4] at h1
      rw [h1]
      exact hsum

end Candidate.Ref
