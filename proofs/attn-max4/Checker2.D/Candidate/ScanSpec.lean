import Candidate.TabSpec

/-!
# Specifications of the prefix scans (`scanMaxM`, `scanMinM`, `scansMaxM`, `scansMinM`).
-/

namespace Candidate.Tables
open CompactCheck Candidate.Loops

section
variable {env : Env}

/-- `scanMaxM f n t acc arr` appends `n+1` entries; entry `a` is `≥ acc` and `≥ f (t+k)` for every `k < a`. -/
theorem spec_scanMaxM (f : Nat → Q) : ∀ (n t : Nat) (acc : Q) (arr : Array Q),
    Spec env (scanMaxM Interp.counting f n t acc arr) fun arr' =>
      ∃ l : List Q, arr'.toList = arr.toList ++ l ∧ l.length = n + 1 ∧
        ∀ a (ha : a < l.length), acc.val ≤ (l[a]).val ∧ ∀ k, k < a → (f (t + k)).val ≤ (l[a]).val
  | 0, t, acc, arr => by
    simp only [scanMaxM]
    refine spec_pure ⟨[acc], by simp, rfl, ?_⟩
    intro a ha
    have : a = 0 := by simp at ha; omega
    subst this
    exact ⟨le_refl _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n+1, t, acc, arr => by
    show Spec env (CostM.qmax "" acc (f t) >>= fun acc' => scanMaxM Interp.counting f n (t+1) acc' (arr.push acc)) _
    refine spec_bind (spec_max "" acc (f t)) fun acc' hacc => ?_
    refine spec_mono ?_ (spec_scanMaxM f n (t+1) acc' (arr.push acc))
    intro arr' ⟨l, hl, hlen, hP⟩
    refine ⟨acc :: l, ?_, by simp [hlen], ?_⟩
    · rw [hl, Array.toList_push, List.append_assoc, List.singleton_append]
    · intro a ha
      cases a with
      | zero => exact ⟨le_refl _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
      | succ a =>
        have ha' : a < l.length := by simpa using ha
        obtain ⟨h1, h2⟩ := hP a ha'
        simp only [List.getElem_cons_succ]
        rw [hacc] at h1
        refine ⟨le_trans (le_max_left _ _) h1, fun k hk => ?_⟩
        cases k with
        | zero => simpa using le_trans (le_max_right _ _) h1
        | succ k =>
          have := h2 k (by omega)
          rw [show t + (k + 1) = t + 1 + k by omega]
          exact this

theorem spec_scanMinM (f : Nat → Q) : ∀ (n t : Nat) (acc : Q) (arr : Array Q),
    Spec env (scanMinM Interp.counting f n t acc arr) fun arr' =>
      ∃ l : List Q, arr'.toList = arr.toList ++ l ∧ l.length = n + 1 ∧
        ∀ a (ha : a < l.length), (l[a]).val ≤ acc.val ∧ ∀ k, k < a → (l[a]).val ≤ (f (t + k)).val
  | 0, t, acc, arr => by
    simp only [scanMinM]
    refine spec_pure ⟨[acc], by simp, rfl, ?_⟩
    intro a ha
    have : a = 0 := by simp at ha; omega
    subst this
    exact ⟨le_refl _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
  | n+1, t, acc, arr => by
    show Spec env (CostM.qmin "" acc (f t) >>= fun acc' => scanMinM Interp.counting f n (t+1) acc' (arr.push acc)) _
    refine spec_bind (spec_min "" acc (f t)) fun acc' hacc => ?_
    refine spec_mono ?_ (spec_scanMinM f n (t+1) acc' (arr.push acc))
    intro arr' ⟨l, hl, hlen, hP⟩
    refine ⟨acc :: l, ?_, by simp [hlen], ?_⟩
    · rw [hl, Array.toList_push, List.append_assoc, List.singleton_append]
    · intro a ha
      cases a with
      | zero => exact ⟨le_refl _, fun k hk => absurd hk (Nat.not_lt_zero _)⟩
      | succ a =>
        have ha' : a < l.length := by simpa using ha
        obtain ⟨h1, h2⟩ := hP a ha'
        simp only [List.getElem_cons_succ]
        rw [hacc] at h1
        refine ⟨le_trans h1 (min_le_left _ _), fun k hk => ?_⟩
        cases k with
        | zero => simpa using le_trans h1 (min_le_right _ _)
        | succ k =>
          have := h2 k (by omega)
          rw [show t + (k + 1) = t + 1 + k by omega]
          exact this

/-- `scansMaxM f len n o arr`: `n` scans of `len+1` entries; entry `o'*(len+1)+a` is `≥ f (o+o') k` for `k < a`. -/
theorem spec_scansMaxM (f : Nat → Nat → Q) (len : Nat) : ∀ (n o : Nat) (arr : Array Q),
    Spec env (scansMaxM Interp.counting f len n o arr) fun arr' =>
      ∃ l : List Q, arr'.toList = arr.toList ++ l ∧ l.length = n * (len + 1) ∧
        ∀ o' a (h : o' * (len + 1) + a < l.length), o' < n → a ≤ len →
          ∀ k, k < a → (f (o + o') k).val ≤ (l[o' * (len + 1) + a]).val
  | 0, o, arr => by
    simp only [scansMaxM]
    exact spec_pure ⟨[], by simp, by simp, fun o' a h ho' _ _ _ => absurd ho' (Nat.not_lt_zero _)⟩
  | n+1, o, arr => by
    show Spec env (scanMaxM Interp.counting (f o) len 0 (f o 0) arr >>= fun arr1 =>
      scansMaxM Interp.counting f len n (o+1) arr1) _
    refine spec_bind (spec_scanMaxM (f o) len 0 (f o 0) arr) fun arr1 ⟨l1, hl1, hlen1, hP1⟩ => ?_
    refine spec_mono ?_ (spec_scansMaxM f len n (o+1) arr1)
    intro arr' ⟨l2, hl2, hlen2, hP2⟩
    refine ⟨l1 ++ l2, by rw [hl2, hl1, List.append_assoc], by simp [hlen1, hlen2]; ring, ?_⟩
    intro o' a h ho' ha k hk
    cases o' with
    | zero =>
      have hlt : a < l1.length := by rw [hlen1]; omega
      rw [List.getElem_append_left (by simpa using hlt)]
      simpa using (hP1 a hlt).2 k hk
    | succ o' =>
      have hge : l1.length ≤ (o' + 1) * (len + 1) + a := by rw [hlen1]; nlinarith
      rw [List.getElem_append_right hge]
      have e : (o' + 1) * (len + 1) + a - l1.length = o' * (len + 1) + a := by rw [hlen1]; ring_nf; omega
      have h2 : o' * (len + 1) + a < l2.length := by
        rw [List.length_append] at h; omega
      have := hP2 o' a h2 (by omega) ha k hk
      rw [show o + (o' + 1) = o + 1 + o' by omega]
      simp only [e]
      exact this

theorem spec_scansMinM (f : Nat → Nat → Q) (len : Nat) : ∀ (n o : Nat) (arr : Array Q),
    Spec env (scansMinM Interp.counting f len n o arr) fun arr' =>
      ∃ l : List Q, arr'.toList = arr.toList ++ l ∧ l.length = n * (len + 1) ∧
        ∀ o' a (h : o' * (len + 1) + a < l.length), o' < n → a ≤ len →
          ∀ k, k < a → (l[o' * (len + 1) + a]).val ≤ (f (o + o') k).val
  | 0, o, arr => by
    simp only [scansMinM]
    exact spec_pure ⟨[], by simp, by simp, fun o' a h ho' _ _ _ => absurd ho' (Nat.not_lt_zero _)⟩
  | n+1, o, arr => by
    show Spec env (scanMinM Interp.counting (f o) len 0 (f o 0) arr >>= fun arr1 =>
      scansMinM Interp.counting f len n (o+1) arr1) _
    refine spec_bind (spec_scanMinM (f o) len 0 (f o 0) arr) fun arr1 ⟨l1, hl1, hlen1, hP1⟩ => ?_
    refine spec_mono ?_ (spec_scansMinM f len n (o+1) arr1)
    intro arr' ⟨l2, hl2, hlen2, hP2⟩
    refine ⟨l1 ++ l2, by rw [hl2, hl1, List.append_assoc], by simp [hlen1, hlen2]; ring, ?_⟩
    intro o' a h ho' ha k hk
    cases o' with
    | zero =>
      have hlt : a < l1.length := by rw [hlen1]; omega
      rw [List.getElem_append_left (by simpa using hlt)]
      simpa using (hP1 a hlt).2 k hk
    | succ o' =>
      have hge : l1.length ≤ (o' + 1) * (len + 1) + a := by rw [hlen1]; nlinarith
      rw [List.getElem_append_right hge]
      have e : (o' + 1) * (len + 1) + a - l1.length = o' * (len + 1) + a := by rw [hlen1]; ring_nf; omega
      have h2 : o' * (len + 1) + a < l2.length := by
        rw [List.length_append] at h; omega
      have := hP2 o' a h2 (by omega) ha k hk
      rw [show o + (o' + 1) = o + 1 + o' by omega]
      simp only [e]
      exact this

end

end Candidate.Tables
