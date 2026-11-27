import Candidate.LibSubClass

/-!
# Soundness of entry 9: the counting

`blockSum_le`: what the checker counts for a largest rank `λ` is at most the number of inputs of
its classes that the network answers correctly. `check_sound` (`Check.lean`) adds the blocks up.

The count is a sum over the classes of inputs of entry 7 (`GrossCubic.clsOf`: the largest rank
`λ`, the query's rank, and the pattern of the other positions holding a token below the largest).
For a pattern of `c'` positions the checker counts `(λ - g + 1)^c'` when the verdict of its class
passed: the inputs with tokens of rank at most `λ - g` at the pattern's positions
(`GrossCubic.countP_PS`), each answered correctly (`correct_class`); and the input `(m, ..., m)`
when its test passed (`GrossCubic.correct_onlyMax`). The classes are disjoint
(`GrossCubic.classes_le`).
-/

namespace GrossSub

open CompactCheck Common AttnClasses GrossCubic Finset

/-! ## The inputs of a pattern -/

theorem countP_range_lt {k lam : ℕ} (hk : k ≤ lam) :
    (List.range lam).countP (fun ρ => decide (ρ < k)) = k := by
  have h := countP_lt (fun _ => true) hk
  simp only [and_true] at h
  rw [h]
  simp

/-- The ranks below `λ` within the gap `g`: `λ - g + 1` of them. -/
theorem countP_gap {lam g : ℕ} (hg1 : 1 ≤ g) (hgl : g ≤ lam) :
    (List.range lam).countP (fun ρ => decide (ρ + g ≤ lam)) = lam - g + 1 := by
  rw [← countP_range_lt (k := lam - g + 1) (lam := lam) (by omega)]
  refine List.countP_congr fun ρ _ => ?_
  simp only [decide_eq_true_eq]
  omega

/-- A pattern without positions is the empty one. -/
theorem pat_zero {L pat : ℕ} (h0 : (inPat L pat).length = 0) (hpat : pat < 2 ^ L) : pat = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.zero_testBit]
  by_cases hi : i < L
  · have hnil := List.length_eq_zero_iff.mp h0
    unfold inPat at hnil
    have := List.filter_eq_nil_iff.mp hnil i (List.mem_range.mpr hi)
    simpa using this
  · exact Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hpat (Nat.pow_le_pow_right (by norm_num) (by omega)))

/-- The label of an input of the class of `λ`: the token of rank `λ`. -/
theorem label_cls {mx : Bool} {N : Net} {lam rq pat : ℕ} {x : Input} (hxV : ∀ t ∈ x, t < N.V)
    (hcl : clsOf mx N.V N.n x = (lam, rq, pat)) :
    (taskOf mx N.n N.V).label x = tok mx N.V lam := by
  rw [label_eq hxV]
  exact congrArg (tok mx N.V) (congrArg Prod.fst hcl)

section Block

variable {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
  (hV : N.V = g.values) (hn : N.n = g.positions) (hn2 : 2 ≤ N.n) (mx : Bool)
  (gap : ℕ → ℕ → ℕ → ℕ) (pbar : ℕ → ℚ) (fEh : ℕ → ℕ → ℚ) (feps fmu fsp : ℕ → ℚ) (ok : Bool)
  (hErr : ok = true → ErrSpec N.V (eqkeF N pbar) fEh feps)
  (hEu : EupuSpec N.V N.D fmu fsp)
  (srt : List (List (Q × Q) × List (Q × Q)))
  (hsrt : ∀ q < N.V, SortedSpec ((List.range (N.n - 1)).map fun p =>
    peF N pbar q p - peF N pbar q (N.n - 1)) (srt.getD q ([], [])).1 (srt.getD q ([], [])).2)
  (avgs : List Q) (one : Q) (hone : one.val = 1)

include hg hw hV hn hn2 hErr hEu hsrt hone in
/-- **A class with a passing verdict.** Its inputs with tokens within the gap at the pattern's
    positions, `(λ - g + 1)^c'` of them, are answered correctly. -/
theorem sub_count_le {lam rq pat c0 : ℕ} (hlam : lam < N.V) (hrq : rq ≤ lam)
    (hpat : pat < 2 ^ (N.n - 1)) (hc0 : c0 < N.n - 1)
    (hcls : ClassOK mx N.V N.n gap (mat N.V N.V fEh) (vec N.V feps) ok srt (vec N.V fsp)
      (rmV mx N.V fEh) (WpreV mx N) avgs one lam (tok mx N.V lam)
      (LsV N.V (tok mx N.V lam) (vec N.V fmu) (ppessV N.V N.n (tok mx N.V lam) (PVm N)))
      (RsV N.V (tok mx N.V lam) (EVm N))
      (RmaxV N.V (tok mx N.V lam) (RsV N.V (tok mx N.V lam) (EVm N)))
      (RminV N.V (tok mx N.V lam) (RsV N.V (tok mx N.V lam) (EVm N))) c0 rq)
    (hcc : (inPat (N.n - 1) pat).length + (if rq = lam then 0 else 1) = c0 + 1) :
    (lam - gapOf gap rq lam (c0 + 1) + 1) ^ (inPat (N.n - 1) pat).length ≤
      Ncls mx g w N lam rq pat := by
  have hQ : N.n - 1 < N.n := by omega
  have hm : tok mx N.V lam < N.V := tok_lt hlam
  have hgg1 := one_le_gapOf gap rq lam (c0 + 1)
  have hggl := (valid_spec hcls.2.1).1
  rw [← countP_gap hgg1 hggl, ← countP_PS mx (by omega) hlam hrq]
  refine List.countP_mono_left fun x hx hps => ?_
  obtain ⟨hlen, hxV⟩ := mem_allInputs_replicate.mp hx
  have hps' := of_decide_eq_true hps
  have hK : ∀ p < N.n - 1, pat.testBit p = true → tok mx N.V (x.getD p 0) < lam ∧
      tok mx N.V (x.getD p 0) + gapOf gap rq lam (c0 + 1) ≤ lam := by
    intro p hp hb
    have := hps' p (by omega)
    simpa [hp, hb] using this
  have hM : ∀ p < N.n - 1, pat.testBit p = false → x.getD p 0 = tok mx N.V lam := by
    intro p hp hb
    have := hps' p (by omega)
    simpa [hp, hb] using this
  have hq : x.getD (N.n - 1) 0 = tok mx N.V rq := by
    have := hps' (N.n - 1) hQ
    simpa using this
  have hsome : rq = lam ∨ ∃ p < N.n - 1, pat.testBit p = false := by
    by_cases hrl : rq = lam
    · exact Or.inl hrl
    · refine Or.inr (by_contra fun hall => ?_)
      push Not at hall
      have hfull : inPat (N.n - 1) pat = List.range (N.n - 1) := by
        unfold inPat
        exact List.filter_eq_self.mpr fun p hp => by
          have := hall p (List.mem_range.mp hp)
          simpa using this
      rw [hfull, List.length_range] at hcc
      simp only [hrl, ↓reduceIte] at hcc
      omega
  have hcl := clsOf_eq hn2 hlam hrq hpat hlen hq (fun p hp hb => (hK p hp hb).1) hM hsome
  simp only [decide_eq_true_eq]
  refine ⟨hcl, ?_⟩
  -- the positions other than the query's not holding `m` are the pattern's
  have hnotm : ∀ p < N.n - 1, (!(Net.tk x p == tok mx N.V lam)) = pat.testBit p := by
    intro p hp
    cases hb : pat.testBit p
    · have h0 : Net.tk x p = tok mx N.V lam := hM p hp hb
      rw [h0]; simp
    · have h1 := (hK p hp hb).1
      have hne : Net.tk x p ≠ tok mx N.V lam := by
        intro h
        have h' : x.getD p 0 = tok mx N.V lam := h
        rw [h', tok_tok hlam] at h1
        omega
      simpa using hne
  have hfil : ((List.range (N.n - 1)).filter fun p => !(Net.tk x p == tok mx N.V lam)) =
      inPat (N.n - 1) pat :=
    List.filter_congr fun p hp => hnotm p (List.mem_range.mp hp)
  refine correct_class hg hw hV hn hn2 mx gap pbar fEh feps fmu fsp ok hErr hEu srt hsrt avgs one
    hone hlam hrq hcls hlen hxV (label_cls hxV hcl) hq (fun p hp hne => ?_)
    (by rw [hfil]; exact hcc)
  cases hb : pat.testBit p
  · exact absurd (hM p hp hb) hne
  · exact (hK p hp hb).2

include hg hw hV hn hn2 hErr hEu hsrt hone in
/-- **A pattern.** What the checker counts for the query of rank `rq` and a pattern of the other
    positions is at most the number of inputs of that class answered correctly. -/
theorem cnt_le {lam rq pat : ℕ} (hlam : lam < N.V) (hrq : rq ≤ lam) (hpat : pat < 2 ^ (N.n - 1))
    (verd : List (List Bool))
    (hverd : ∀ c0 rq, (verd.getD c0 []).getD rq false = true → c0 < N.n - 1 ∧ rq ≤ lam ∧
      ClassOK mx N.V N.n gap (mat N.V N.V fEh) (vec N.V feps) ok srt (vec N.V fsp)
        (rmV mx N.V fEh) (WpreV mx N) avgs one lam (tok mx N.V lam)
        (LsV N.V (tok mx N.V lam) (vec N.V fmu) (ppessV N.V N.n (tok mx N.V lam) (PVm N)))
        (RsV N.V (tok mx N.V lam) (EVm N))
        (RmaxV N.V (tok mx N.V lam) (RsV N.V (tok mx N.V lam) (EVm N)))
        (RminV N.V (tok mx N.V lam) (RsV N.V (tok mx N.V lam) (EVm N))) c0 rq) :
    cntOf Interp.counting gap lam rq (inPat (N.n - 1) pat).length
      (onlyMaxV N.V (tok mx N.V lam) (EUm N) (EVm N) (ppessV N.V N.n (tok mx N.V lam) (PVm N)))
      verd ≤ Ncls mx g w N lam rq pat := by
  have hQ : N.n - 1 < N.n := by omega
  have hm : tok mx N.V lam < N.V := tok_lt hlam
  unfold cntOf
  by_cases hrl : rq = lam
  · subst hrl
    simp only [↓reduceIte]
    by_cases hc0 : (inPat (N.n - 1) pat).length = 0
    · -- the input `(m, ..., m)`
      simp only [hc0, ↓reduceIte]
      have hp0 := pat_zero hc0 hpat
      subst hp0
      cases hb : onlyMaxV N.V (tok mx N.V rq) (EUm N) (EVm N)
          (ppessV N.V N.n (tok mx N.V rq) (PVm N))
      · exact Nat.zero_le _
      · have hx : List.replicate N.n (tok mx N.V rq) ∈ allInputs (List.replicate N.n N.V) :=
          mem_allInputs_replicate.mpr ⟨List.length_replicate, fun t ht =>
            (List.eq_of_mem_replicate ht) ▸ hm⟩
        have hcl : clsOf mx N.V N.n (List.replicate N.n (tok mx N.V rq)) = (rq, rq, 0) :=
          clsOf_eq hn2 hlam le_rfl (by positivity) List.length_replicate
            (by simp [List.getD_eq_getElem?_getD, hQ])
            (fun p _ h => by simp at h)
            (fun p hp _ => by simp [List.getD_eq_getElem?_getD, show p < N.n by omega])
            (Or.inl rfl)
        refine List.countP_pos_iff.mpr ⟨_, hx, ?_⟩
        simp only [decide_eq_true_eq]
        have hxV : ∀ t ∈ List.replicate N.n (tok mx N.V rq), t < N.V :=
          fun t ht => (List.eq_of_mem_replicate ht) ▸ hm
        exact ⟨hcl, correct_onlyMax hg hw hV hn hm (label_cls hxV hcl) hb⟩
    · simp only [hc0, ↓reduceIte]
      cases he : (verd.getD ((inPat (N.n - 1) pat).length - 1) []).getD rq false
      · exact Nat.zero_le _
      · obtain ⟨hc0', -, hcls⟩ := hverd _ _ he
        have := sub_count_le hg hw hV hn hn2 mx gap pbar fEh feps fmu fsp ok hErr hEu srt hsrt
          avgs one hone hlam le_rfl hpat hc0' hcls (by simp only [↓reduceIte]; omega)
        rw [Nat.sub_add_cancel (by omega)] at this
        simpa [Nat.pow_eq] using this
  · simp only [hrl, ↓reduceIte]
    cases he : (verd.getD (inPat (N.n - 1) pat).length []).getD rq false
    · exact Nat.zero_le _
    · obtain ⟨hc0', -, hcls⟩ := hverd _ _ he
      have := sub_count_le hg hw hV hn hn2 mx gap pbar fEh feps fmu fsp ok hErr hEu srt hsrt
        avgs one hone hlam hrq hpat hc0' hcls (by simp only [hrl, ↓reduceIte])
      simpa [Nat.pow_eq] using this

include hg hw hV hn hn2 hErr hEu hsrt hone in
/-- **A block.** The count of a block is at most the number of inputs of its classes answered
    correctly. -/
theorem blockSum_le {lam : ℕ} (hlam : lam < N.V) (verd : List (List Bool))
    (hverd : ∀ c0 rq, (verd.getD c0 []).getD rq false = true → c0 < N.n - 1 ∧ rq ≤ lam ∧
      ClassOK mx N.V N.n gap (mat N.V N.V fEh) (vec N.V feps) ok srt (vec N.V fsp)
        (rmV mx N.V fEh) (WpreV mx N) avgs one lam (tok mx N.V lam)
        (LsV N.V (tok mx N.V lam) (vec N.V fmu) (ppessV N.V N.n (tok mx N.V lam) (PVm N)))
        (RsV N.V (tok mx N.V lam) (EVm N))
        (RmaxV N.V (tok mx N.V lam) (RsV N.V (tok mx N.V lam) (EVm N)))
        (RminV N.V (tok mx N.V lam) (RsV N.V (tok mx N.V lam) (EVm N))) c0 rq) :
    blockSum gap N.n lam (onlyMaxV N.V (tok mx N.V lam) (EUm N) (EVm N)
        (ppessV N.V N.n (tok mx N.V lam) (PVm N))) verd ≤
      ∑ rq ∈ range (lam + 1), ∑ pat ∈ range (2 ^ (N.n - 1)), Ncls mx g w N lam rq pat := by
  unfold blockSum
  simp only [Nat.add_eq, Nat.pow_eq]
  have inner : ∀ rq a, (List.range (2 ^ (N.n - 1))).foldl (fun a pat => a +
      cntOf Interp.counting gap lam rq (inPat (N.n - 1) pat).length
        (onlyMaxV N.V (tok mx N.V lam) (EUm N) (EVm N)
          (ppessV N.V N.n (tok mx N.V lam) (PVm N))) verd) a =
      a + ∑ pat ∈ range (2 ^ (N.n - 1)), cntOf Interp.counting gap lam rq
        (inPat (N.n - 1) pat).length (onlyMaxV N.V (tok mx N.V lam) (EUm N) (EVm N)
          (ppessV N.V N.n (tok mx N.V lam) (PVm N))) verd := by
    intro rq a
    rw [foldl_add_map, sum_range_eq]
  simp only [inner]
  rw [foldl_add_map, sum_range_eq, Nat.zero_add]
  refine Finset.sum_le_sum fun rq hrq => Finset.sum_le_sum fun pat hpat => ?_
  exact cnt_le hg hw hV hn hn2 mx gap pbar fEh feps fmu fsp ok hErr hEu srt hsrt avgs one hone
    hlam (Nat.lt_succ_iff.mp (mem_range.mp hrq)) (mem_range.mp hpat) verd hverd

end Block

/-! ## The blocks add up -/

theorem forall₂_sum_le {α : Type} {R : α → ℕ → Prop} (f : α → ℕ) : ∀ {l : List α} {out : List ℕ},
    List.Forall₂ R l out → (∀ a ∈ l, ∀ b, R a b → b ≤ f a) → out.sum ≤ (l.map f).sum
  | [], [], List.Forall₂.nil, _ => le_rfl
  | a :: l, b :: out, List.Forall₂.cons hab hrest, h => by
    simp only [List.sum_cons, List.map_cons]
    exact add_le_add (h a List.mem_cons_self b hab)
      (forall₂_sum_le f hrest fun a' ha' => h a' (List.mem_cons_of_mem _ ha'))

end GrossSub
