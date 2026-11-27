import Candidate.LibCubicCorrect

/-!
# Soundness of entry 7

`check_sound`: for the family's graph, every count a run of the checker returns is at most the
number of inputs the network answers correctly, for every weights and certificate.

A run that succeeds returns `countV` (`sat_check`), a sum over the classes of inputs: the largest
rank `lam`, the query's rank `rq`, and the pattern of the other positions holding a token below
the largest. What the checker counts for a class is at most the number of its inputs answered
correctly (`class_bound`):

* the pattern without positions: the input `(m, ..., m)` or `(m, ..., m, q)`, counted if its test
  passes (`correct_onlyMax`, `correct_queryOnly`);
* a pattern of `c` positions: `|G|^c`, the inputs with tokens of `G` at the pattern's positions,
  `G` the non-maximal tokens whose verdict at `c` passes (`correct_withNonmax`); the checker
  assembles the number from comparisons (`patCountV_eq`), and the inputs are a product set
  (`countP_prod`).

The classes are disjoint (`classes_le`), so the counts add up to at most the number of inputs
answered correctly.
-/

namespace GrossCubic

open CompactCheck Common AttnClasses Finset

/-! ## Sums and counts -/

theorem foldl_add_map {α : Type} (f : α → ℕ) : ∀ (l : List α) (a : ℕ),
    l.foldl (fun a i => a + f i) a = a + (l.map f).sum
  | [], a => by simp
  | i :: l, a => by
    rw [List.foldl_cons, foldl_add_map f l, List.map_cons, List.sum_cons]
    ring

theorem foldl_nat_add : ∀ (l : List ℕ) (a : ℕ), l.foldl Nat.add a = a + l.sum
  | [], a => by simp
  | i :: l, a => by
    rw [List.foldl_cons, foldl_nat_add l, List.sum_cons]
    change a + i + l.sum = a + (i + l.sum)
    ring

theorem sum_le_single {s : Finset ℕ} {f : ℕ → ℕ} (a : ℕ) (h : ∀ i ∈ s, i ≠ a → f i = 0) :
    ∑ i ∈ s, f i ≤ f a := by
  by_cases ha : a ∈ s
  · rw [Finset.sum_eq_single_of_mem a ha h]
  · rw [Finset.sum_eq_zero fun i hi => h i hi fun e => ha (e ▸ hi)]
    exact Nat.zero_le _

/-- Ranks, read backwards. -/
theorem countP_reflect (V : ℕ) (P : ℕ → Bool) :
    (List.range V).countP (fun t => P (V - 1 - t)) = (List.range V).countP P := by
  rw [countP_eq_sum, countP_eq_sum, sum_range_eq, sum_range_eq]
  exact Finset.sum_range_reflect (fun t => if P t then 1 else 0) V

theorem countP_tok (mx : Bool) (V : ℕ) (P : ℕ → Bool) :
    (List.range V).countP (fun t => P (tok mx V t)) = (List.range V).countP P := by
  cases mx
  · exact countP_reflect V P
  · rfl

theorem countP_lt (H : ℕ → Bool) {lam : ℕ} : ∀ {V : ℕ}, lam ≤ V →
    (List.range V).countP (fun ρ => decide (ρ < lam ∧ H ρ = true)) =
      (List.range lam).countP H := by
  intro V hV
  induction V, hV using Nat.le_induction with
  | base => exact List.countP_congr fun ρ hρ => by simp [List.mem_range.mp hρ]
  | succ V hV ih =>
    rw [List.range_succ, List.countP_append, ih]
    simp [show ¬ V < lam by omega]

/-- The tokens whose rank is below `lam` and passes `H` number as the ranks below `lam` that
    pass. -/
theorem countP_rank (mx : Bool) {V lam : ℕ} (hlam : lam ≤ V) (H : ℕ → Bool) :
    (List.range V).countP (fun t => decide (tok mx V t < lam ∧ H (tok mx V t) = true)) =
      (List.range lam).countP H := by
  have h := countP_tok mx V (fun ρ => decide (ρ < lam ∧ H ρ = true))
  rw [h]
  exact countP_lt H hlam

theorem countP_eq_one {V a : ℕ} (ha : a < V) :
    (List.range V).countP (fun t => decide (t = a)) = 1 := by
  rw [countP_eq_sum, sum_range_eq]
  simp [Finset.sum_ite_eq', ha]

theorem sum_cond_val : ∀ vs : List Bool,
    ((vs.map fun b => cond b (⟨1⟩ : Q) ⟨0⟩).map (·.val)).sum = (vs.countP id : ℚ)
  | [] => by simp
  | b :: vs => by
    rw [List.map_cons, List.map_cons, List.sum_cons, sum_cond_val vs, List.countP_cons]
    cases b
    · simp
    · simp only [Bool.cond_true, id, ↓reduceIte, Nat.cast_add, Nat.cast_one]
      ring

/-- **The count of a pattern.** The checker's count for `c = c' + 1` positions is `|G|^c`, `|G|`
    the number of verdicts that pass. -/
theorem patCountV_eq {lam c' V : ℕ} (hlam : lam ≤ V - 1) (vs : List Bool)
    (hvs : vs.length = lam) :
    patCountV lam c' vs ⟨1⟩ (jsV V) = (vs.countP id) ^ (c' + 1) := by
  unfold patCountV
  split
  · rename_i h
    subst h
    rw [foldl_add_map (fun b => cond b 1 0), countP_eq_sum]
    simp [cond_eq_ite]
  · rename_i h
    rw [foldl_add_map, Nat.zero_add]
    have hg : (sumLV (vs.map fun b => cond b ⟨1⟩ ⟨0⟩)).val = (vs.countP id : ℚ) := by
      rw [sumLV_val, sum_cond_val]
    have hgl : vs.countP id ≤ lam := hvs ▸ List.countP_le_length
    rw [← sum_thresholds (c' + 1) (vs.countP id) (by omega) lam hgl]
    congr 1
    refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [getD_map_range _ hi', jsV, getD_map_range _ (by omega), hg]
    simp only [Nat.cast_le, Nat.pow_eq]
    by_cases hle : i + 1 ≤ vs.countP id <;> simp [hle]

/-! ## Classes -/

/-- The largest rank of an input. -/
def lamOf (mx : Bool) (V : ℕ) (x : Input) : ℕ := (x.map (tok mx V)).foldl max 0

/-- The positions, other than the query's, holding a token below the largest, as bits. -/
def patX (mx : Bool) (V n : ℕ) (x : Input) : ℕ :=
  patOf ((List.range (n - 1)).map fun p => decide (tok mx V (x.getD p 0) < lamOf mx V x))

/-- The class of an input: its largest rank, its query's rank, and its pattern. -/
def clsOf (mx : Bool) (V n : ℕ) (x : Input) : ℕ × ℕ × ℕ :=
  (lamOf mx V x, tok mx V (x.getD (n - 1) 0), patX mx V n x)

theorem mem_getD {x : Input} {t : ℕ} (ht : t ∈ x) : ∃ p < x.length, x.getD p 0 = t := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ht
  exact ⟨i, hi, by rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]⟩

/-- **The class of an input**, from its positions: the query of rank `rq`, the positions of the
    pattern holding tokens of rank below `lam`, the others the token of rank `lam`, and some
    position holding it. -/
theorem clsOf_eq {mx : Bool} {V n lam rq pat : ℕ} (hn2 : 2 ≤ n) (hlam : lam < V) (hrq : rq ≤ lam)
    (hpat : pat < 2 ^ (n - 1)) {x : Input} (hx : x.length = n)
    (hq : x.getD (n - 1) 0 = tok mx V rq)
    (hK : ∀ p < n - 1, pat.testBit p = true → tok mx V (x.getD p 0) < lam)
    (hM : ∀ p < n - 1, pat.testBit p = false → x.getD p 0 = tok mx V lam)
    (hsome : rq = lam ∨ ∃ p < n - 1, pat.testBit p = false) :
    clsOf mx V n x = (lam, rq, pat) := by
  have hrqV : rq < V := by omega
  have hrank : ∀ p < n, tok mx V (x.getD p 0) ≤ lam := by
    intro p hp
    by_cases hpq : p < n - 1
    · cases hb : pat.testBit p
      · rw [hM p hpq hb, tok_tok hlam]
      · exact (hK p hpq hb).le
    · have : p = n - 1 := by omega
      subst this
      rw [hq, tok_tok hrqV]
      exact hrq
  have hlamx : lamOf mx V x = lam := by
    unfold lamOf
    apply le_antisymm
    · have hne : x.map (tok mx V) ≠ [] := by
        intro h
        rw [List.map_eq_nil_iff] at h
        subst h
        simp at hx
        omega
      obtain ⟨t, ht, he⟩ := List.mem_map.mp (foldl_max_mem hne)
      obtain ⟨p, hp, rfl⟩ := mem_getD ht
      rw [← he]
      exact hrank p (by omega)
    · rcases hsome with rfl | ⟨p, hp, hb⟩
      · refine AttnClasses.le_foldl_max 0 (List.mem_map.mpr ⟨x.getD (n - 1) 0, ?_, ?_⟩)
        · exact tk_mem (by omega)
        · rw [hq, tok_tok hrqV]
      · refine AttnClasses.le_foldl_max 0 (List.mem_map.mpr ⟨x.getD p 0, tk_mem (by omega), ?_⟩)
        rw [hM p hp hb, tok_tok hlam]
  refine Prod.ext hlamx (Prod.ext ?_ ?_)
  · change tok mx V (x.getD (n - 1) 0) = rq
    rw [hq, tok_tok hrqV]
  · change patX mx V n x = pat
    unfold patX
    rw [hlamx]
    refine Nat.eq_of_testBit_eq fun i => ?_
    rw [testBit_patOf]
    by_cases hi : i < n - 1
    · rw [getD_map_range _ hi]
      cases hb : pat.testBit i
      · rw [hM i hi hb, tok_tok hlam]
        simp
      · exact decide_eq_true (hK i hi hb)
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega), Option.getD_none,
        Nat.testBit_lt_two_pow
          (lt_of_lt_of_le hpat (Nat.pow_le_pow_right (by norm_num) (by omega)))]

/-! ## A class's inputs -/

/-- The inputs of a pattern of `c` positions whose tokens pass `H`: `|G|^c`. -/
theorem countP_PS (mx : Bool) {V n lam rq pat : ℕ} (hn : 0 < n) (hlam : lam < V) (hrq : rq ≤ lam)
    (H : ℕ → Bool) :
    (allInputs (List.replicate n V)).countP (fun x => decide (∀ p < n,
      (if p < n - 1 then (if pat.testBit p = true then
        tok mx V (x.getD p 0) < lam ∧ H (tok mx V (x.getD p 0)) = true
        else x.getD p 0 = tok mx V lam) else x.getD p 0 = tok mx V rq))) =
      ((List.range lam).countP H) ^ (inPat (n - 1) pat).length := by
  rw [countP_prod V n (fun p t => if p < n - 1 then (if pat.testBit p = true then
        tok mx V t < lam ∧ H (tok mx V t) = true else t = tok mx V lam) else t = tok mx V rq)]
  have hm : tok mx V lam < V := tok_lt hlam
  have hq : tok mx V rq < V := tok_lt (by omega)
  have e : ∀ p ∈ range n, (List.range V).countP (fun t => decide (if p < n - 1 then
      (if pat.testBit p = true then tok mx V t < lam ∧ H (tok mx V t) = true
        else t = tok mx V lam) else t = tok mx V rq)) =
      if p < n - 1 then (if pat.testBit p then (List.range lam).countP H else 1) else 1 := by
    intro p _
    by_cases hp : p < n - 1
    · simp only [hp, ↓reduceIte]
      cases hb : pat.testBit p
      · simp only [Bool.false_eq_true, ↓reduceIte]
        exact countP_eq_one hm
      · simp only [↓reduceIte]
        exact countP_rank mx hlam.le H
    · simp only [hp, ↓reduceIte]
      exact countP_eq_one hq
  rw [Finset.prod_congr rfl e]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Finset.prod_range_succ]
  simp only [Nat.add_sub_cancel, lt_irrefl, ↓reduceIte, mul_one]
  rw [← prod_pat]
  exact Finset.prod_congr rfl fun p hp => by simp [mem_range.mp hp]

open Classical in
/-- The number of inputs of a class answered correctly. -/
noncomputable abbrev Ncls (mx : Bool) (g : Graph) (w : Weights ℚ) (N : Net) (lam rq pat : ℕ) : ℕ :=
  (allInputs (List.replicate N.n N.V)).countP fun x =>
    decide (clsOf mx N.V N.n x = (lam, rq, pat) ∧ Correct g w (taskOf mx N.n N.V) x)

/-- **A class.** What the checker counts for a class is at most the number of its inputs
    answered correctly. -/
theorem class_bound {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) (hV2 : 2 ≤ N.V) (hn2 : 2 ≤ N.n) (mx : Bool)
    {XE XP : List (List (Q × Q))} (hXE : BoundsE N XE) (hXP : BoundsP N XP)
    {lam rq pat : ℕ} (hlam : lam < N.V) (hrq : rq ≤ lam) (hpat : pat < 2 ^ (N.n - 1)) :
    (if pat = 0 then (if rq = lam then
        cond (onlyMaxV N.V (tok mx N.V lam) (EUm N) (EVm N)
          (ppessV N.V N.n (tok mx N.V lam) (PVm N))) 1 0
      else cond (queryOnlyV N.V N.n (tok mx N.V lam) (tok mx N.V rq) (EUm N) (EVm N)
          (ppessV N.V N.n (tok mx N.V lam) (PVm N)) XE XP) 1 0) else 0) +
      (0 :: cntsV mx N.V N.n lam rq (usOf mx N lam) (ksOf mx N lam) XE XP
        ((jsV N.V).getD 0 ⟨0⟩) (jsV N.V)).getD (inPat (N.n - 1) pat).length 0 ≤
      Ncls mx g w N lam rq pat := by
  have hQ : N.n - 1 < N.n := by omega
  have hrqV : rq < N.V := by omega
  have hm : tok mx N.V lam < N.V := tok_lt hlam
  have hqV : tok mx N.V rq < N.V := tok_lt hrqV
  have hsp : (taskOf mx N.n N.V).space = List.replicate N.n N.V := by cases mx <;> rfl
  -- the label of an input of the class
  have hlab : ∀ {x : Input}, (∀ t ∈ x, t < N.V) → clsOf mx N.V N.n x = (lam, rq, pat) →
      (taskOf mx N.n N.V).label x = tok mx N.V lam := by
    intro x hxV hcl
    rw [label_eq hxV]
    exact congrArg (tok mx N.V) (congrArg Prod.fst hcl)
  have hone : (jsV N.V).getD 0 ⟨0⟩ = ⟨1⟩ := by
    rw [jsV, getD_map_range _ (by omega)]
    simp
  by_cases hp0 : pat = 0
  · subst hp0
    have hin : inPat (N.n - 1) 0 = [] := by simp [inPat]
    rw [hin]
    simp only [↓reduceIte, List.length_nil, List.getD_cons_zero, add_zero]
    by_cases hrl : rq = lam
    · subst hrl
      simp only [↓reduceIte]
      cases hb : onlyMaxV N.V (tok mx N.V rq) (EUm N) (EVm N)
          (ppessV N.V N.n (tok mx N.V rq) (PVm N))
      · exact Nat.zero_le _
      · -- the input `(m, ..., m)`
        have hx : List.replicate N.n (tok mx N.V rq) ∈ allInputs (List.replicate N.n N.V) :=
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
        exact ⟨hcl, correct_onlyMax hg hw hV hn hm
          (hlab (fun t ht => (List.eq_of_mem_replicate ht) ▸ hm) hcl) hb⟩
    · simp only [hrl, ↓reduceIte]
      have hrl' : rq < lam := by omega
      cases hb : queryOnlyV N.V N.n (tok mx N.V lam) (tok mx N.V rq) (EUm N) (EVm N)
          (ppessV N.V N.n (tok mx N.V lam) (PVm N)) XE XP
      · exact Nat.zero_le _
      · -- the input `(m, ..., m, q)`
        have hxV : ∀ t ∈ List.replicate (N.n - 1) (tok mx N.V lam) ++ [tok mx N.V rq],
            t < N.V := by
          intro t ht
          rcases List.mem_append.mp ht with h | h
          · exact (List.eq_of_mem_replicate h) ▸ hm
          · rw [List.mem_singleton.mp h]; exact hqV
        have hlen : (List.replicate (N.n - 1) (tok mx N.V lam) ++ [tok mx N.V rq]).length =
            N.n := by simp; omega
        have hx : List.replicate (N.n - 1) (tok mx N.V lam) ++ [tok mx N.V rq] ∈
            allInputs (List.replicate N.n N.V) := mem_allInputs_replicate.mpr ⟨hlen, hxV⟩
        have hcl : clsOf mx N.V N.n (List.replicate (N.n - 1) (tok mx N.V lam) ++
            [tok mx N.V rq]) = (lam, rq, 0) :=
          clsOf_eq hn2 hlam hrq (by positivity) hlen tk_query_last
            (fun p _ h => by simp at h)
            (fun p hp _ => tk_query hp)
            (Or.inr ⟨0, by omega, Nat.zero_testBit 0⟩)
        refine List.countP_pos_iff.mpr ⟨_, hx, ?_⟩
        simp only [decide_eq_true_eq]
        exact ⟨hcl, correct_queryOnly hg hw hV hn hn2 hm hqV hXE hXP (hlab hxV hcl) hb⟩
  · simp only [hp0, ↓reduceIte, Nat.zero_add]
    set c := (inPat (N.n - 1) pat).length with hc
    rcases Nat.eq_zero_or_pos c with hc0 | hc1
    · rw [hc0]
      exact Nat.zero_le _
    obtain ⟨c', hc'⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    rw [hc', List.getD_cons_succ]
    by_cases hcn : c' < ncsOf N.n lam rq
    · rw [cntsV, getD_map_range _ hcn, hone]
      set verd := verdV mx N.V N.n lam rq (usOf mx N lam) (ksOf mx N lam) XE XP with hverd
      set H : ℕ → Bool := fun κ => (verd.getD κ []).getD c' false with hH
      have hvs : (verd.map fun l => l.getD c' false).countP id = (List.range lam).countP H := by
        rw [hverd, verdV, List.map_map, List.countP_map]
        refine List.countP_congr fun κ hκ => ?_
        simp only [Function.comp_apply, id, hH, hverd, verdV]
        rw [getD_map_range _ (List.mem_range.mp hκ)]
      rw [patCountV_eq (by omega) _ (by simp [hverd, verdV]), hvs, ← hc', hc,
        ← countP_PS mx (by omega) hlam hrq H]
      refine List.countP_mono_left fun x hx hps => ?_
      obtain ⟨hlen, hxV⟩ := mem_allInputs_replicate.mp hx
      have hps' := of_decide_eq_true hps
      have hK : ∀ p < N.n - 1, pat.testBit p = true →
          tok mx N.V (x.getD p 0) < lam ∧ H (tok mx N.V (x.getD p 0)) = true := by
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
          have : c = N.n - 1 := by rw [hc, hfull, List.length_range]
          simp only [ncsOf, hrl, ↓reduceIte] at hcn
          omega
      have hcl := clsOf_eq hn2 hlam hrq hpat hlen hq (fun p hp hb => (hK p hp hb).1) hM hsome
      simp only [decide_eq_true_eq]
      refine ⟨hcl, ?_⟩
      exact correct_withNonmax hg hw hV hn hn2 mx hXE hXP hlam hrq hpat hc.symm (by omega)
        (by omega) hlen hxV (hlab hxV hcl) hq
        (fun p hp hb => by
          have := hK p hp hb
          refine ⟨this.1, ?_⟩
          have e : c - 1 = c' := by omega
          rw [e]
          exact this.2)
        hM
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [cntsV]; omega),
        Option.getD_none]
      exact Nat.zero_le _

/-! ## The classes add up -/

/-- One input is in one class at most. -/
theorem one_class (a b c V M : ℕ) (R : Prop) [Decidable R] :
    ∑ lam ∈ range V, ∑ rq ∈ range (lam + 1), ∑ pat ∈ range M,
      (if (a, b, c) = (lam, rq, pat) ∧ R then 1 else 0) ≤ if R then 1 else 0 := by
  refine le_trans (sum_le_single a fun lam _ hne => Finset.sum_eq_zero fun rq _ =>
    Finset.sum_eq_zero fun pat _ => ite_eq_right fun h => hne (Prod.mk.inj h.1).1.symm) ?_
  refine le_trans (sum_le_single b fun rq _ hne => Finset.sum_eq_zero fun pat _ =>
    ite_eq_right fun h => hne (Prod.mk.inj (Prod.mk.inj h.1).2).1.symm) ?_
  refine le_trans (sum_le_single c fun pat _ hne =>
    ite_eq_right fun h => hne (Prod.mk.inj (Prod.mk.inj h.1).2).2.symm) ?_
  simp

/-- **Disjoint classes.** The inputs with `P`, counted class by class, are at most the inputs with
    `P`. -/
theorem classes_le {α : Type} (cl : α → ℕ × ℕ × ℕ) (P : α → Prop) [DecidablePred P] (V M : ℕ) :
    ∀ l : List α, ∑ lam ∈ range V, ∑ rq ∈ range (lam + 1), ∑ pat ∈ range M,
      l.countP (fun x => decide (cl x = (lam, rq, pat) ∧ P x)) ≤ l.countP fun x => decide (P x)
  | [] => by simp
  | x :: l => by
    simp only [List.countP_cons, Finset.sum_add_distrib]
    refine add_le_add (classes_le cl P V M l) ?_
    obtain ⟨a, b, c⟩ := cl x
    simpa using one_class a b c V M (P x)

/-- The block of a largest rank, as sums. -/
theorem blockV_eq (mx : Bool) (N : Net) (XE XP : List (List (Q × Q))) (one : Q) (js : List Q)
    (lam : ℕ) :
    blockV mx N.V N.n (EUm N) (EVm N) (PVm N) XE XP one js lam =
      cond (onlyMaxV N.V (tok mx N.V lam) (EUm N) (EVm N)
        (ppessV N.V N.n (tok mx N.V lam) (PVm N))) 1 0 +
      ∑ rq ∈ range lam, cond (queryOnlyV N.V N.n (tok mx N.V lam) (tok mx N.V rq) (EUm N) (EVm N)
        (ppessV N.V N.n (tok mx N.V lam) (PVm N)) XE XP) 1 0 +
      ∑ rq ∈ range (lam + 1), ∑ pat ∈ range (2 ^ (N.n - 1)),
        (0 :: cntsV mx N.V N.n lam rq (usOf mx N lam) (ksOf mx N lam) XE XP one js).getD
          (inPat (N.n - 1) pat).length 0 := by
  unfold blockV
  rw [foldl_nat_add, foldl_add_map, List.map_map, sum_range_eq, sum_range_eq]
  simp only [Function.comp_apply]
  congr 1
  refine Finset.sum_congr rfl fun rq _ => ?_
  rw [withNonmaxV, foldl_add_map, Nat.zero_add, sum_range_eq]
  rfl

/-- **The count.** Every input counted is answered correctly. -/
theorem countV_le {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) (hV2 : 2 ≤ N.V) (hn2 : 2 ≤ N.n) (mx : Bool)
    {XE XP : List (List (Q × Q))} (hXE : BoundsE N XE) (hXP : BoundsP N XP) :
    countV mx N XE XP ≤ numCorrect g w (taskOf mx N.n N.V) := by
  classical
  have hsp : (taskOf mx N.n N.V).space = List.replicate N.n N.V := by cases mx <;> rfl
  have h1 : countV mx N XE XP ≤ ∑ lam ∈ range N.V, ∑ rq ∈ range (lam + 1),
      ∑ pat ∈ range (2 ^ (N.n - 1)), Ncls mx g w N lam rq pat := by
    unfold countV
    rw [foldl_nat_add, Nat.zero_add, sum_range_eq]
    refine Finset.sum_le_sum fun lam hlam => ?_
    have hlam' := mem_range.mp hlam
    rw [blockV_eq]
    have hb := fun rq (hrq : rq ∈ range (lam + 1)) pat (hpat : pat ∈ range (2 ^ (N.n - 1))) =>
      class_bound hg hw hV hn hV2 hn2 mx hXE hXP hlam' (Nat.lt_succ_iff.mp (mem_range.mp hrq))
        (mem_range.mp hpat)
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum fun rq hrq => Finset.sum_le_sum
      fun pat hpat => hb rq hrq pat hpat)
    simp only [Finset.sum_add_distrib]
    congr 1
    simp only [Finset.sum_ite_eq', mem_range, show 0 < 2 ^ (N.n - 1) by positivity, ↓reduceIte]
    rw [Finset.sum_range_succ, add_comm, ite_eq_left rfl]
    congr 1
    refine Finset.sum_congr rfl fun rq hrq => ?_
    rw [ite_eq_right (Nat.ne_of_lt (mem_range.mp hrq))]
  have h2 := classes_le (clsOf mx N.V N.n) (fun x => Correct g w (taskOf mx N.n N.V) x) N.V
    (2 ^ (N.n - 1)) (allInputs (List.replicate N.n N.V))
  unfold numCorrect
  rw [hsp]
  exact h1.trans h2

/-! ## Soundness -/

/-- **Soundness.** For a graph of the family and the label `max` (`mx`) or `min`, every count a run
    of the checker returns is at most the number of inputs the network answers correctly, for
    every weights and certificate. -/
theorem check_sound {g : Graph} (hg : IsAttn g) (mx : Bool) (w : Weights ℚ) (c : Cert) (n : ℕ)
    (cost : Cost)
    (h : CostM.exec (check Interp.counting mx g (taskOf mx g.positions g.values)) ⟨w, c⟩ =
      some (n, cost)) :
    n ≤ numCorrect g w (taskOf mx g.positions g.values) := by
  unfold CostM.exec at h
  have h0 := h
  simp only [check, Interp.counting_bind] at h
  obtain ⟨sE, c1, hsE, h⟩ := Runs.bind_some h
  obtain ⟨sP, c2, hsP, h⟩ := Runs.bind_some h
  obtain ⟨sQ, c3, hsQ, h⟩ := Runs.bind_some h
  obtain ⟨sK, c4, hsK, h⟩ := Runs.bind_some h
  obtain ⟨sV, c5, hsV, h⟩ := Runs.bind_some h
  obtain ⟨sO, c6, hsO, h⟩ := Runs.bind_some h
  obtain ⟨sU, c7, hsU, h⟩ := Runs.bind_some h
  obtain ⟨sC, c8, hsC, h⟩ := Runs.bind_some h
  obtain ⟨lE, c9, hlE, h⟩ := Runs.bind_some h
  obtain ⟨lP, c10, hlP, h⟩ := Runs.bind_some h
  obtain ⟨lQ, c11, hlQ, h⟩ := Runs.bind_some h
  obtain ⟨lK, c12, hlK, h⟩ := Runs.bind_some h
  obtain ⟨lV, c13, hlV, h⟩ := Runs.bind_some h
  obtain ⟨lO, c14, hlO, h⟩ := Runs.bind_some h
  obtain ⟨lU, c15, hlU, h⟩ := Runs.bind_some h
  obtain ⟨lC, c16, hlC, h⟩ := Runs.bind_some h
  obtain ⟨tE, hE, rfl⟩ := weightShape_some hsE
  obtain ⟨tP, hP, rfl⟩ := weightShape_some hsP
  obtain ⟨tQ, hQ, rfl⟩ := weightShape_some hsQ
  obtain ⟨tK, hK, rfl⟩ := weightShape_some hsK
  obtain ⟨tV, hV, rfl⟩ := weightShape_some hsV
  obtain ⟨tO, hO, rfl⟩ := weightShape_some hsO
  obtain ⟨tU, hU, rfl⟩ := weightShape_some hsU
  obtain ⟨tC, hC, rfl⟩ := weightShape_some hsC
  obtain ⟨tE', hE', rfl⟩ := weightSize_some hlE
  obtain ⟨tP', hP', rfl⟩ := weightSize_some hlP
  obtain ⟨tQ', hQ', rfl⟩ := weightSize_some hlQ
  obtain ⟨tK', hK', rfl⟩ := weightSize_some hlK
  obtain ⟨tV', hV', rfl⟩ := weightSize_some hlV
  obtain ⟨tO', hO', rfl⟩ := weightSize_some hlO
  obtain ⟨tU', hU', rfl⟩ := weightSize_some hlU
  obtain ⟨tC', hC', rfl⟩ := weightSize_some hlC
  have := hE.symm.trans hE'; cases this
  have := hP.symm.trans hP'; cases this
  have := hQ.symm.trans hQ'; cases this
  have := hK.symm.trans hK'; cases this
  have := hV.symm.trans hV'; cases this
  have := hO.symm.trans hO'; cases this
  have := hU.symm.trans hU'; cases this
  have := hC.symm.trans hC'; cases this
  by_cases hwf : (wellFormed g.values g.positions (tE.shape.getD 1 0) (tQ.shape.getD 1 0)
      [tE.shape, tP.shape, tQ.shape, tK.shape, tV.shape, tO.shape, tU.shape, tC.shape]
      [tE.data.size, tP.data.size, tQ.data.size, tK.data.size, tV.data.size, tO.data.size,
        tU.data.size, tC.data.size] && Nat.ble 2 g.values && Nat.ble 2 g.positions) = true
  · simp only [Bool.and_eq_true, Nat.ble_eq] at hwf
    obtain ⟨⟨hwf, hV2⟩, hn2⟩ := hwf
    have hw := WF_of_wellFormed hE hP hQ hK hV hO hU hC hwf
    obtain ⟨XE, XP, hXE, hXP, rfl⟩ :=
      sat_check (env := ⟨w, c⟩) mx (taskOf mx g.positions g.values) hw rfl rfl hV2 hn2 _ _ _ h0
    exact countV_le hg hw rfl rfl hV2 hn2 mx hXE hXP
  · simp only [hwf, Bool.false_eq_true, ↓reduceIte, Interp.counting_pure, CostM.run_pure,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Nat.zero_le _

/-- **Count and cost.** On well-formed weights with `V, n ≥ 2`, when `exp` accepts both parts of
    every score, the count is `countV` and the bill is `bill V n d h`. -/
theorem check_billed {N : Net} (mx : Bool) {g : Graph} (task : Task) {w : Weights ℚ}
    (hw : N.WF w) (hV : N.V = g.values) (hn : N.n = g.positions) (hV2 : 2 ≤ N.V)
    (hn2 : 2 ≤ N.n) (hexpE : ∀ q < N.V, ∀ t < N.V, (expInterval (N.SEf q t)).isSome)
    (hexpP : ∀ q < N.V, ∀ p < N.n, (expInterval (N.SPf q p)).isSome) (c : Cert) :
    CostM.billed (check Interp.counting mx g task) ⟨w, c⟩ =
      some (countV mx N (expMat N.V N.V N.SEf) (expMat N.V N.n N.SPf), bill N.V N.n N.d N.h) :=
  (runs_check (env := ⟨w, c⟩) mx task hw hV hn hV2 hn2 hexpE hexpP).billed

end GrossCubic
