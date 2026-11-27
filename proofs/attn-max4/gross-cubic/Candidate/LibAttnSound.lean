import Candidate.LibAttnCheck

/-!
# Soundness of entry 6

`check_sound`: for the family's graph, every count a run of the checker returns is at most the
number of inputs the network answers correctly, for every weights and certificate.

A run that succeeds returns the count over the table of verdicts (`sat_check`). An input is
counted if the verdict of its class is true; the class's sum then lower-bounds the input's own sum
`Σ_p K(q, x_p, p, ℓ)`, which is therefore positive (`verdict_pos`): the label's positions and the
query enter exactly, every other position through a running minimum over ranks up to the class's
largest. `correct_of_bound` (Family.lean) turns the positive sum into a correct answer
(`verdict_correct`).
-/

namespace AttnClasses

open CompactCheck Common Finset

/-! ## Ranks -/

theorem tok_lt {mx : Bool} {V ρ : ℕ} (h : ρ < V) : tok mx V ρ < V := by
  unfold tok; split <;> omega

theorem tok_tok {mx : Bool} {V t : ℕ} (h : t < V) : tok mx V (tok mx V t) = t := by
  unfold tok; split <;> omega

/-- The task of the label `max` or `min`. -/
def taskOf (mx : Bool) (n V : ℕ) : Task := if mx then maxTask n V else minTask n V

theorem foldl_max_rev {V : ℕ} :
    ∀ (x : List ℕ) (acc : ℕ), acc ≤ V - 1 → (∀ t ∈ x, t < V) →
    (x.map (V - 1 - ·)).foldl max (V - 1 - acc) = V - 1 - x.foldl min acc
  | [], _, _, _ => rfl
  | t :: x, acc, hacc, hx => by
    have ht := hx t List.mem_cons_self
    simp only [List.map_cons, List.foldl_cons]
    have : max (V - 1 - acc) (V - 1 - t) = V - 1 - min acc t := by omega
    rw [this]
    exact foldl_max_rev x (min acc t) (by omega) fun u hu => hx u (List.mem_cons_of_mem _ hu)

theorem foldl_min_le : ∀ (x : List ℕ) (acc : ℕ), x.foldl min acc ≤ acc
  | [], _ => le_rfl
  | t :: x, acc => le_trans (foldl_min_le x (min acc t)) (min_le_left _ _)

/-- The label is the token of the largest rank. -/
theorem label_eq {mx : Bool} {n V : ℕ} {x : Input} (hxV : ∀ t ∈ x, t < V) :
    (taskOf mx n V).label x = tok mx V ((x.map (tok mx V)).foldl max 0) := by
  cases mx with
  | true =>
    have : tok true V = fun ρ => ρ := funext fun _ => rfl
    simp [taskOf, maxTask, this, tok]
  | false =>
    have : tok false V = (V - 1 - ·) := funext fun _ => rfl
    rw [this]
    simp only [taskOf, Bool.false_eq_true, ↓reduceIte, minTask]
    have hV : 0 < V ∨ x = [] := by
      rcases x with _ | ⟨t, x⟩
      · exact Or.inr rfl
      · exact Or.inl (by have := hxV t List.mem_cons_self; omega)
    rcases hV with hV | rfl
    · have h := foldl_max_rev x (V - 1) le_rfl hxV
      rw [Nat.sub_self] at h
      have hm := foldl_min_le x (V - 1)
      rw [h]
      omega
    · simp

theorem foldl_max_choice : ∀ (l : List ℕ) (a : ℕ), l.foldl max a = a ∨ l.foldl max a ∈ l
  | [], _ => Or.inl rfl
  | b :: l, a => by
    simp only [List.foldl_cons]
    rcases foldl_max_choice l (max a b) with h | h
    · rw [h]
      rcases Nat.le_total a b with hab | hab
      · right; rw [max_eq_right hab]; exact List.mem_cons_self
      · left; exact max_eq_left hab
    · right; exact List.mem_cons_of_mem _ h

/-- The largest rank is one of them. -/
theorem foldl_max_mem {l : List ℕ} (hl : l ≠ []) : l.foldl max 0 ∈ l := by
  obtain ⟨a, l, rfl⟩ : ∃ a l', l = a :: l' := List.exists_cons_of_ne_nil hl
  simp only [List.foldl_cons, Nat.zero_max]
  rcases foldl_max_choice l a with h | h
  · rw [h]; exact List.mem_cons_self
  · exact List.mem_cons_of_mem _ h

theorem le_foldl_max_init : ∀ (x : List ℕ) (a : ℕ), a ≤ x.foldl max a
  | [], _ => le_rfl
  | t :: x, a => le_trans (le_max_left a t) (le_foldl_max_init x (max a t))

/-- Every rank is at most the largest. -/
theorem le_foldl_max : ∀ {x : List ℕ} {t : ℕ} (a : ℕ), t ∈ x → t ≤ x.foldl max a
  | [], _, _, h => absurd h List.not_mem_nil
  | u :: x, t, a, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact le_trans (le_max_right a t) (le_foldl_max_init x _)
    · exact le_foldl_max (max a u) h

/-- The inputs of `k` positions of `V` tokens. -/
theorem mem_allInputs_replicate : ∀ {k V : ℕ} {x : Input},
    x ∈ allInputs (List.replicate k V) ↔ x.length = k ∧ ∀ t ∈ x, t < V
  | 0, V, x => by
    simp only [List.replicate_zero, allInputs, List.mem_singleton]
    constructor
    · rintro rfl; simp
    · rintro ⟨h, -⟩; exact List.eq_nil_of_length_eq_zero h
  | k + 1, V, x => by
    simp only [List.replicate_succ, allInputs, List.mem_flatMap, List.mem_range, List.mem_map]
    constructor
    · rintro ⟨t, ht, y, hy, rfl⟩
      obtain ⟨hyl, hyV⟩ := mem_allInputs_replicate.mp hy
      refine ⟨by simp [hyl], fun u hu => ?_⟩
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ht
      · exact hyV u hu
    · rintro ⟨hl, hV⟩
      cases x with
      | nil => simp at hl
      | cons t y =>
        refine ⟨t, hV t List.mem_cons_self, y, ?_, rfl⟩
        exact mem_allInputs_replicate.mpr
          ⟨by simpa using hl, fun u hu => hV u (List.mem_cons_of_mem _ hu)⟩

/-! ## Patterns as bits -/

/-- The number whose bit `p` is entry `p` of `bits`, as `verdict` builds it. -/
def patOf (bits : List Bool) : ℕ := bits.foldr (fun b a => 2 * a + cond b 1 0) 0

theorem testBit_patOf : ∀ (bits : List Bool) (p : ℕ), (patOf bits).testBit p = bits.getD p false
  | [], p => by simp [patOf]
  | b :: bits, 0 => by
    cases b <;> simp [patOf, Nat.testBit_zero, Nat.mul_mod_right]
  | b :: bits, p + 1 => by
    have h : (2 * patOf bits + cond b 1 0) / 2 = patOf bits := by
      cases b <;> simp only [Bool.cond_false, Bool.cond_true] <;> omega
    rw [show patOf (b :: bits) = 2 * patOf bits + cond b 1 0 from rfl, Nat.testBit_succ, h,
      testBit_patOf bits p, List.getD_cons_succ]

theorem patOf_lt : ∀ (bits : List Bool), patOf bits < 2 ^ bits.length
  | [] => by simp [patOf]
  | b :: bits => by
    have := patOf_lt bits
    rw [show patOf (b :: bits) = 2 * patOf bits + cond b 1 0 from rfl, List.length_cons, pow_succ]
    cases b <;> simp <;> omega

/-! ## Sums of lists -/

theorem sum_filter_split {γ : Type} (f : γ → ℚ) (q : γ → Bool) :
    ∀ l : List γ, (l.map f).sum = ((l.filter q).map f).sum + ((l.filter fun a => !q a).map f).sum
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, sum_filter_split f q l]
    cases h : q a <;> simp [h] <;> ring

theorem foldl_val {γ : Type} (F : γ → ℚ) (l : List γ) (b : Q) :
    (l.foldl (fun s p => (⟨s.val + F p⟩ : Q)) b).val = b.val + (l.map F).sum := by
  obtain ⟨a⟩ := b
  exact foldl_acc F l a

theorem sum_le_sum_of_le {γ : Type} {f g : γ → ℚ} :
    ∀ {l : List γ}, (∀ a ∈ l, f a ≤ g a) →
    (l.map f).sum ≤ (l.map g).sum
  | [], _ => by simp
  | a :: l, h => by
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h a List.mem_cons_self)
      (sum_le_sum_of_le fun b hb => h b (List.mem_cons_of_mem _ hb))

theorem getD_map_range {γ : Type} {m i : ℕ} (f : ℕ → γ) (hi : i < m) (z : γ) :
    ((List.range m).map f).getD i z = f i := by
  simp [List.getD_eq_getElem?_getD, hi]

/-! ## A class that passes bounds its inputs -/

/-- **The class's sum bounds the input's.** If the verdict of the class of a valid input `x` is
    true, then `Σ_p K(q, x_p, p, ℓ) > 0`, with `q` the query token and `ℓ` the token of the
    largest rank. -/
theorem verdict_pos (mx : Bool) {V n : ℕ} (hn : 0 < n) (X : List (List (List (Q × Q))))
    (Dd : List (List Q)) (G : List (List (List Q))) {x : Input} (hx : x.length = n)
    (hxV : ∀ t ∈ x, t < V) (hv : verdict Interp.counting mx V n (vtV mx V n X Dd G) x = true) :
    0 < ((List.range n).map fun p => (kV X Dd G (x.getD (n - 1) 0) (x.getD p 0) p
      (tok mx V ((x.map (tok mx V)).foldl max 0))).val).sum := by
  set rs := x.map (tok mx V) with hrs
  set lam := rs.foldl max 0 with hlam
  have hrsl : rs.length = n := by simp [hrs, hx]
  have hrank : ∀ p < n, rs.getD p 0 = tok mx V (x.getD p 0) := fun p hp => by
    simp [hrs, List.getD_eq_getElem?_getD, hx, hp]
  have hxp : ∀ p < n, x.getD p 0 < V := fun p hp => hxV _ (tk_mem (by omega))
  have hrsV : ∀ r ∈ rs, r < V := by
    intro r hr
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hr
    exact tok_lt (hxV t ht)
  have hle : ∀ r ∈ rs, r ≤ lam := fun r hr => le_foldl_max 0 hr
  have hne : rs ≠ [] := by intro h; rw [h] at hrsl; simp at hrsl; omega
  have hlamm : lam ∈ rs := foldl_max_mem hne
  have hlamV : lam < V := hrsV _ hlamm
  have hgetle : ∀ p < n, rs.getD p 0 ≤ lam := fun p hp => hle _ (by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
    exact List.getElem_mem _)
  -- the query
  have hQ : n - 1 < n := by omega
  have hlast : rs.getLastD 0 = rs.getD (n - 1) 0 := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD, hrsl]
  set ρq := rs.getLastD 0 with hρq
  have hρqV : ρq < V := by rw [hlast, hrank _ hQ]; exact tok_lt (hxp _ hQ)
  have hρqle : ρq ≤ lam := by rw [hlast]; exact hgetle _ hQ
  have htq : tok mx V ρq = x.getD (n - 1) 0 := by rw [hlast, hrank _ hQ, tok_tok (hxp _ hQ)]
  -- the pattern
  set os := rs.take (n - 1) with hos
  have hosg : ∀ p < n - 1, os.getD p 0 = rs.getD p 0 := fun p hp => by
    simp [hos, List.getD_eq_getElem?_getD, hp]
  set bits := (List.range (n - 1)).map fun p => os.getD p 0 == lam with hbits
  have hbit : ∀ p < n - 1, (patOf bits).testBit p = (os.getD p 0 == lam) := fun p hp => by
    rw [testBit_patOf, hbits, getD_map_range _ hp]
  have hpat : patOf bits < 2 ^ (n - 1) := by
    have := patOf_lt bits
    simpa [hbits] using this
  -- unfold the verdict
  unfold verdict at hv
  dsimp only at hv
  change ((((vtV mx V n X Dd G).getD ρq []).getD lam []).getD (patOf bits) []).getD
    ((os.filter fun r => r ≠ lam).foldl max 0) false = true at hv
  rw [vtV, getD_map_range _ hρqV, getD_map_range _ hlamV, ite_eq_left hρqle, blockVal, patternsV,
    getD_map_range _ hpat] at hv
  -- the positions holding the label, and the others
  set Pb := (List.range (n - 1)).filter (patOf bits).testBit with hPbdef
  set Rb := (List.range (n - 1)).filter (fun p => !(patOf bits).testBit p) with hRbdef
  have hPb : ∀ p, p ∈ Pb ↔ p < n - 1 ∧ os.getD p 0 = lam := fun p => by
    rw [hPbdef, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hp, hb⟩; exact ⟨hp, by rw [hbit p hp] at hb; simpa using hb⟩
    · rintro ⟨hp, he⟩; exact ⟨hp, by rw [hbit p hp]; simpa using he⟩
  have hRb : ∀ p, p ∈ Rb ↔ p < n - 1 ∧ os.getD p 0 ≠ lam := fun p => by
    rw [hRbdef, List.mem_filter, List.mem_range]
    constructor
    · rintro ⟨hp, hb⟩; exact ⟨hp, by rw [hbit p hp] at hb; simpa using hb⟩
    · rintro ⟨hp, he⟩; exact ⟨hp, by rw [hbit p hp]; simpa using he⟩
  -- the label is held at the query or at another position
  have hPne : ¬(ρq ≠ lam ∧ Pb = []) := by
    rintro ⟨h1, h2⟩
    obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hlamm
    have hpn : p < n := by rw [← hrsl]; exact hp
    have hgp : rs.getD p 0 = lam := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some, hpe]
    by_cases hpq : p = n - 1
    · subst hpq; exact h1 (by rw [hlast, hgp])
    · have : p ∈ Pb := (hPb p).mpr ⟨by omega, by rw [hosg p (by omega), hgp]⟩
      rw [h2] at this
      exact absurd this (List.not_mem_nil)
  rw [ite_eq_right hPne] at hv
  simp only [htq] at hv
  -- the input's own sum
  set κ : ℕ → ℚ := fun p => (kV X Dd G (x.getD (n - 1) 0) (x.getD p 0) p (tok mx V lam)).val
    with hκ
  have hxl : ∀ p ∈ Pb, x.getD p 0 = tok mx V lam := fun p hp => by
    obtain ⟨hp1, hp2⟩ := (hPb p).mp hp
    rw [hosg p hp1, hrank p (by omega)] at hp2
    rw [← hp2, tok_tok (hxp p (by omega))]
  have hsum : ((List.range n).map κ).sum = κ (n - 1) + ((Pb.map κ).sum + (Rb.map κ).sum) := by
    have hr : List.range n = List.range (n - 1) ++ [n - 1] := by
      rw [← List.range_succ]; congr 1; omega
    rw [hr, List.map_append, List.sum_append, sum_filter_split κ (patOf bits).testBit]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    ring
  have hbase : (Pb.foldl (fun s p => (⟨s.val + ((((List.range (n - 1)).map fun p =>
      kV X Dd G (x.getD (n - 1) 0) (tok mx V lam) p (tok mx V lam)).getD p ⟨0⟩).val)⟩ : Q))
      (kV X Dd G (x.getD (n - 1) 0) (x.getD (n - 1) 0) (n - 1) (tok mx V lam))).val =
      κ (n - 1) + (Pb.map κ).sum := by
    rw [foldl_val]
    congr 1
    refine congrArg List.sum (List.map_congr_left fun p hp => ?_)
    have hp1 := ((hPb p).mp hp).1
    rw [getD_map_range _ hp1, hκ]
    simp only
    rw [hxl p hp]
  by_cases hR : Rb = []
  · -- no position is left: the class is one input up to the label's positions
    rw [ite_eq_left hR] at hv
    have hR0 : (os.filter fun r => r ≠ lam) = [] := by
      rw [List.filter_eq_nil_iff]
      intro r hr
      obtain ⟨p, hp, hpe⟩ := List.mem_iff_getElem.mp hr
      have hpl : p < n - 1 := by simpa [hos, hrsl] using hp
      have hg : os.getD p 0 = r := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some, hpe]
      by_contra hne'
      have : p ∈ Rb := (hRb p).mpr ⟨hpl, by rw [hg]; simpa using hne'⟩
      rw [hR] at this
      exact absurd this List.not_mem_nil
    rw [hR0] at hv
    simp only [List.foldl_nil, List.getD_cons_zero, decide_eq_true_eq] at hv
    rw [hbase] at hv
    rw [hsum, hR]
    simpa using hv
  · rw [ite_eq_right hR] at hv
    obtain ⟨p0, hp0⟩ := List.exists_mem_of_ne_nil Rb hR
    obtain ⟨hp01, hp02⟩ := (hRb p0).mp hp0
    have hRne : (os.filter fun r => r ≠ lam) ≠ [] := by
      intro h
      have : os.getD p0 0 ∈ os.filter fun r => r ≠ lam := by
        rw [List.mem_filter]
        refine ⟨?_, by simpa using hp02⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hos, hrsl]; omega),
          Option.getD_some]
        exact List.getElem_mem _
      rw [h] at this
      exact absurd this List.not_mem_nil
    set ρ' := (os.filter fun r => r ≠ lam).foldl max 0 with hρ'
    have hρ'm := foldl_max_mem hRne
    rw [← hρ'] at hρ'm
    obtain ⟨hρ'os, hρ'ne⟩ := List.mem_filter.mp hρ'm
    have hρ'lt : ρ' < lam := by
      have := hle ρ' (List.mem_of_mem_take hρ'os)
      have : ρ' ≠ lam := by simpa using hρ'ne
      omega
    rw [getD_map_range _ hρ'lt] at hv
    simp only [decide_eq_true_eq] at hv
    rw [foldl_val, hbase] at hv
    -- the rows of minima are there: the query holds the label, or there are three positions
    have hcond : ρq = lam ∨ 3 ≤ n := by
      by_cases hq : ρq = lam
      · exact Or.inl hq
      · right
        have hPne' : Pb ≠ [] := fun h => hPne ⟨hq, h⟩
        obtain ⟨p1, hp1⟩ := List.exists_mem_of_ne_nil Pb hPne'
        obtain ⟨hp11, hp12⟩ := (hPb p1).mp hp1
        have : p1 ≠ p0 := fun h => hp02 (h ▸ hp12)
        omega
    rw [ite_eq_left hcond] at hv
    have hkp : ∀ p ∈ Rb, ((((List.range (n - 1)).map fun p => scanVal min ((List.range lam).map
        fun ρ => kV X Dd G (x.getD (n - 1) 0) (tok mx V ρ) p (tok mx V lam))).getD p []).getD ρ'
        ⟨0⟩).val ≤ κ p := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := (hRb p).mp hp
      rw [getD_map_range _ hp1]
      have hj : rs.getD p 0 ≤ ρ' := by
        refine le_foldl_max 0 (List.mem_filter.mpr ⟨?_, by
          rw [← hosg p hp1]; simpa using hp2⟩)
        rw [← hosg p hp1, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp [hos, hrsl]; omega), Option.getD_some]
        exact List.getElem_mem _
      have h1 := scanVal_min_le ((List.range lam).map
        fun ρ => kV X Dd G (x.getD (n - 1) 0) (tok mx V ρ) p (tok mx V lam))
        (i := ρ') (by simpa using hρ'lt) hj
      rw [getD_map_range _ (by omega), hrank p (by omega), tok_tok (hxp p (by omega))] at h1
      exact h1
    have hle' := sum_le_sum_of_le hkp
    rw [hsum]
    linarith

/-! ## From the bound to a correct answer -/

/-- `min (lo H) (hi H) ≤ e H` for `lo ≤ e ≤ hi`, whatever the sign of `H`. -/
theorem min_mul_le {lo hi H : ℚ} {e : ℝ} (hlo : (lo : ℝ) ≤ e) (hhi : e ≤ (hi : ℝ)) :
    ((min (lo * H) (hi * H) : ℚ) : ℝ) ≤ e * H := by
  push_cast
  rcases le_or_gt 0 (H : ℝ) with hH | hH
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right hlo hH)
  · exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right hhi hH.le)

/-- **One input.** If the verdict of the class of a valid input is true, the network answers it
    correctly. -/
theorem verdict_correct {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) (mx : Bool) {X : List (List (List (Q × Q)))}
    (hX : ∀ q < N.V, ∀ t < N.V, ∀ p < N.n,
      expInterval (N.SEf q t + N.SPf q p) =
        some ((((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).1.val,
          (((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).2.val))
    {x : Input} (hx : x.length = N.n) (hxV : ∀ t ∈ x, t < N.V)
    (hv : verdict Interp.counting mx N.V N.n (vtV mx N.V N.n X N.DdTab N.GTab) x = true) :
    Correct g w (taskOf mx N.n N.V) x := by
  have hn0 : 0 < N.n := by have := hg.2.2.1; omega
  have hpos := verdict_pos mx hn0 X N.DdTab N.GTab hx hxV hv
  set ℓ := tok mx N.V ((x.map (tok mx N.V)).foldl max 0) with hℓ
  have hlab : (taskOf mx N.n N.V).label x = ℓ := label_eq hxV
  have hxp : ∀ p < N.n, x.getD p 0 < N.V := fun p hp => hxV _ (tk_mem (by omega))
  have hQ : N.n - 1 < N.n := by omega
  have hq := hxp _ hQ
  have hℓV : ℓ < N.V := by
    rw [hℓ]
    refine tok_lt ?_
    have hne : x.map (tok mx N.V) ≠ [] := by
      intro h; rw [List.map_eq_nil_iff] at h; subst h; simp at hx; omega
    have := foldl_max_mem hne
    obtain ⟨t, ht, he⟩ := List.mem_map.mp this
    rw [← he]; exact tok_lt (hxV t ht)
  refine correct_of_bound hg hw hV hn hx hxV (by rw [hlab]; exact hℓV)
    (μ := (((N.DdTab.getD (x.getD (N.n - 1) 0) []).getD ℓ ⟨0⟩).val : ℝ))
    (G := fun p => ((((N.GTab.getD (x.getD p 0) []).getD p []).getD ℓ ⟨0⟩).val : ℝ))
    (κ := fun p => ((kV X N.DdTab N.GTab (x.getD (N.n - 1) 0) (x.getD p 0) p ℓ).val : ℝ))
    ?_ ?_ ?_ ?_
  · intro j hj hne
    rw [hlab] at hne ⊢
    rw [Net.DdTab, getD_map_range _ hq]
    have := margVal_le (vec N.V (N.D (x.getD (N.n - 1) 0))) (l := ℓ) (j := j)
      (by rw [length_vec]; exact hℓV) (by rw [length_vec]; exact hj) hne
    rw [getD_vec hℓV, getD_vec hj] at this
    exact_mod_cast this
  · intro p hp j hj hne
    rw [hlab] at hne ⊢
    rw [Net.GTab, getD_map_range _ (hxp p hp), getD_map_range _ hp]
    have := margVal_le (vec N.V (N.O (x.getD p 0) p)) (l := ℓ) (j := j)
      (by rw [length_vec]; exact hℓV) (by rw [length_vec]; exact hj) hne
    rw [getD_vec hℓV, getD_vec hj] at this
    exact_mod_cast this
  · intro p hp
    have hX' := hX _ hq _ (hxp p hp) p hp
    obtain ⟨hlo, hhi⟩ := expInterval_spec hX'
    have hS : N.SEf (x.getD (N.n - 1) 0) (x.getD p 0) + N.SPf (x.getD (N.n - 1) 0) p =
        N.S (x.getD (N.n - 1) 0) (x.getD p 0) p := N.score_eq _ _ _
    rw [hS] at hlo hhi
    simp only [kV]
    have := min_mul_le (H := ((N.DdTab.getD (x.getD (N.n - 1) 0) []).getD ℓ ⟨0⟩).val +
      (((N.GTab.getD (x.getD p 0) []).getD p []).getD ℓ ⟨0⟩).val) hlo hhi
    push_cast at this ⊢
    exact this
  · have : (0 : ℝ) < (((List.range N.n).map fun p =>
        (kV X N.DdTab N.GTab (x.getD (N.n - 1) 0) (x.getD p 0) p ℓ).val).sum : ℚ) := by
      exact_mod_cast hpos
    rw [sum_range_eq] at this
    push_cast at this
    exact this

theorem foldl_count {γ : Type} (f : γ → Bool) : ∀ (l : List γ) (a : ℕ),
    l.foldl (fun a x => Nat.add a (cond (f x) 1 0)) a = a + l.countP f
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_count f l, List.countP_cons]
    cases f x <;> simp
    omega

/-- **The count.** Every input counted is answered correctly. -/
theorem countOf_le {g : Graph} (hg : IsAttn g) {w : Weights ℚ} {N : Net} (hw : N.WF w)
    (hV : N.V = g.values) (hn : N.n = g.positions) (mx : Bool) {X : List (List (List (Q × Q)))}
    (hX : ∀ q < N.V, ∀ t < N.V, ∀ p < N.n,
      expInterval (N.SEf q t + N.SPf q p) =
        some ((((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).1.val,
          (((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).2.val)) :
    countOf mx N.V N.n (taskOf mx N.n N.V) (vtV mx N.V N.n X N.DdTab N.GTab) ≤
      numCorrect g w (taskOf mx N.n N.V) := by
  classical
  unfold countOf numCorrect
  rw [foldl_count, Nat.zero_add]
  refine List.countP_mono_left fun x hx hv => ?_
  have hsp : (taskOf mx N.n N.V).space = List.replicate N.n N.V := by
    cases mx <;> rfl
  rw [hsp] at hx
  obtain ⟨hlen, hxV⟩ := mem_allInputs_replicate.mp hx
  exact decide_eq_true (verdict_correct hg hw hV hn mx hX hlen hxV hv)

/-! ## Soundness -/

/-- The checker's test of the shapes and lengths gives the family's weights. -/
theorem WF_of_wellFormed {w : Weights ℚ} {V n d h : ℕ} {tE tP tQ tK tV tO tU tC : Tensor ℚ}
    (hE : List.lookup nE w = some tE) (hP : List.lookup nP w = some tP)
    (hQ : List.lookup nQ w = some tQ) (hK : List.lookup nK w = some tK)
    (hV : List.lookup nV w = some tV) (hO : List.lookup nO w = some tO)
    (hU : List.lookup nU w = some tU) (hC : List.lookup nC w = some tC)
    (hwf : wellFormed V n d h [tE.shape, tP.shape, tQ.shape, tK.shape, tV.shape, tO.shape,
      tU.shape, tC.shape] [tE.data.size, tP.data.size, tQ.data.size, tK.data.size, tV.data.size,
      tO.data.size, tU.data.size, tC.data.size] = true) :
    (⟨V, n, d, h, tE, tP, tQ, tK, tV, tO, tU, tC⟩ : Net).WF w := by
  unfold wellFormed at hwf
  simp only [Bool.and_eq_true, beq_iff_eq, List.cons.injEq, and_true] at hwf
  obtain ⟨⟨hEs, hPs, hQs, hKs, hVs, hOs, hUs, hCs⟩, hEn, hPn, hQn, hKn, hVn, hOn, hUn,
    hCn⟩ := hwf
  exact ⟨hE, hEs, hEn, hP, hPs, hPn, hQ, hQs, hQn, hK, hKs, hKn, hV, hVs, hVn, hO, hOs, hOn,
    hU, hUs, hUn, hC, hCs, hCn⟩

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
  by_cases hwf : wellFormed g.values g.positions (tE.shape.getD 1 0) (tQ.shape.getD 1 0)
      [tE.shape, tP.shape, tQ.shape, tK.shape, tV.shape, tO.shape, tU.shape, tC.shape]
      [tE.data.size, tP.data.size, tQ.data.size, tK.data.size, tV.data.size, tO.data.size,
        tU.data.size, tC.data.size] = true
  · have hw := WF_of_wellFormed hE hP hQ hK hV hO hU hC hwf
    obtain ⟨X, hX, rfl⟩ :=
      sat_check (env := ⟨w, c⟩) mx (taskOf mx g.positions g.values) hw rfl rfl
      (by have := hg.2.2.1; simpa using this) _ _ _ h0
    exact countOf_le hg hw rfl rfl mx hX
  · simp only [hwf, Bool.false_eq_true, ↓reduceIte, Interp.counting_pure, CostM.run_pure,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Nat.zero_le _

/-- **Count and cost.** On well-formed weights, when `exp` accepts every score, the count is the
    number of inputs whose class passes and the bill is `bill V n d h`. -/
theorem check_billed {N : Net} (mx : Bool) {g : Graph} (task : Task) {w : Weights ℚ}
    (hw : N.WF w) (hV : N.V = g.values) (hn : N.n = g.positions) (hn0 : 0 < N.n)
    (hexp : ∀ q < N.V, ∀ t < N.V, ∀ p < N.n, (expInterval (N.SEf q t + N.SPf q p)).isSome)
    (c : Cert) :
    CostM.billed (check Interp.counting mx g task) ⟨w, c⟩ =
      some (countOf mx N.V N.n task (vtV mx N.V N.n
        (expTab N.V N.n fun q t p => N.SEf q t + N.SPf q p) N.DdTab N.GTab),
        bill N.V N.n N.d N.h) :=
  (runs_check (env := ⟨w, c⟩) mx task hw hV hn hn0 hexp).billed

end AttnClasses
