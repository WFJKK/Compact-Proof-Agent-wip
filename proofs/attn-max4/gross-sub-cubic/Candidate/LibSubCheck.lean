import Candidate.LibSubSound

/-!
# The checker of entry 9, run

`rs_check`: on well-formed weights with `V, n ≥ 2` and a certificate with the numbers the method
needs, every run that succeeds returns a count of at most the inputs the network answers
correctly, and is billed `subBill err eu gap V n d h`. `check_sound` covers every weights and
certificate (the checker refuses, with count 0, those it cannot read).
-/

namespace GrossSub

open CompactCheck Common AttnClasses GrossCubic Finset

variable {env : Env}

/-! ## Maps over the rows of a table -/

theorem rs_mapM_loop_map {α β γ : Type} {f : γ → Interp.counting.M β} {h : α → γ}
    {P : α → β → Prop} {c : α → ℕ} : ∀ (l : List α) (bs : List β),
      (∀ a ∈ l, RS (f (h a)) env (P a) (c a)) →
      RS (@List.mapM.loop Interp.counting.M (instMonadInterp Interp.counting) γ β f (l.map h) bs)
        env (fun out => ∃ ys, out = bs.reverse ++ ys ∧ List.Forall₂ P l ys) (l.map c).sum
  | [], bs, _ => (RS.pure ⟨[], by simp, List.Forall₂.nil⟩).congr (by simp)
  | a :: l, bs, hh => by
    simp only [List.map_cons, List.mapM.loop, Interp.counting_bind]
    refine (RS.bind (m := (l.map c).sum) (hh a List.mem_cons_self) fun b hb => ?_).congr
      (by simp)
    refine (rs_mapM_loop_map l (b :: bs) fun a' ha' => hh a' (List.mem_cons_of_mem _ ha')).mono ?_
    rintro out ⟨ys, rfl, hys⟩
    exact ⟨b :: ys, by simp, List.Forall₂.cons hb hys⟩

/-- A map over the rows of `mat m k F`, row `i` with the property `P i`. -/
theorem rs_mapM_mat {β : Type} {f : List Q → Interp.counting.M β} {P : ℕ → β → Prop} {c : ℕ}
    (m k : ℕ) (F : ℕ → ℕ → ℚ) (hh : ∀ i < m, RS (f (vec k (F i))) env (P i) c) :
    RS (@List.mapM Interp.counting.M (instMonadInterp Interp.counting) (List Q) β f
      (mat m k F)) env (fun out => List.Forall₂ P (List.range m) out) (m * c) := by
  rw [mat_eq]
  refine ((rs_mapM_loop_map (c := fun _ => c) (List.range m) [] fun i hi =>
    hh i (List.mem_range.mp hi)).mono ?_).congr (by rw [sum_map_const', List.length_range])
  rintro out ⟨ys, rfl, hys⟩
  simpa using hys

theorem runs_mat_vadd (m k : ℕ) (A : ℕ → ℕ → ℚ) (b : ℕ → ℚ) :
    Runs ((mat m k A).mapM (vadd Interp.counting · (vec k b))) env
      (mat m k fun i a => A i a + b a) (m * k) :=
  runs_mapM_mat m k A fun i _ => runs_vadd k (A i) b

theorem runs_mat_vsub (m k : ℕ) (A : ℕ → ℕ → ℚ) (b : ℕ → ℚ) :
    Runs ((mat m k A).mapM (vsub Interp.counting · (vec k b))) env
      (mat m k fun i a => A i a - b a) (m * k) :=
  runs_mapM_mat m k A fun i _ => runs_vsub k (A i) b

/-! ## The bill -/

/-- **The bill** of entry 9 on a network with `V` tokens, `n` positions, width `d` and head size
    `h`, for the methods `err`, `eu` and the plan `gap`: the tables, step 1, the sorted positional
    errors, the paths, the direct path, the running extrema, and the blocks. -/
def subBill (err eu : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (V n d h : ℕ) : ℕ :=
  h * d + (V * d + (V * d + (n * d + (d * d * h + (errCost err V d h + (h * n * d + (d * n * h +
    (V * n * d + (V * sortedCost n + (d * d * h + (d * V * d + (V * V * d + (n * V * d + (V * V * d
    + (eupuCost eu V d + (V * ((V - 1) + ((V - 1) + 0)) + (V * (2 * (V - 1) + 1) + ((V - 1) + (1 +
    (((List.range V).map (subBlockCost V n gap)).sum + (0)))))))))))))))))))))

/-- The number of certificate numbers the checker needs. -/
def certNeed (err V n d h : ℕ) : ℕ := 2 * d + 2 * (V * n) + errCertLen err V d h

/-! ## The run -/

/-- The checker's test of the weights and the certificate passes on the family's weights with
    `V, n ≥ 2` and a certificate with the numbers the method needs. -/
theorem guard_sub {N : Net} {w : Weights ℚ} (hw : N.WF w) (hV2 : 2 ≤ N.V) (hn2 : 2 ≤ N.n)
    {err cs : ℕ} (hcs : certNeed err N.V N.n N.d N.h ≤ cs) :
    (wellFormed N.V N.n N.d N.h
      [N.E.shape, N.P.shape, N.WQ.shape, N.WK.shape, N.WV.shape, N.WO.shape, N.U.shape, N.C.shape]
      [N.E.data.size, N.P.data.size, N.WQ.data.size, N.WK.data.size, N.WV.data.size,
        N.WO.data.size, N.U.data.size, N.C.data.size] && Nat.ble 2 N.V && Nat.ble 2 N.n &&
      Nat.ble (2 * N.d + 2 * (N.V * N.n) + errCertLen err N.V N.d N.h) cs) = true := by
  rw [guard_of_WF hw hV2 hn2, Bool.true_and, Nat.ble_eq]
  exact hcs

/-- **The run.** On well-formed weights with `V, n ≥ 2` and a certificate with the numbers the
    method needs, every run that succeeds returns at most the number of inputs the network answers
    correctly, and is billed `subBill`. -/
theorem rs_check {N : Net} (mx : Bool) (err eu : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) {g : Graph}
    (hg : IsAttn g) (task : Task) (hw : N.WF env.weights) (hV : N.V = g.values)
    (hn : N.n = g.positions) (hV2 : 2 ≤ N.V) (hn2 : 2 ≤ N.n)
    (hcs : certNeed err N.V N.n N.d N.h ≤ env.cert.size) :
    RS (check Interp.counting mx err eu gap g task) env
      (fun count => count ≤ numCorrect g env.weights (taskOf mx N.n N.V))
      (subBill err eu gap N.V N.n N.d N.h) := by
  have hQ : N.n - 1 < N.n := by omega
  have hcs' := hcs
  unfold certNeed errCertLen at hcs'
  unfold check
  refine RS.bind0 (runs_weightShape hw.hE) ?_
  refine RS.bind0 (runs_weightShape hw.hP) ?_
  refine RS.bind0 (runs_weightShape hw.hQ) ?_
  refine RS.bind0 (runs_weightShape hw.hK) ?_
  refine RS.bind0 (runs_weightShape hw.hV) ?_
  refine RS.bind0 (runs_weightShape hw.hO) ?_
  refine RS.bind0 (runs_weightShape hw.hU) ?_
  refine RS.bind0 (runs_weightShape hw.hC) ?_
  refine RS.bind0 (runs_weightSize hw.hE) ?_
  refine RS.bind0 (runs_weightSize hw.hP) ?_
  refine RS.bind0 (runs_weightSize hw.hQ) ?_
  refine RS.bind0 (runs_weightSize hw.hK) ?_
  refine RS.bind0 (runs_weightSize hw.hV) ?_
  refine RS.bind0 (runs_weightSize hw.hO) ?_
  refine RS.bind0 (runs_weightSize hw.hU) ?_
  refine RS.bind0 (runs_weightSize hw.hC) ?_
  refine RS.bind0 runs_certSize ?_
  dsimp only
  rw [← hV, ← hn, hw.hEs, hw.hQs]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [← hw.hEs, ← hw.hQs, ite_eq_left (guard_sub hw hV2 hn2 hcs)]
  refine RS.bind0 (runs_rows hw.hE hw.hEn) ?_
  refine RS.bind0 (runs_rows hw.hP hw.hPn) ?_
  refine RS.bind0 (runs_weight hw.hC (by rw [hw.hCn]; omega)) ?_
  rstep (runs_Qc hw)
  refine RS.bind0 (runs_cols hw.hK hw.hKn) ?_
  refine RS.bind0 (runs_rows hw.hV hw.hVn) ?_
  refine RS.bind0 (runs_cols hw.hO hw.hOn) ?_
  refine RS.bind0 (runs_cols hw.hU hw.hUn) ?_
  refine RS.bind0 (runs_rows hw.hU hw.hUn) ?_
  refine RS.bind0 (runs_certVec 0 N.d (by split_ifs at hcs' <;> omega)) ?_
  refine RS.bind0 (runs_certVec N.d N.d (by split_ifs at hcs' <;> omega)) ?_
  refine RS.bind0 (runs_certVec (2 * N.d) (2 * (N.V * N.n)) (by split_ifs at hcs' <;> omega)) ?_
  simp only [getD_mat hQ]
  rstep (runs_rq N)
  rstep (runs_mat_vadd _ _ _ _)
  rstep (runs_mat_vsub _ _ _ _)
  rw [tr_mat, tr_mat]
  rstep (runs_mm _ _ _ _ _)
  obtain ⟨fEh, feps, ok, hrun, hspec⟩ := runs_errOut (env := env) err N.V N.d N.h
    (2 * N.d + 2 * (N.V * N.n)) (eqF N) (ekF N fun a => certAt env (0 + a)) (qcF N) (kcF N)
    (by unfold certNeed at hcs; omega)
  rstep hrun
  rstep (runs_mm _ _ _ _ _)
  rw [tr_mat]
  rstep (runs_mm _ _ _ _ _)
  rw [tr_mat]
  rstep (runs_mm _ _ _ _ _)
  refine RS.bind (rs_mapM_mat (c := sortedCost N.n) N.V N.n _ fun q _ => rs_sortedSums N.n _)
    fun srt hsrt => ?_
  rstep (runs_mm _ _ _ _ _)
  rstep (runs_mm _ _ _ _ _)
  rw [transpose_mat]
  rstep (runs_mm _ _ _ _ _)
  rstep (runs_mm _ _ _ _ _)
  rstep (runs_mm _ _ _ _ _)
  obtain ⟨fmu, fsp, hrun2, hspec2⟩ := runs_eupuOut (env := env) eu N.V N.d (eqF N)
    (fun a j => N.U.get (a * N.V + j)) (fun a => certAt env (N.d + a))
  rstep hrun2
  rstep (runs_mapM_range (c := (N.V - 1) + ((N.V - 1) + 0)) N.V fun q _ =>
    Runs.bind' (runs_scan (fun a b => runs_max cat a b) _)
      (Runs.bind' (runs_scan (fun a b => runs_min cat a b) _) (Runs.pure _) rfl rfl) rfl
      (by simp))
  rstep (runs_mapM_range (c := 2 * (N.V - 1) + 1) N.V fun ρ hρ => by
    rw [getD_mat (tok_lt hρ)]; exact runs_spread N.V _)
  rstep ((runs_scan (fun a b => runs_max cat a b) _).congr rfl (by simp))
  rstep (runs_lit cat 1)
  refine RS.bind (rs_mapM (c := subBlockCost N.V N.n gap) (List.range N.V) fun lam hlam =>
    rs_block mx N.n gap _ _ _ _ _ _ _ _ _ _ _ _ _ (List.mem_range.mp hlam)) fun cs hcsb => ?_
  refine RS.pure ?_
  classical
  have hsrt' : ∀ q < N.V, SortedSpec ((List.range (N.n - 1)).map fun p =>
      peF N (fun a => certAt env (0 + a)) q p - peF N (fun a => certAt env (0 + a)) q (N.n - 1))
      (srt.getD q ([], [])).1 (srt.getD q ([], [])).2 :=
    fun q hq => forall₂_range_getD hsrt ([], []) hq
  have h1 : cs.sum ≤ ((List.range N.V).map fun lam => ∑ rq ∈ range (lam + 1),
      ∑ pat ∈ range (2 ^ (N.n - 1)), Ncls mx g env.weights N lam rq pat).sum := by
    refine forall₂_sum_le _ hcsb fun lam hlam cnt hc => ?_
    obtain ⟨verd, hverd, rfl⟩ := hc
    exact blockSum_le hg hw hV hn hn2 mx gap (fun a => certAt env (0 + a)) fEh feps fmu fsp ok
      hspec hspec2 srt hsrt' _ ⟨((1 : ℕ) : ℚ)⟩ (by simp) (List.mem_range.mp hlam) verd hverd
  have h2 := classes_le (clsOf mx N.V N.n) (fun x => Correct g env.weights (taskOf mx N.n N.V) x)
    N.V (2 ^ (N.n - 1)) (allInputs (List.replicate N.n N.V))
  have hsp : (taskOf mx N.n N.V).space = List.replicate N.n N.V := by cases mx <;> rfl
  rw [foldl_nat_add, Nat.zero_add]
  unfold numCorrect
  rw [hsp]
  rw [sum_range_eq] at h1
  exact h1.trans h2

/-! ## Soundness and the bill -/

/-- **Soundness.** For a graph of the family, the label `max` (`mx`) or `min`, every method `err`,
    `eu` and every plan `gap`: every count a run of the checker returns is at most the number of
    inputs the network answers correctly, for every weights and certificate. -/
theorem check_sound {g : Graph} (hg : IsAttn g) (mx : Bool) (err eu : ℕ)
    (gap : ℕ → ℕ → ℕ → ℕ) (w : Weights ℚ) (c : Cert) (n : ℕ) (cost : Cost)
    (h : CostM.exec (check Interp.counting mx err eu gap g (taskOf mx g.positions g.values))
      ⟨w, c⟩ = some (n, cost)) :
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
  obtain ⟨cs, c17, hcs, h⟩ := Runs.bind_some h
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
  obtain ⟨rfl, -⟩ := (runs_certSize (env := ⟨w, c⟩)).det hcs
  by_cases hwf : (wellFormed g.values g.positions (tE.shape.getD 1 0) (tQ.shape.getD 1 0)
      [tE.shape, tP.shape, tQ.shape, tK.shape, tV.shape, tO.shape, tU.shape, tC.shape]
      [tE.data.size, tP.data.size, tQ.data.size, tK.data.size, tV.data.size, tO.data.size,
        tU.data.size, tC.data.size] && Nat.ble 2 g.values && Nat.ble 2 g.positions &&
      Nat.ble (2 * tE.shape.getD 1 0 + 2 * (g.values * g.positions) +
        errCertLen err g.values (tE.shape.getD 1 0) (tQ.shape.getD 1 0)) c.size) = true
  · simp only [Bool.and_eq_true, Nat.ble_eq] at hwf
    obtain ⟨⟨⟨hwf, hV2⟩, hn2⟩, hcz⟩ := hwf
    have hw := WF_of_wellFormed hE hP hQ hK hV hO hU hC hwf
    exact ((rs_check (env := ⟨w, c⟩) mx err eu gap hg _ hw rfl rfl hV2 hn2 hcz) _ _ _ h0).1
  · simp only [hwf, Bool.false_eq_true, ↓reduceIte, Interp.counting_pure, CostM.run_pure,
      Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]
    exact Nat.zero_le _

/-- **Count and cost.** On well-formed weights with `V, n ≥ 2` and a certificate with the numbers
    the method needs, a run that succeeds counts at most the inputs answered correctly and is
    billed `subBill err eu gap V n d h`. -/
theorem check_billed {N : Net} (mx : Bool) (err eu : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) {g : Graph}
    (hg : IsAttn g) (task : Task) {w : Weights ℚ} (hw : N.WF w) (hV : N.V = g.values)
    (hn : N.n = g.positions) (hV2 : 2 ≤ N.V) (hn2 : 2 ≤ N.n) {c : Cert}
    (hcs : certNeed err N.V N.n N.d N.h ≤ c.size) {count bill : ℕ}
    (h : CostM.billed (check Interp.counting mx err eu gap g task) ⟨w, c⟩ = some (count, bill)) :
    count ≤ numCorrect g w (taskOf mx N.n N.V) ∧ bill = subBill err eu gap N.V N.n N.d N.h :=
  (rs_check (env := ⟨w, c⟩) mx err eu gap hg task hw hV hn hV2 hn2 hcs).billed h

end GrossSub
