import Candidate.LibAttnRuns

/-!
# The checker of entry 6, run on well-formed weights

`runs_check`: when `exp` accepts every score, the checker's run, with its count and its bill
`bill V n d h`. `sat_check`: what any run that succeeds returns, whether or not `exp` accepts every
score: the count over the table of verdicts, built from tables whose entries are the path tables
and the bounds `exp` gives on the scores.
-/

namespace AttnClasses

open CompactCheck Common Finset

/-- The bill of the checker on a network with `V` tokens, `n` positions, width `d` and head size
    `h`: the path tables, the margins, the bounds on `exp`, and the classes. -/
def bill (V n d h : ℕ) : ℕ :=
  h * d + (V * d + (V * h * d + (V * h * d + (V * V * h + (n * h * d + (V * n * h + (d * d * h +
    (d * V * d + (V * V * d + (n * V * d + (1 * V * d + (V * V * d + (V * (V + margCost V) +
    (V * (n * (V + margCost V)) + (V * (V * (n * 4)) + (vtCost V n + 0))))))))))))))))

namespace Net

variable (N : Net)

/-- The table of margins of the direct path, as the checker computes it. -/
def DdTab : List (List Q) := (List.range N.V).map fun t => margVal (vec N.V (N.D t))

/-- The table of margins of the paths through the head. -/
def GTab : List (List (List Q)) :=
  (List.range N.V).map fun t => (List.range N.n).map fun p => margVal (vec N.V (N.O t p))

/-- The scores, as the checker adds them up. -/
def SEf (q t : ℕ) : ℚ := ∑ k ∈ range N.h, N.qc q k * N.ek t k

def SPf (q p : ℕ) : ℚ := ∑ k ∈ range N.h, N.qc q k * N.pk p k

end Net

/-- The count, from a table of verdicts. -/
def countOf (mx : Bool) (V n : ℕ) (task : Task) (vt : List (List (List (List Bool)))) : ℕ :=
  (allInputs task.space).foldl
    (fun a x => Interp.counting.nadd a
      (Interp.counting.countB (verdict Interp.counting mx V n vt x)))
    Interp.counting.nzero

theorem singleton_vec (k : ℕ) (f : ℕ → ℚ) : [vec k f] = mat 1 k fun _ j => f j := by
  simp [mat, vec]

theorem wellFormed_of_WF {N : Net} {w : Weights ℚ} (hw : N.WF w) :
    wellFormed N.V N.n N.d N.h
      [N.E.shape, N.P.shape, N.WQ.shape, N.WK.shape, N.WV.shape, N.WO.shape, N.U.shape, N.C.shape]
      [N.E.data.size, N.P.data.size, N.WQ.data.size, N.WK.data.size, N.WV.data.size,
        N.WO.data.size, N.U.data.size, N.C.data.size] = true := by
  simp [wellFormed, hw.hEs, hw.hPs, hw.hQs, hw.hKs, hw.hVs, hw.hOs, hw.hUs, hw.hCs, hw.hEn, hw.hPn,
    hw.hQn, hw.hKn, hw.hVn, hw.hOn, hw.hUn, hw.hCn]

/-- **The run.** On well-formed weights, when `exp` accepts every score, the checker counts the
    inputs whose class passes and is billed `bill V n d h`. -/
theorem runs_check {N : Net} (mx : Bool) {g : Graph} (task : Task) {env : Env}
    (hw : N.WF env.weights) (hV : N.V = g.values) (hn : N.n = g.positions) (hn0 : 0 < N.n)
    (hexp : ∀ q < N.V, ∀ t < N.V, ∀ p < N.n, (expInterval (N.SEf q t + N.SPf q p)).isSome) :
    Runs (check Interp.counting mx g task) env
      (countOf mx N.V N.n task (vtV mx N.V N.n (expTab N.V N.n fun q t p => N.SEf q t + N.SPf q p)
        N.DdTab N.GTab)) (bill N.V N.n N.d N.h) := by
  have hQ : N.n - 1 < N.n := by omega
  unfold check
  refine Runs.bind0 (runs_weightShape hw.hE) ?_
  refine Runs.bind0 (runs_weightShape hw.hP) ?_
  refine Runs.bind0 (runs_weightShape hw.hQ) ?_
  refine Runs.bind0 (runs_weightShape hw.hK) ?_
  refine Runs.bind0 (runs_weightShape hw.hV) ?_
  refine Runs.bind0 (runs_weightShape hw.hO) ?_
  refine Runs.bind0 (runs_weightShape hw.hU) ?_
  refine Runs.bind0 (runs_weightShape hw.hC) ?_
  refine Runs.bind0 (runs_weightSize hw.hE) ?_
  refine Runs.bind0 (runs_weightSize hw.hP) ?_
  refine Runs.bind0 (runs_weightSize hw.hQ) ?_
  refine Runs.bind0 (runs_weightSize hw.hK) ?_
  refine Runs.bind0 (runs_weightSize hw.hV) ?_
  refine Runs.bind0 (runs_weightSize hw.hO) ?_
  refine Runs.bind0 (runs_weightSize hw.hU) ?_
  refine Runs.bind0 (runs_weightSize hw.hC) ?_
  dsimp only
  rw [← hV, ← hn, hw.hEs, hw.hQs]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [← hw.hEs, ← hw.hQs, ite_eq_left (wellFormed_of_WF hw)]
  refine Runs.bind0 (runs_rows hw.hE hw.hEn) ?_
  refine Runs.bind0 (runs_rows hw.hP hw.hPn) ?_
  refine Runs.bind0 (runs_weight hw.hC (by rw [hw.hCn]; omega)) ?_
  refine Runs.bind (runs_Qc hw) ?_
  refine Runs.bind0 (runs_cols hw.hK hw.hKn) ?_
  refine Runs.bind0 (runs_rows hw.hV hw.hVn) ?_
  refine Runs.bind0 (runs_cols hw.hO hw.hOn) ?_
  refine Runs.bind0 (runs_cols hw.hU hw.hUn) ?_
  simp only [getD_mat hQ]
  refine Runs.bind (runs_rq N) ?_
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  rw [transpose_mat]
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  rw [singleton_vec]
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  refine Runs.bind (runs_Dd N) ?_
  refine Runs.bind (runs_G N) ?_
  refine Runs.bind (runs_X N.V N.n N.SEf N.SPf hexp) ?_
  refine Runs.bind (runs_vt mx N.V N.n _ _ _) ?_
  exact Runs.pure _

/-- One deterministic step of a run that succeeds. -/
macro "sstep " t:term : tactic =>
  `(tactic| (refine Sat.bind (Sat.of_runs $t) fun _ h => ?_; subst h))

/-- **What a run returns.** On well-formed weights, every run of the checker that succeeds
    returns the count over the table of verdicts built from the margins of the path tables and
    from bounds on `exp` of the scores, `exp` having accepted every score. -/
theorem sat_check {N : Net} (mx : Bool) {g : Graph} (task : Task) {env : Env}
    (hw : N.WF env.weights) (hV : N.V = g.values) (hn : N.n = g.positions) (hn0 : 0 < N.n) :
    Sat (check Interp.counting mx g task) env fun count => ∃ X : List (List (List (Q × Q))),
      (∀ q < N.V, ∀ t < N.V, ∀ p < N.n,
        expInterval (N.SEf q t + N.SPf q p) =
          some ((((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).1.val,
            (((X.getD q []).getD t []).getD p (⟨0⟩, ⟨0⟩)).2.val)) ∧
      count = countOf mx N.V N.n task (vtV mx N.V N.n X N.DdTab N.GTab) := by
  have hQ : N.n - 1 < N.n := by omega
  unfold check
  sstep (runs_weightShape hw.hE)
  sstep (runs_weightShape hw.hP)
  sstep (runs_weightShape hw.hQ)
  sstep (runs_weightShape hw.hK)
  sstep (runs_weightShape hw.hV)
  sstep (runs_weightShape hw.hO)
  sstep (runs_weightShape hw.hU)
  sstep (runs_weightShape hw.hC)
  sstep (runs_weightSize hw.hE)
  sstep (runs_weightSize hw.hP)
  sstep (runs_weightSize hw.hQ)
  sstep (runs_weightSize hw.hK)
  sstep (runs_weightSize hw.hV)
  sstep (runs_weightSize hw.hO)
  sstep (runs_weightSize hw.hU)
  sstep (runs_weightSize hw.hC)
  dsimp only
  rw [← hV, ← hn, hw.hEs, hw.hQs]
  simp only [List.getD_cons_succ, List.getD_cons_zero]
  rw [← hw.hEs, ← hw.hQs, ite_eq_left (wellFormed_of_WF hw)]
  sstep (runs_rows hw.hE hw.hEn)
  sstep (runs_rows hw.hP hw.hPn)
  sstep (runs_weight hw.hC (by rw [hw.hCn]; omega))
  sstep (runs_Qc hw)
  sstep (runs_cols hw.hK hw.hKn)
  sstep (runs_rows hw.hV hw.hVn)
  sstep (runs_cols hw.hO hw.hOn)
  sstep (runs_cols hw.hU hw.hUn)
  simp only [getD_mat hQ]
  sstep (runs_rq N)
  sstep (runs_mm _ _ _ _ _)
  sstep (runs_mm _ _ _ _ _)
  sstep (runs_mm _ _ _ _ _)
  sstep (runs_mm _ _ _ _ _)
  sstep (runs_mm _ _ _ _ _)
  sstep (runs_mm _ _ _ _ _)
  sstep (runs_mm _ _ _ _ _)
  rw [transpose_mat]
  sstep (runs_mm _ _ _ _ _)
  sstep (runs_mm _ _ _ _ _)
  rw [singleton_vec]
  sstep (runs_mm _ _ _ _ _)
  sstep (runs_mm _ _ _ _ _)
  sstep (runs_Dd N)
  sstep (runs_G N)
  refine Sat.bind (sat_X N.V N.n N.SEf N.SPf) fun X hX => ?_
  sstep (runs_vt mx N.V N.n X N.DdTab N.GTab)
  exact Sat.pure ⟨X, hX, rfl⟩

end AttnClasses
