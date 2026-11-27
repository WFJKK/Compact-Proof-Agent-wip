import Candidate.LibCubicRuns

/-!
# The checker of entry 7, run on well-formed weights

`runs_check`: when `exp` accepts both parts of every score, the checker's run, with its count and
its bill `bill V n d h`. `sat_check`: what any run that succeeds returns, whether or not `exp`
accepts every part: the count over the blocks, built from the path tables and from the bounds `exp`
gives on the two parts of the scores.
-/

namespace GrossCubic

open CompactCheck Common AttnClasses Finset

/-- `E W_V W_O U`, entry `(t, j)`: `EVOU`. -/
def evT (N : Net) (t j : ℕ) : ℚ := ∑ a ∈ range N.d, N.E.get (t * N.d + a) * N.vou a j

/-- `P W_V W_O U`, entry `(p, j)`: `PVOU`. -/
def pvT (N : Net) (p j : ℕ) : ℚ := ∑ a ∈ range N.d, N.P.get (p * N.d + a) * N.vou a j

/-- The numbers `1, ..., V - 1`, as the checker writes them. -/
def jsV (V : ℕ) : List Q := (List.range (V - 1)).map fun i => ⟨((i + 1 : ℕ) : ℚ)⟩

/-- The count, from the bounds `XE`, `XP` on `exp` of the two parts of the scores. -/
def countV (mx : Bool) (N : Net) (XE XP : List (List (Q × Q))) : ℕ :=
  ((List.range N.V).map (blockV mx N.V N.n (mat N.V N.V N.D) (mat N.V N.V (evT N))
    (mat N.n N.V (pvT N)) XE XP ((jsV N.V).getD 0 ⟨0⟩) (jsV N.V))).foldl Nat.add 0

/-- The bill of the checker on a network with `V` tokens, `n` positions, width `d` and head size
    `h`: the path tables, the bounds on `exp`, the numbers `1, ..., V - 1`, and the blocks. -/
def bill (V n d h : ℕ) : ℕ :=
  h * d + (V * d + (V * h * d + (V * h * d + (V * V * h + (n * h * d + (V * n * h + (d * d * h +
    (d * V * d + (V * V * d + (n * V * d + (V * V * d + (V * (V * 3) + (V * (n * 3) +
    ((V - 1) + (((List.range V).map (blockCost V n)).sum + 0)))))))))))))))

/-- The checker's test of the weights passes on the family's weights with `V, n ≥ 2`. -/
theorem guard_of_WF {N : Net} {w : Weights ℚ} (hw : N.WF w) (hV2 : 2 ≤ N.V) (hn2 : 2 ≤ N.n) :
    (wellFormed N.V N.n N.d N.h
      [N.E.shape, N.P.shape, N.WQ.shape, N.WK.shape, N.WV.shape, N.WO.shape, N.U.shape, N.C.shape]
      [N.E.data.size, N.P.data.size, N.WQ.data.size, N.WK.data.size, N.WV.data.size,
        N.WO.data.size, N.U.data.size, N.C.data.size] && Nat.ble 2 N.V && Nat.ble 2 N.n) =
      true := by
  rw [wellFormed_of_WF hw]
  simp [Nat.ble_eq, hV2, hn2]

/-- **The run.** On well-formed weights with `V, n ≥ 2`, when `exp` accepts both parts of every
    score, the checker returns `countV` and is billed `bill V n d h`. -/
theorem runs_check {N : Net} (mx : Bool) {g : Graph} (task : Task) {env : Env}
    (hw : N.WF env.weights) (hV : N.V = g.values) (hn : N.n = g.positions) (hV2 : 2 ≤ N.V)
    (hn2 : 2 ≤ N.n) (hexpE : ∀ q < N.V, ∀ t < N.V, (expInterval (N.SEf q t)).isSome)
    (hexpP : ∀ q < N.V, ∀ p < N.n, (expInterval (N.SPf q p)).isSome) :
    Runs (check Interp.counting mx g task) env
      (countV mx N (expMat N.V N.V N.SEf) (expMat N.V N.n N.SPf)) (bill N.V N.n N.d N.h) := by
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
  rw [← hw.hEs, ← hw.hQs, ite_eq_left (guard_of_WF hw hV2 hn2)]
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
  refine Runs.bind (runs_mm _ _ _ _ _) ?_
  refine Runs.bind (runs_expT N.V N.V N.SEf hexpE) ?_
  refine Runs.bind (runs_expT N.V N.n N.SPf hexpP) ?_
  refine Runs.bind ((runs_mapM (c := fun _ => 1) _ fun i _ => runs_lit cat _).congr rfl
    (by simp)) ?_
  refine Runs.bind (runs_mapM _ fun lam hlam =>
    runs_block mx _ _ _ _ _ _ _ _ (List.mem_range.mp hlam)) ?_
  exact Runs.pure _

/-- **What a run returns.** On well-formed weights with `V, n ≥ 2`, every run of the checker that
    succeeds returns `countV` of bounds on `exp` of the two parts of the scores, `exp` having
    accepted every part. -/
theorem sat_check {N : Net} (mx : Bool) {g : Graph} (task : Task) {env : Env}
    (hw : N.WF env.weights) (hV : N.V = g.values) (hn : N.n = g.positions) (hV2 : 2 ≤ N.V)
    (hn2 : 2 ≤ N.n) :
    Sat (check Interp.counting mx g task) env fun count => ∃ XE XP : List (List (Q × Q)),
      (∀ q < N.V, ∀ t < N.V, expInterval (N.SEf q t) =
        some ((bt2 Interp.counting XE q t).1.val, (bt2 Interp.counting XE q t).2.val)) ∧
      (∀ q < N.V, ∀ p < N.n, expInterval (N.SPf q p) =
        some ((bt2 Interp.counting XP q p).1.val, (bt2 Interp.counting XP q p).2.val)) ∧
      count = countV mx N XE XP := by
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
  rw [← hw.hEs, ← hw.hQs, ite_eq_left (guard_of_WF hw hV2 hn2)]
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
  sstep (runs_mm _ _ _ _ _)
  refine Sat.bind (sat_expT N.V N.V N.SEf) fun XE hXE => ?_
  refine Sat.bind (sat_expT N.V N.n N.SPf) fun XP hXP => ?_
  sstep (runs_mapM (c := fun _ => 1) _ fun i _ => runs_lit cat _)
  sstep (runs_mapM _ fun lam hlam => runs_block mx _ _ _ _ XE XP _ _ (List.mem_range.mp hlam))
  exact Sat.pure ⟨XE, XP, hXE, hXP, rfl⟩

end GrossCubic
