import Candidate.LibCubicChecker

/-!
# Entry 9: Gross et al.'s sub-cubic proofs

The sub-cubic proofs of Gross et al. for Max-of-K (`gbmi/exp_max_of_n/verification/subcubic.py`,
`quadratic.py` and `LargestWrongLogitQuadraticConfig` in `verification/__init__.py`, at `fb5b181`),
as one checker in the counted language, for the one-head attention models of entry 6. Their 100
configurations (5 ways of handling `EUPU`, 2 of the attention, 10 of the error of the attention's
low-rank approximation) are a parameter: the method `err` of the error (6 checkers for their 10
choices), the method `eu` of the direct path (3 for their 5), and the certificate, which holds
their directions and averages (a choice that leaves out an average or a direction is its
certificate with zeros there).

Notation, with the scale `c` folded into `W_Q` (`Qc`, entry 6's queries) and `p̄` a vector of the
certificate (their mean of the positional embedding):

    Eq = E + P_Q,   Ek = E + p̄,   Perr = P - p̄
    EQKE[q, t] = c Eq_q W_Q · Ek_t W_K,   PE[q, p] = c Eq_q W_Q · Perr_p W_K

so that the score of token `t` at position `p` is `EQKE[q, t] + PE[q, p]`, for every `p̄`.

1. `EQKE = Ê + R`, `Ê` a sum of rank-one matrices and `ε_q` a bound on the spread of row `q` of
   `R` (`errOut`). Their certificate directions need not be singular vectors: the decomposition
   is an identity for any, with the cross terms kept in `Ê`.
2. For the query `q`, the largest token `m` (of rank `λ`), `c` positions holding other tokens, all
   of rank at most `λ - g` (`g` the gap of the plan, a public table): the attention on `m`'s
   positions is at least that of `a_lo = Ê[q, m] - max_{k ≤ λ - g} Ê[q, k] - ε_q` with `m` at the
   positions where `PE` is smallest, and at most that of `a_hi` (running minimum, `+ ε_q`) with
   `m` where `PE` is largest. The positional errors are sorted by a network of `min` and `max`.
3. The logit bound: `logit_j - logit_m ≤ L_j + α R_j + (1 - α) W + s_q` for every input of the
   class, `α` the attention on `m`, `R_j = EVOU[m, j] - EVOU[m, m]`, `W` the largest spread of a
   row of `EVOU` over the tokens of rank at most `λ - g`, `L_j` the direct path's mean part plus
   the positional path pessimised, `s_q` the direct path's spread (`eu`).
4. With `avg` from the certificate, `L_j + α R_j + (1 - α) W + s_q` is at most
   `G(α) = max_j (L_j + avg R_j) + (1 - avg) W + s_q + max((α - avg)(R* - W))` over
   `R* ∈ {R_max, R_min}`, and the test is `G < 0` at the endpoint the slopes call for (both when
   their signs differ), cleared of the softmax's denominator: with `α = A / (A + B)`,
   `A (G₀ + (1 - avg)(R* - W)) + B (G₀ - avg (R* - W)) < 0`, `A` and `B` bounded from `exp`.
5. A passing class counts its `(λ - g + 1)^c'` inputs for each pattern of `c'` positions.

Two of their steps are corrected (their code takes `R_max` alone in step 4, and one endpoint
whenever `R_max ≥ W`); and their code counts `(λ - g)^c'` inputs of a class, one token short of
the ones it covers.
-/

namespace GrossSub

open CompactCheck AttnClasses GrossCubic

section Checker

variable (I : Interp)

/-! ## Helpers -/

/-- The smallest entry of a list (zero for the empty list). -/
def minL : List I.V → I.M I.V
  | [] => pure I.zero
  | a :: rs => rs.foldlM (fun s v => I.min cat s v) a

/-- `max xs - min xs`. -/
def spread (xs : List I.V) : I.M I.V := do
  let a ← maxL I xs
  let b ← minL I xs
  I.sub cat a b

/-- `|x|`, as `max x (-x)`. -/
def absV (x : I.V) : I.M I.V := do
  let y ← I.neg cat x
  I.max cat x y

/-- Numbers `off, ..., off + k - 1` of the certificate. -/
def certVec (off k : ℕ) : I.M (List I.V) := (List.range k).mapM fun i => I.cert (off + i)

/-- A matrix of `rows × cols` numbers of the certificate, row by row, from `off`. -/
def certMat (off rows cols : ℕ) : I.M (List (List I.V)) :=
  (List.range rows).mapM fun i => certVec I (off + i * cols) cols

/-- The transpose of a matrix with `cols` columns (free: it only rearranges). -/
def tr (cols : ℕ) (A : List (List I.V)) : List (List I.V) :=
  (List.range cols).map fun j => A.map fun r => r.getD j I.zero

/-- Entry `i` of a vector. -/
def at1 (v : List I.V) (i : ℕ) : I.V := v.getD i I.zero

/-- `A[i][k] - u_i w_k`, for `A` of `rows × cols`. -/
def subOuter (rows cols : ℕ) (A : List (List I.V)) (u w : List I.V) : I.M (List (List I.V)) :=
  (List.range rows).mapM fun i => do
    let nu ← I.neg cat (at1 I u i)
    (List.range cols).mapM fun k => I.muladd cat (at2 I A i k) nu (at1 I w k)

/-- `uᵀ A`: `Σ_s u_s A[s][k]` for each of the `cols` columns. -/
def vecMat (cols : ℕ) (u : List I.V) (A : List (List I.V)) : I.M (List I.V) :=
  (tr I cols A).mapM (dot I u)

/-- `A v`: `Σ_k A[i][k] v_k` for each row. -/
def matVec (A : List (List I.V)) (v : List I.V) : I.M (List I.V) :=
  A.mapM fun r => dot I r v

/-- `Σ_k |l_k - a_k| s_k`. -/
def absDot (l a s : List I.V) (k : ℕ) : I.M I.V :=
  (List.range k).foldlM (fun acc i => do
    let x ← I.sub cat (at1 I l i) (at1 I a i)
    let y ← absV I x
    I.muladd cat acc y (at1 I s i)) I.zero

/-- The bound of `max_row_diffs_per_dim_2` on the spread of row `i` of `l r`, for every row: with
    `a` a row (their mean row of `l`, or zero), `spread(a r) + Σ_k |l[i][k] - a_k| spread(r[k])`.
    `l` has `k` columns, `r` has `cols` columns. -/
def rowBound (k cols : ℕ) (l r : List (List I.V)) (a : List I.V) : I.M (List I.V) := do
  let sr ← r.mapM (spread I)
  let ar ← vecMat I cols a r
  let s0 ← spread I ar
  l.mapM fun li => do
    let t ← absDot I li a sr k
    I.add cat s0 t

/-! ## Sorting -/

/-- Insert into a sorted list: one pass of compare-and-exchange. -/
def insertV (x : I.V) : List I.V → I.M (List I.V)
  | [] => pure [x]
  | y :: ys => do
    let lo ← I.min cat x y
    let hi ← I.max cat x y
    let rest ← insertV hi ys
    pure (lo :: rest)

/-- Sort ascending, by insertion: a network of `min` and `max`. -/
def sortV : List I.V → I.M (List I.V)
  | [] => pure []
  | x :: xs => do
    let s ← sortV xs
    insertV I x s

/-- Running sums from the left: `[0, x_0, x_0 + x_1, ...]`. -/
def prefixSums (xs : List I.V) : I.M (List I.V) := do
  let p ← xs.foldlM (fun (acc : I.V × List I.V) v => do
    let s ← I.add cat acc.1 v
    pure (s, acc.2 ++ [s])) (I.zero, [I.zero])
  pure p.2

/-- Running sums from the right: entry `i` is `Σ_{j ≥ i} x_j`, for `i = 0, ..., L`. -/
def suffixSums (xs : List I.V) : I.M (List I.V) := do
  let p ← prefixSums I xs.reverse
  pure p.reverse

/-! ## The error of the approximation of `EQKE` -/

/-- Their `split_SVD` at the certificate's `u`, `v`, for `EQKE = A B` (`A`: `V × r`, `B`:
    `r × V`): `A₀ = u uᵀ A`, `B₀ = B v vᵀ`, `Ar = A - A₀`, `Br = B - B₀`, and
    `Ê = A₀ B + Ar B₀ = u (uᵀ A B) + (Ar B v) vᵀ`, so that `EQKE = Ê + Ar Br`. -/
def svdSplit (V r : ℕ) (A B : List (List I.V)) (u v : List I.V) :
    I.M (List (List I.V) × List (List I.V) × List (List I.V)) := do
  let uA ← vecMat I r u A
  let Ar ← subOuter I V r A u uA
  let Bv ← matVec I B v
  let Br ← subOuter I r V B Bv v
  let x ← vecMat I V uA B
  let y ← matVec I Ar Bv
  let Eh ← (List.range V).mapM fun q => (List.range V).mapM fun t => do
    let a ← I.muladd cat I.zero (at1 I u q) (at1 I x t)
    I.muladd cat a (at1 I y q) (at1 I v t)
  pure (Eh, Ar, Br)

/-- The two factors their `FactoredMatrix` reduces `EQKE` to: `(Eq W_Q, W_Kᵀ Ekᵀ)` when the head
    is narrower than the model, else `(Eq W_Q W_Kᵀ, Ekᵀ)`; `Qc`, `Kc` are the columns of `c W_Q`
    and `W_K`, `Mqk = c W_Q W_Kᵀ`. -/
def factors (d h : ℕ) (Eq Ek Qc Kc Mqk : List (List I.V)) :
    I.M (List (List I.V) × List (List I.V)) :=
  if h < d then do
    let A ← mm I Eq Qc
    let B ← mm I Kc Ek
    pure (A, B)
  else do
    let A ← mm I Eq (tr I d Mqk)
    pure (A, tr I d Ek)

/-- `X - F Fᵀ` has a diagonal that dominates, row and column together, with `F` of the
    certificate: then `X` is positive semidefinite. -/
def psdOk (r : ℕ) (X F : List (List I.V)) : I.M I.B := do
  let FF ← mm I F F
  let D ← (List.range r).mapM fun i => (List.range r).mapM fun j =>
    I.sub cat (at2 I X i j) (at2 I FF i j)
  let oks ← (List.range r).mapM fun i => do
    let off ← ((List.range r).filter fun j => j != i).foldlM (fun acc j => do
      let a ← absV I (at2 I D i j)
      let b ← absV I (at2 I D j i)
      let s ← I.add cat acc a
      I.add cat s b) I.zero
    let dd ← I.add cat (at2 I D i i) (at2 I D i i)
    I.le cat off dd
  oks.foldlM (fun a b => I.band cat a b) I.btrue

/-- Their `svd` bound `√2 σ₁(Ar Br)`, certified: `T`, `F₁`, `F₂` and `ε` from the certificate at
    `off`, with `T Tᵀ - Arᵀ Ar ⪰ 0` and `ε² - 2 Tᵀ Br Brᵀ T ⪰ 0` (each `X - F Fᵀ` dominated by its
    diagonal), and `ε ≥ 0`. -/
def svdBound (r off : ℕ) (Ar Br : List (List I.V)) : I.M (I.V × I.B) := do
  let T ← certMat I off r r
  let F1 ← certMat I (off + r * r) r r
  let F2 ← certMat I (off + 2 * (r * r)) r r
  let e ← I.cert (off + 3 * (r * r))
  let ArT := tr I r Ar
  let GA ← mm I ArT ArT
  let GB ← mm I Br Br
  let TT ← mm I T T
  let X1 ← (List.range r).mapM fun i => (List.range r).mapM fun j =>
    I.sub cat (at2 I TT i j) (at2 I GA i j)
  let ok1 ← psdOk I r X1 F1
  let TtT := tr I r T
  let GBT ← mm I GB TtT
  let TGT ← mm I TtT (tr I r GBT)
  let e2 ← I.muladd cat I.zero e e
  let X2 ← (List.range r).mapM fun i => (List.range r).mapM fun j => do
    let t2 ← I.add cat (at2 I TGT i j) (at2 I TGT i j)
    I.sub cat (if i = j then e2 else I.zero) t2
  let ok2 ← psdOk I r X2 F2
  let ok3 ← I.le cat I.zero e
  let ok12 ← I.band cat ok1 ok2
  let ok ← I.band cat ok12 ok3
  pure (e, ok)

/-- The subproduct decomposition (their `decompose_EQKE_error_quadratic`) at the certificate's
    directions `kd`, `qd`, `skd`, `sqd` (tokens) and `qu`, `ku` (model): the rank-one parts of
    `Ek`, `Eq`, their remainders, of `c W_Q` and `W_K`, the six rank-one terms of `Ê`, and the four
    factors `Qe2`, `Wqe`, `Wke`, `Ke2` of the remainder `Qe2 Wqe Wkeᵀ Ke2ᵀ`. `Wq`, `Wk` are the rows
    of `c W_Q` and `W_K`. -/
def subDecomp (V d h off : ℕ) (Eq Ek Wq Wk Mqk : List (List I.V)) :
    I.M (List (List I.V) × List (List I.V) × List (List I.V) × List (List I.V) ×
      List (List I.V)) := do
  let kd ← certVec I off V
  let qd ← certVec I (off + V) V
  let skd ← certVec I (off + 2 * V) V
  let sqd ← certVec I (off + 3 * V) V
  let qu ← certVec I (off + 4 * V) d
  let ku ← certVec I (off + 4 * V + d) d
  let k1 ← vecMat I d kd Ek
  let Ke ← subOuter I V d Ek kd k1
  let q1 ← vecMat I d qd Eq
  let Qe ← subOuter I V d Eq qd q1
  let k2 ← vecMat I d skd Ke
  let Ke2 ← subOuter I V d Ke skd k2
  let q2 ← vecMat I d sqd Qe
  let Qe2 ← subOuter I V d Qe sqd q2
  let wq1 ← vecMat I h qu Wq
  let Wqe ← subOuter I d h Wq qu wq1
  let wk1 ← vecMat I h ku Wk
  let Wke ← subOuter I d h Wk ku wk1
  let z1 ← vecMat I d q1 Mqk
  let x1 ← matVec I Ek z1
  let z2 ← matVec I Mqk k1
  let y2 ← matVec I Qe z2
  let z3 ← vecMat I d q2 Mqk
  let x3 ← matVec I Ke z3
  let z4 ← matVec I Mqk k2
  let y4 ← matVec I Qe2 z4
  let z5 ← matVec I Wk wq1
  let x5 ← matVec I Ke2 z5
  let y5 ← matVec I Qe2 qu
  let z6 ← matVec I Wqe wk1
  let y6 ← matVec I Qe2 z6
  let x6 ← matVec I Ke2 ku
  let Eh ← (List.range V).mapM fun q => (List.range V).mapM fun t => do
    let a1 ← I.muladd cat I.zero (at1 I qd q) (at1 I x1 t)
    let a2 ← I.muladd cat a1 (at1 I y2 q) (at1 I kd t)
    let a3 ← I.muladd cat a2 (at1 I sqd q) (at1 I x3 t)
    let a4 ← I.muladd cat a3 (at1 I y4 q) (at1 I skd t)
    let a5 ← I.muladd cat a4 (at1 I y5 q) (at1 I x5 t)
    I.muladd cat a5 (at1 I y6 q) (at1 I x6 t)
  pure (Eh, Qe2, Wqe, Wke, Ke2)

/-- Step 1: `Ê`, the bounds `ε_q` on the spread of the rows of `EQKE - Ê`, and whether the
    certificate's checks pass. `err`: 0 `svd`; 1 `max_diff`, `mean+max_diff` (the mean row from
    the certificate); 2 `max_diff_exact`; 3 `exact_EQKE+max_diff_exact`; 4 `max_diff_subproduct`,
    `mean+max_diff_subproduct`; 5 the three `..._subproduct_recursive`. -/
def errOut (err V d h off : ℕ) (Eq Ek Qc Kc Mqk : List (List I.V)) :
    I.M (List (List I.V) × List I.V × I.B) :=
  if err ≤ 2 then do
    let r := if h < d then h else d
    let fb ← factors I d h Eq Ek Qc Kc Mqk
    let u ← certVec I off V
    let v ← certVec I (off + V) V
    let s ← svdSplit I V r fb.1 fb.2 u v
    if err = 0 then do
      let eb ← svdBound I r (off + 2 * V) s.2.1 s.2.2
      pure (s.1, List.replicate V eb.1, eb.2)
    else if err = 1 then do
      let a ← certVec I (off + 2 * V) r
      let eps ← rowBound I r V s.2.1 s.2.2 a
      pure (s.1, eps, I.btrue)
    else do
      let R ← mm I s.2.1 (tr I V s.2.2)
      let eps ← R.mapM (spread I)
      pure (s.1, eps, I.btrue)
  else if err = 3 then do
    let Qs ← mm I Eq Qc
    let Ks ← mm I Ek Kc
    let Eh ← mm I Qs Ks
    pure (Eh, List.replicate V I.zero, I.btrue)
  else do
    let Wq := tr I d Qc
    let Wk := tr I d Kc
    let s ← subDecomp I V d h off Eq Ek Wq Wk Mqk
    let Qe2 := s.2.1
    let Wqe := s.2.2.1
    let Wke := s.2.2.2.1
    let Ke2 := s.2.2.2.2
    let o2 := off + 4 * V + 2 * d
    let a0 ← certVec I o2 d
    let a1 ← certVec I (o2 + d) h
    let a2 ← certVec I (o2 + d + h) d
    let m3 := tr I d Ke2
    if err = 4 then do
      -- break points: (m0, m1 m2 m3), (m0 m1, m2 m3), (m0 m1 m2, m3)
      let r2 ← mm I (tr I h Wke) Ke2
      let r1 ← mm I Wqe (tr I V r2)
      let l2 ← mm I Qe2 (tr I h Wqe)
      let l3 ← mm I l2 Wke
      let b1 ← rowBound I d V Qe2 r1 a0
      let b2 ← rowBound I h V l2 r2 a1
      let b3 ← rowBound I d V l3 m3 a2
      let eps ← (List.range V).mapM fun q => do
        let x ← I.min cat (at1 I b1 q) (at1 I b2 q)
        I.min cat x (at1 I b3 q)
      pure (s.1, eps, I.btrue)
    else do
      -- recursively, a mean row at each level (zero where their choice has none)
      let f3 ← m3.mapM (spread I)
      let a2m3 ← vecMat I V a2 m3
      let s2 ← spread I a2m3
      let f2 ← (tr I h Wke).mapM fun row => do
        let t ← absDot I row a2 f3 d
        I.add cat s2 t
      let a1m2 ← vecMat I d a1 (tr I h Wke)
      let a1m3 ← vecMat I V a1m2 m3
      let s1 ← spread I a1m3
      let f1 ← Wqe.mapM fun row => do
        let t ← absDot I row a1 f2 h
        I.add cat s1 t
      let a0m1 ← vecMat I h a0 Wqe
      let a0m2 ← vecMat I d a0m1 (tr I h Wke)
      let a0m3 ← vecMat I V a0m2 m3
      let s0 ← spread I a0m3
      let eps ← Qe2.mapM fun row => do
        let t ← absDot I row a0 f1 d
        I.add cat s0 t
      pure (s.1, eps, I.btrue)

/-- The length of the method's part of the certificate. -/
def errCertLen (err V d h : ℕ) : ℕ :=
  let r := if h < d then h else d
  if err = 0 then 2 * V + 3 * (r * r) + 1
  else if err = 1 then 2 * V + r
  else if err = 2 then 2 * V
  else if err = 3 then 0
  else 4 * V + 2 * d + (d + h + d)

/-! ## Steps 2 to 5 -/

/-- The gap of the plan, at least one. -/
def gapOf (gap : ℕ → ℕ → ℕ → ℕ) (rq lam c : ℕ) : ℕ := Nat.max 1 (gap rq lam c)

/-- The gap of `W` for `λ` and `c`: the smallest over the queries `rq ≤ λ`. -/
def gapW (gap : ℕ → ℕ → ℕ → ℕ) (lam c : ℕ) : ℕ :=
  ((List.range (lam + 1)).map fun rq => gapOf gap rq lam c).foldl Nat.min (gapOf gap lam lam c)

/-- Whether the class of the query of rank `rq`, the largest rank `λ` and `c` other positions is
    one of the proof's: `λ ≥ g`, and the query is the largest token or at most `λ - g`. -/
def valid (gap : ℕ → ℕ → ℕ → ℕ) (rq lam c : ℕ) : Bool :=
  Nat.ble (gapOf gap rq lam c) lam && (rq == lam || Nat.ble (gapOf gap rq lam c + rq) lam)

/-- `kup b y + kup b' y' < 0`: the cleared test of one endpoint and one `R*`. -/
def endTest (A B : I.V × I.V) (yA yB : I.V) : I.M I.B := do
  let a ← kup I A yA
  let b ← kup I B yB
  let s ← I.add cat a b
  I.lt cat s I.zero

/-- The test of one endpoint: for `R*` = `R_max` and `R_min`, with the constants `K` (their
    `KA`, `KB` per `R*`) and the query's spread `sq`. -/
def endpoint (A B : I.V × I.V) (K : List (I.V × I.V)) (sq : I.V) : I.M I.B := do
  let ts ← K.mapM fun k => do
    let yA ← I.add cat k.1 sq
    let yB ← I.add cat k.2 sq
    endTest I A B yA yB
  ts.foldlM (fun a b => I.band cat a b) I.btrue

/-- Bounds on `e^a (s + c1)` from bounds on `e^a` and on `s` (`c1` zero or one), the lower bound
    on `e^a` clamped at zero. -/
def scaleB (ea s : I.V × I.V) (c1 : I.V) : I.M (I.V × I.V) := do
  let x ← I.max cat I.zero ea.1
  let lo ← I.add cat s.1 c1
  let hi ← I.add cat s.2 c1
  let a ← I.muladd cat I.zero x lo
  let b ← I.muladd cat I.zero ea.2 hi
  pure (a, b)

/-- Bounds on `s + c2`. -/
def shiftB (s : I.V × I.V) (c2 : I.V) : I.M (I.V × I.V) := do
  let a ← I.add cat s.1 c2
  let b ← I.add cat s.2 c2
  pure (a, b)

/-- One class: the query of rank `rq` (token `q`), the largest of rank `λ` (token `m`), `c` other
    positions, gap `g`. `Eh`, `eps`: step 1; `rmax`, `rmin`: running extrema of `Ê[q]` over the
    ranks; `pre`, `suf`: bounds on the sums of `e^{PE}` of the `k` smallest (`k` largest) sorted
    positional errors; `KL`, `KH`: the constants of the two endpoints; `dir`: `R_max < W` and
    `W ≤ R_min`; `sq` the query's spread; `one` the number one. -/
def classTest (n rq lam c g q m : ℕ) (Eh : List (List I.V)) (eps : List I.V)
    (rmax rmin : List I.V) (pre suf : List (I.V × I.V)) (KL KH : List (I.V × I.V))
    (dir : I.B × I.B) (sq one : I.V) : I.M I.B := do
  let L := n - 1
  let k := if rq = lam then n - c - 1 else n - c
  let c1 := if rq = lam then one else I.zero
  let c2 := if rq = lam then I.zero else one
  let e := at2 I Eh q m
  let x1 ← I.sub cat e (at1 I rmax (lam - g))
  let alo ← I.sub cat x1 (at1 I eps q)
  let x2 ← I.sub cat e (at1 I rmin (lam - g))
  let ahi ← I.add cat x2 (at1 I eps q)
  let elo ← I.exp cat alo
  let ehi ← I.exp cat ahi
  let Alo ← scaleB I elo (pre.getD k (I.zero, I.zero)) c1
  let Blo ← shiftB I (suf.getD k (I.zero, I.zero)) c2
  let Ahi ← scaleB I ehi (suf.getD (L - k) (I.zero, I.zero)) c1
  let Bhi ← shiftB I (pre.getD (L - k) (I.zero, I.zero)) c2
  let tlo ← endpoint I Alo Blo KL sq
  let thi ← endpoint I Ahi Bhi KH sq
  let p1 ← I.band cat dir.1 tlo
  let p2 ← I.band cat dir.2 thi
  let p3 ← I.band cat tlo thi
  let p12 ← I.bor cat p1 p2
  I.bor cat p12 p3

/-- The constants of one endpoint, for `R* = R_max` and `R_min`: with `G₀` the largest
    `L_j + avg R_j` plus `(1 - avg) W`, `(G₀ + (1 - avg)(R* - W), G₀ - avg (R* - W))`. -/
def endConsts (V m : ℕ) (Ls Rs : List I.V) (Rmax Rmin W avg one : I.V) :
    I.M (List (I.V × I.V)) := do
  let ys ← (others V m).mapM fun j => I.muladd cat (at1 I Ls j) avg (at1 I Rs j)
  let top ← maxL I ys
  let om ← I.sub cat one avg
  let g0 ← I.muladd cat top om W
  [Rmax, Rmin].mapM fun Rx => do
    let dx ← I.sub cat Rx W
    let ka ← I.muladd cat g0 om dx
    let t ← I.muladd cat I.zero avg dx
    let kb ← I.sub cat g0 t
    pure (ka, kb)

/-- The direct path: their split of `EUPU` into a part shared by the queries, `μ U` (`L_j` is
    centered at `m`), and each query's spread `s_q`. `eu`: 0 `μ` from the certificate (their
    `mean_query+max_diff`, `svd_query+max_diff`, and `max_diff` with `μ = 0`),
    `s_q = Σ_a |Eq[q][a] - μ_a| (max_j U[a][j] - min_j U[a][j])`; 1 `max_diff_exact`, the spread
    of row `q` of `EUPU`; 2 `global_max_diff_exact`, the spread of the whole table. -/
def eupuOut (eu V d : ℕ) (Eq EU Ur : List (List I.V)) (mu : List I.V) :
    I.M (List I.V × List I.V) :=
  if eu = 0 then do
    let muU ← vecMat I V mu Ur
    let su ← Ur.mapM (spread I)
    let sp ← Eq.mapM fun row => absDot I row mu su d
    pure (muU, sp)
  else if eu = 1 then do
    let sp ← EU.mapM (spread I)
    pure (List.replicate V I.zero, sp)
  else do
    let tops ← EU.mapM (maxL I)
    let bots ← EU.mapM (minL I)
    let top ← maxL I tops
    let bot ← minL I bots
    let s ← I.sub cat top bot
    pure (List.replicate V I.zero, List.replicate V s)

/-- Entrywise difference. -/
def vsub (xs ys : List I.V) : I.M (List I.V) :=
  (List.zip xs ys).mapM fun p => I.sub cat p.1 p.2

/-- For one query token: its positional errors relative to the query's position, sorted, bounds on
    their `exp`, and the sums of the bounds of the `k` smallest (`pre[k]`) and of all from the
    `k`-th on (`suf[k]`), as pairs of lower and upper bounds. -/
def sortedSums (n : ℕ) (row : List I.V) : I.M (List (I.V × I.V) × List (I.V × I.V)) := do
  let offs ← (List.range (n - 1)).mapM fun p => I.sub cat (at1 I row p) (at1 I row (n - 1))
  let w ← sortV I offs
  let ex ← w.mapM (I.exp cat)
  let plo ← prefixSums I (ex.map (·.1))
  let phi ← prefixSums I (ex.map (·.2))
  let slo ← suffixSums I (ex.map (·.1))
  let shi ← suffixSums I (ex.map (·.2))
  pure (List.zip plo phi, List.zip slo shi)

/-- The number of inputs of a pattern of `c'` positions in the class of the query of rank `rq`:
    `(λ - g + 1)^c'` if the class passes; the input `(m, ..., m)` if `rq = λ` and `c' = 0`. -/
def cntOf (gap : ℕ → ℕ → ℕ → ℕ) (lam rq c' : ℕ) (b0 : I.B) (verd : List (List I.B)) : I.N :=
  if rq = lam then
    (if c' = 0 then I.countB b0
     else I.nscale (Nat.pow (lam - gapOf gap rq lam c' + 1) c')
       ((verd.getD (c' - 1) []).getD rq I.bfalse))
  else I.nscale (Nat.pow (lam - gapOf gap rq lam (c' + 1) + 1) c')
    ((verd.getD c' []).getD rq I.bfalse)

/-- Every input whose largest token has rank `λ`. -/
def block (mx : Bool) (V n : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (EU EV PV Eh : List (List I.V))
    (eps : List I.V) (ok : I.B) (srt : List (List (I.V × I.V) × List (I.V × I.V)))
    (muU sp : List I.V) (rm : List (List I.V × List I.V)) (Wpre avgs : List I.V) (one : I.V)
    (lam : ℕ) : I.M I.N := do
  let m := tok mx V lam
  let Pp ← ppess I V n m PV
  let b0 ← onlyMax I V m EU EV Pp
  let Rs ← (List.range V).mapM fun j => I.sub cat (at2 I EV m j) (at2 I EV m m)
  let Rmax ← maxL I ((others V m).map (at1 I Rs))
  let Rmin ← minL I ((others V m).map (at1 I Rs))
  let Ls ← (List.range V).mapM fun j => do
    let a ← I.sub cat (at1 I muU j) (at1 I muU m)
    I.add cat a (at1 I Pp j)
  let verd ← (List.range (n - 1)).mapM fun c0 =>
    if Nat.ble (gapW gap lam (c0 + 1)) lam then do
      let W := at1 I Wpre (lam - gapW gap lam (c0 + 1))
      let KL ← endConsts I V m Ls Rs Rmax Rmin W (at1 I avgs (lam * n + (c0 + 1))) one
      let KH ← endConsts I V m Ls Rs Rmax Rmin W (at1 I avgs (V * n + lam * n + (c0 + 1))) one
      let d1 ← I.lt cat Rmax W
      let d2 ← I.le cat W Rmin
      (List.range (lam + 1)).mapM fun rq =>
        if valid gap rq lam (c0 + 1) then do
          let q := tok mx V rq
          let t ← classTest I n rq lam (c0 + 1) (gapOf gap rq lam (c0 + 1)) q m Eh eps
            (rm.getD q ([], [])).1 (rm.getD q ([], [])).2 (srt.getD q ([], [])).1
            (srt.getD q ([], [])).2 KL KH (d1, d2) (at1 I sp q) one
          I.band cat t ok
        else pure I.bfalse
    else pure ((List.range (lam + 1)).map fun _ => I.bfalse)
  pure ((List.range (lam + 1)).foldl (fun a rq =>
    (List.range (Nat.pow 2 (n - 1))).foldl (fun a pat =>
      I.nadd a (cntOf I gap lam rq (inPat (n - 1) pat).length b0 verd)) a) I.nzero)

/-- The checker: the label `max` (`mx`) or `min`, the method `err` of step 1, the method `eu` of
    the direct path, the plan `gap` (by the ranks of the query, of the largest token, and the
    number of other positions), the graph `g` and the task. The certificate: `p̄` (`d`), `μ`
    (`d`), the averages (`2 V n`: endpoint, `λ`, `c`), then the method's numbers
    (`errCertLen`); the checker refuses (count 0) a certificate with fewer numbers. -/
def check (mx : Bool) (err eu : ℕ) (gap : ℕ → ℕ → ℕ → ℕ) (g : Graph) (_task : Task) :
    I.M I.N := do
  let sE ← I.weightShape nE
  let sP ← I.weightShape nP
  let sQ ← I.weightShape nQ
  let sK ← I.weightShape nK
  let sV ← I.weightShape nV
  let sO ← I.weightShape nO
  let sU ← I.weightShape nU
  let sC ← I.weightShape nC
  let lE ← I.weightSize nE
  let lP ← I.weightSize nP
  let lQ ← I.weightSize nQ
  let lK ← I.weightSize nK
  let lV ← I.weightSize nV
  let lO ← I.weightSize nO
  let lU ← I.weightSize nU
  let lC ← I.weightSize nC
  let cs ← I.certSize
  let V := g.values
  let n := g.positions
  let d := sE.getD 1 0
  let h := sQ.getD 1 0
  if wellFormed V n d h [sE, sP, sQ, sK, sV, sO, sU, sC] [lE, lP, lQ, lK, lV, lO, lU, lC] &&
      Nat.ble 2 V && Nat.ble 2 n &&
      Nat.ble (2 * d + 2 * (V * n) + errCertLen err V d h) cs then do
    let Es ← (List.range V).mapM (row I nE d)
    let Ps ← (List.range n).mapM (row I nP d)
    let c ← I.weight nC 0
    let Qc ← (List.range h).mapM fun k => do
      let w ← col I nQ d h k
      w.mapM fun v => I.muladd cat I.zero v c
    let Kc ← (List.range h).mapM (col I nK d h)
    let Vr ← (List.range d).mapM (row I nV h)
    let Oc ← (List.range d).mapM (col I nO h d)
    let Uc ← (List.range V).mapM (col I nU d V)
    let Ur ← (List.range d).mapM (row I nU V)
    let pbar ← certVec I 0 d
    let mu ← certVec I d d
    let avgs ← certVec I (2 * d) (2 * (V * n))
    let Eq ← Es.mapM (vadd I · (Ps.getD (n - 1) []))
    let Ek ← Es.mapM (vadd I · pbar)
    let Perr ← Ps.mapM (vsub I · pbar)
    let Mqk ← mm I (tr I d Qc) (tr I d Kc)
    -- step 1
    let s1 ← errOut I err V d h (2 * d + 2 * (V * n)) Eq Ek Qc Kc Mqk
    -- the positional errors, sorted, and bounds on the sums of their `exp`
    let Kp ← mm I Kc Perr
    let Bp ← mm I (tr I d Qc) (tr I n Kp)
    let PE ← mm I Eq (tr I n Bp)
    let srt ← PE.mapM (sortedSums I n)
    -- the paths
    let VOU ← mm I (← mm I Vr Oc) Uc
    let VOUc := (List.range V).map fun j => VOU.map (·.getD j I.zero)
    let EV ← mm I Es VOUc
    let PV ← mm I Ps VOUc
    let EU ← mm I Eq Uc
    let du ← eupuOut I eu V d Eq EU Ur mu
    -- running extrema of `Ê[q]` over the ranks
    let rm ← (List.range V).mapM fun q => do
      let r := (List.range V).map fun ρ => at2 I s1.1 q (tok mx V ρ)
      let a ← scan I (I.max cat) r
      let b ← scan I (I.min cat) r
      pure (a, b)
    -- `W` for each largest rank allowed: the largest spread of a row of `EVOU` up to that rank
    let evs ← (List.range V).mapM fun ρ => spread I (EV.getD (tok mx V ρ) [])
    let Wpre ← scan I (I.max cat) evs
    let one ← I.lit cat 1
    let cs ← (List.range V).mapM
      (block I mx V n gap EU EV PV s1.1 s1.2.1 s1.2.2 srt du.1 du.2 rm Wpre avgs one)
    pure (cs.foldl I.nadd I.nzero)
  else pure I.nzero

end Checker

end GrossSub
