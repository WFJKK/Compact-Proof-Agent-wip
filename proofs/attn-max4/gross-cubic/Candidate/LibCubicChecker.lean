import Candidate.LibAttnChecker

/-!
# Entry 7: Gross et al.'s cubic proof

The cubic proof of Gross et al. for Max-of-K (`gbmi/exp_max_of_n/verification/cubic.py` of their
code, at the commit the pipeline ran, `fb5b181`), as a checker in the counted language, for the
one-head attention models of entry 6: `n` positions, `V` tokens, the label the largest token
(`max`) or the smallest (`min`; they reverse the vocabulary, here the ranks of `AttnClasses.tok`
do it). The path tables are entry 6's, in their names (their `EQKE` and `EQKP` are unscaled, the
scale applied in the softmax; here the scale `c` is folded in):

    EUPU[q, j] = (E_q + P_Q) U
    EVOU[t, j] = E_t W_V W_O U
    PVOU[p, j] = P_p W_V W_O U
    EQKE[q, t] = c (E_q + P_Q) W_Q · E_t W_K
    EQKP[q, p] = c (E_q + P_Q) W_Q · P_p W_K

For each largest token `m` (the token of the largest rank `λ`), with `j` ranging over the other
outputs:

* `Pp[j] = max_p (PVOU[p, j] - PVOU[p, m])`: the positional path, pessimised as if all attention
  went to its worst position;
* `u[q] = max_j EUPU[q, j] - EUPU[q, m]`, per query token;
* `v[t] = max_j (EVOU[t, j] + Pp[j]) - EVOU[t, m]`, per key token.

Then `logit_j - logit_m ≤ u[q] + Σ_p α_p v[x_p]`, and an input is answered correctly if
`Σ_p e^{s_p} (v[x_p] + u[q]) < 0`, the softmax's denominator cleared, `s_p` the score (for each
input the same test as theirs, the denominator being positive). Inputs are taken by their query
token `q`, the largest token `m`, and the set `A` of the other positions holding a token below `m`:

* `A` empty: the inputs `(m, ..., m)` and `(m, ..., m, q)`, tested output by output (their cases
  with only the largest token, and with the query and the largest token), the positional path still
  pessimised;
* `A` of `c` positions (`1 ≤ c ≤ n - 1` if the query holds `m`, else `c ≤ n - 2`): for each
  non-maximal token `k`, the test of the inputs with `k` at `c` positions, for the worst choice of
  the `c` positions, found by trying every pattern of `c` positions (their code sorts the positional
  scores instead; the same verdicts, at a cost that grows as `2^n`); the inputs whose non-maximal
  tokens all pass are counted, `|G|^c` of them for each `A` (their convexity argument: an input with
  several non-maximal tokens is no worse than the one with only its worst).

The bounds on `e^{s_p}` are those of the counted language's `exp` on the two parts of the score,
`e^{EQKE[q, t]}` and `e^{EQKP[q, p]}`; `kup` takes `max (lo y, hi y)`, an upper bound on `e y`
for `lo ≤ e ≤ hi` whatever the sign of `y`. The number `|G|^c` of a pattern is assembled from the
comparisons `i ≤ |G|`, `Σ_i (i^c - (i - 1)^c) [i ≤ |G|]`: the counted language does not multiply
counts.

The checker reads the weights' shapes and lengths (free) and refuses (count 0) unless they are the
family's with `V ≥ 2` and `n ≥ 2`.
-/

namespace GrossCubic

open CompactCheck AttnClasses

section Checker

variable (I : Interp)

/-- `max (lo y) (hi y)`: an upper bound on `e y` for every `e` between the bounds `b = (lo, hi)`. -/
def kup (b : I.V × I.V) (y : I.V) : I.M I.V := do
  let a ← I.muladd cat I.zero b.1 y
  let c ← I.muladd cat I.zero b.2 y
  I.max cat a c

/-- The largest entry of a list (zero for the empty list). -/
def maxL : List I.V → I.M I.V
  | [] => pure I.zero
  | a :: rs => rs.foldlM (fun s v => I.max cat s v) a

/-- The sum of a list (zero for the empty list). -/
def sumL : List I.V → I.M I.V
  | [] => pure I.zero
  | a :: rs => rs.foldlM (fun s v => I.add cat s v) a

/-- Entry `(i, j)` of a table of numbers. -/
def at2 (A : List (List I.V)) (i j : ℕ) : I.V := (A.getD i []).getD j I.zero

/-- Entry `(i, j)` of a table of bounds. -/
def bt2 (A : List (List (I.V × I.V))) (i j : ℕ) : I.V × I.V :=
  (A.getD i []).getD j (I.zero, I.zero)

/-- The outputs other than `m`. -/
def others (V m : ℕ) : List ℕ := (List.range V).filter fun j => j != m

/-- Bounds on `exp` of every entry of a table. -/
def expT (A : List (List I.V)) : I.M (List (List (I.V × I.V))) :=
  A.mapM fun r => r.mapM fun s => I.exp cat s

/-- The positions (among the `L` other than the query's) in the pattern `pat`. -/
def inPat (L pat : ℕ) : List ℕ := (List.range L).filter pat.testBit

/-- `Pp[j] = max_p (PVOU[p, j] - PVOU[p, m])`, for every output `j`. -/
def ppess (V n m : ℕ) (PV : List (List I.V)) : I.M (List I.V) :=
  (List.range V).mapM fun j => do
    let ds ← (List.range n).mapM fun p => I.sub cat (at2 I PV p j) (at2 I PV p m)
    maxL I ds

/-- `u[t] = max_{j ≠ m} EUPU[t, j] - EUPU[t, m]`, for the query token `t`. -/
def dirU (V m t : ℕ) (EU : List (List I.V)) : I.M I.V := do
  let a ← maxL I ((others V m).map fun j => at2 I EU t j)
  I.sub cat a (at2 I EU t m)

/-- `v[t] = max_{j ≠ m} (EVOU[t, j] + Pp[j]) - EVOU[t, m]`, for the key token `t`. -/
def keyE (V m t : ℕ) (EV : List (List I.V)) (Pp : List I.V) : I.M I.V := do
  let ys ← (others V m).mapM fun j => I.add cat (at2 I EV t j) (Pp.getD j I.zero)
  let a ← maxL I ys
  I.sub cat a (at2 I EV t m)

/-- The input `(m, ..., m)`: every position holds `m`, each output tested with the positional path
    pessimised. -/
def onlyMax (V m : ℕ) (EU EV : List (List I.V)) (Pp : List I.V) : I.M I.B := do
  let vs ← (others V m).mapM fun j => do
    let a ← I.add cat (at2 I EU m j) (at2 I EV m j)
    I.add cat a (Pp.getD j I.zero)
  let top ← maxL I vs
  let rhs ← I.add cat (at2 I EU m m) (at2 I EV m m)
  I.lt cat top rhs

/-- Bounds on a product `x y` of two positive numbers from bounds on each, the lower ones
    clamped at zero. -/
def prodB (a b : I.V × I.V) : I.M (I.V × I.V) := do
  let x ← I.max cat I.zero a.1
  let y ← I.max cat I.zero b.1
  let lo ← I.muladd cat I.zero x y
  let hi ← I.muladd cat I.zero a.2 b.2
  pure (lo, hi)

/-- `kup w (a + v - c)`: one position's term of one output, from its weight's bounds `w`. -/
def term (w : I.V × I.V) (a v c : I.V) : I.M I.V := do
  let s ← I.add cat a v
  kup I w (← I.sub cat s c)

/-- The input `(m, ..., m, q)` with `q` below `m`, output by output, the positional path
    pessimised: the weights of the positions holding `m` and of the query, as products of
    bounds. -/
def queryOnly (V n m q : ℕ) (EU EV : List (List I.V)) (Pp : List I.V)
    (XE XP : List (List (I.V × I.V))) : I.M I.B := do
  let slo ← sumL I ((List.range (n - 1)).map fun p => (bt2 I XP q p).1)
  let shi ← sumL I ((List.range (n - 1)).map fun p => (bt2 I XP q p).2)
  let wm ← prodB I (bt2 I XE q m) (slo, shi)
  let wq ← prodB I (bt2 I XE q q) (bt2 I XP q (n - 1))
  let c1 ← I.add cat (at2 I EU q m) (at2 I EV m m)
  let c2 ← I.add cat (at2 I EU q m) (at2 I EV q m)
  let ubs ← (others V m).mapM fun j => do
    let a ← I.add cat (at2 I EU q j) (Pp.getD j I.zero)
    let k1 ← term I wm a (at2 I EV m j) c1
    let k2 ← term I wq a (at2 I EV q j) c2
    I.add cat k1 k2
  let top ← maxL I ubs
  I.lt cat top I.zero

/-- The verdicts of one non-maximal token, from the bounds `pk` of its terms at the positions
    other than the query's and those `pm` of the largest token: for `c = 1, ..., ncs`, whether
    `qb + Σ_{p ∈ A} (pk[p] - pm[p]) < 0` for every set `A` of `c` positions (the largest such sum,
    over the patterns of `c` bits). -/
def kverd (n : ℕ) (qb : I.V) (pk pm : List I.V) (ncs : ℕ) : I.M (List I.B) := do
  let dps ← (List.range (n - 1)).mapM fun p => I.sub cat (pk.getD p I.zero) (pm.getD p I.zero)
  let sums ← (List.range (Nat.pow 2 (n - 1))).mapM fun pat =>
    sumL I ((inPat (n - 1) pat).map fun p => dps.getD p I.zero)
  (List.range ncs).mapM fun c' => do
    let top ← maxL I (((List.range (Nat.pow 2 (n - 1))).filter fun pat =>
      (inPat (n - 1) pat).length == c' + 1).map fun pat => sums.getD pat I.zero)
    let tot ← I.add cat qb top
    I.lt cat tot I.zero

/-- The number of inputs of one pattern of `c = c' + 1` positions: `|G|^c`, with `G` the
    non-maximal tokens whose verdict `vs` passes. For `c = 1` the count of the verdicts; else
    `Σ_j (j^c - (j - 1)^c) [j ≤ |G|]`, `|G|` as a number and `js[i] = i + 1`. -/
def patCount (lam c' : ℕ) (vs : List I.B) (one : I.V) (js : List I.V) : I.M I.N := do
  if c' = 0 then
    pure (vs.foldl (fun a b => I.nadd a (I.countB b)) I.nzero)
  else do
    let sel ← vs.mapM fun b => I.selectV cat b one I.zero
    let g ← sumL I sel
    let bs ← (List.range lam).mapM fun i => I.le cat (js.getD i I.zero) g
    pure ((List.range lam).foldl (fun a i =>
      I.nadd a (I.nscale (Nat.pow (i + 1) (c' + 1) - Nat.pow i (c' + 1)) (bs.getD i I.bfalse)))
      I.nzero)

/-- The inputs with the query of rank `rq`, the largest token `m` of rank `lam`, and at least
    one other position holding a token below `m`. `us`, `ks`: `u` and `E` of the tokens of rank
    `≤ lam`. -/
def withNonmax (mx : Bool) (V n lam rq : ℕ) (us ks : List I.V)
    (XE XP : List (List (I.V × I.V))) (one : I.V) (js : List I.V) : I.M I.N := do
  let q := tok mx V rq
  let uq := us.getD rq I.zero
  let phis ← (List.range (lam + 1)).mapM fun r => do
    let y ← I.add cat (ks.getD r I.zero) uq
    kup I (bt2 I XE q (tok mx V r)) y
  let psis ← (List.range (lam + 1)).mapM fun r =>
    (List.range (n - 1)).mapM fun p => kup I (bt2 I XP q p) (phis.getD r I.zero)
  let psiq ← kup I (bt2 I XP q (n - 1)) (phis.getD rq I.zero)
  let base ← sumL I (psis.getD lam [])
  let qb ← I.add cat base psiq
  let ncs := if rq = lam then n - 1 else n - 2
  let verd ← (List.range lam).mapM fun kappa =>
    kverd I n qb (psis.getD kappa []) (psis.getD lam []) ncs
  let cnts ← (List.range ncs).mapM fun c' =>
    patCount I lam c' (verd.map fun l => l.getD c' I.bfalse) one js
  -- a pattern of `c` positions counts `cnts[c - 1]`; none for `c = 0` or `c > ncs`
  pure ((List.range (Nat.pow 2 (n - 1))).foldl (fun a pat =>
    I.nadd a ((I.nzero :: cnts).getD (inPat (n - 1) pat).length I.nzero)) I.nzero)

/-- Every input whose largest token has rank `lam`. -/
def block (mx : Bool) (V n : ℕ) (EU EV PV : List (List I.V)) (XE XP : List (List (I.V × I.V)))
    (one : I.V) (js : List I.V) (lam : ℕ) : I.M I.N := do
  let m := tok mx V lam
  let Pp ← ppess I V n m PV
  let us ← (List.range (lam + 1)).mapM fun r => dirU I V m (tok mx V r) EU
  let ks ← (List.range (lam + 1)).mapM fun r => keyE I V m (tok mx V r) EV Pp
  let b0 ← onlyMax I V m EU EV Pp
  let b1 ← (List.range lam).mapM fun rq =>
    queryOnly I V n m (tok mx V rq) EU EV Pp XE XP
  let cs ← (List.range (lam + 1)).mapM fun rq => withNonmax I mx V n lam rq us ks XE XP one js
  pure (cs.foldl I.nadd (b1.foldl (fun a b => I.nadd a (I.countB b)) (I.countB b0)))

/-- The checker, for the label `max` (`mx`) or `min`, the graph `g` and the task `task`. -/
def check (mx : Bool) (g : Graph) (_task : Task) : I.M I.N := do
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
  let V := g.values
  let n := g.positions
  let d := sE.getD 1 0
  let h := sQ.getD 1 0
  if wellFormed V n d h [sE, sP, sQ, sK, sV, sO, sU, sC] [lE, lP, lQ, lK, lV, lO, lU, lC] &&
      Nat.ble 2 V && Nat.ble 2 n then do
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
    let last := Ps.getD (n - 1) []
    let Eq ← Es.mapM (vadd I · last)
    let Qs ← mm I Eq Qc
    let SE ← mm I Qs (← mm I Es Kc)
    let SP ← mm I Qs (← mm I Ps Kc)
    let VOU ← mm I (← mm I Vr Oc) Uc
    let VOUc := (List.range V).map fun j => VOU.map (·.getD j I.zero)
    let EV ← mm I Es VOUc
    let PV ← mm I Ps VOUc
    let EU ← mm I Eq Uc
    let XE ← expT I SE
    let XP ← expT I SP
    let js ← (List.range (V - 1)).mapM fun i => I.lit cat (i + 1)
    let cs ← (List.range V).mapM (block I mx V n EU EV PV XE XP (js.getD 0 I.zero) js)
    pure (cs.foldl I.nadd I.nzero)
  else pure I.nzero

end Checker

end GrossCubic
