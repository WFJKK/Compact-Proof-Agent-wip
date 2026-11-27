import Candidate.LibCommonBasic

/-!
# Entry 6: one-head attention, path tables and pessimised classes

The family: the one-layer, one-head, attention-only transformer of Gross et al. (the pipeline's
`models/attn-max2/model.py`, the same for every attention task), with `n` positions, `V` tokens,
width `d` and head size `h`, read at the last position `Q = n - 1`; the label is the largest token
(`max`) or the smallest (`min`). On input `x`, with query token `q = x_Q`,

    logit_j = D[q, j] + Σ_p α_p · O[x_p, p, j],     α = softmax_p (S[q, x_p, p]),

where `D[q] = (E_q + P_Q) U` is the direct path, `O[t, p] = (E_t + P_p) W_V W_O U` what token `t`
at position `p` writes through the head, and `S[q, t, p] = c (E_q + P_Q) W_Q · (E_t + P_p) W_K` its
attention score (`c` the scale). These are the path tables; they cost `O(V² d)`.

Write `ℓ` for the label. For every output `j ≠ ℓ`, since the weights add up to one,

    logit_ℓ - logit_j = Σ_p α_p ((D[q, ℓ] - D[q, j]) + (O[x_p, p, ℓ] - O[x_p, p, j]))
                      ≥ Σ_p α_p (Dd[q, ℓ] + G[x_p, p, ℓ]),

with the margins `Dd[q, ℓ] = D[q, ℓ] - max_{j ≠ ℓ} D[q, j]` and
`G[t, p, ℓ] = O[t, p, ℓ] - max_{j ≠ ℓ} O[t, p, j]`. Multiplied by the softmax's
denominator, the input is answered correctly if

    Σ_p K(q, x_p, p, ℓ) > 0,    K(q, t, p, ℓ) = min (lo · H, hi · H),

with `H = Dd[q, ℓ] + G[t, p, ℓ]` and `lo ≤ exp S[q, t, p] ≤ hi` from `exp`'s enclosure,
since `K ≤ exp(S) · H` whatever the sign of `H`.

Inputs are tested by classes. Ranks order the tokens so that the label is the largest rank (the
token itself for `max`, `V - 1 - t` for `min`). A class fixes the query's rank `ρq`, the label's
rank `λ`, the set `P` of the other positions that hold the label (`pat`, as bits) and the largest
rank `ρ'` at the remaining positions `R`. Its test bounds the positions in `R` by the running
minimum of `K` over ranks up to `ρ'`:

    K(q, q, Q, ℓ) + Σ_{p ∈ P} K(q, ℓ, p, ℓ)
      + Σ_{p ∈ R} min_{ρ ≤ ρ'} K(q, tok ρ, p, ℓ) > 0.

There are `O(V³ 2^n)` classes, each tested with about `n` operations. The verdicts go into a table,
and the count looks up each input's class in it: that is bookkeeping on public structure, free,
and every input of a class that passes is counted.

The checker reads the weights' shapes and lengths (free) and refuses (count 0) unless they are the
family's.
-/

namespace AttnClasses

open CompactCheck

/-! ## Names -/

def nE : String := "E"
def nP : String := "P"
def nQ : String := "WQ"
def nK : String := "WK"
def nV : String := "WV"
def nO : String := "WO"
def nU : String := "U"
def nC : String := "#const0"

/-- The category of every charge. -/
def cat : String := "attn"

/-- The token of rank `ρ`: `ρ` when the label is the largest token, `V - 1 - ρ` when it is the
    smallest. On `[0, V)` it is its own inverse, so it also gives a token's rank. -/
def tok (mx : Bool) (V ρ : ℕ) : ℕ := if mx then ρ else V - 1 - ρ

/-- The weights have the family's shapes and lengths: `E : V × d`, `P : n × d`,
    `W_Q, W_K, W_V : d × h`, `W_O : h × d`, `U : d × V`, and the scale a number. -/
def wellFormed (V n d h : ℕ) (s : List (List ℕ)) (l : List ℕ) : Bool :=
  s == [[V, d], [n, d], [d, h], [d, h], [d, h], [h, d], [d, V], []] &&
    l == [V * d, n * d, d * h, d * h, d * h, h * d, d * V, 1]

section Checker

variable (I : Interp)

/-- Row `i` of a matrix with `cols` columns. -/
def row (nm : String) (cols i : ℕ) : I.M (List I.V) :=
  (List.range cols).mapM fun j => I.weight nm (i * cols + j)

/-- Column `j` of a matrix with `rows` rows and `cols` columns. -/
def col (nm : String) (rows cols j : ℕ) : I.M (List I.V) :=
  (List.range rows).mapM fun i => I.weight nm (i * cols + j)

/-- `Σ_i x_i y_i`, one multiply-add per term. -/
def dot (xs ys : List I.V) : I.M I.V :=
  (List.zip xs ys).foldlM (fun s p => I.muladd cat s p.1 p.2) I.zero

/-- The products of the rows `A` with the columns `B`: `C[i][j] = A[i] · B[j]`. -/
def mm (A B : List (List I.V)) : I.M (List (List I.V)) :=
  A.mapM fun r => B.mapM (dot I r)

/-- Entrywise sum. -/
def vadd (xs ys : List I.V) : I.M (List I.V) :=
  (List.zip xs ys).mapM fun p => I.add cat p.1 p.2

/-- Running maxima or minima: `out[i] = f (... f (r_0, r_1) ..., r_i)`. -/
def scan (f : I.V → I.V → I.M I.V) : List I.V → I.M (List I.V)
  | [] => pure []
  | a :: rs => do
    let p ← rs.foldlM (fun (acc : I.V × List I.V) v => do
      let m ← f acc.1 v
      pure (m, acc.2 ++ [m])) (a, [a])
    pure p.2

/-- `r[l] - max_{j ≠ l} r[j]` for every `l`, from the running maxima from either end. -/
def marg (r : List I.V) : I.M (List I.V) := do
  let pre ← scan I (I.max cat) r
  let suf ← scan I (I.max cat) r.reverse
  (List.range r.length).mapM fun l => do
    let m ← if l = 0 then pure (suf.getD (r.length - 2) I.zero)
      else if l + 1 = r.length then pure (pre.getD (l - 1) I.zero)
      else I.max cat (pre.getD (l - 1) I.zero) (suf.getD (r.length - 2 - l) I.zero)
    I.sub cat (r.getD l I.zero) m

/-- A lower bound on `exp(S) · (dd + gg)` from the bounds `b` on `exp(S)`. -/
def kterm (b : I.V × I.V) (dd gg : I.V) : I.M I.V := do
  let hh ← I.add cat dd gg
  let a ← I.muladd cat I.zero b.1 hh
  let c ← I.muladd cat I.zero b.2 hh
  I.min cat a c

/-- For each position `p < n - 1`, the running minima of `K (tok ρ) p` over the ranks
    `ρ < lam`. -/
def minRows (mx : Bool) (V n lam : ℕ) (K : ℕ → ℕ → I.M I.V) : I.M (List (List I.V)) :=
  (List.range (n - 1)).mapM fun p => do
    let r ← (List.range lam).mapM fun ρ => K (tok mx V ρ) p
    scan I (I.min cat) r

/-- The verdicts of the patterns of one query rank `ρq` and label rank `lam`, from the query's term
    `kq`, the label's terms `kl` and the running minima `kp`: for each pattern `pat` (the other
    positions holding the label are its bits), empty if no input has it, `[v]` if no position is
    left, else one verdict per largest rank `ρ' < lam` there. (`Nat.pow` and `List.isEmpty`, not
    `2 ^ _` and `= []`: with Mathlib imported, those elaborate to instances that are not in the
    counted language.) -/
def patterns (n ρq lam : ℕ) (kq : I.V) (kl : List I.V) (kp : List (List I.V)) :
    I.M (List (List I.B)) :=
  (List.range (Nat.pow 2 (n - 1))).mapM fun pat => do
    let P := (List.range (n - 1)).filter pat.testBit
    let R := (List.range (n - 1)).filter fun p => !pat.testBit p
    if ρq ≠ lam ∧ P.isEmpty then pure [] else do
      let base ← P.foldlM (fun s p => I.add cat s (kl.getD p I.zero)) kq
      if R.isEmpty then do
        let b ← I.lt cat I.zero base
        pure [b]
      else (List.range lam).mapM fun ρ => do
        let s ← R.foldlM (fun s p => I.add cat s ((kp.getD p []).getD ρ I.zero)) base
        I.lt cat I.zero s

/-- The verdicts of the classes with query rank `ρq` and label rank `lam ≥ ρq`. The rows of the
    other positions are needed when the query holds the label or there are three positions
    or more. -/
def block (mx : Bool) (V n : ℕ) (X : List (List (List (I.V × I.V)))) (Dd : List (List I.V))
    (G : List (List (List I.V))) (ρq lam : ℕ) : I.M (List (List I.B)) := do
  let tq := tok mx V ρq
  let l := tok mx V lam
  let K := fun t p => kterm I (((X.getD tq []).getD t []).getD p (I.zero, I.zero))
    ((Dd.getD tq []).getD l I.zero) (((G.getD t []).getD p []).getD l I.zero)
  let kq ← K tq (n - 1)
  let kl ← (List.range (n - 1)).mapM (K l)
  let kp ← (if ρq = lam ∨ 3 ≤ n then minRows I mx V n lam K else pure [])
  patterns I n ρq lam kq kl kp

/-- The verdict of the class of input `x` in the table `vt`. -/
def verdict (mx : Bool) (V n : ℕ) (vt : List (List (List (List I.B)))) (x : Input) : I.B :=
  let rs := x.map (tok mx V)
  let lam := rs.foldl max 0
  let os := rs.take (n - 1)
  let pat := ((List.range (n - 1)).map fun p => os.getD p 0 == lam).foldr
    (fun b a => 2 * a + cond b 1 0) 0
  let R := os.filter fun r => r ≠ lam
  (((vt.getD (rs.getLastD 0) []).getD lam []).getD pat []).getD (R.foldl max 0) I.bfalse

/-- The checker, for the label `max` (`mx`) or `min`, the graph `g` and the task `task`. -/
def check (mx : Bool) (g : Graph) (task : Task) : I.M I.N := do
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
  if wellFormed V n d h [sE, sP, sQ, sK, sV, sO, sU, sC] [lE, lP, lQ, lK, lV, lO, lU, lC] then do
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
    let Qs ← mm I (← Es.mapM (vadd I · last)) Qc
    let SE ← mm I Qs (← mm I Es Kc)
    let SP ← mm I Qs (← mm I Ps Kc)
    let VOU ← mm I (← mm I Vr Oc) Uc
    let VOUc := (List.range V).map fun j => VOU.map (·.getD j I.zero)
    let EO ← mm I Es VOUc
    let PO ← mm I Ps VOUc
    let PU ← mm I [last] Uc
    let Dd ← (← mm I Es Uc).mapM fun r => do marg I (← vadd I r (PU.getD 0 []))
    let G ← EO.mapM fun r => PO.mapM fun s => do marg I (← vadd I r s)
    let X ← (List.zip SE SP).mapM fun p => p.1.mapM fun s => p.2.mapM fun s' => do
      I.exp cat (← I.add cat s s')
    let vt ← (List.range V).mapM fun ρq => (List.range V).mapM fun lam =>
      if ρq ≤ lam then block I mx V n X Dd G ρq lam else pure []
    pure ((allInputs task.space).foldl (fun a x => I.nadd a (I.countB (verdict I mx V n vt x)))
      I.nzero)
  else pure I.nzero

end Checker

end AttnClasses
