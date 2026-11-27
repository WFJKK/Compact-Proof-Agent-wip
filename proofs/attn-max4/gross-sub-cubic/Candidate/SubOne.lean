import Candidate.LibSubCheck

/-!
# Entry 9's checker cut to one configuration

`check1` is entry 9's `check` with the method of the error fixed to `max_diff` (`err = 1`) and the method
of the direct path to `mean_query+max_diff` (`eu = 0`): the branches of `errOut`, `eupuOut` and
`errCertLen` that those choices take, and nothing else. It computes what `check I mx 1 0` computes, the same
operations in the same order (`check1_eq`, by definition), so entry 9's soundness theorem holds for it as
it is. Entry 9 carries all 100 of their configurations in one checker, and the open lane measures a
checker's description with every branch it holds; this one holds only the branches it runs.
-/

namespace GrossSub

open CompactCheck AttnClasses GrossCubic

section Checker

variable (I : Interp)

/-- Step 1 for `max_diff` (`errOut`'s branch for `err = 1`): their `split_SVD` at the certificate's
    directions and a bound on each row of the remainder from the certificate's mean row. -/
def errOut1 (V d h off : ℕ) (Eq Ek Qc Kc Mqk : List (List I.V)) :
    I.M (List (List I.V) × List I.V × I.B) := do
  let r := if h < d then h else d
  let fb ← factors I d h Eq Ek Qc Kc Mqk
  let u ← certVec I off V
  let v ← certVec I (off + V) V
  let s ← svdSplit I V r fb.1 fb.2 u v
  let a ← certVec I (off + 2 * V) r
  let eps ← rowBound I r V s.2.1 s.2.2 a
  pure (s.1, eps, I.btrue)

/-- The direct path for `mean_query+max_diff` (`eupuOut`'s branch for `eu = 0`). -/
def eupuOut0 (V d : ℕ) (Eq Ur : List (List I.V)) (mu : List I.V) :
    I.M (List I.V × List I.V) := do
  let muU ← vecMat I V mu Ur
  let su ← Ur.mapM (spread I)
  let sp ← Eq.mapM fun row => absDot I row mu su d
  pure (muU, sp)

/-- Entry 9's `check` for `err = 1` and `eu = 0`. -/
def check1 (mx : Bool) (gap : ℕ → ℕ → ℕ → ℕ) (g : Graph) (_task : Task) :
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
      Nat.ble (2 * d + 2 * (V * n) + (2 * V + (if h < d then h else d))) cs then do
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
    let s1 ← errOut1 I V d h (2 * d + 2 * (V * n)) Eq Ek Qc Kc Mqk
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
    let du ← eupuOut0 I V d Eq Ur mu
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

/-- `check1` is `check` at `err = 1`, `eu = 0`: the branches not taken unfold away. -/
theorem check1_eq (I : Interp) (mx : Bool) (gap : ℕ → ℕ → ℕ → ℕ) (g : Graph) (task : Task) :
    check1 I mx gap g task = check I mx 1 0 gap g task := rfl

end GrossSub
