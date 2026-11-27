import Candidate.Checker

/-!
# The group checker with a slack threshold (c003): `lo * h` for every near term, and the test
`theta < L_j` with `theta = 4 * deltamax * H` (deltamax: the widest exp interval of the pair, H: a bound on |h|).
-/

namespace Candidate.Checker2
open CompactCheck Candidate.Loops Candidate.Tables Candidate.Checker

/-- `lo * h`: below `e * h` up to `(hi - lo) * |h|`. -/
def loProdM (I : Interp) (lo h : I.V) : I.M I.V := I.muladd "" I.zero lo h

/-- `4 * H` with `H = (max ov - min ov) + (max dm - min dm) ≥ |h|` for every term. -/
def boundH (I : Interp) (tabs : Tabs I) : I.M I.V := do
  let ovMax ← maxM I (fun k => tabs.ov.getD k I.zero) 16384 (tabs.ov.getD 0 I.zero)
  let ovMin ← minM I (fun k => tabs.ov.getD k I.zero) 16384 (tabs.ov.getD 0 I.zero)
  let dmMax ← maxM I (fun k => tabs.dm.getD k I.zero) 4096 (tabs.dm.getD 0 I.zero)
  let dmMin ← minM I (fun k => tabs.dm.getD k I.zero) 4096 (tabs.dm.getD 0 I.zero)
  let r1 ← I.sub "" ovMax ovMin
  let r2 ← I.sub "" dmMax dmMin
  let h ← I.add "" r1 r2
  let four ← I.lit "" 4
  I.muladd "" I.zero four h

/-- All `j ≠ m` have a lower bound `L_j` above `theta`. -/
def okOfM (I : Interp) (term Fm Fm1 fx3 : Array I.V) (theta : I.V) (m istar : Nat) : I.M I.B :=
  allM I (fun j =>
    if j = m then pure I.btrue else do
      let L0 ← I.add "" (fx3.getD j I.zero) (cSel I term Fm Fm1 istar 0 j)
      let L1 ← I.add "" L0 (cSel I term Fm Fm1 istar 1 j)
      let L2 ← I.add "" L1 (cSel I term Fm Fm1 istar 2 j)
      I.lt "" theta L2) 64 I.btrue

/-- The four flags of the groups (t3, m, i*), i* < 4, for `1 ≤ m`, `t3 ≤ m`, shift `K`, window start `a`. -/
def groupFlagsK (I : Interp) (tabs : Tabs I) (H4 : I.V) (t3 m : Nat) (K : I.V) (a : Nat) : I.M (List I.B) := do
  let cpr ← tableM I (fun j => I.sub "" (tabs.dm.getD (t3*64+j) I.zero) (tabs.dm.getD (t3*64+m) I.zero)) 64 0 (E0 I)
  -- exp bounds at slot i*3 + (t-a), t ∈ [a, m]
  let exlo ← tableM I (fun k =>
    if a + k%3 ≤ m then do
      let p ← expAt I tabs K t3 (k/3) (a + k%3)
      pure p.1
    else pure I.zero) 9 0 (E0 I)
  let exhi ← tableM I (fun k =>
    if a + k%3 ≤ m then do
      let p ← expAt I tabs K t3 (k/3) (a + k%3)
      pure p.2
    else pure I.zero) 9 0 (E0 I)
  let e3 ← expAt I tabs K t3 3 t3
  let negEfar ← tableM I (fun i =>
    if a = 0 then pure I.zero else do
      let d ← I.sub "" (tabs.spre.getD ((t3*3+i)*65+a) I.zero) K
      let p ← I.exp "" d
      I.neg "" p.2) 3 0 (E0 I)
  -- the widest interval, and the threshold
  let dtab ← tableM I (fun k => I.sub "" (exhi.getD k I.zero) (exlo.getD k I.zero)) 9 0 (E0 I)
  let d3 ← I.sub "" e3.2 e3.1
  let dmax ← maxM I (fun k => dtab.getD k I.zero) 9 d3
  let theta ← I.muladd "" I.zero dmax H4
  -- the t = m term, index i*64+j
  let term ← tableM I (fun k => do
    let h ← hM I tabs cpr m (k/64) m (k%64)
    loProdM I (exlo.getD (k/64*3 + (m-a)) I.zero) h) 192 0 (E0 I)
  -- lower bound over the range [0, m), index i*64+j
  let Fm ← tableM I (fun k => do
    let near ← minRangeM I (fun t => do
      let h ← hM I tabs cpr m (k/64) t (k%64)
      loProdM I (exlo.getD (k/64*3 + (t-a)) I.zero) h) a (m - a)
    if a = 0 then pure near else do
      let n1 ← I.sub "" (tabs.ovmax.getD ((k/64*64+k%64)*65+a) I.zero) (tabs.ovmin.getD ((k/64*64+m)*65+a) I.zero)
      let n2 ← I.add "" (cpr.getD (k%64) I.zero) n1
      let n3 ← I.max "" I.zero n2
      let far ← I.muladd "" I.zero (negEfar.getD (k/64) I.zero) n3
      I.min "" near far) 192 0 (E0 I)
  -- lower bound over the range [0, m]
  let Fm1 ← tableM I (fun k => I.min "" (Fm.getD k I.zero) (term.getD k I.zero)) 192 0 (E0 I)
  -- position 3, token t3
  let fx3 ← tableM I (fun j => do
    let h ← hM I tabs cpr m 3 t3 j
    loProdM I e3.1 h) 64 0 (E0 I)
  if t3 = m then do
    let ok3 ← okOfM I term Fm Fm1 fx3 theta m 3
    pure [I.bfalse, I.bfalse, I.bfalse, ok3]
  else do
    let ok0 ← okOfM I term Fm Fm1 fx3 theta m 0
    let ok1 ← okOfM I term Fm Fm1 fx3 theta m 1
    let ok2 ← okOfM I term Fm Fm1 fx3 theta m 2
    pure [ok0, ok1, ok2, I.bfalse]

def groupFlags (I : Interp) (tabs : Tabs I) (H4 : I.V) (t3 m W : Nat) : I.M (List I.B) :=
  groupFlagsK I tabs H4 t3 m (tabs.kk.getD (t3*64+m) I.zero) (if W = 1 then m - 1 else m - 2)

/-- The flags of `(t3, m) = (g2/64, g2%64)` when it is a valid pair with `t3` in the plan's slice; else all false. -/
def stepFlags (I : Interp) (tabs : Tabs I) (H4 : I.V) (plan : List Nat) (lo hi g2 : Nat) : I.M (List I.B) :=
  if g2 / 64 ≤ g2 % 64 && g2 % 64 ≠ 0 && lo ≤ g2 / 64 && g2 / 64 < hi then
    groupFlags I tabs H4 (g2 / 64) (g2 % 64) (plan.getD (2 + g2 % 64) 2)
  else pure [I.bfalse, I.bfalse, I.bfalse, I.bfalse]

/-- Flags of all groups, in group order `(t3*64+m)*4 + i*`; only `t3 ∈ [lo, hi)` are computed. -/
def groupsM (I : Interp) (tabs : Tabs I) (H4 : I.V) (plan : List Nat) (lo hi : Nat) : Nat → Nat → Array I.B → I.M (Array I.B)
  | 0, _, arr => pure arr
  | k+1, g2, arr => do
    let fl ← stepFlags I tabs H4 plan lo hi g2
    groupsM I tabs H4 plan lo hi k (g2+1)
      ((((arr.push (fl.getD 0 I.bfalse)).push (fl.getD 1 I.bfalse)).push (fl.getD 2 I.bfalse)).push (fl.getD 3 I.bfalse))

def D (plan : List Nat) : Checker := fun I => do
  let ok ← shapesOk I
  if !ok then pure I.nzero else do
    let tabs ← buildTabs I
    let H4 ← boundH I tabs
    let flags ← groupsM I tabs H4 plan (plan.getD 0 0) (plan.getD 1 64) 4096 0 (Array.mk [])
    pure (sumInputs I [64, 64, 64, 64] (fun x => I.countB (flags.getD (gidx x) I.bfalse)))

end Candidate.Checker2