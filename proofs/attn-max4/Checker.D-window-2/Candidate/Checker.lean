import Candidate.Tables

/-!
# The group checker (c002, W = 2): per (t3, m) exact near-window terms, loose far bound, flags per group.
-/

namespace Candidate.Checker
open CompactCheck Protected.N_attn_max4_v64_s0 Candidate.Loops Candidate.Tables

/-- `min (lo*h) (hi*h)`: a lower bound on `e*h` for `lo ≤ e ≤ hi`. -/
def lbProdM (I : Interp) (lo hi h : I.V) : I.M I.V := do
  let a ← I.muladd "" I.zero lo h
  let b ← I.muladd "" I.zero hi h
  I.min "" a b

/-- `acc && f 0 && ... && f (n-1)`. -/
def allM (I : Interp) (f : Nat → I.M I.B) : Nat → I.B → I.M I.B
  | 0, acc => pure acc
  | k+1, acc => do
    let b ← f k
    let acc' ← I.band "" acc b
    allM I f k acc'

/-- `min (f t0) ... (f (t0+n-1))` for `n ≥ 1` (`n = 0` is read as 1). -/
def minRangeM (I : Interp) (f : Nat → I.M I.V) (t0 : Nat) : Nat → I.M I.V
  | 0 => f t0
  | 1 => f t0
  | n+2 => do
    let acc ← minRangeM I f t0 (n+1)
    let v ← f (t0+n+1)
    I.min "" acc v

/-- `(ov[i,t,m] - ov[i,t,j]) - cpr[j]` = `(Dm[m]+OV[i,t,m]) - (Dm[j]+OV[i,t,j])`. -/
def hM (I : Interp) (tabs : Tabs I) (cpr : Array I.V) (m i t j : Nat) : I.M I.V := do
  let d ← I.sub "" (tabs.ov.getD ((i*64+t)*64+m) I.zero) (tabs.ov.getD ((i*64+t)*64+j) I.zero)
  I.sub "" d (cpr.getD j I.zero)

/-- Bounds on `exp (s[t3,i,t] - K)`. -/
def expAt (I : Interp) (tabs : Tabs I) (K : I.V) (t3 i t : Nat) : I.M (I.V × I.V) := do
  let d ← I.sub "" (tabs.s.getD ((t3*4+i)*64+t) I.zero) K
  I.exp "" d

/-- The lower bound used for position `i` in the group `i*`: the `t = m` term at `i*`, the range `[0, m]`
    before it, the range `[0, m)` after it. -/
def cSel (I : Interp) (term Fm Fm1 : Array I.V) (istar i j : Nat) : I.V :=
  if i = istar then term.getD (i*64+j) I.zero
  else if i < istar then Fm1.getD (i*64+j) I.zero else Fm.getD (i*64+j) I.zero

/-- All `j ≠ m` have a positive lower bound `L_j`. -/
def okOfM (I : Interp) (term Fm Fm1 fx3 : Array I.V) (m istar : Nat) : I.M I.B :=
  allM I (fun j =>
    if j = m then pure I.btrue else do
      let L0 ← I.add "" (fx3.getD j I.zero) (cSel I term Fm Fm1 istar 0 j)
      let L1 ← I.add "" L0 (cSel I term Fm Fm1 istar 1 j)
      let L2 ← I.add "" L1 (cSel I term Fm Fm1 istar 2 j)
      I.lt "" I.zero L2) 64 I.btrue

/-- The four flags of the groups (t3, m, i*), i* < 4, for `1 ≤ m`, `t3 ≤ m`, shift `K`, window start `a`. -/
def groupFlagsK (I : Interp) (tabs : Tabs I) (t3 m : Nat) (K : I.V) (a : Nat) : I.M (List I.B) := do
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
  -- the t = m term, index i*64+j
  let term ← tableM I (fun k => do
    let h ← hM I tabs cpr m (k/64) m (k%64)
    lbProdM I (exlo.getD (k/64*3 + (m-a)) I.zero) (exhi.getD (k/64*3 + (m-a)) I.zero) h) 192 0 (E0 I)
  -- lower bound over the range [0, m), index i*64+j
  let Fm ← tableM I (fun k => do
    let near ← minRangeM I (fun t => do
      let h ← hM I tabs cpr m (k/64) t (k%64)
      lbProdM I (exlo.getD (k/64*3 + (t-a)) I.zero) (exhi.getD (k/64*3 + (t-a)) I.zero) h) a (m - a)
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
    lbProdM I e3.1 e3.2 h) 64 0 (E0 I)
  if t3 = m then do
    let ok3 ← okOfM I term Fm Fm1 fx3 m 3
    pure [I.bfalse, I.bfalse, I.bfalse, ok3]
  else do
    let ok0 ← okOfM I term Fm Fm1 fx3 m 0
    let ok1 ← okOfM I term Fm Fm1 fx3 m 1
    let ok2 ← okOfM I term Fm Fm1 fx3 m 2
    pure [ok0, ok1, ok2, I.bfalse]

def groupFlags (I : Interp) (tabs : Tabs I) (t3 m : Nat) : I.M (List I.B) :=
  groupFlagsK I tabs t3 m (tabs.kk.getD (t3*64+m) I.zero) (m - 2)

/-- The flags of `(t3, m) = (g2/64, g2%64)` when it is a valid pair with `t3` in the plan's slice; else all false. -/
def stepFlags (I : Interp) (tabs : Tabs I) (lo hi g2 : Nat) : I.M (List I.B) :=
  if g2 / 64 ≤ g2 % 64 && g2 % 64 ≠ 0 && lo ≤ g2 / 64 && g2 / 64 < hi then
    groupFlags I tabs (g2 / 64) (g2 % 64)
  else pure [I.bfalse, I.bfalse, I.bfalse, I.bfalse]

/-- Flags of all groups, in group order `(t3*64+m)*4 + i*`; only `t3 ∈ [lo, hi)` are computed. -/
def groupsM (I : Interp) (tabs : Tabs I) (lo hi : Nat) : Nat → Nat → Array I.B → I.M (Array I.B)
  | 0, _, arr => pure arr
  | k+1, g2, arr => do
    let fl ← stepFlags I tabs lo hi g2
    groupsM I tabs lo hi k (g2+1)
      ((((arr.push (fl.getD 0 I.bfalse)).push (fl.getD 1 I.bfalse)).push (fl.getD 2 I.bfalse)).push (fl.getD 3 I.bfalse))

def D (plan : List Nat) : Checker := fun I => do
  let ok ← shapesOk I
  if !ok then pure I.nzero else do
    let tabs ← buildTabs I
    let flags ← groupsM I tabs (plan.getD 0 0) (plan.getD 1 64) 4096 0 (Array.mk [])
    pure (sumInputs I [64, 64, 64, 64] (fun x => I.countB (flags.getD (gidx x) I.bfalse)))

end Candidate.Checker
