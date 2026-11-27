import Candidate.Checker2

/-!
# Checker3: Checker2 with the `t3`-independent parts of the group stage precomputed once per `(i, t, m, j)`:
`dov` (the OV difference of the near window) and `n1` (the far bound's OV range).
-/

namespace Candidate.Checker3
open CompactCheck Candidate.Loops Candidate.Tables Candidate.Checker Candidate.Checker2

/-- The window start of `m` under the plan. -/
def aOf (plan : List Nat) (m : Nat) : Nat := if plan.getD (2 + m) 2 = 1 then m - 1 else m - 2

/-- `dov[(i*3+r)*4096 + m*64 + j] = ov[i, a_m + r, m] - ov[i, a_m + r, j]` when `a_m + r ≤ m` (else 0). -/
def buildDov (I : Interp) (tabs : Tabs I) (plan : List Nat) : I.M (Array I.V) :=
  tableM I (fun k =>
    if aOf plan (k / 64 % 64) + k / 4096 % 3 ≤ k / 64 % 64 then
      I.sub "" (tabs.ov.getD ((k / 4096 / 3 * 64 + (aOf plan (k / 64 % 64) + k / 4096 % 3)) * 64 + k / 64 % 64) I.zero)
        (tabs.ov.getD ((k / 4096 / 3 * 64 + (aOf plan (k / 64 % 64) + k / 4096 % 3)) * 64 + k % 64) I.zero)
    else pure I.zero) 36864 0 (E0 I)

/-- `n1[(i*64+j)*64 + m] = ovmax[i, j, a_m] - ovmin[i, m, a_m]`. -/
def buildN1 (I : Interp) (tabs : Tabs I) (plan : List Nat) : I.M (Array I.V) :=
  tableM I (fun k =>
    I.sub "" (tabs.ovmax.getD ((k / 4096 * 64 + k / 64 % 64) * 65 + aOf plan (k % 64)) I.zero)
      (tabs.ovmin.getD ((k / 4096 * 64 + k % 64) * 65 + aOf plan (k % 64)) I.zero)) 12288 0 (E0 I)

/-- `dov[i, t, m, j] - cpr[j]` = `(Dm[m]+OV[i,t,m]) - (Dm[j]+OV[i,t,j])`. -/
def hD (I : Interp) (dov cpr : Array I.V) (m a i t j : Nat) : I.M I.V :=
  I.sub "" (dov.getD ((i*3 + (t-a))*4096 + m*64 + j) I.zero) (cpr.getD j I.zero)

/-- The four flags of the groups (t3, m, i*), i* < 4, for `1 ≤ m`, `t3 ≤ m`, shift `K`, window start `a`. -/
def groupFlagsK (I : Interp) (tabs : Tabs I) (dov n1 : Array I.V) (H4 : I.V) (t3 m : Nat) (K : I.V) (a : Nat) :
    I.M (List I.B) := do
  let cpr ← tableM I (fun j => I.sub "" (tabs.dm.getD (t3*64+j) I.zero) (tabs.dm.getD (t3*64+m) I.zero)) 64 0 (E0 I)
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
  let dtab ← tableM I (fun k => I.sub "" (exhi.getD k I.zero) (exlo.getD k I.zero)) 9 0 (E0 I)
  let d3 ← I.sub "" e3.2 e3.1
  let dmax ← maxM I (fun k => dtab.getD k I.zero) 9 d3
  let theta ← I.muladd "" I.zero dmax H4
  let term ← tableM I (fun k => do
    let h ← hD I dov cpr m a (k/64) m (k%64)
    loProdM I (exlo.getD (k/64*3 + (m-a)) I.zero) h) 192 0 (E0 I)
  let Fm ← tableM I (fun k => do
    let near ← minRangeM I (fun t => do
      let h ← hD I dov cpr m a (k/64) t (k%64)
      loProdM I (exlo.getD (k/64*3 + (t-a)) I.zero) h) a (m - a)
    if a = 0 then pure near else do
      let n2 ← I.add "" (cpr.getD (k%64) I.zero) (n1.getD ((k/64*64 + k%64)*64 + m) I.zero)
      let n3 ← I.max "" I.zero n2
      let far ← I.muladd "" I.zero (negEfar.getD (k/64) I.zero) n3
      I.min "" near far) 192 0 (E0 I)
  let Fm1 ← tableM I (fun k => I.min "" (Fm.getD k I.zero) (term.getD k I.zero)) 192 0 (E0 I)
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

/-- The flags of `(t3, m) = (g2/64, g2%64)` when it is a valid pair with `t3` in the plan's slice; else all false. -/
def stepFlags (I : Interp) (tabs : Tabs I) (dov n1 : Array I.V) (H4 : I.V) (plan : List Nat) (lo hi g2 : Nat) :
    I.M (List I.B) :=
  if g2 / 64 ≤ g2 % 64 && g2 % 64 ≠ 0 && lo ≤ g2 / 64 && g2 / 64 < hi then
    groupFlagsK I tabs dov n1 H4 (g2 / 64) (g2 % 64) (tabs.kk.getD (g2 / 64 * 64 + g2 % 64) I.zero) (aOf plan (g2 % 64))
  else pure [I.bfalse, I.bfalse, I.bfalse, I.bfalse]

/-- Flags of all groups, in group order `(t3*64+m)*4 + i*`; only `t3 ∈ [lo, hi)` are computed. -/
def groupsM (I : Interp) (tabs : Tabs I) (dov n1 : Array I.V) (H4 : I.V) (plan : List Nat) (lo hi : Nat) :
    Nat → Nat → Array I.B → I.M (Array I.B)
  | 0, _, arr => pure arr
  | k+1, g2, arr => do
    let fl ← stepFlags I tabs dov n1 H4 plan lo hi g2
    groupsM I tabs dov n1 H4 plan lo hi k (g2+1)
      ((((arr.push (fl.getD 0 I.bfalse)).push (fl.getD 1 I.bfalse)).push (fl.getD 2 I.bfalse)).push (fl.getD 3 I.bfalse))

def D (plan : List Nat) : Checker := fun I => do
  let ok ← shapesOk I
  if !ok then pure I.nzero else do
    let tabs ← buildTabs I
    let H4 ← boundH I tabs
    let dov ← buildDov I tabs plan
    let n1 ← buildN1 I tabs plan
    let flags ← groupsM I tabs dov n1 H4 plan (plan.getD 0 0) (plan.getD 1 64) 4096 0 (Array.mk [])
    pure (sumInputs I [64, 64, 64, 64] (fun x => I.countB (flags.getD (gidx x) I.bfalse)))

end Candidate.Checker3