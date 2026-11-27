import Candidate.Count

/-!
# The checker's tables (counted language) and a timing probe: tables + the free count loop with dummy flags.
NOT a sound checker: `Dtest` is for measuring only.
-/

namespace Candidate.Tables
open CompactCheck Protected.N_attn_max4_v64_s0 Candidate.Loops

/-- Prefix maxima: entry `a` (a = 0..n) is max(acc0, f 0, ..., f (a-1)). -/
def scanMaxM (I : Interp) (f : Nat → I.V) : Nat → Nat → I.V → Array I.V → I.M (Array I.V)
  | 0, _, acc, arr => pure (arr.push acc)
  | k+1, t, acc, arr => do
    let acc' ← I.max "" acc (f t)
    scanMaxM I f k (t+1) acc' (arr.push acc)

def scanMinM (I : Interp) (f : Nat → I.V) : Nat → Nat → I.V → Array I.V → I.M (Array I.V)
  | 0, _, acc, arr => pure (arr.push acc)
  | k+1, t, acc, arr => do
    let acc' ← I.min "" acc (f t)
    scanMinM I f k (t+1) acc' (arr.push acc)

/-- Several scans in a row, one per outer index `o < n`, each of `len+1` entries. -/
def scansMaxM (I : Interp) (f : Nat → Nat → I.V) (len : Nat) : Nat → Nat → Array I.V → I.M (Array I.V)
  | 0, _, arr => pure arr
  | k+1, o, arr => do
    let arr' ← scanMaxM I (f o) len 0 (f o 0) arr
    scansMaxM I f len k (o+1) arr'

def scansMinM (I : Interp) (f : Nat → Nat → I.V) (len : Nat) : Nat → Nat → Array I.V → I.M (Array I.V)
  | 0, _, arr => pure arr
  | k+1, o, arr => do
    let arr' ← scanMinM I (f o) len 0 (f o 0) arr
    scansMinM I f len k (o+1) arr'

structure Tabs (I : Interp) where
  sc : I.V
  last : Array I.V   -- [t3*32+d]
  dm : Array I.V     -- [t3*64+j]
  ov : Array I.V     -- [(i*64+t)*64+j]
  s : Array I.V      -- [(t3*4+i)*64+t]
  kk : Array I.V     -- [t3*64+m] = max_{i<4,t<=m} s[t3,i,t]
  ovmax : Array I.V  -- [(i*65+a)*64+j] = max_{t<a} ov[i,t,j]  (i<3)
  ovmin : Array I.V
  spre : Array I.V   -- [(t3*3+i)*65+a] = max_{t<a} s[t3,i,t]  (i<3)

def E0 (I : Interp) : Array I.V := Array.mk []

def buildTabs (I : Interp) : I.M (Tabs I) := do
  let sc ← I.weight "#const0" 0
  let last ← tableM I (fun k => do
    let e ← I.weight "E" k
    let p ← I.weight "P" (96 + k % 32)
    I.add "" e p) 2048 0 (E0 I)
  let dm ← tableM I (fun k =>
    dotM I (fun d => pure (last.getD (k / 64 * 32 + d) I.zero)) (fun d => I.weight "U" (d * 64 + k % 64)) 32 I.zero)
    4096 0 (E0 I)
  let vwo ← tableM I (fun k =>
    dotM I (fun d' => I.weight "WV" (k / 32 * 32 + d')) (fun d' => I.weight "WO" (d' * 32 + k % 32)) 32 I.zero)
    1024 0 (E0 I)
  let wov ← tableM I (fun k =>
    dotM I (fun d2 => pure (vwo.getD (k / 64 * 32 + d2) I.zero)) (fun d2 => I.weight "U" (d2 * 64 + k % 64)) 32 I.zero)
    2048 0 (E0 I)
  let ove ← tableM I (fun k =>
    dotM I (fun d => I.weight "E" (k / 64 * 32 + d)) (fun d => pure (wov.getD (d * 64 + k % 64) I.zero)) 32 I.zero)
    4096 0 (E0 I)
  let ovp ← tableM I (fun k =>
    dotM I (fun d => I.weight "P" (k / 64 * 32 + d)) (fun d => pure (wov.getD (d * 64 + k % 64) I.zero)) 32 I.zero)
    256 0 (E0 I)
  let ov ← tableM I (fun k =>
    I.add "" (ove.getD (k % 4096) I.zero) (ovp.getD (k / 4096 * 64 + k % 64) I.zero)) 16384 0 (E0 I)
  let qm ← tableM I (fun k => do
    let v ← dotM I (fun d => pure (last.getD (k / 32 * 32 + d) I.zero)) (fun d => I.weight "WQ" (d * 32 + k % 32)) 32 I.zero
    I.muladd "" I.zero v sc) 2048 0 (E0 I)
  let ek ← tableM I (fun k =>
    dotM I (fun d => I.weight "E" (k / 32 * 32 + d)) (fun d => I.weight "WK" (d * 32 + k % 32)) 32 I.zero)
    2048 0 (E0 I)
  let pk ← tableM I (fun k =>
    dotM I (fun d => I.weight "P" (k / 32 * 32 + d)) (fun d => I.weight "WK" (d * 32 + k % 32)) 32 I.zero)
    128 0 (E0 I)
  let sqe ← tableM I (fun k =>
    dotM I (fun d' => pure (qm.getD (k / 64 * 32 + d') I.zero)) (fun d' => pure (ek.getD (k % 64 * 32 + d') I.zero)) 32 I.zero)
    4096 0 (E0 I)
  let sqp ← tableM I (fun k =>
    dotM I (fun d' => pure (qm.getD (k / 4 * 32 + d') I.zero)) (fun d' => pure (pk.getD (k % 4 * 32 + d') I.zero)) 32 I.zero)
    256 0 (E0 I)
  let s ← tableM I (fun k =>
    I.add "" (sqe.getD (k / 256 * 64 + k % 64) I.zero) (sqp.getD (k / 64) I.zero)) 16384 0 (E0 I)
  -- kk[t3*64+m]: running max over m of max_i s[t3,i,m]
  let kk ← scansMaxM I (fun t3 m => s.getD (t3 * 256 + m) I.zero) 0 0 0 (E0 I)  -- placeholder, replaced below
  let kk ← tableM I (fun g => do
    let t3 := g / 64
    let m := g % 64
    let a ← I.max "" (s.getD (t3 * 256 + m) I.zero) (s.getD (t3 * 256 + 64 + m) I.zero)
    let b ← I.max "" (s.getD (t3 * 256 + 128 + m) I.zero) (s.getD (t3 * 256 + 192 + m) I.zero)
    let c ← I.max "" a b
    if m == 0 then pure c else I.max "" c (kk.getD (g - 1) I.zero)) 4096 0 (E0 I)
  let ovmax ← scansMaxM I (fun o t => ov.getD ((o / 64 * 64 + t) * 64 + o % 64) I.zero) 64 192 0 (E0 I)
  let ovmin ← scansMinM I (fun o t => ov.getD ((o / 64 * 64 + t) * 64 + o % 64) I.zero) 64 192 0 (E0 I)
  let spre ← scansMaxM I (fun o t => s.getD ((o / 3 * 4 + o % 3) * 64 + t) I.zero) 64 192 0 (E0 I)
  pure ⟨sc, last, dm, ov, s, kk, ovmax, ovmin, spre⟩

/-- The group of an input: (t3, max, last position of the max). -/
def gidx (x : Input) : Nat :=
  let m := x.foldl max 0
  let t3 := x.getD 3 0
  let istar := (List.range 4).foldl (fun p i => if x.getD i 0 = m then i else p) 0
  (t3 * 64 + m) * 4 + istar

def shapesOk (I : Interp) : I.M Bool := do
  let sE ← I.weightShape "E"
  let nE ← I.weightSize "E"
  let sP ← I.weightShape "P"
  let nP ← I.weightSize "P"
  let sQ ← I.weightShape "WQ"
  let nQ ← I.weightSize "WQ"
  let sK ← I.weightShape "WK"
  let nK ← I.weightSize "WK"
  let sV ← I.weightShape "WV"
  let nV ← I.weightSize "WV"
  let sO ← I.weightShape "WO"
  let nO ← I.weightSize "WO"
  let sU ← I.weightShape "U"
  let nU ← I.weightSize "U"
  let sC ← I.weightShape "#const0"
  let nC ← I.weightSize "#const0"
  pure (sE == [64, 32] && nE == 2048 && sP == [4, 32] && nP == 128 && sQ == [32, 32] && nQ == 1024
    && sK == [32, 32] && nK == 1024 && sV == [32, 32] && nV == 1024 && sO == [32, 32] && nO == 1024
    && sU == [32, 64] && nU == 2048 && sC == [] && nC == 1)

/-- TIMING PROBE ONLY (unsound as a count): tables, then dummy flags. -/
def Dtest (plan : List Nat) : Checker := fun I => do
  let ok ← shapesOk I
  if !ok then pure I.nzero else do
    let tabs ← buildTabs I
    let flags ← tableB I (fun g => do
      let t3 := g / 256
      let m := g / 4 % 64
      if t3 < plan.getD 0 0 || t3 ≥ plan.getD 1 64 then pure I.bfalse else
      I.lt "" (tabs.s.getD (t3 * 256 + m) I.zero) (tabs.kk.getD (t3 * 64 + m) I.zero)) 16384 0 (Array.mk [])
    pure (sumInputs I [64, 64, 64, 64] (fun x => I.countB (flags.getD (gidx x) I.bfalse)))

/-- TIMING PROBE ONLY: the free count loop alone (flags all true). -/
def Dcount (plan : List Nat) : Checker := fun I => do
  let ok ← shapesOk I
  if !ok then pure I.nzero else do
    let flags ← tableB I (fun g => if g < plan.getD 0 0 then pure I.bfalse else pure I.btrue) 16384 0 (Array.mk [])
    pure (sumInputs I [64, 64, 64, 64] (fun x => I.countB (flags.getD (gidx x) I.bfalse)))

end Candidate.Tables
