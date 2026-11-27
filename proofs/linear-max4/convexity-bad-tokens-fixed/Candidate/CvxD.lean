import Candidate.CountedMat

/-!
# The convexity-only checker for max4-v64-s0 (definitions only; soundness in CvxSound.lean)

Ref.D without symmetry and without "only neighbours compete". Inputs are split into product boxes with set-valued
sides by binary splits, as in Ref.D: for each largest token `m` the box of tokens `≤ m` gives the 15 class boxes
(which positions hold `m`), each walked on its own. At a node the plan's bad tokens are fixed: every free side is
split into those tokens and the good set `G`, at every free position at once. The box whose free sides are all
`G` is tested against all 63 competitors (per side `d_j(t)` for a fixed token, the minimum over `G` for a free
side; the sum; compare; and). Children that keep a free slot are walked again with their own bad lists; fully
fixed children are tested exactly; at a node with one free slot the bad tokens are wrong inputs and skipped.
Every ordered box is tested; no verdict is shared. The minima of a set are computed once per `m` (a table).
The plan: a depth, then per class the bad lists of its nodes in depth-first order.
-/

namespace Candidate.Ref

open CompactCheck Protected.N_max4_v64_s0 Candidate.Counted

abbrev Box := List (List Nat)

/-! ## The plan -/

/-- A list of `n = p.head` tokens read downward from `x` by gaps (`x - 1 - g`). -/
def rd (x : Nat) (p : List Nat) : List Nat × List Nat :=
  ((List.range (p.headD 0)).foldl (fun st _ =>
    let y := st.1 - 1 - st.2.2.headD 0
    (y, st.2.1 ++ [y], st.2.2.tail)) (x, [], p.tail)).2

/-- The children of a node with bad tokens `B` and `rf` free slots that keep a free slot: one bad token fixed
    (`rf ≥ 2`), then two (`rf ≥ 3`, pairs in list order). -/
def kids (B : List Nat) (rf : Nat) : List (List Nat) :=
  cond (2 ≤ rf) (B.map fun b => [b]) [] ++
    cond (3 ≤ rf) ((List.range B.length).flatMap fun i => (B.drop i).map fun b => [B.getD i 0, b]) []

/-- The bad lists of a node (sorted fixed tokens `F`, `rf` free slots, free set `S`) and of its subtree, depth
    first: entries (fixed tokens, bad tokens), and the rest of the plan. -/
def dnode (m : Nat) : Nat → List Nat → Nat → List Nat → List Nat → List (List Nat × List Nat) × List Nat
  | 0, _, _, _, p => ([], p)
  | fuel + 1, F, rf, S, p =>
    let r := rd m p
    let G := S.filter fun t => !r.1.contains t
    (cond G.isEmpty [] (kids r.1 rf)).foldl (fun st sel =>
      let e := dnode m fuel (F ++ sel).mergeSort (rf - sel.length) G st.2
      (st.1 ++ e.1, e.2)) ([(F, r.1)], r.2)

/-- Per class `i = 4 m + k - 1` its table of bad lists (classes with a free slot and `m ≥ 1`). -/
def decode (V : Nat) (p : List Nat) : List (List (List Nat × List Nat)) :=
  ((List.range (V * 4)).foldl (fun st i =>
    let e := cond (i / 4 != 0 && i % 4 != 3) (dnode (i / 4) (p.headD 0 + 1) [] (3 - i % 4) (List.range (i / 4)) st.2)
      ([], st.2)
    (st.1 ++ [e.1], e.2)) ([], p.tail)).1

/-! ## Boxes (free) -/

def srt (c : Box) : Box := c.mergeSort fun a b => decide (a.headD 0 ≤ b.headD 0)

def bsz (c : Box) : Nat := c.foldr (fun s n => s.length * n) 1

/-- Binary splits of position `p` by each token of `B` in turn, the remainder last. -/
def splitAt (p : Nat) (c : Box) (B : List Nat) : List Box :=
  let r := B.foldl (fun st b => (st.1.filter (· != b), st.2 ++ [c.set p (st.1.filter (· == b))])) (c.getD p [], [])
  r.2 ++ [c.set p r.1]

/-- Every position whose set is `S` split by `B`. -/
def refine (c : Box) (S B : List Nat) : List Box :=
  (List.range 4).foldl (fun bs p => bs.flatMap fun d => cond (d.getD p [] == S) (splitAt p d B) [d]) [c]

/-! ## Charged parts -/

/-- The running minima `min_{t ≤ i} d(t)`, `i < n` (at least one): `n - 1` charged minima. -/
def scan (I : Interp) (d : List I.V) (n : Nat) : I.M (List I.V) :=
  (List.range' 1 (n - 1)).foldlM (fun acc t => do
    let v ← I.min ct (acc.getLastD I.zero) (d.getD t I.zero)
    pure (acc ++ [v])) [d.getD 0 I.zero]

/-- `min_{t ∈ s} d(t)`: a set that starts `0, 1, ..., c - 1` starts from the running minimum `pr[c - 1]`. -/
def lo (I : Interp) (d pr : List I.V) (s : List Nat) : I.M I.V :=
  let c := min ((List.range s.length).takeWhile fun i => s.getD i 0 == i).length pr.length
  (s.drop (max c 1)).foldlM (fun a t => I.min ct a (d.getD t I.zero))
    (cond (c == 0) (d.getD (s.headD 0) I.zero) (pr.getD (c - 1) I.zero))

/-- Per competitor `j ≠ m`: `(j, row as an array, row, running minima)`. -/
abbrev Rws (I : Interp) := List (Nat × Array I.V × List I.V × List I.V)

/-- The table of minima of this `m`: (fingerprint, set, minima aligned with the competitors). -/
abbrev MTbl (I : Interp) := List ((Nat × Nat) × List Nat × List I.V)

/-- The minima of the set `G` for every competitor: from the table of this `m`, or computed once and added. -/
def mins (I : Interp) (rws : Rws I) (G : List Nat) (tbl : MTbl I) : I.M (List I.V × MTbl I) :=
  match tbl.find? (fun e => e.1 == (G.length, G.foldl (· + ·) 0) && e.2.1 == G) with
  | some e => pure (e.2.2, tbl)
  | none => do
    let ms ← mapC I (fun r => lo I r.2.2.1 r.2.2.2 G) rws
    pure (ms, ((G.length, G.foldl (· + ·) 0), G, ms) :: tbl)

/-- A box against every competitor `j ≠ m`: per side `d_j(t)` for a single token, `ms[j]` for the free set `G`;
    the sum positive. The box must hold `[m]`, tokens `≤ m`, and sides that are `G` or single tokens. -/
def tst (I : Interp) (m : Nat) (rws : Rws I) (c : Box) (G : List Nat) (ms : List I.V) : I.M I.B :=
  cond (c.length == 4 && c.contains [m] && c.all fun s => s.all (· ≤ m) && (s == G || s.length == 1))
    (let sd := c.map fun s => (s == G, s.headD 0)
     (rws.zip ms).foldlM (fun acc rm => do
      let v ← sd.tail.foldlM (fun a q => I.add ct a (cond q.1 rm.2 (rm.1.2.1.getD q.2 I.zero)))
        (cond (sd.headD (false, 0)).1 rm.2 (rm.1.2.1.getD (sd.headD (false, 0)).2 I.zero))
      let ok ← I.lt ct I.zero v
      I.band ct acc ok) I.btrue)
    (pure I.bfalse)

/-- A node: a fully fixed box is tested exactly; otherwise its free sides `S` are split by the node's bad tokens,
    the box whose free sides are all `G` is tested, and the other pieces go to `k` (none at one free slot). -/
def nodeW (I : Interp) (m : Nat) (rws : Rws I) (tab : List (List Nat × List Nat))
    (k : Box → List Nat → List Nat → MTbl I → I.M (I.N × MTbl I))
    (c : Box) (S F : List Nat) (tbl : MTbl I) : I.M (I.N × MTbl I) :=
  let rf := c.count S
  cond (rf == 0) (do
    let g ← tst I m rws c [] (rws.map fun _ => I.zero)
    pure (I.nscale (bsz c) g, tbl)) (
    let B := (tab.lookup F).getD []
    let G := S.filter fun t => !B.contains t
    (refine c S B).foldlM (fun st d => cond (bsz d == 0) (pure st) (do
      let r ← cond (d.count G == rf) (do
          let mt ← mins I rws G st.2
          let g ← tst I m rws d G mt.1
          pure (I.nscale (bsz d) g, mt.2))
        (cond (rf == 1) (pure (I.nzero, st.2))
          (k d G ((d.filter fun s => s != [m] && s != G).map (·.headD 0)).mergeSort st.2))
      pure (I.nadd st.1 r.1, r.2))) (I.nzero, tbl))

/-- The walk of a class box: `fuel` levels of children below the root. -/
def walk (I : Interp) (m : Nat) (rws : Rws I) (tab : List (List Nat × List Nat)) :
    Nat → Box → List Nat → List Nat → MTbl I → I.M (I.N × MTbl I)
  | 0 => nodeW I m rws tab fun _ _ _ t => pure (I.nzero, t)
  | fuel + 1 => nodeW I m rws tab (walk I m rws tab fuel)

/-- Level `m = fuel - 1`: the box of tokens `≤ m` split into its 16 patterns; the one without `m` is the next level. -/
def top (I : Interp) (V : Nat) (mat : List (List I.V)) (tabs : List (List (List Nat × List Nat))) (depth : Nat) :
    Nat → Box → I.M I.N
  | 0, _ => pure I.nzero
  | m + 1, c => do
    let dr ← mapC I (fun j => cond (j == m) (pure [])
      (mapC I (fun ab => I.sub ct ab.1 ab.2) (((mat.getD m []).take (m + 1)).zip ((mat.getD j []).take (m + 1)))))
      (List.range V)
    let pm ← mapC I (fun j => cond (j == m) (pure []) (scan I (dr.getD j []) m)) (List.range V)
    let rws := ((List.range V).filter (· != m)).map fun j => (j, Array.mk (dr.getD j []), dr.getD j [], pm.getD j [])
    let S := c.headD []
    let G := S.filter (· != m)
    let r ← (refine c S [m]).foldlM (fun st d => cond (bsz d == 0) (pure st) (cond (d.all (· == G)) (do
        let n ← top I V mat tabs depth m d
        pure (I.nadd st.1 n, st.2)) (do
        let r ← walk I m rws (tabs.getD (m * 4 + d.count [m] - 1) []) depth d G [] st.2
        pure (I.nadd st.1 r.1, r.2)))) (I.nzero, [])
    pure r.1

def nE : String := "embedding.weight"
def nL : String := "linear.weight"
def nU : String := "unembedding.weight"

def D (p : List Nat) : Checker := fun I => do
  let es ← I.weightShape nE
  let ls ← I.weightShape nL
  let us ← I.weightShape nU
  let esz ← I.weightSize nE
  let lsz ← I.weightSize nL
  let usz ← I.weightSize nU
  match es with
  | [d, V] =>
    if ls = [d, d] ∧ us = [V, d] ∧ esz = d * V ∧ lsz = d * d ∧ usz = V * d ∧ graph.values = V then do
      let le ← mapC I (fun k => leRow I d V k) (List.range d)
      let mat ← mapC I (fun j => matRow I d V j le) (List.range V)
      top I V mat (decode V p) (p.headD 0) V (List.replicate 4 (List.range V))
    else pure I.nzero
  | _ => pure I.nzero

end Candidate.Ref
