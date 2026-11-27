import Candidate.CountedMat

/-!
# The reference checker for max4-v64-s0 (definitions only; soundness in RefSound.lean)

Inputs are split into product boxes with set-valued sides (a box is four lists of tokens), by binary splits
(`S.filter (· == b)` / `S.filter (· != b)`), so the boxes never overlap. For each largest token `m` the box of
tokens `≤ m` is split into the 16 patterns of positions holding `m`; a pattern with `k` copies of `m` is a class.
Competitors not in the plan's list `J` are dismissed once per class by `k D_j(m) + (4 - k) min_{t<m} D_j(t) > 0`
(`safe`). The others are tested per node: bad tokens (from the plan) are fixed, the other free positions range
over the good set, and the test is the per-set lower bound summed over the box (`grp`); a box with one free
position is split into single tokens, each tested exactly. Tests are shared between the orderings of a node
through a table keyed by the sorted box (`srt`): a leaf counts only if its own sorted box is the stored key.
-/

namespace Candidate.Ref

open CompactCheck Protected.N_max4_v64_s0 Candidate.Counted

abbrev Box := List (List Nat)

/-! ## The plan: per (m, k) four kinds of lists, each a count and gaps -/

/-- A list of `n = p.head` tokens read from `x` by gaps, downward (`x - 1 - g`) or upward (`x + 1 + g`). -/
def rd (x : Nat) (up : Bool) (p : List Nat) : List Nat × List Nat :=
  ((List.range (p.headD 0)).foldl (fun st _ =>
    let y := cond up (st.1 + 1 + st.2.2.headD 0) (st.1 - 1 - st.2.2.headD 0)
    (y, st.2.1 ++ [y], st.2.2.tail)) (x, [], p.tail)).2

/-- One class: the unsafe competitors `J` (below, then above m), the bad tokens at the root, one list per bad
    token, and the competitors `J1` tested token by token in a one-slot box (the others once, on its whole side). -/
def dcls (m : Nat) (p : List Nat) : ((List Nat × List Nat) × List Nat × List (List Nat)) × List Nat :=
  let a := rd m false p
  let b := rd m true a.2
  let c := rd m false b.2
  let d := c.1.foldl (fun st _ => let e := rd m false st.2; (st.1 ++ [e.1], e.2)) ([], c.2)
  let f := rd m false d.2
  let g := rd m true f.2
  (((a.1 ++ b.1, f.1 ++ g.1), c.1, d.1), g.2)

def decode (V : Nat) (p : List Nat) : List ((List Nat × List Nat) × List Nat × List (List Nat)) :=
  ((List.range (V * 4)).foldl (fun st i => let e := dcls (i / 4) st.2; (st.1 ++ [e.1], e.2)) ([], p)).1

/-- The plan's bad tokens of a node with fixed tokens `F`. -/
def planB (e : ((List Nat × List Nat) × List Nat × List (List Nat))) (F : List Nat) : List Nat :=
  cond F.isEmpty e.2.1 (cond (F.length == 1) (((e.2.1.zip e.2.2).lookup (F.headD 0)).getD []) [])

/-! ## Boxes (free) -/

/-- Sorted by first token: the sets of a key (`[m]`, fixed tokens, one free set below and apart from them) have
    different first tokens, so every ordering of a box sorts to the same key. -/
def srt (c : Box) : Box := c.mergeSort fun a b => decide (a.headD 0 ≤ b.headD 0)

def bsz (c : Box) : Nat := c.foldr (fun s n => s.length * n) 1

/-- Binary splits of position `p` by each token of `B` in turn, the remainder last. -/
def splitAt (p : Nat) (c : Box) (B : List Nat) : List Box :=
  let r := B.foldl (fun st b => (st.1.filter (· != b), st.2 ++ [c.set p (st.1.filter (· == b))])) (c.getD p [], [])
  r.2 ++ [c.set p r.1]

/-- Every position whose set is `S` split by `B`. -/
def refine (c : Box) (S B : List Nat) : List Box :=
  (List.range 4).foldl (fun bs p => bs.flatMap fun d => cond (d.getD p [] == S) (splitAt p d B) [d]) [c]

/-- A key the tests may stand for: four sets, `k` of them `[m]`, the others nonempty and below `m`. -/
def kok (m k : Nat) (key : Box) : Bool :=
  key.length == 4 && key.count [m] == k && k != 0 && key.all fun s => s == [m] || (!s.isEmpty && s.all (· < m))

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

/-- The safe test of a class: `k D_j(m) + (4 - k) min_{t<m} D_j(t) > 0` for every competitor not in `J`. -/
def safe (I : Interp) (V m k : Nat) (J : List Nat) (dr pm : List (List I.V)) : I.M I.B := do
  let lk ← I.lit ct k
  let lr ← I.lit ct (4 - k)
  ((List.range V).filter fun j => j != m && !J.contains j).foldlM (fun acc j => do
    let a ← I.muladd ct I.zero lk ((dr.getD j []).getD m I.zero)
    let v ← I.muladd ct a lr ((pm.getD j []).getD (m - 1) I.zero)
    let ok ← I.lt ct I.zero v
    I.band ct acc ok) I.btrue

/-- `-base < lo s` for each competitor and its negated base, and-ed into `acc`. -/
def tst (I : Interp) (dr pm : List (List I.V)) (s : List Nat) (jbs : List (Nat × I.V)) (acc : I.B) : I.M I.B :=
  jbs.foldlM (fun acc jb => do
    let l ← lo I (dr.getD jb.1 []) (pm.getD jb.1 []) s
    let ok ← I.lt ct jb.2 l
    I.band ct acc ok) acc

/-- The tests of a group: for each competitor in `J` the lower bounds of `base` summed once (negated); the
    competitors not in `J1` tested once on the whole side `W` (`-base < lo W`), then per variant set `v ⊆ W` the
    key `srt (base ++ [v])` with its verdict: `-base < lo v` for the competitors in `J1`. -/
def grp (I : Interp) (m k : Nat) (J J1 : List Nat) (sf : I.B) (dr pm : List (List I.V)) (base : Box) (W : List Nat)
    (vs : List (List Nat)) : I.M (List (Box × I.B)) := do
  let bs ← mapC I (fun j => base.foldlM (fun a s => do
    let l ← lo I (dr.getD j []) (pm.getD j []) s
    I.sub ct a l) I.zero) J
  let h ← tst I dr pm W ((J.zip bs).filter fun jb => !J1.contains jb.1) sf
  mapC I (fun v => do
    let key := srt (base ++ [v])
    let g ← cond (kok m k key) (tst I dr pm v ((J.zip bs).filter fun jb => J1.contains jb.1) h) (pure I.bfalse)
    pure (key, g)) vs

abbrev Tbl (I : Interp) := List (Box × List (Box × I.B))

/-- The count of a group's sub-boxes: each counts only if its own sorted box is the stored key. -/
def cnt (I : Interp) (p : Nat) (subs : List Box) (es : List (Box × I.B)) : I.N :=
  (subs.zip es).foldl (fun n de =>
    I.nadd n (cond (srt (de.1.eraseIdx p ++ [de.1.getD p []]) == de.2.1) (I.nscale (bsz de.1) de.2.2) I.nzero)) I.nzero

/-- A leaf box with free set `S` at `rf` positions: one group (one-slot boxes: one per token). -/
def leaf (I : Interp) (m k : Nat) (J J1 : List Nat) (sf : I.B) (dr pm : List (List I.V)) (c : Box) (S : List Nat)
    (rf : Nat) (tbl : Tbl I) : I.M (I.N × Tbl I) :=
  let p := cond (rf == 1) (c.idxOf S) 3
  let subs := cond (rf == 1) (splitAt p c S) [c]
  match tbl.find? (·.1 == srt c) with
  | some e => pure (cnt I p subs e.2, tbl)
  | none => do
    let es ← grp I m k J J1 sf dr pm (c.eraseIdx p) (c.getD p []) (subs.map (·.getD p []))
    pure (cnt I p subs es, tbl ++ [(srt c, es)])

/-- The walk of a class box: refine by the plan's bad tokens while two or more positions are free. -/
def walk (I : Interp) (m k : Nat) (e : ((List Nat × List Nat) × List Nat × List (List Nat))) (sf : I.B)
    (dr pm : List (List I.V)) : Nat → Box → List Nat → List Nat → Tbl I → I.M (I.N × Tbl I)
  | 0, c, S, _, tbl => leaf I m k e.1.1 e.1.2 sf dr pm c S (c.count S) tbl
  | fuel + 1, c, S, F, tbl =>
    let rf := c.count S
    let B := cond (2 ≤ rf) (planB e F) []
    cond B.isEmpty (leaf I m k e.1.1 e.1.2 sf dr pm c S rf tbl) (
      let G := S.filter fun t => !B.contains t
      (refine c S B).foldlM (fun st d => cond (bsz d == 0) (pure st) (do
        let r ← cond (d.count G == rf) (leaf I m k e.1.1 e.1.2 sf dr pm d G rf st.2)
          (walk I m k e sf dr pm fuel d G (((d.filter fun s => s != [m] && s != G).map (·.headD 0)).mergeSort) st.2)
        pure (I.nadd st.1 r.1, r.2))) (I.nzero, tbl))

/-- A class the plan says nothing about. -/
def e0 : ((List Nat × List Nat) × List Nat × List (List Nat)) := (([], []), [], [])

/-- Level `m = fuel - 1`: the box of tokens `≤ m` split into its 16 patterns; the one without `m` is the next level. -/
def top (I : Interp) (V : Nat) (mat : List (List I.V)) (tab : List ((List Nat × List Nat) × List Nat × List (List Nat))) :
    Nat → Box → I.M I.N
  | 0, _ => pure I.nzero
  | m + 1, c => do
    let dr ← mapC I (fun j => cond (j == m) (pure [])
      (mapC I (fun ab => I.sub ct ab.1 ab.2) (((mat.getD m []).take (m + 1)).zip ((mat.getD j []).take (m + 1)))))
      (List.range V)
    let pm ← mapC I (fun j => cond (j == m) (pure []) (scan I (dr.getD j []) m)) (List.range V)
    let sfs ← mapC I (fun k => safe I V m k (tab.getD (m * 4 + k - 1) e0).1.1 dr pm) [1, 2, 3, 4]
    let S := c.headD []
    let G := S.filter (· != m)
    let r ← (refine c S [m]).foldlM (fun st d => cond (bsz d == 0) (pure st) (cond (d.all (· == G)) (do
        let n ← top I V mat tab m d
        pure (I.nadd st.1 n, st.2)) (do
        let k := d.count [m]
        let r ← walk I m k (tab.getD (m * 4 + k - 1) e0) (sfs.getD (k - 1) I.bfalse) dr pm 3 d G [] st.2
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
      top I V mat (decode V p) V (List.replicate 4 (List.range V))
    else pure I.nzero
  | _ => pure I.nzero

end Candidate.Ref
