-- [excerpt] CompactCheck/Exp.lean as this run offers it: the bounds on `exp` that `CostM.qexp` (`I.exp`) returns.
-- [excerpt] Lines marked like this one are notes. Every other line is a line of the Lean project's file,
-- [excerpt] in its order. The file holds more than is shown here.

-- [excerpt] `expBounds x` gives integers `L` and `H` with `L ≤ exp x * 2^120 ≤ H` (`expBounds_spec` in
-- [excerpt] ExpSound.lean); `expInterval x` gives them as rationals, `(L / 2^120, H / 2^120)` (`expInterval_spec`).
-- [excerpt] For `|x| = y * 2^m` with `y ≤ 2^-8`: the series of `exp y`, its terms rounded down for the lower
-- [excerpt] bound and up for the upper one, then `m` squarings rounded outwards; for `x < 0`, `1 / exp |x|`.

namespace CompactCheck

/-- Results of `exp` and `softmax` are multiples of `2^-expPrecision`. -/
def expPrecision : Nat := 120

/-- `exp` is refused for arguments of `2^maxExpLog2` or more, and enclosed by
    `[0, 2^-120]` below `-2^maxExpLog2`. -/
def maxExpLog2 : Int := 12

/-- `⌈a / b⌉` for `b > 0`. -/
def ceilDiv (a b : Int) : Int := -((-a) / b)

/-- A dyadic rational `x = ±A * 2^e` as `(A, e)` with `A = |numerator|`, or
    `none` if the denominator is not a power of two. -/
def dyadicParts (x : Rat) : Option (Nat × Int) :=
  if x.den = 2 ^ x.den.log2 then some (x.num.natAbs, -(x.den.log2 : Int)) else none

/-- `A * 2^s` rounded down and up. -/
def scaledArg (A : Nat) (s : Int) : Int × Int :=
  if s ≥ 0 then (A * 2 ^ s.toNat, A * 2 ^ s.toNat)
  else (A / 2 ^ (-s).toNat, ceilDiv A (2 ^ (-s).toNat))

/-- The terms of the series from term `k` on, `tlo` and `thi` being term `k`
    at `2^-W` rounded down and up. Returns the lower sum and the upper sum,
    the latter with twice the first term left out. At most `fuel` terms. -/
def expSeries (W : Nat) (ylo yhi : Int) : Nat → Nat → Int → Int → Int → Int → Option (Int × Int)
  | 0, _, _, _, _, _ => none
  | fuel + 1, k, tlo, thi, loSum, hiSum =>
    let tlo' := tlo * ylo / (((k + 1 : Nat) : Int) * 2 ^ W)
    let thi' := ceilDiv (thi * yhi) (((k + 1 : Nat) : Int) * 2 ^ W)
    if thi' ≤ 1 then some (loSum + tlo, hiSum + thi + 2 * thi')
    else expSeries W ylo yhi fuel (k + 1) tlo' thi' (loSum + tlo) (hiSum + thi)

/-- Square `n` times at `2^-W`, the lower bound rounded down and the upper
    bound up. -/
def expSquare (W : Nat) : Nat → Int × Int → Int × Int
  | 0, p => p
  | n + 1, (L, H) => expSquare W n (L * L / 2 ^ W, ceilDiv (H * H) (2 ^ W))

/-- From the two sums at `2^-W` to the bounds at `2^-120`: for `x < 0` the
    reciprocals, then `m` squarings, all rounded outwards. -/
def expFinish (neg : Bool) (W m : Nat) (sums : Int × Int) : Int × Int :=
  let start : Int × Int :=
    if neg then (2 ^ (2 * W) / sums.2, ceilDiv (2 ^ (2 * W)) sums.1) else sums
  let r := expSquare W m start
  (r.1 / 2 ^ (W - expPrecision), ceilDiv r.2 (2 ^ (W - expPrecision)))

-- [excerpt] `(L, H)` with `L ≤ exp (±A * 2^e) * 2^120 ≤ H`, the sign `-` if `neg`; `none` for an argument
-- [excerpt] of `2^12` or more. Below, `|x| < 2^(bl + e)` with `bl` the number of bits of `A`;
-- [excerpt] `y = |x| / 2^m ≤ 2^-8`, and `y * 2^W = A * 2^(e - m + W)`.
def expBoundsParts (neg : Bool) (A : Nat) (e : Int) : Option (Int × Int) :=
  if A = 0 then some (2 ^ expPrecision, 2 ^ expPrecision) else
  if ((A.log2 + 1 : Nat) : Int) + e > maxExpLog2 then (if neg then some (0, 1) else none) else
  let m : Nat := (max 0 (((A.log2 + 1 : Nat) : Int) + e + 8)).toNat
  let W : Nat := expPrecision + m + 32
  let y := scaledArg A (e - m + W)
  (expSeries W y.1 y.2 (W + 2) 0 (2 ^ W) (2 ^ W) 0 0).map (expFinish neg W m)

-- [excerpt] `(L, H)` with `L ≤ exp x * 2^120 ≤ H`. `none` for an argument of `2^12` or more, and for a
-- [excerpt] number that is not dyadic (the network's numbers all are).
def expBounds (x : Rat) : Option (Int × Int) :=
  match dyadicParts x with
  | none => none
  | some (A, e) => expBoundsParts (x < 0) A e

/-- The bounds as rationals: `(L / 2^120, H / 2^120)`. -/
def expInterval (x : Rat) : Option (Rat × Rat) :=
  (expBounds x).map fun (L, H) => ((L : Rat) / 2 ^ expPrecision, (H : Rat) / 2 ^ expPrecision)

end CompactCheck
