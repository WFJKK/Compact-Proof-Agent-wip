-- [excerpt] CompactCheck/ExpSound.lean as this run offers it: the bounds on `exp` are right, for the real exponential.
-- [excerpt] Lines marked like this one are notes. Every other line is a line of the Lean project's file,
-- [excerpt] in its order. The file holds more than is shown here.

import Mathlib.Analysis.Complex.Exponential
import CompactCheck.Exp

namespace CompactCheck

open Real Finset

/-- **The exp bounds are right**: `L ≤ exp x * 2^120 ≤ H`. -/
theorem expBounds_spec {x : ℚ} {L H : ℤ} (h : expBounds x = some (L, H)) :
    (L : ℝ) ≤ exp x * 2 ^ expPrecision ∧ exp x * 2 ^ expPrecision ≤ H := by
-- [excerpt] (proof not shown)

/-- The same, as rationals: `exp x` lies in `expInterval x`. -/
theorem expInterval_spec {x lo hi : ℚ} (h : expInterval x = some (lo, hi)) :
    (lo : ℝ) ≤ exp x ∧ exp x ≤ hi := by
-- [excerpt] (proof not shown)

end CompactCheck
