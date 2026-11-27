import Protected.N_attn_max4_v64_s0
import Candidate.SubOne

/-!
# Gross et al.'s sub-cubic proof on attn-max4-v64-s0, as a planned checker

The checker and its soundness theorem are the Compact-Proof-Library's entry 9 (`GrossSub`, their
`verification/subcubic.py` at fb5b181, with its two corrections), unchanged apart from module names and
the lemma that reads the certificate; here they are applied to the protected network of the run
attn-max4-ptl-1, in their configuration EUPU mean_query+max_diff (`eu = 0`), attention mean_query+diff
(its averages are in the certificate), error max_diff (`err = 1`).

The plan is their gaps (`min_gaps`): entry `(c * V + λ) * V + rq` is the gap of the class of query rank
`rq`, largest rank `λ` and `c` other positions, minus one; an entry past the plan's end is gap 1. Entry 9's
`check_sound` holds for every gap, so `D_sound` holds for every plan.

The checker runs `check1` (`SubOne.lean`), entry 9's `check` with only this configuration's branches, which
is `check` by definition (`check1_eq`).
-/

namespace Candidate.Sub

open CompactCheck GrossSub Protected.N_attn_max4_v64_s0

/-- The gap the plan `p` gives the class `(rq, λ, c)` of a network with `V` tokens. -/
def gapOfPlan (V : ℕ) (p : List ℕ) (rq lam c : ℕ) : ℕ := p.getD ((c * V + lam) * V + rq) 0 + 1

/-- The planned checker on this network: the label is the largest token. -/
def D : List ℕ → Checker := fun p I => check1 I true (gapOfPlan graph.values p) graph task

theorem graph_isAttn : AttnClasses.IsAttn graph := ⟨rfl, rfl, by decide, by decide⟩

/-- Sound for every plan: the soundness shape of a planned checker. -/
theorem D_sound : ∀ (p : List ℕ) (w : Weights ℚ) (c : Cert) (n : ℕ) (cost : Cost),
    CostM.exec (D p Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun p w c n cost h => check_sound graph_isAttn true 1 0 (gapOfPlan graph.values p) w c n cost
    (by rw [← check1_eq]; exact h)

end Candidate.Sub
