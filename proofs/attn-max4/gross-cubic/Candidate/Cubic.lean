import Protected.N_attn_max4_v64_s0
import Candidate.LibCubicSound

/-!
# Gross et al.'s cubic proof on attn-max4-v64-s0

The checker and its soundness theorem are the Compact-Proof-Library's entry 7 (`GrossCubic`, their
`verification/cubic.py` at fb5b181), unchanged apart from module names; here they are applied to the
protected network of the run attn-max4-ptl-1. The run on the network is left to the service
(`"run": "compiled"`).
-/

namespace Candidate.Cubic

open CompactCheck GrossCubic Protected.N_attn_max4_v64_s0

/-- The checker on this network: the label is the largest token. -/
def D : Checker := fun I => check I true graph task

theorem graph_isAttn : AttnClasses.IsAttn graph := ⟨rfl, rfl, by decide, by decide⟩

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task :=
  fun w c n cost h => check_sound graph_isAttn true w c n cost h

end Candidate.Cubic
