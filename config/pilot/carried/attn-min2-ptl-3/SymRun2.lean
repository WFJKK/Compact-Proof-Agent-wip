import Protected.N_attn_min2_v64d8_s1_c1889_h910a46e6a9c5eac2
import Candidate.SymSem
import Candidate.SymRun
import Candidate.SymGlue
import CompactCheck.SemanticsKernel

/-!
# The three symbolic stages with tag-interleaved variables `var (tag + 16·k)`

Tags: 0 residual, 1 head, 2 E, 3 P, 4 WQ, 5 scale, 6 WK, 7 WV, 8 WO, 9 U, 10 one-hot input.
With this numbering every accessor of the real closed form is exactly `fun k => ρ (tag + 16 k)`.
-/

set_option linter.unusedSectionVars false

namespace Candidate.SymRun2
open CompactCheck Candidate.SymSem Candidate.SymRun Candidate.SymGlue Protected.N_attn_min2_v64d8_s1_c1889_h910a46e6a9c5eac2

def tv (tag k : Nat) : Sym := Sym.var (tag + 16 * k)

/-- A tensor of variables `tag + 16·(off + i)`, `i < n`. -/
def tT (tag off n : Nat) (shape : List Nat) : Tensor Sym :=
  ⟨shape, Array.ofFn (fun i : Fin n => tv tag (off + i))⟩

def tW : Weights Sym :=
  [("E", tT 2 0 512 [64, 8]), ("P", tT 3 0 16 [2, 8]), ("WQ", tT 4 0 64 [8, 8]),
   ("#const0", tT 5 0 1 []), ("WK", tT 6 0 64 [8, 8]), ("WV", tT 7 0 64 [8, 8]),
   ("WO", tT 8 0 64 [8, 8]), ("U", tT 9 0 512 [8, 64])]

def residT : Tensor Sym := ⟨[1, 2, 8], Array.ofFn fun k : Fin 16 => cfResid (tv 10) (tv 2) (tv 3) k⟩
def lastT : Tensor Sym := ⟨[1, 8], Array.ofFn fun i : Fin 8 => tv 0 (8 + i)⟩
def headT : Tensor Sym := ⟨[1, 8], Array.ofFn fun h : Fin 8 => cfHead (tv 0) (tv 4) (tv 6) (tv 7) (tv 5 0) h⟩
def logitT : Tensor Sym :=
  ⟨[1, 64], Array.ofFn fun j : Fin 64 => cfLogit (fun i => tv 0 (8 + i)) (tv 1) (tv 8) (tv 9) j⟩

def dummy : Tensor Sym := ⟨[], #[]⟩
def v0 : Array (Tensor Sym) := #[tT 10 0 128 [1, 2, 64]]
def vA : Array (Tensor Sym) := #[dummy, dummy, dummy, dummy, tT 0 0 16 [1, 2, 8]]
def vB : Array (Tensor Sym) :=
  #[dummy, dummy, dummy, dummy, dummy, tT 0 8 8 [1, 8], dummy, dummy, dummy, dummy, dummy,
    dummy, dummy, dummy, dummy, dummy, dummy, dummy, dummy, dummy, tT 1 0 8 [1, 8]]

set_option maxRecDepth 100000 in
theorem st0 : (semOps graph tW [0, 0] ops0 v0).map (fun o => (o.size, o[4]?)) =
    some (5, some residT) := by
  rw [semOps_eqK]; decide +kernel

set_option maxRecDepth 100000 in
theorem stA : (semOps graph tW [0, 0] opsA vA).map (fun o => (o.size, o[5]?, o[20]?)) =
    some (21, some lastT, some headT) := by
  rw [semOps_eqK]; decide +kernel

set_option maxRecDepth 100000 in
theorem stB : (semOps graph tW [0, 0] opsB vB).map (fun o => (o.size, o[25]?)) =
    some (26, some logitT) := by
  rw [semOps_eqK]; decide +kernel

/-! ## Facts about the graph and the stages, decided -/

theorem nodes_split : graph.nodes = Op.input :: (ops0 ++ opsA ++ opsB) := by rfl
theorem output_eq : graph.output = 25 := by rfl
theorem positions_eq : graph.positions = 2 := by rfl
theorem values_eq : graph.values = 64 := by rfl
theorem ops0_supported : ops0.all supported = true := by decide
theorem opsA_supported : opsA.all supported = true := by decide
theorem opsB_supported : opsB.all supported = true := by decide
theorem ops0_noInput : noInput ops0 = true := by decide
theorem opsA_noInput : noInput opsA = true := by decide
theorem opsB_noInput : noInput opsB = true := by decide
theorem ops0_len : ops0.length = 4 := by decide
theorem opsA_len : opsA.length = 16 := by decide
theorem opsB_len : opsB.length = 5 := by decide
theorem opsA_refs : ∀ i ∈ opsA.flatMap refs, i < 5 → i = 4 := by decide
theorem opsB_refs : ∀ i ∈ opsB.flatMap refs, i < 21 → i = 5 ∨ i = 20 := by decide
theorem ops0_names : paramNames ops0 = ["E", "P"] := by decide
theorem opsA_names : paramNames opsA = ["WQ", "#const0", "WK", "WV"] := by decide
theorem opsB_names : paramNames opsB = ["WO", "U"] := by decide

section
variable {α : Type} [Zero α] [One α] [Add α] [Mul α] [Neg α] [ExpDiv α]
theorem semOps_size (g : Graph) (w : Weights α) (x : Input) :
    ∀ (ops : List Op) (v o : Array (Tensor α)), semOps g w x ops v = some o → o.size = v.size + ops.length
  | [], v, o, h => by simp only [semOps, Option.some.injEq] at h; subst h; simp
  | op :: ops, v, o, h => by
    simp only [semOps] at h
    cases hv : semOp g w x v op with
    | none => simp [hv] at h
    | some t =>
      simp only [hv] at h
      have := semOps_size g w x ops (v.push t) o h
      simp at this; simp; omega
end

end Candidate.SymRun2
