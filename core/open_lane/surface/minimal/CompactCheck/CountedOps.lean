-- [excerpt] CompactCheck/CountedOps.lean as this run offers it: the counted language.
-- [excerpt] Lines marked like this one are notes. Every other line is a line of the Lean project's file,
-- [excerpt] in its order. The file holds more than is shown here.

namespace CompactCheck

namespace CostM

/-- The single rule on one input: `singleOk`, charged as one exact forward pass and the final comparison
    (`singleCost`). `none` if the forward pass cannot be billed on this graph. -/
def single (g : Graph) (task : Task) (x : Input) : CostM Bool := ⟨fun env c =>
  match singleCost g env.weights with
  | some sc => some (singleOk g env.weights task x, c.add "single" sc)
  | none => none⟩

/-! ## Specifications of the monad and the operations -/

theorem run_pure (a : α) (env : Env) (c : Cost) : (pure a : CostM α).run env c = some (a, c) := rfl

theorem run_bind (x : CostM α) (f : α → CostM β) (env : Env) (c : Cost) :
    (x >>= f).run env c = match x.run env c with
      | some (a, c') => (f a).run env c'
      | none => none := rfl

theorem single_spec {g : Graph} {task : Task} {x : Input} {env : Env} {c c' : Cost}
    (h : (single g task x).run env c = some (true, c')) : singleOk g env.weights task x = true := by
  simp only [single] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact h.1
  · cases h

/-- From the instance theorem of a scored submission, `billed D env = some (n, L)`, the hypothesis of
    its soundness theorem: `D` ran to `n` with some bill. -/
theorem exec_of_billed {x : CostM α} {env : Env} {a : α} {L : Nat}
    (h : billed x env = some (a, L)) : ∃ c, exec x env = some (a, c) := by
  unfold billed at h
  match hx : exec x env with
  | none => rw [hx] at h; cases h
  | some (a', c) =>
    rw [hx] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨c, by rw [h.1]⟩

end CostM

/-! ## The interface -/

/-- An interpreter of the counted language. A checker is a function of one of these: it can use the
    operations below and ordinary Lean on lists, `Nat` indices and strings, and nothing else about `M`,
    `V`, `B` or `N`. The charges named are those of `Interp.counting`. -/
structure Interp : Type 1 where
  /-- The monad of the computation. -/
  M : Type → Type
  monad : Monad M
  /-- A number of the network or the certificate, or computed from them. -/
  V : Type
  /-- A truth value computed from numbers. -/
  B : Type
  /-- A count of inputs, computed from truth values. -/
  N : Type
  /-- Entry `i` of the weight `name`, in row-major order. Free: the weights are charged once per
      proof (`extract`, E). -/
  weight : String → Nat → M V
  /-- The shape of a weight, for loops. Free. -/
  weightShape : String → M (List Nat)
  /-- The number of entries of a weight (its data length). Free: structural metadata, like the shape. With
      it a checker establishes that a tensor is well formed (length equals the product of the shape) by a
      concrete comparison, instead of paying a forward pass for it. -/
  weightSize : String → M Nat
  /-- Number `i` of the certificate. Free: the certificate is charged once per proof (`read`). -/
  cert : Nat → M V
  /-- How many numbers the certificate holds. Free. -/
  certSize : M Nat
  /-- A numeral, as a number read from the proof file: 1. -/
  lit : String → Nat → M V
  /-- Zero, free: the Python checker starts its sums at 0 without charge. -/
  zero : V
  /-- Arithmetic, 1 each; `muladd acc a b` is `acc + a * b`. -/
  add : String → V → V → M V
  sub : String → V → V → M V
  muladd : String → V → V → V → M V
  neg : String → V → M V
  min : String → V → V → M V
  max : String → V → V → M V
  /-- Comparisons, 1 each: the only source of truth values about numbers. -/
  lt : String → V → V → M B
  le : String → V → V → M B
  eq : String → V → V → M B
  /-- Bounds on `exp a` (`Exp.lean`), charged 3; the monad fails if the argument is out of range. -/
  exp : String → V → M (V × V)
  /-- Add to the bill. A program can only make itself longer. -/
  charge : String → Nat → M Unit
  /-- Fail: the checker certifies nothing. -/
  fail : {α : Type} → M α
  /-- The two constant truth values, free. -/
  btrue : B
  bfalse : B
  /-- What a truth value can become, and nothing else: a count (`countB`: one if true; `nscale k`: the
      concrete `k` if true, else zero), a choice between two numbers (`selectV`, charged 1 like `min`), or
      another truth value through a gate (charged 1 each). There is no branching: a checker's own code
      never learns a truth value, so what it computes next never depends on the network; and no operation
      takes a count together with a truth value, so a count is only ever a sum of concrete multiples of
      truth values (see the header). -/
  countB : B → N
  nscale : Nat → B → N
  selectV : String → B → V → V → M V
  bnot : String → B → M B
  band : String → B → B → M B
  bor : String → B → B → M B
  /-- Counts. Free, as the Python checker's bookkeeping is. -/
  nzero : N
  nsucc : N → N
  nadd : N → N → N
  nofNat : Nat → N
-- [excerpt] The single-input rule, charged as one exact forward pass and the final comparison (CostM.single).
  single : Graph → Task → Input → M B
  /-- The single rule on a general network (attention): the general checker's exact forward pass on one
      input, charged as cost-v3 charges a single leaf of a general network (`CostM.gsingle`,
      `CountedGeneral.lean`; its soundness is `CostM.gsingle_correct`). `single` covers linear networks
      only; on a network with attention it fails. -/
  gsingle : Graph → Task → Input → M B
-- [excerpt] (The structure has further fields. This run does not offer them.)

instance instMonadInterp (I : Interp) : Monad I.M := I.monad

/-- A scored checker: a computation of a count, for every interpreter. -/
abbrev Checker := (I : Interp) → I.M I.N

/-- The interpreter the service runs: the charges of `cost-v3`, in `CostM`. -/
@[reducible] def Interp.counting : Interp where
  M := CostM
  monad := inferInstance
  V := Q
  B := Bool
  N := Nat
  weight := CostM.weight
  weightShape := CostM.weightShape
  weightSize := CostM.weightSize
  cert := CostM.cert
  certSize := CostM.certSize
  lit := CostM.lit
  zero := ⟨0⟩
  add := CostM.qadd
  sub := CostM.qsub
  muladd := CostM.qmuladd
  neg := CostM.qneg
  min := CostM.qmin
  max := CostM.qmax
  lt := CostM.qlt
  le := CostM.qle
  eq := CostM.qeq
  exp := CostM.qexp
  charge := CostM.charge
  fail := CostM.fail
  btrue := true
  bfalse := false
  countB := fun b => cond b 1 0
  nscale := fun k b => cond b k 0
  selectV := fun cat b x y => ⟨fun _ c => some (cond b x y, c.add cat 1)⟩
  bnot := fun cat b => ⟨fun _ c => some (!b, c.add cat 1)⟩
  band := fun cat a b => ⟨fun _ c => some (a && b, c.add cat 1)⟩
  bor := fun cat a b => ⟨fun _ c => some (a || b, c.add cat 1)⟩
  nzero := 0
  nsucc := Nat.succ
  nadd := Nat.add
  nofNat := id
  single := CostM.single
  gsingle := CostM.gsingle
-- [excerpt] (and the further fields)

/-! ## The counting interpreter, operation by operation (all by `rfl`, for `simp`) -/

namespace Interp

@[simp] theorem counting_M : counting.M = CostM := rfl
@[simp] theorem counting_V : counting.V = Q := rfl
@[simp] theorem counting_B : counting.B = Bool := rfl
@[simp] theorem counting_N : counting.N = Nat := rfl
@[simp] theorem counting_weight : counting.weight = CostM.weight := rfl
@[simp] theorem counting_weightShape : counting.weightShape = CostM.weightShape := rfl
@[simp] theorem counting_weightSize : counting.weightSize = CostM.weightSize := rfl
@[simp] theorem counting_cert : counting.cert = CostM.cert := rfl
@[simp] theorem counting_certSize : counting.certSize = CostM.certSize := rfl
@[simp] theorem counting_lit : counting.lit = CostM.lit := rfl
@[simp] theorem counting_zero : counting.zero = (⟨(0 : Rat)⟩ : Q) := rfl
@[simp] theorem counting_add : counting.add = CostM.qadd := rfl
@[simp] theorem counting_sub : counting.sub = CostM.qsub := rfl
@[simp] theorem counting_muladd : counting.muladd = CostM.qmuladd := rfl
@[simp] theorem counting_neg : counting.neg = CostM.qneg := rfl
@[simp] theorem counting_min : counting.min = CostM.qmin := rfl
@[simp] theorem counting_max : counting.max = CostM.qmax := rfl
@[simp] theorem counting_lt : counting.lt = CostM.qlt := rfl
@[simp] theorem counting_le : counting.le = CostM.qle := rfl
@[simp] theorem counting_eq : counting.eq = CostM.qeq := rfl
@[simp] theorem counting_exp : counting.exp = CostM.qexp := rfl
@[simp] theorem counting_charge : counting.charge = CostM.charge := rfl
@[simp] theorem counting_btrue : counting.btrue = true := rfl
@[simp] theorem counting_bfalse : counting.bfalse = false := rfl
@[simp] theorem counting_countB (b : counting.B) : counting.countB b = cond b 1 0 := rfl
@[simp] theorem counting_nscale (k : Nat) (b : counting.B) : counting.nscale k b = cond b k 0 := rfl
theorem counting_selectV_run (cat : String) (b : Bool) (x y : Q) (env : Env) (c : Cost) :
    (counting.selectV cat b x y).run env c = some (cond b x y, c.add cat 1) := rfl
theorem counting_bnot_run (cat : String) (b : Bool) (env : Env) (c : Cost) :
    (counting.bnot cat b).run env c = some (!b, c.add cat 1) := rfl
theorem counting_band_run (cat : String) (a b : Bool) (env : Env) (c : Cost) :
    (counting.band cat a b).run env c = some (a && b, c.add cat 1) := rfl
theorem counting_bor_run (cat : String) (a b : Bool) (env : Env) (c : Cost) :
    (counting.bor cat a b).run env c = some (a || b, c.add cat 1) := rfl
@[simp] theorem counting_nzero : counting.nzero = (0 : Nat) := rfl
@[simp] theorem counting_nsucc : counting.nsucc = Nat.succ := rfl
@[simp] theorem counting_nadd : counting.nadd = Nat.add := rfl
@[simp] theorem counting_nofNat : counting.nofNat = id := rfl
@[simp] theorem counting_single : counting.single = CostM.single := rfl
@[simp] theorem counting_gsingle : counting.gsingle = CostM.gsingle := rfl

/-- `do` notation in a checker uses the interpreter's monad; for the counting interpreter that is
    `CostM`'s, so `CostM.run_bind` and `CostM.run_pure` apply once these two are rewritten. -/
@[simp] theorem counting_bind {α β : Type} (x : counting.M α) (f : α → counting.M β) :
    (@Bind.bind counting.M (instMonadInterp counting).toBind α β x f) =
      (@Bind.bind CostM CostM.instMonad.toBind α β x f) := rfl

@[simp] theorem counting_pure {α : Type} (a : α) :
    (@Pure.pure counting.M (instMonadInterp counting).toPure α a) =
      (@Pure.pure CostM CostM.instMonad.toPure α a) := rfl

end Interp

end CompactCheck
