-- [excerpt] CompactCheck/CountedGeneralSound.lean as this run offers it: an input the general single rule accepts is answered correctly.
-- [excerpt] Lines marked like this one are notes. Every other line is a line of the Lean project's file,
-- [excerpt] in its order. The file holds more than is shown here.

namespace CompactCheck

namespace CostM

theorem gsingle_correct {g : Graph} {task : Task} {x : Input} {env : Env} {c c' : Cost}
    (h : (gsingle g task x).run env c = some (true, c')) : Correct g env.weights task x := by
  have h' : (match dweights env.weights with
      | none => none
      | some dw =>
        match gsingleRun g dw task x with
        | some (b, k) => some (b, c.add "single" k)
        | none => none) = some (true, c') := h
  cases hdw : dweights env.weights with
  | none => simp [hdw] at h'
  | some dw =>
    simp only [hdw] at h'
    cases hr : gsingleRun g dw task x with
    | none => simp [hr] at h'
    | some p =>
      obtain ⟨b, k⟩ := p
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h'
      rw [h'.1] at hr
      exact generalSingle_correct hdw (gsingleRun_generalSingle hr)

end CostM

end CompactCheck
