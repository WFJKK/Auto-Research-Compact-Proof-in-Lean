import CompactCheck.GeneralSound
import CompactCheck.CountedGeneral

/-!
# The soundness of the counted single rule on general networks

A run of `CostM.gsingle g task x` that answers `true` means the network answers `x` correctly, in the real
semantics of the specification (`Correct`, with the real exponential): the verdict is `generalSingle`'s
(`gsingleRun_generalSingle`), and `generalSingle_correct` (GeneralSound.lean) is the general checker's
soundness theorem for a single leaf.
-/

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
