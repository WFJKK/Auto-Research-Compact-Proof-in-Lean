import CompactCheck.GeneralSound
import CompactCheck.CountedGeneral

/-!
# The soundness of the counted single rule on general networks

A run of `CostM.gsingle g task x` that answers `true` means the network answers `x` correctly, in
the real semantics of the specification (`Correct`, with the real exponential): the verdict is
`generalSingle`'s (`gsingleRun_generalSingle`), and `generalSingle_correct` (GeneralSound.lean) is
the general checker's soundness theorem for a single leaf. A run of `CostM.ginterval g task box`
that answers `true` means the same for every input of the box (`generalInterval_correct`).
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

/-- A run of the interval rule that answers `true` means the network answers every input of the box
    correctly (`generalInterval_correct`). -/
theorem ginterval_correct {g : Graph} {task : Task} {box : Box} {env : Env} {c c' : Cost}
    (h : (ginterval g task box).run env c = some (true, c')) (x : Input) (hx : inBox box x = true) :
    Correct g env.weights task x := by
  have h' : (match dweights env.weights with
      | none => none
      | some dw =>
        match gintervalRun g dw task box with
        | some (b, k) => some (b, c.add "interval" k)
        | none => none) = some (true, c') := h
  cases hdw : dweights env.weights with
  | none => simp [hdw] at h'
  | some dw =>
    simp only [hdw] at h'
    cases hr : gintervalRun g dw task box with
    | none => simp [hr] at h'
    | some p =>
      obtain ⟨b, k⟩ := p
      simp only [hr, Option.some.injEq, Prod.mk.injEq] at h'
      rw [h'.1] at hr
      exact generalInterval_correct hdw (gintervalRun_generalInterval hr) x hx

end CostM

end CompactCheck
