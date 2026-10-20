import CompactCheck.CountedCheck

/-!
# Counted operations: the checker's rules as charged primitives

Operations a scored checker may use besides the arithmetic of `Counted.lean`: each one runs a piece of
the existing checker (whose soundness is proved) and charges what `cost-v3` charges for it, through the
same formulas as `CountedCheck.lean`. Their results are sealed numbers or booleans, so a checker built
from them is billed for everything it learns about the network. Every operation comes with its
specification: what its result means in terms of the checker's own functions, so that a soundness proof
of a program never looks inside the monad.

This file uses only core Lean.
-/

namespace CompactCheck

namespace CostM

/-- The single rule on one input: `singleOk`, charged as one exact forward pass and the final comparison
    (`singleCost`). `none` if the forward pass cannot be billed on this graph. -/
def single (g : Graph) (task : Task) (x : Input) : CostM Bool := ⟨fun env c =>
  match singleCost g env.weights with
  | some sc => some (singleOk g env.weights task x, c.add "single" sc)
  | none => none⟩

/-- The interval rule on one box, with no approximation: `intervalLeaf`, charged as `intervalCost`.
    `false` (not an error) if the box has no constant label; `none` if the rule cannot follow the
    network. -/
def interval (g : Graph) (task : Task) (box : Box) : CostM Bool := ⟨fun env c =>
  match task.constantLabel box with
  | none => some (false, c)
  | some l =>
    match intervalCost g env.weights box l none, intervalLeaf g env.weights task box none with
    | some ic, .ok b => some (b, c.add "interval" ic)
    | _, _ => none⟩

/-! ## Specifications -/

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

theorem interval_spec {g : Graph} {task : Task} {box : Box} {env : Env} {c c' : Cost}
    (h : (interval g task box).run env c = some (true, c')) :
    intervalLeaf g env.weights task box none = .ok true := by
  simp only [interval] at h
  split at h
  · simp at h
  · split at h
    · rename_i ic b hm
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      rw [h.1] at hm
      exact hm
    · cases h

end CostM

end CompactCheck
