import Protected.N_max2_tiny_v8_s0_c64
import CompactCheck.Soundness
import CompactCheck.CountedOps

/-!
# A scored open-lane proof: brute force in the counted language

The same argument as `max2_tiny_brute`, written so that it has a length (docs/COUNTED.md): the checker
`D : Checker` is a function of the interpreter `I`; it runs the single-input rule on every input through
`I.single`, which the counting interpreter charges as one exact forward pass, and counts the passes with
`I.ifN`. Nothing else in `D` touches a number of the network, and nothing in `D` can look inside `I.B` or
`I.N`, so the bill is the single-rule cost times the number of inputs.

* General layer: `countSingles`, `D`, and `D_sound`, for all weights and certificates (the certificate is
  empty here and never read). The soundness theorem is about `D Interp.counting`, the interpreter the
  service runs; its proof rewrites the interpreter's operations to `CostM`'s and uses their specifications.
* Specific layer: the kernel evaluates `CostM.billed (D Interp.counting) ⟨weights, cert⟩` on the protected
  weights (`D_instance`), and the target follows.
-/

namespace Candidate.Max2TinyScored

open CompactCheck Protected.N_max2_tiny_v8_s0_c64

/-! ## General layer -/

/-- The single-input rule on each input of `xs`, counting the passes; each call is billed. -/
def countSingles (I : Interp) (g : Graph) (task : Task) : List Input → I.M I.N
  | [] => pure I.nzero
  | x :: xs => do
    let ok ← I.single g task x
    let n ← countSingles I g task xs
    I.ifN ok (pure (I.nsucc n)) (pure n)

/-- The checker: every input of the task's space. -/
def D : Checker := fun I => countSingles I graph task (allInputs task.space)

open Classical in
/-- `countSingles` never counts more than the inputs that are correct, for any weights and bill. -/
theorem countSingles_le (env : Env) : ∀ (xs : List Input) (c : Cost) (n : Nat) (c' : Cost),
    (countSingles Interp.counting graph task xs).run env c = some (n, c') →
    n ≤ xs.countP (fun x => decide (Correct graph env.weights task x))
  | [], c, n, c', h => by
    simp only [countSingles, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    omega
  | x :: xs, c, n, c', h => by
    simp only [countSingles, CostM.run_bind] at h
    split at h
    · rename_i ok c1 hs
      split at h
      · rename_i m c2 hm
        have ih := countSingles_le env xs c1 m c2 hm
        rw [List.countP_cons]
        cases ok with
        | false => simp only [Bool.cond_false, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h; omega
        | true =>
          have hc : Correct graph env.weights task x := singleOk_correct graph env.weights task x (CostM.single_spec hs)
          simp only [Bool.cond_true, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
          simp only [hc, decide_true, ite_true]
          omega
      · cases h
    · cases h

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  unfold numCorrect
  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h

/-! ## Specific layer -/

/-- The kernel runs the single rule on all 64 inputs of the protected weights: all pass, and the bill is
    64 forward passes at 63 operations each. -/
theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (64, 64 * 63) := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  obtain ⟨cost, h⟩ := CostM.exec_of_billed D_instance
  exact D_sound weights cert 64 cost h

end Candidate.Max2TinyScored
