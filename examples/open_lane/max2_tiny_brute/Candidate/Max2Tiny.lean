import Protected.N_max2_tiny_v8_s0_c64
import CompactCheck.Soundness

/-!
# A hand-built open-lane proof: brute force, in the two-layer shape

The simplest argument outside the split-tree language, written the way every scored proof will be:

* a general layer, true for all weights: a checker `D` (here: run the checker's exact single-input
  test on every input and count the passes) and its soundness theorem, `D w ≤ numCorrect graph w task`
  for every `w`, from `singleOk_correct`;
* a specific layer: the kernel evaluates `D weights` on the protected weights, and the target follows.

Nothing here is a proof file, a rule or a certificate. The general layer never mentions the weights; the
only place they appear is the instance `D weights = 64`.
-/

namespace Candidate.Max2Tiny

open CompactCheck Protected.N_max2_tiny_v8_s0_c64

/-! ## General layer -/

/-- The checker: the single-input test on every input, for any weights of this graph. -/
def D (w : Weights ℚ) : Nat :=
  (allInputs task.space).countP (fun x => singleOk graph w task x)

/-- Soundness of `D`, for all weights: an input that passes the single-input test is answered
    correctly in the sense of `Spec.lean`. -/
theorem D_sound (w : Weights ℚ) : D w ≤ numCorrect graph w task := by
  unfold D numCorrect
  apply List.countP_mono_left
  intro x _ hx
  simp only [decide_eq_true_eq]
  exact singleOk_correct graph w task x hx

/-! ## Specific layer -/

/-- The kernel runs the network on all 64 inputs of the protected weights (all of them answered correctly). -/
theorem D_weights : D weights = 64 := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  calc claimedCount = 64 := rfl
    _ = D weights := D_weights.symm
    _ ≤ numCorrect graph weights task := D_sound weights

end Candidate.Max2Tiny
