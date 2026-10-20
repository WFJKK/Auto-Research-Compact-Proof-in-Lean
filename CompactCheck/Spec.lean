import Mathlib.Analysis.Complex.Exponential
import CompactCheck.Semantics

/-!
# The spec: what the network computes, and what "correct" means

This is the file a reader has to trust. Every theorem about the checker
ends in a statement about `Correct` and `numCorrect` below, and they say
what they say only if these definitions mean what they should. They rest
on four other files:

* `Network.lean`: what a graph is;
* `Eval.lean` and `Semantics.lean`: what each operation computes. Each
  definition there is the formula in its docstring, written once for any
  number type; here it is used with the real numbers, and `exp` is the real
  exponential;
* `Task.lean`: the input space and the correct answer to each input.

The weights are the network's float weights, which are rational numbers,
read as real numbers. So are the numbers in a model's code, such as the
scale `1 / sqrt(d_head)` of attention: they are written as the float64
values the Python code holds.
-/

namespace CompactCheck

noncomputable section

/-- `exp` and `softmax` use the real exponential and the real division. -/
instance realExpDiv : ExpDiv ℝ := ⟨Real.exp, (· / ·)⟩

/-- The weights as real numbers. -/
def realWeights (w : Weights ℚ) : Weights ℝ :=
  w.map fun p => (p.1, p.2.map (fun q : ℚ => (q : ℝ)))

/-- What the network computes on input `x`, over the real numbers. -/
def realOutput (g : Graph) (w : Weights ℚ) (x : Input) : Option (Tensor ℝ) :=
  semGraph g (realWeights w) x

/-- The network answers `x` correctly: its output is a vector of `n` logits
    (shape `[1, n]`), the label is one of the `n` outputs, and the label's
    logit is strictly larger than every other logit. A tie counts as wrong. -/
def Correct (g : Graph) (w : Weights ℚ) (task : Task) (x : Input) : Prop :=
  ∃ out : Tensor ℝ, realOutput g w x = some out ∧ out.shape = [1, out.data.size] ∧
    task.label x < out.data.size ∧
    ∀ j < out.data.size, j ≠ task.label x → out.get j < out.get (task.label x)

open Classical in
/-- The number of inputs the network answers correctly. -/
def numCorrect (g : Graph) (w : Weights ℚ) (task : Task) : Nat :=
  (allInputs task.space).countP fun x => decide (Correct g w task x)

end

end CompactCheck
