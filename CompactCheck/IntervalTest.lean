import CompactCheck.Check

/-!
# Tests for the interval rule

Small cases worked out by hand. The rule is also compared with the Python
checker on random proofs for every network in the zoo (see `scripts/`).
The build fails if any `#guard` is false.
-/

namespace IntervalTest

open CompactCheck

/-- A tensor of rationals, for writing tests. -/
def T (shape : List Nat) (data : List Rat) : Tensor Rat := ⟨shape, data.toArray⟩

/-! ## The pieces -/

def f (t : Nat) : Rat := [5, 2, 7, 1].getD t 0

#guard rangeMin f 0 3 == 1
#guard rangeMin f 1 2 == 2
#guard rangeMax f 0 2 == 7
#guard rangeMin f 2 2 == 7 && rangeMax f 3 3 == 1

/-- Rows `[1, 2, 3]` and `[4, 5, 6]`. -/
def W : Tensor Rat := T [2, 3] [1, 2, 3,  4, 5, 6]

-- The box {0, 1} × {2}. Its inputs (0, 2) and (1, 2) have the summed
-- one-hot vectors [1, 0, 1] and [0, 1, 1], which W maps to [4, 10] and
-- [5, 11]: the bounds are exact here.
#guard ilinearOneHot [⟨0, 1⟩, ⟨2, 2⟩] 2 3 true W none ==
  some (.bounds (T [1, 2] [4, 10]) (T [1, 2] [5, 11]))
-- Per position: the columns 0..1 at position 0, column 2 at position 1.
#guard ilinearOneHot [⟨0, 1⟩, ⟨2, 2⟩] 2 3 false W none ==
  some (.bounds (T [1, 2, 2] [1, 4,  3, 6]) (T [1, 2, 2] [2, 5,  3, 6]))
-- A weight whose columns are not the vocabulary.
#guard ilinearOneHot [⟨0, 1⟩, ⟨2, 2⟩] 2 4 true W none == none

-- Interval arithmetic: x0 ∈ [0, 2], x1 ∈ [1, 3].
-- Row [1, -1]: x0 - x1 ∈ [0 - 3, 2 - 1] = [-3, 1]. Row [2, 0]: [0, 4].
#guard ilinearBounds (T [2, 2] [1, -1,  2, 0]) none (T [1, 2] [0, 1]) (T [1, 2] [2, 3]) ==
  some (.bounds (T [1, 2] [-3, 0]) (T [1, 2] [1, 4]))
#guard ilinearBounds (T [2, 2] [1, -1,  2, 0]) (some (T [2] [10, 20]))
    (T [1, 2] [0, 1]) (T [1, 2] [2, 3]) ==
  some (.bounds (T [1, 2] [7, 20]) (T [1, 2] [11, 24]))

-- The one-hot input may only be summed over the positions.
#guard isum 1 (.oneHot false) == some (.oneHot true)
#guard isum (-2) (.oneHot false) == some (.oneHot true)
#guard isum 2 (.oneHot false) == none
#guard isum 1 (.oneHot true) == none
-- Bounds add up.
#guard isum 1 (.bounds (T [1, 2, 2] [1, 2,  3, 4]) (T [1, 2, 2] [5, 6,  7, 8])) ==
  some (.bounds (T [1, 2] [4, 6]) (T [1, 2] [12, 14]))
#guard iadd (.bounds (T [1, 2] [1, 2]) (T [1, 2] [3, 4]))
    (.bounds (T [1, 2] [10, 20]) (T [1, 2] [30, 40])) ==
  some (.bounds (T [1, 2] [11, 22]) (T [1, 2] [33, 44]))
#guard iadd (.oneHot true) (.bounds (T [1, 2] [1, 2]) (T [1, 2] [3, 4])) == none

/-! ## A network that computes the maximum

The logits are `M[:, x0] + M[:, x1]`, with `M[v, t] = 3` if `t = v`, `1` if
`t < v` and `-3` if `t > v`. The label's logit is at least 4 and every
other logit at most 2, so every input is answered correctly. -/

def M : Tensor Rat := T [3, 3] [3, -3, -3,  1, 3, -3,  1, 1, 3]

/-- The contracted form: one linear map after the sum. -/
def g1 : Graph := ⟨2, 3, [.input, .sum 0 1, .linear 1 "M" none], 2⟩

/-- The same network as two maps, the identity first. -/
def g2 : Graph := ⟨2, 3, [.input, .sum 0 1, .linear 1 "I" none, .linear 2 "M" none], 3⟩

def w : Weights Rat := [("M", M), ("I", T [3, 3] [1, 0, 0,  0, 1, 0,  0, 0, 1])]

def task : Task := maxTask 2 3

-- The box {2} × {0, 1, 2}: label 2. The margins over outputs 0 and 1 are
-- (3 + 3) + min(1 - 3, 1 + 3, 3 + 3) = 4 and (3 + 3) + min(0, -2, 6) = 4,
-- the true smallest margins, since only one position varies.
#guard (linearMargins [⟨2, 2⟩, ⟨0, 2⟩] 3 M none 2 none 2 (.oneHot true)).toOption == some [4, 4, 0]
#guard (intervalLeaf g1 w task [⟨2, 2⟩, ⟨0, 2⟩] none).toOption == some true
-- Through the identity first, the bounds after it are [0, 0, 1] and
-- [1, 1, 2], and the margin bounds are again 4 and 4.
#guard (intervalLeaf g2 w task [⟨2, 2⟩, ⟨0, 2⟩] none).toOption == some true
-- {1, 2} × {2}: label 2, margins 10 and 4.
#guard (linearMargins [⟨1, 2⟩, ⟨2, 2⟩] 3 M none 2 none 2 (.oneHot true)).toOption == some [10, 4, 0]
-- The largest token is not the same for every input of {0, 1, 2}².
#guard task.constantLabel [⟨0, 2⟩, ⟨0, 2⟩] == none
#guard (intervalLeaf g1 w task [⟨0, 2⟩, ⟨0, 2⟩] none).toOption == some false

-- A proof: x0 = 2 with any x1 (3 inputs), x0 = 1 with x1 ≤ 1 (2 inputs),
-- two single leaves, and one leaf whose label is not constant.
def tree : SplitTree :=
  .split 0 [1, 2]
    [.split 1 [1] [.leaf .single, .leaf (.interval none)],
     .split 1 [2] [.leaf (.interval none), .leaf .single],
     .leaf (.interval none)]

def proof (net : String) : ProofFile := ⟨net, false, [], [], tree⟩

#guard (checkProof g1 w task (proof "g1")).toOption == some 7
#guard (checkProof g2 w task (proof "g2")).toOption == some 7
-- Brute force certifies all 9 inputs.
#guard (checkProof g1 w task ⟨"g1", false, [], [], fullTree task.space⟩).toOption == some 9

/-! ## A network that is wrong on (2, 0)

The small max2-shaped network of `EvalTest.lean`, whose output on [2, 0]
is [4, 3/2, 5/2]. As an interval leaf, the box {2} × {0} gets the exact
margins 5/2 - 4 and 5/2 - 3/2, so it is not certified. -/

def gBad : Graph where
  positions := 2
  values := 3
  nodes := [.input, .sum 0 1, .linear 1 "E" none, .linear 2 "L" (some "b"), .linear 3 "U" none]
  output := 4

def wBad : Weights Rat :=
  [("E", T [2, 3] [1, 0, 2,  0, 1, 1]),
   ("L", T [2, 2] [1, 1,  0, 1]),
   ("b", T [2] [0, 1/2]),
   ("U", T [3, 2] [1, 0,  0, 1,  1, -1])]

#guard (intervalLeaf gBad wBad task [⟨2, 2⟩, ⟨0, 0⟩] none).toOption == some false

/-! ## Proofs the interval rule rejects as a whole -/

-- Adding the one-hot input to itself.
def gAdd : Graph := ⟨2, 3, [.input, .add 0 0, .sum 1 1, .linear 2 "M" none], 3⟩
#guard (intervalLeaf gAdd w task [⟨2, 2⟩, ⟨0, 2⟩] none).toBool == false
-- An output computed per position (no sum over the positions).
def gPer : Graph := ⟨2, 3, [.input, .linear 0 "M" none], 1⟩
#guard (intervalLeaf gPer w task [⟨2, 2⟩, ⟨0, 2⟩] none).toBool == false
-- An interval leaf that names an approximation the proof does not give.
#guard (checkProof g1 w task ⟨"g1", false, [], [], .leaf (.interval (some "A"))⟩).toBool
  == false

end IntervalTest
