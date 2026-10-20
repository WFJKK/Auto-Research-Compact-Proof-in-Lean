import CompactCheck.Eval

/-!
# Tests for `Eval.lean`

Small cases worked out by hand. The evaluator is also compared with
PyTorch and with the Python checker on every network in the zoo (see
`scripts/`). The build fails if any `#guard` is false.
-/

namespace EvalTest

open CompactCheck

/-- A tensor of rationals, for writing tests. -/
def T (shape : List Nat) (data : List Rat) : Tensor Rat := ⟨shape, data.toArray⟩

-- The one-hot input of the tokens [2, 0], with 3 values per position.
#guard (oneHotInput 2 3 [2, 0] : Option (Tensor Rat)) ==
  some (T [1, 2, 3] [0, 0, 1,  1, 0, 0])
-- A token outside the vocabulary, or the wrong number of positions: none.
#guard (oneHotInput 2 3 [3, 0] : Option (Tensor Rat)) == none
#guard (oneHotInput 2 3 [1] : Option (Tensor Rat)) == none

-- Summing over the positions (dimension 1, or -2 counted from the end).
#guard sumOp 1 (T [1, 2, 3] [0, 0, 1,  1, 0, 0]) == some (T [1, 3] [1, 0, 1])
#guard sumOp (-2) (T [1, 2, 3] [0, 0, 1,  1, 0, 0]) == some (T [1, 3] [1, 0, 1])
-- Summing over the last dimension instead.
#guard sumOp 2 (T [1, 2, 3] [1, 2, 3,  4, 5, 6]) == some (T [1, 2] [6, 15])
-- Summing over the batch dimension.
#guard sumOp 0 (T [1, 2] [7, 8]) == some (T [2] [7, 8])
-- A dimension that does not exist.
#guard sumOp 3 (T [1, 2, 3] [1, 2, 3,  4, 5, 6]) == none
#guard sumOp (-4) (T [1, 2, 3] [1, 2, 3,  4, 5, 6]) == none

/-- A weight of shape [2, 3]. -/
def W : Tensor Rat := T [2, 3] [1, 2, 3,  4, 5, 6]

-- A linear map on a vector: [1, 0, 1] ↦ [1 + 3, 4 + 6].
#guard linearOp W none (T [1, 3] [1, 0, 1]) == some (T [1, 2] [4, 10])
-- With a bias.
#guard linearOp W (some (T [2] [10, 20])) (T [1, 3] [1, 0, 1]) == some (T [1, 2] [14, 30])
-- On every position separately: [0, 0, 1] ↦ [3, 6] and [1, 0, 0] ↦ [1, 4].
#guard linearOp W none (T [1, 2, 3] [0, 0, 1,  1, 0, 0]) == some (T [1, 2, 2] [3, 6,  1, 4])
-- Exact fractions.
#guard linearOp (T [1, 2] [1/3, 1/6]) none (T [1, 2] [1, 2]) == some (T [1, 1] [2/3])
-- Shapes that do not fit: wrong last dimension, wrong bias, malformed weight.
#guard linearOp W none (T [1, 2] [1, 0]) == none
#guard linearOp W (some (T [3] [1, 2, 3])) (T [1, 3] [1, 0, 1]) == none
#guard linearOp (T [2, 3] [1, 2]) none (T [1, 3] [1, 0, 1]) == none

-- Entrywise sums.
#guard addOp (T [1, 2] [1, 2]) (T [1, 2] [10, 20]) == some (T [1, 2] [11, 22])
#guard addOp (T [1, 2] [1, 2]) (T [2] [10, 20]) == none

/-! A small network in the shape of max2: sum the one-hot input over the
positions, then three linear maps. -/

def g : Graph where
  positions := 2
  values := 3
  nodes := [.input, .sum 0 1, .linear 1 "E" none, .linear 2 "L" (some "b"), .linear 3 "U" none]
  output := 4

def w : Weights Rat :=
  [("E", T [2, 3] [1, 0, 2,  0, 1, 1]),
   ("L", T [2, 2] [1, 1,  0, 1]),
   ("b", T [2] [0, 1/2]),
   ("U", T [3, 2] [1, 0,  0, 1,  1, -1])]

-- Input [2, 0]: summed one-hot [1, 0, 1]; E gives [3, 1]; L and b give
-- [4, 3/2]; U gives [4, 3/2, 5/2].
#guard evalGraph g w [2, 0] == some (T [1, 3] [4, 3/2, 5/2])
-- The positions are summed first, so the order of the tokens does not matter.
#guard evalGraph g w [0, 2] == evalGraph g w [2, 0]
-- A missing weight, or an argument that is not an earlier operation: none.
#guard evalGraph g (w.filter (·.1 != "b")) [2, 0] == none
#guard evalGraph { g with nodes := [.input, .sum 2 1] , output := 1 } w [2, 0] == none

end EvalTest
