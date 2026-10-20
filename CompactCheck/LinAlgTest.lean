import CompactCheck.LinAlg

/-!
# Edge cases for `LinAlg.lean`

Written by hand: one or two tests per operation, chosen at the edges
(empty vectors, ties, mismatched lengths, out-of-range indices). The
build fails if any `#guard` is false. Random tests against a Python
reference are in `LinAlgRandomTest.lean`.
-/

namespace LinAlgTest

open CompactCheck

/-! ## Vectors -/

-- Exact fractions: nothing is rounded.
#guard vecAdd [1/2, 1/3] [1/2, 2/3] == ([1, 1] : Vec)
#guard vecDot [1/3, 1/3, 1/3] [1, 1, 1] == (1 : Rat)

-- Operations on two vectors stop at the shorter one.
#guard vecAdd [1, 2, 3] [10, 20] == ([11, 22] : Vec)
#guard vecSub [5] [1, 2] == ([4] : Vec)
#guard vecDot [1, 2, 3] [10, 20] == (50 : Rat)
#guard vecAdd [] [1, 2] == ([] : Vec)

-- Reading outside a vector gives 0.
#guard vecGet [7, 8] 1 == (8 : Rat)
#guard vecGet [7, 8] 5 == (0 : Rat)

-- One-hot vectors. A position beyond the end gives all zeros.
#guard oneHot 4 2 == ([0, 0, 1, 0] : Vec)
#guard oneHot 3 7 == ([0, 0, 0] : Vec)
#guard oneHot 0 0 == ([] : Vec)

-- Absolute value.
#guard ratAbs (-3/4) == (3/4 : Rat)
#guard ratAbs 0 == (0 : Rat)
#guard vecAbs [-1, 2, -1/2] == ([1, 2, 1/2] : Vec)

-- Scale and shift.
#guard vecScale (1/2) [2, -3] == ([1, -3/2] : Vec)
#guard vecShift (-2) [5, 0] == ([3, -2] : Vec)

-- Slices: entries lo to hi, both included.
#guard vecSlice [10, 11, 12, 13] 1 2 == ([11, 12] : Vec)
#guard vecSlice [10, 11, 12, 13] 2 2 == ([12] : Vec)
#guard vecSlice [10, 11, 12, 13] 0 3 == ([10, 11, 12, 13] : Vec)
#guard vecSlice [10, 11, 12, 13] 3 9 == ([13] : Vec)
#guard vecSlice [10, 11, 12, 13] 3 1 == ([] : Vec)

-- Summing vectors. The empty sum is the zero vector of length n, not [].
#guard vecSumList 3 [] == ([0, 0, 0] : Vec)
#guard vecSumList 2 [[1, 2], [3, 4], [5, 6]] == ([9, 12] : Vec)

-- Max and min, and 0 for the empty vector.
#guard listMax [3, 9, 4] == (9 : Rat)
#guard listMax [-2, -5] == (-2 : Rat)
#guard listMin [3, 9, 4] == (3 : Rat)
#guard listMax [] == (0 : Rat)
#guard listMin [] == (0 : Rat)

/-! ## Margins and the final test -/

-- Margins: v[l] - v[j] for every j.
#guard marginsAt [1, 5, 3] 1 == ([4, 0, 2] : Vec)

-- The final test skips entry l and needs every other entry > 0.
#guard allPosExcept [1, -7, 2] 1 == true
#guard allPosExcept [1, 0, 2] 0 == false       -- 0 is not > 0
#guard allPosExcept [] 0 == true

-- strictMaxAt: the label's entry must be strictly the largest.
#guard strictMaxAt [1, 5, 3] 1 == true
#guard strictMaxAt [1, 5, 3] 0 == false
#guard strictMaxAt [1, 5, 5] 1 == false        -- a tie is never accepted
#guard strictMaxAt [7] 0 == true               -- one output: nothing to beat
#guard strictMaxAt [-1, -2] 5 == false         -- a label beyond the end
#guard strictMaxAt [] 0 == false

-- boxDotLower with c = [1, -2], centre [0, 0], radius [1, 1]:
-- the worst corner is x = [-1, 1], where c · x = -3.
#guard boxDotLower [1, -2] [0, 0] [1, 1] == (-3 : Rat)
-- Radius zero: the box is a single point, and the bound is exact.
#guard boxDotLower [1, -2] [3, 1] [0, 0] == (1 : Rat)

/-! ## Matrices -/

/-- A small example of shape (2, 3). -/
def W0 : Mat := [[1, 2, 3],
                 [4, 5, 6]]

#guard matRow W0 1 == ([4, 5, 6] : Vec)
#guard matRow W0 2 == ([] : Vec)
#guard matGet W0 1 2 == (6 : Rat)
#guard matGet W0 5 5 == (0 : Rat)
#guard matNumCols W0 == 3
#guard matCol W0 2 == ([3, 6] : Vec)
#guard matVec W0 [1, 1, 1] == ([6, 15] : Vec)
#guard matTranspose W0 == ([[1, 4], [2, 5], [3, 6]] : Mat)
#guard matTranspose [] == ([] : Mat)
#guard matMul W0 [[1, 0], [0, 1], [1, 1]] == ([[4, 5], [10, 11]] : Mat)
#guard matSub W0 [[1, 1, 1], [1, 1, 1]] == ([[0, 1, 2], [3, 4, 5]] : Mat)
#guard matAbs [[1, -2], [-3, 4]] == ([[1, 2], [3, 4]] : Mat)
#guard matMaxAbs [[1, -7], [3, 4]] == (7 : Rat)
#guard matMaxAbs [] == (0 : Rat)
#guard minOverCols W0 1 2 == ([2, 5] : Vec)
#guard maxOverCols W0 0 1 == ([2, 5] : Vec)
#guard matRowDiffs W0 1 == ([[3, 3, 3], [0, 0, 0]] : Mat)

-- Shapes: the check rejects ragged and wrongly sized matrices.
#guard matHasShape W0 2 3 == true
#guard matHasShape W0 3 2 == false
#guard matHasShape [[1, 2], [3]] 2 2 == false
#guard matHasShape [] 0 5 == true

-- W times a one-hot vector is a column of W. This is why the forward
-- pass never builds one-hot vectors.
#guard matVec W0 (oneHot 3 1) == matCol W0 1

end LinAlgTest
