import CompactCheck.Json

/-!
# Tests for the approximate rule

Small cases worked out by hand. The rule is also compared with the Python
checker on every network in the zoo (see `scripts/`). The build fails if any
`#guard` is false.
-/

namespace ApproxTest

open CompactCheck

/-- A tensor of rationals, for writing tests. -/
def T (shape : List Nat) (data : List Rat) : Tensor Rat := ⟨shape, data.toArray⟩

/-! ## The three forms -/

-- P = [[1, 2, 3], [2, 4, 6]] as a dense matrix and as F G with F = [[1], [2]]
-- and G = [[1, 2, 3]].
def Pd : ApproxForm := .dense (T [2, 3] [1, 2, 3,  2, 4, 6])
def Pl : ApproxForm := .lowRank (T [2, 1] [1, 2]) (T [1, 3] [1, 2, 3])

#guard (List.range 2).all fun o => (List.range 3).all fun t => Pd.entry 3 o t == Pl.entry 3 o t
#guard Pl.entry 3 1 2 == 6

-- Lower bounds on P[l, t] - P[j, t] over t = 0, 1, 2. For l = 0 the
-- differences with row 1 are -1, -2, -3. The low-rank bound uses
-- c = F[0] - F[1] = -1 < 0, hence the largest entry of G, 3.
#guard Pd.rowBounds 3 2 0 0 2 == #[0, -3]
#guard Pl.rowBounds 3 2 0 0 2 == #[0, -3]
-- For l = 1: c = 1 ≥ 0, hence the smallest entry of G, 1.
#guard Pl.rowBounds 3 2 1 0 2 == #[1, 0]
-- Only the tokens 1 and 2.
#guard Pd.rowBounds 3 2 0 1 2 == #[0, -3]
#guard Pd.rowBounds 3 2 1 0 1 == #[1, 0]
-- A low-rank bound is not always the smallest difference: with
-- F = [[1, 1], [0, 0]] and G = [[0, 1], [1, 0]], P[0] = [1, 1] but the bound
-- is 0 + 0 = 0.
#guard (ApproxForm.lowRank (T [2, 2] [1, 1,  0, 0]) (T [2, 2] [0, 1,  1, 0])).rowBounds 2 2 0 0 1 ==
  #[0, 0]

-- The error max |W - P|.
#guard approxError (T [2, 3] [1, 2, 3,  2, 4, 6]) Pd == 0
#guard approxError (T [2, 3] [1, 2, 3,  2, 4, 13/2]) Pl == 1/2
#guard approxError (T [2, 3] [0, 2, 3,  2, 4, 6]) Pd == 1

/-! ## Reading an approximation of a map -/

def W : Tensor Rat := T [2, 3] [1, 2, 3,  2, 4, 6]

#guard (approxForm W (.dense [[1, 2, 3], [2, 4, 6]])).toOption == some Pd
#guard (approxForm W (.lowRank [[1], [2]] [[1, 2, 3]])).toOption == some Pl
-- [start, end, value]: row 0 is 1 on columns 0 to 1 and 3 on column 2.
#guard (approxForm W (.rowSegments [[(0, 1, 1), (2, 2, 3)], [(0, 2, 4)]])).toOption ==
  some (.dense (T [2, 3] [1, 1, 3,  4, 4, 4]))
-- Wrong shapes.
#guard (approxForm W (.dense [[1, 2, 3]])).toBool == false
#guard (approxForm W (.dense [[1, 2], [2, 4]])).toBool == false
#guard (approxForm W (.dense [[1, 2, 3], [2, 4]])).toBool == false
#guard (approxForm W (.dense [])).toBool == false
-- An inner dimension of 0, or above min(2, 3) = 2.
#guard (approxForm W (.lowRank [[], []] [])).toBool == false
#guard (approxForm W (.lowRank [[1, 1, 1], [2, 2, 2]] [[1, 2, 3], [1, 2, 3], [1, 2, 3]])).toBool ==
  false
#guard (approxForm W (.lowRank [[1], [2]] [[1, 2]])).toBool == false
-- Segments that skip a column, overlap, end too late or too early, run
-- backwards, or are missing.
#guard (approxForm W (.rowSegments [[(0, 0, 1), (2, 2, 3)], [(0, 2, 4)]])).toBool == false
#guard (approxForm W (.rowSegments [[(0, 1, 1), (1, 2, 3)], [(0, 2, 4)]])).toBool == false
#guard (approxForm W (.rowSegments [[(0, 3, 1)], [(0, 2, 4)]])).toBool == false
#guard (approxForm W (.rowSegments [[(0, 1, 1)], [(0, 2, 4)]])).toBool == false
#guard (approxForm W (.rowSegments [[(0, -1, 1)], [(0, 2, 4)]])).toBool == false
#guard (approxForm W (.rowSegments [[], [(0, 2, 4)]])).toBool == false
#guard (approxForm W (.rowSegments [[(0, 2, 4)]])).toBool == false

/-! ## Interval leaves with an approximation

The max network of `IntervalTest.lean`: the logits are `M[:, x0] + M[:, x1]`. -/

def M : Tensor Rat := T [3, 3] [3, -3, -3,  1, 3, -3,  1, 1, 3]
def g : Graph := ⟨2, 3, [.input, .sum 0 1, .linear 1 "M" none], 2⟩
def w : Weights Rat := [("M", M)]
def task : Task := maxTask 2 3

/-- The approximation `rows` of the output map. -/
def approx (rows : List (List Rat)) : Approx :=
  let form : ApproxForm := .dense (T [3, 3] rows.flatten)
  { name := "P", of := 2, W := M, form, eps := approxError M form }

def exact : Approx := approx [[3, -3, -3], [1, 3, -3], [1, 1, 3]]
-- P[0, 0] = 4 instead of 3: the error is 1.
def off : Approx := approx [[4, -3, -3], [1, 3, -3], [1, 1, 3]]

#guard exact.eps == 0 && off.eps == 1
#guard (buildApprox g w ⟨"P", 2, .dense [[4, -3, -3], [1, 3, -3], [1, 1, 3]]⟩).toOption.map
  (fun a => (a.of, a.form, a.eps)) == some (2, off.form, 1)

-- The box {2} × {0, 1, 2}: the exact margins are 4 and 4 (`IntervalTest`).
-- With P = M they are the same. With the error, output 0 gets
-- (3 + 3) + min(1 - 4, 1 + 3, 3 + 3) - 2 = 1 and output 1 gets
-- (3 + 3) + min(0, -2, 6) - 2 = 2.
#guard approxMargins [⟨2, 2⟩, ⟨0, 2⟩] 3 M none 2 exact == [4, 4, 0]
#guard approxMargins [⟨2, 2⟩, ⟨0, 2⟩] 3 M none 2 off == [1, 2, -2]
#guard (intervalLeaf g w task [⟨2, 2⟩, ⟨0, 2⟩] (some off)).toOption == some true
-- A position with one token uses the exact difference: on the input (2, 0)
-- the logits are [0, -2, 4], whatever the approximation.
#guard approxMargins [⟨2, 2⟩, ⟨0, 0⟩] 3 M none 2 off == [4, 6, 0]

-- A larger error: P = M + 4 everywhere, so eps = 4 and the bounds drop by 8.
def far : Approx := approx [[7, 1, 1], [5, 7, 1], [5, 5, 7]]
#guard far.eps == 4
#guard (intervalLeaf g w task [⟨2, 2⟩, ⟨0, 2⟩] (some far)).toOption == some false

-- An approximation of a map that is not the output, on the summed one-hot
-- input, rejects the proof.
def g2 : Graph := ⟨2, 3, [.input, .sum 0 1, .linear 1 "M" none, .linear 1 "M" none], 3⟩
#guard (intervalLeaf g2 w task [⟨2, 2⟩, ⟨0, 2⟩] (some exact)).toBool == false
#guard (intervalLeaf g2 w task [⟨2, 2⟩, ⟨0, 2⟩] (some { exact with of := 3 })).toOption ==
  some true
-- Only linear maps can be approximated.
#guard (buildApprox g w ⟨"P", 1, .dense [[3, -3, -3], [1, 3, -3], [1, 1, 3]]⟩).toBool == false

/-! ## Numbers -/

open Lean (Json JsonNumber)

#guard (parseNumber (.str "1.25")).toOption == some (5/4)
#guard (parseNumber (.str " -3/4 ")).toOption == some (-3/4)
#guard (parseNumber (.str "+3/6")).toOption == some (1/2)
#guard (parseNumber (.str ".5")).toOption == some (1/2)
#guard (parseNumber (.str "5.")).toOption == some 5
#guard (parseNumber (.str "007")).toOption == some 7
-- Not dyadic, not a number, exponents, a zero denominator.
#guard (parseNumber (.str "0.1")).toBool == false
#guard (parseNumber (.str "1/3")).toBool == false
#guard (parseNumber (.str "1e-3")).toBool == false
#guard (parseNumber (.str ".")).toBool == false
#guard (parseNumber (.str "")).toBool == false
#guard (parseNumber (.str "-")).toBool == false
#guard (parseNumber (.str "1/0")).toBool == false
#guard (parseNumber (.str "1/2/3")).toBool == false
#guard (parseNumber (.str "--1")).toBool == false
-- Integers below 2^160.
#guard (parseNumber (.num ⟨2 ^ 160 - 1, 0⟩)).toOption == some ((2 ^ 160 - 1 : Nat) : Rat)
#guard (parseNumber (.num ⟨-(2 ^ 160), 0⟩)).toBool == false
#guard (parseNumber (.bool true)).toBool == false
#guard (parseNumber .null).toBool == false
-- A number with a fraction part is a float: 0.1 is the nearest binary64.
#guard (parseNumber (.num ⟨1, 1⟩)).toOption == some (3602879701896397 / 36028797018963968)
#guard (parseNumber (.num ⟨-15, 1⟩)).toOption == some (-3/2)
-- 2^53 + 1 is halfway between two floats: ties go to the even one, 2^53.
#guard (parseNumber (.num ⟨90071992547409930, 1⟩)).toOption == some 9007199254740992
-- Too small for a float: 0. The smallest float is 2^-1074.
#guard (parseNumber (.num ⟨1, 400⟩)).toOption == some 0
#guard (parseNumber (.num ⟨5, 324⟩)).toOption == some (1 / ((2 ^ 1074 : Nat) : Rat))
-- The largest float, and a number past it.
#guard nearestFloat (17976931348623157 * 10 ^ 292) 1 == some (((2 ^ 53 - 1) * 2 ^ 971 : Nat) : Rat)
#guard nearestFloat (18 * 10 ^ 307) 1 == none
-- Floats above 2^160 are too large for a proof number.
#guard (parseNumber (.num ⟨(2 ^ 200 : Nat) * 10, 1⟩)).toBool == false

end ApproxTest
