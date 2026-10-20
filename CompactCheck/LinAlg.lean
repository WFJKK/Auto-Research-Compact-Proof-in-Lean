/-!
# Linear algebra for the checker

Vectors and matrices over the rationals, with the operations the checker
needs. All arithmetic is exact: nothing is ever rounded.

This file uses only core Lean, not Mathlib. That keeps it quick to load
and keeps the compiled checker small. Lemmas about these operations,
which will use Mathlib, go in a separate file.

Conventions:
* A vector is a list of rationals.
* A matrix is a list of rows. Shape (out, in) means `out` rows, each of
  length `in`, like the weight of a torch `nn.Linear`, so `matVec W x`
  is `W x`.
* Operations on two vectors stop at the shorter one. Every matrix read
  from a file is checked with `matHasShape` first, so in the checker
  lengths always match.
* Reading an entry outside a vector gives 0.
-/

namespace CompactCheck

/-! ## Types -/

/-- A vector: a list of exact rational numbers. -/
abbrev Vec := List Rat

/-- A matrix: a list of rows, each a `Vec`. -/
abbrev Mat := List Vec

/-! ## Numbers -/

/-- The absolute value of a rational number. -/
def ratAbs (a : Rat) : Rat :=
  if a < 0 then -a else a

/-! ## Vectors -/

/-- Entry `i` of `v`, or 0 if `i` is out of range. -/
def vecGet (v : Vec) (i : Nat) : Rat :=
  v.getD i 0

/-- The zero vector of length `n`. -/
def vecZero (n : Nat) : Vec :=
  List.replicate n 0

/-- The one-hot vector of length `n`: 1 at position `t`, 0 elsewhere. -/
def oneHot (n t : Nat) : Vec :=
  (List.range n).map (fun i => if i = t then 1 else 0)

/-- Entrywise sum. -/
def vecAdd : Vec → Vec → Vec
  | x :: xs, y :: ys => (x + y) :: vecAdd xs ys
  | _, _ => []

/-- Entrywise difference. -/
def vecSub : Vec → Vec → Vec
  | x :: xs, y :: ys => (x - y) :: vecSub xs ys
  | _, _ => []

/-- `c` times every entry. -/
def vecScale (c : Rat) (v : Vec) : Vec :=
  v.map (fun a => c * a)

/-- `c` added to every entry. -/
def vecShift (c : Rat) (v : Vec) : Vec :=
  v.map (fun a => a + c)

/-- Entrywise absolute value. -/
def vecAbs (v : Vec) : Vec :=
  v.map ratAbs

/-- Dot product: multiply entrywise and add up. -/
def vecDot : Vec → Vec → Rat
  | x :: xs, y :: ys => x * y + vecDot xs ys
  | _, _ => 0

/-- Entries `lo` to `hi` of `v`, both included. -/
def vecSlice (v : Vec) (lo hi : Nat) : Vec :=
  (v.drop lo).take (hi + 1 - lo)

/-- The sum of a list of vectors of length `n`. It starts from the zero
    vector of length `n`: since `vecAdd` stops at the shorter input,
    starting from `[]` would give `[]`. -/
def vecSumList (n : Nat) (vs : List Vec) : Vec :=
  vs.foldl vecAdd (vecZero n)

/-- The largest entry, or 0 for the empty vector. -/
def listMax : Vec → Rat
  | [] => 0
  | [x] => x
  | x :: xs => max x (listMax xs)

/-- The smallest entry, or 0 for the empty vector. -/
def listMin : Vec → Rat
  | [] => 0
  | [x] => x
  | x :: xs => min x (listMin xs)

/-! ## Margins and the final test -/

/-- The margin of entry `l` over each entry: `v[l] - v[j]` for every `j`.
    The entry for `j = l` is 0. -/
def marginsAt (v : Vec) (l : Nat) : Vec :=
  let vl := vecGet v l
  v.map (fun a => vl - a)

/-- Every entry except entry `l` is strictly positive. Applied to margins,
    this is the final test of both the single and the interval rule. -/
def allPosExcept (v : Vec) (l : Nat) : Bool :=
  ((List.range v.length).zip v).all fun (j, a) => j == l || 0 < a

/-- Entry `l` exists and is strictly larger than every other entry.
    Ties are never accepted. -/
def strictMaxAt (v : Vec) (l : Nat) : Bool :=
  l < v.length && allPosExcept (marginsAt v l) l

/-- A lower bound on `c · x` over every `x` with `|x - centre| ≤ radius`
    entrywise: `c · centre - |c| · radius`. A corner of the box attains
    it, so no better bound exists. -/
def boxDotLower (c centre radius : Vec) : Rat :=
  vecDot c centre - vecDot (vecAbs c) radius

/-! ## Matrices -/

/-- Row `i` of `W`, or the empty vector if `i` is out of range. -/
def matRow (W : Mat) (i : Nat) : Vec :=
  W.getD i []

/-- Entry `(i, j)` of `W`, or 0 if out of range. -/
def matGet (W : Mat) (i j : Nat) : Rat :=
  vecGet (matRow W i) j

/-- The number of columns, read from the first row. -/
def matNumCols (W : Mat) : Nat :=
  (matRow W 0).length

/-- `W` has `m` rows, each of length `n`. -/
def matHasShape (W : Mat) (m n : Nat) : Bool :=
  W.length == m && W.all (fun row => row.length == n)

/-- Column `t` of `W`. -/
def matCol (W : Mat) (t : Nat) : Vec :=
  W.map (fun row => vecGet row t)

/-- `W x`: each row of `W` dotted with `x`. -/
def matVec (W : Mat) (x : Vec) : Vec :=
  W.map (fun row => vecDot row x)

/-- Entrywise difference of two matrices of the same shape. -/
def matSub : Mat → Mat → Mat
  | r :: rs, s :: ss => vecSub r s :: matSub rs ss
  | _, _ => []

/-- Entrywise absolute value `|W|`. -/
def matAbs (W : Mat) : Mat :=
  W.map vecAbs

/-- The largest absolute value of any entry, or 0 for the empty matrix. -/
def matMaxAbs (W : Mat) : Rat :=
  listMax (W.map (fun row => listMax (vecAbs row)))

/-- The transpose of `W`. The number of columns is read from the first
    row, which is right for every matrix that passed `matHasShape`. -/
def matTranspose (W : Mat) : Mat :=
  (List.range (matNumCols W)).map (fun t => matCol W t)

/-- Matrix product `A B`. Row `i` of `A B` is `Bᵀ` applied to row `i`
    of `A`. -/
def matMul (A B : Mat) : Mat :=
  let Bt := matTranspose B
  A.map (fun row => matVec Bt row)

/-- For each row, the smallest entry among columns `lo` to `hi`. -/
def minOverCols (W : Mat) (lo hi : Nat) : Vec :=
  W.map (fun row => listMin (vecSlice row lo hi))

/-- For each row, the largest entry among columns `lo` to `hi`. -/
def maxOverCols (W : Mat) (lo hi : Nat) : Vec :=
  W.map (fun row => listMax (vecSlice row lo hi))

/-- Row `l` minus every row: the rows `W_l - W_j`, one per `j`. Dotted
    with an input, row `j` gives the margin of output `l` over output `j`. -/
def matRowDiffs (W : Mat) (l : Nat) : Mat :=
  let rowL := matRow W l
  W.map (fun row => vecSub rowL row)

end CompactCheck
