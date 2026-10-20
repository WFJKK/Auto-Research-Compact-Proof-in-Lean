import CompactCheck.Interval

/-!
# The approximate rule: reading an approximation

A proof file may give a simpler matrix `P` for a linear map with weight `W`
(usually a contraction), in one of three forms (`core/check/approx.py`):

* `dense`: `P` written out;
* `low_rank`: `P = F G`, with `F` of shape `[out, r]` and `G` of shape
  `[r, in]`, where `0 < r ≤ min(out, in)`;
* `row_segments`: each row of `P` is constant on consecutive column ranges,
  given as `[start, end, value]` triples covering every column in order.

The checker computes the largest error `eps = max |W - P|` exactly
(`approxError`), and interval leaves that name the approximation use it
(`approxMargins` in `Interval.lean`).

Here the approximation is checked against the shape of `W`, as the Python
checker does, so that the two checkers reject the same proofs. Soundness
does not depend on these checks: whatever `P` is, `eps` bounds `|W - P|`.

A `row_segments` approximation becomes the dense matrix it describes. Its
error is the Python checker's (for each segment, the larger of `|max - v|`
and `|min - v|` over its entries of `W`), and so are its bounds: merging the
segments of two rows gives the smallest difference over the tokens, exactly
as the dense form computes it.

This file uses only core Lean.
-/

namespace CompactCheck

/-- An approximation's matrix as a proof file writes it. -/
inductive RawForm where
  | dense (values : List (List Rat))
  | lowRank (left right : List (List Rat))
  | rowSegments (rows : List (List (Int × Int × Rat)))
deriving Repr

/-- An approximation from a proof file: its name, the position of the linear
    map it approximates (after the contractions), and its matrix. -/
structure ApproxSpec where
  name : String
  of : Nat
  form : RawForm
deriving Repr

/-- A matrix from its rows: `nRows` rows, all of the same length (`nCols`
    if given). -/
def matrixOf (what : String) (rows : List (List Rat)) (nRows : Nat) (nCols : Option Nat) :
    Except String (Tensor Rat) :=
  match rows with
  | [] => .error s!"{what} must be a list of rows"
  | r0 :: _ =>
    if rows.length != nRows then .error s!"{what} needs {nRows} rows"
    else if nCols.any (· != r0.length) then .error s!"{what} needs {nCols.getD 0} columns"
    else if rows.any (·.length != r0.length) then .error s!"{what} rows differ in length"
    else .ok ⟨[nRows, r0.length], rows.flatten.toArray⟩

/-- One row of a `row_segments` approximation with `n` columns, from column
    `expect` on: the segments must cover the columns in order. -/
def segmentRow (i n : Nat) : List (Int × Int × Rat) → Nat → Except String (List Rat)
  | [], expect =>
    if expect == n then .ok [] else .error s!"row {i}: segments must reach the last column"
  | (a, b, v) :: rest, expect =>
    if a != (expect : Int) || b < a || b ≥ (n : Int) then
      .error s!"row {i}: segments must cover the columns in order"
    else
      (segmentRow i n rest (b.toNat + 1)).map (List.replicate (b.toNat + 1 - expect) v ++ ·)

/-- The matrix a `row_segments` approximation describes, with `out` rows and
    `inn` columns. -/
def segmentsMatrix (rows : List (List (Int × Int × Rat))) (out inn : Nat) :
    Except String (Tensor Rat) := do
  unless rows.length == out do
    throw s!"rows needs one list of segments per output ({out})"
  let mut data : Array Rat := #[]
  let mut i := 0
  for segs in rows do
    if segs.isEmpty then throw s!"row {i} has no segments"
    data := data ++ (← segmentRow i inn segs 0).toArray
    i := i + 1
  return ⟨[out, inn], data⟩

/-- The approximation's matrix, checked against the weight `W` it
    approximates. -/
def approxForm (W : Tensor Rat) : RawForm → Except String ApproxForm
  | .dense values =>
    .dense <$> matrixOf "values" values (W.shape.getD 0 0) (some (W.shape.getD 1 0))
  | .lowRank left right => do
    let out := W.shape.getD 0 0
    let inn := W.shape.getD 1 0
    let F ← matrixOf "left" left out none
    let r := F.shape.getD 1 0
    unless 0 < r && r ≤ min out inn do
      throw s!"low_rank inner dimension must be between 1 and {min out inn}, not {r}"
    let G ← matrixOf "right" right r (some inn)
    return .lowRank F G
  | .rowSegments rows => .dense <$> segmentsMatrix rows (W.shape.getD 0 0) (W.shape.getD 1 0)

/-- An approximation of a linear map of the graph, with its error. -/
def buildApprox (g : Graph) (w : Weights Rat) (s : ApproxSpec) : Except String Approx :=
  match g.nodes[s.of]? with
  | some (.linear _ wn _) =>
    match List.lookup wn w with
    | some W =>
      match approxForm W s.form with
      | .ok form => .ok { name := s.name, of := s.of, W, form, eps := approxError W form }
      | .error e => .error s!"approximation {s.name}: {e}"
    | none => .error s!"the weight {wn} is missing"
  | _ => .error s!"approximation {s.name} is not of a linear map"

/-- All the approximations of a proof file; their names must differ. -/
def buildApproxs (g : Graph) (w : Weights Rat) : List ApproxSpec → Except String (List Approx)
  | [] => .ok []
  | s :: rest =>
    match buildApprox g w s, buildApproxs g w rest with
    | .ok a, .ok as =>
      if as.any (·.name == a.name) then .error s!"approximation {a.name} is defined twice"
      else .ok (a :: as)
    | .error e, _ => .error e
    | _, .error e => .error e

end CompactCheck
