import CompactCheck.Json

/-!
# Tests for the symmetry rule

Small cases worked out by hand. The rule is also compared with the Python
checker on every network in the zoo (see `scripts/`). The build fails if any
`#guard` is false.
-/

namespace SymmetryTest

open CompactCheck

/-- A tensor of rationals, for writing tests. -/
def T (shape : List Nat) (data : List Rat) : Tensor Rat := ⟨shape, data.toArray⟩

/-! ## Which networks the rule accepts -/

/-- The max network of `IntervalTest.lean`: the input, its sum over the
    positions, one linear map. -/
def g : Graph := ⟨2, 3, [.input, .sum 0 1, .linear 1 "M" none], 2⟩

def M : Tensor Rat := T [3, 3] [3, -3, -3,  1, 3, -3,  1, 1, 3]
def w : Weights Rat := [("M", M)]

#guard inputNodes g.nodes == [0]
#guard symmetricNet g
-- The positions dimension counted from the end.
#guard symmetricNet ⟨2, 3, [.input, .sum 0 (-2), .linear 1 "M" none], 2⟩
-- A sum over the tokens, a linear map per position, the input read twice, the input
-- added to itself, the input as the output, two inputs.
#guard !symmetricNet ⟨2, 3, [.input, .sum 0 2, .linear 1 "M" none], 2⟩
#guard !symmetricNet ⟨2, 3, [.input, .linear 0 "M" none, .sum 1 1], 2⟩
#guard !symmetricNet ⟨2, 3, [.input, .sum 0 1, .sum 0 1, .add 1 2, .linear 3 "M" none], 4⟩
#guard !symmetricNet ⟨2, 3, [.input, .add 0 0, .sum 1 1, .linear 2 "M" none], 3⟩
#guard !symmetricNet ⟨2, 3, [.input, .sum 0 1], 0⟩
#guard !symmetricNet ⟨2, 3, [.input, .input, .sum 0 1, .linear 2 "M" none], 3⟩

/-! ## Counting -/

#guard sortTokens [2, 0, 1, 0] == [0, 0, 1, 2]
-- The box {0} × {0, 1, 2} holds the sorted inputs (0, 0), (0, 1) and (0, 2);
-- with their reorderings, 5 inputs.
#guard sortedCount [3, 3] [[⟨0, 0⟩, ⟨0, 2⟩]] == 5
-- The box {1, 2} × {0} holds no sorted input.
#guard sortedCount [3, 3] [[⟨1, 2⟩, ⟨0, 0⟩]] == 0
-- Three positions: the sorted inputs of {0} × {1} × {1, 2} are (0, 1, 1)
-- and (0, 1, 2), with 3 and 6 reorderings.
#guard sortedCount [3, 3, 3] [[⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 2⟩]] == 9

/-! ## Proofs -/

def task : Task := maxTask 2 3

/-- Single leaves for the sorted inputs, skip for the others. -/
def sortedSingles : SplitTree :=
  .split 0 [1, 2] ((List.range 3).map fun a =>
    .split 1 [1, 2] ((List.range 3).map fun b => .leaf (if a ≤ b then .single else .skip)))

def proof (symmetry : Bool) (tree : SplitTree) : ProofFile := ⟨"g", symmetry, [], [], tree⟩

-- Without symmetry the six single leaves certify six inputs; with it, all nine.
#guard (checkProof g w task (proof false sortedSingles)).toOption == some 6
#guard (checkProof g w task (proof true sortedSingles)).toOption == some 9
-- A leaf of unsorted inputs counts nothing under symmetry. Certified single
-- leaves (0, 0) and (1, 0): the sorted version (0, 1) of (1, 0) is not in a
-- certified leaf.
def twoSingles : SplitTree :=
  .split 0 [1, 2] [.split 1 [1] [.leaf .single, .leaf .skip],
    .split 1 [1] [.leaf .single, .leaf .skip], .leaf .skip]
#guard (checkProof g w task (proof false twoSingles)).toOption == some 2
#guard (checkProof g w task (proof true twoSingles)).toOption == some 1
-- Interval leaves {a} × {a, ..., 2}: label not constant except for a = 2.
#guard (checkProof g w task (proof true (.split 0 [1, 2]
    [.leaf (.interval none), .split 1 [1] [.leaf .skip, .leaf (.interval none)],
     .split 1 [2] [.leaf .skip, .leaf (.interval none)]]))).toOption == some 1

-- The rule is refused for a network that reads its input per position, and
-- for a task whose label depends on the order.
def gPer : Graph := ⟨2, 3, [.input, .sum 0 1, .linear 0 "M" none], 2⟩
#guard (checkProof gPer w task (proof true sortedSingles)).toBool == false

def firstToken : Task :=
  { maxTask 2 3 with
    name := "first"
    label := fun x => x.headD 0
    constantLabel := fun _ => none
    constantLabel_spec := by intro _ _ _ h; cases h
    labelSymmetric := false
    labelSymmetric_spec := by intro h; cases h }
#guard (checkProof g w firstToken (proof true sortedSingles)).toBool == false
#guard (checkProof g w firstToken (proof false sortedSingles)).toBool == true

/-! ## Reading -/

open Lean (Json) in
def gJson : Json := Json.mkObj [("schema", .str "split-tree-v1"), ("network", .str "g"),
  ("symmetry", .bool true), ("tree", Json.mkObj [("leaf", .str "skip")])]

#guard (parseProof gJson ["x", "sum_1", "M"]).toOption.map (·.symmetry) == some true

/-! ## Whole proof files -/

def net : NetworkFile :=
  { network := "g", graph := g, names := ["x", "sum_1", "M"], weights := w, task }

#guard countScalars gJson == 4
#guard (checkProofFile net gJson).toOption == some 0
-- Another network's proof.
#guard (checkProofFile { net with network := "h" } gJson).toBool == false
-- Too many numbers and strings: more than 50 * 9 + 10^6, here 3 and the
-- numbers in the notes.
open Lean (Json) in
def withNotes (k : Nat) : Json := Json.mkObj [("schema", .str "split-tree-v1"),
  ("network", .str "g"), ("notes", .arr (Array.replicate k (.num 1))),
  ("tree", Json.mkObj [("leaf", .str "skip")])]
#guard (checkProofFile net (withNotes 1000447)).toOption == some 0
#guard (checkProofFile net (withNotes 1000448)).toBool == false

end SymmetryTest
