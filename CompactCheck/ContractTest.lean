import CompactCheck.Json

/-!
# Tests for the contract rule

Small cases worked out by hand. The rule is also compared with the Python
checker on every network in the zoo (see `scripts/`). The build fails if any
`#guard` is false.
-/

namespace ContractTest

open CompactCheck

/-- A tensor of rationals, for writing tests. -/
def T (shape : List Nat) (data : List Rat) : Tensor Rat := ⟨shape, data.toArray⟩

/-! ## Products -/

-- [[1, 2], [3, 4]] times [[5, 6, 7], [8, 9, 10]].
#guard (T [2, 2] [1, 2,  3, 4]).matMul (T [2, 3] [5, 6, 7,  8, 9, 10]) ==
  some (T [2, 3] [21, 24, 27,  47, 54, 61])
-- Shapes that do not fit.
#guard (T [2, 2] [1, 2,  3, 4]).matMul (T [3, 2] [1, 2,  3, 4,  5, 6]) == none
#guard (T [2, 2] [1, 2,  3, 4]).matVec (T [2] [1, 1]) == some (T [2] [3, 7])

/-! ## Composing maps

The small max2-shaped network of `EvalTest.lean`: E, then L with bias b,
then U. Composing E and L gives weight L E and bias b; composing that with U
gives U L E and bias U b. -/

def E : Tensor Rat := T [2, 3] [1, 0, 2,  0, 1, 1]
def L : Tensor Rat := T [2, 2] [1, 1,  0, 1]
def b : Tensor Rat := T [2] [0, 1/2]
def U : Tensor Rat := T [3, 2] [1, 0,  0, 1,  1, -1]

#guard composeLinear E none L (some b) == some (T [2, 3] [1, 1, 3,  0, 1, 1], some b)
#guard composeLinear (T [2, 3] [1, 1, 3,  0, 1, 1]) (some b) U none ==
  some (T [3, 3] [1, 1, 3,  0, 1, 1,  1, 0, 2], some (T [3] [0, 1/2, -1/2]))

def g : Graph where
  positions := 2
  values := 3
  nodes := [.input, .sum 0 1, .linear 1 "E" none, .linear 2 "L" (some "b"), .linear 3 "U" none]
  output := 4

def w : Weights Rat := [("E", E), ("L", L), ("b", b), ("U", U)]

/-- The network's output on every input, after the contractions. -/
def outputs (chains : List (List Nat)) : Option (List (Option (Tensor Rat))) :=
  match contractAll g w chains with
  | .ok (g', w') => some ((allInputs [3, 3]).map (evalGraph g' w'))
  | .error _ => none

-- The whole chain: one map, U L E with bias U b. On [2, 0] the summed
-- one-hot input is [1, 0, 1], so the output is [4, 3/2, 5/2] as before.
#guard (match contractAll g w [[2, 3, 4]] with
  | .ok (g', w') => g'.nodes[4]? == some (.linear 1 "#contract0.weight" (some "#contract0.bias")) &&
      evalGraph g' w' [2, 0] == some (T [1, 3] [4, 3/2, 5/2])
  | .error _ => false)
-- The contracted network computes what the network computes, on every input:
-- in one step, in two steps, or for part of the chain.
#guard outputs [[2, 3, 4]] == outputs []
#guard outputs [[2, 3], [3, 4]] == outputs []
#guard outputs [[3, 4]] == outputs []

-- Chains the rule refuses: one map, not consecutive, in the wrong order, a
-- sum in the chain, and a map already contracted away.
#guard outputs [[2]] == none
#guard outputs [[2, 4]] == none
#guard outputs [[3, 2]] == none
#guard outputs [[1, 2]] == none
#guard outputs [[2, 3], [2, 3]] == none

-- A map that feeds two others does not contract with the next one, though it
-- can end a chain.
def g2 : Graph := { g with nodes := g.nodes ++ [.add 3 3], output := 5 }
#guard (contractAll g2 w [[3, 4]]).toBool == false
#guard (contractAll g2 w [[2, 3]]).toBool == true
-- Nor does the network's output.
#guard (contractAll { g with output := 3 } w [[3, 4]]).toBool == false

/-! ## Names in proof files

A proof names the maps as the Python checker's graph does; after a
contraction, its last map has the contraction's name and the others have
none. -/

def names : List String := ["a", "sum_1", "embedding", "linear", "unembedding"]

#guard (resolveContractions names [("M", ["embedding", "linear", "unembedding"])]).toOption ==
  some ([[2, 3, 4]], #[some "a", some "sum_1", none, none, some "M"])
#guard ((resolveContractions names [("EL", ["embedding", "linear"]),
    ("M", ["EL", "unembedding"])]).toOption.map (·.1)) == some [[2, 3], [3, 4]]
-- A map contracted away has no name any more, and names are not reused.
#guard (resolveContractions names [("EL", ["embedding", "linear"]),
    ("M", ["linear", "unembedding"])]).toBool == false
#guard (resolveContractions names [("linear", ["embedding", "linear"])]).toBool == false
#guard (resolveContractions names [("", ["embedding", "linear"])]).toBool == false

end ContractTest
