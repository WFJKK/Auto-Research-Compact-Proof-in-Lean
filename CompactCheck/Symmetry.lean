import CompactCheck.Contract

/-!
# The symmetry rule

With `"symmetry": true`, an accepted leaf certifies the inputs in it whose
tokens are in non-decreasing order, together with all their reorderings
(`sorted_orbit_count` in `core/check/proof.py`). The rule holds when

* the network reads its input only through a sum over the positions, so it
  computes the same output for every reordering of an input
  (`symmetricNet`), and
* reordering the tokens never changes the label (`Task.labelSymmetric`,
  proved for each task).

Then an input is answered correctly exactly when its sorted version is. The
checker counts the inputs whose sorted version lies in a certified leaf
(`sortedCount`). The leaves do not overlap, so this is the Python checker's
count: each sorted input in a certified leaf, times its number of distinct
reorderings.

This file uses only core Lean.
-/

namespace CompactCheck

/-- Whether an operation is the input. -/
def Op.isInput : Op → Bool
  | .input => true
  | _ => false

/-- The positions of the graph's input operations. -/
def inputNodes (nodes : List Op) : List Nat :=
  (List.range nodes.length).filter fun k => nodes[k]?.any Op.isInput

/-- The symmetry rule's test on the network: it has one input, which is not
    its output, and only a sum over the positions reads it
    (`summed_over_positions_first` in `core/check/trace.py`). -/
def symmetricNet (g : Graph) : Bool :=
  match inputNodes g.nodes with
  | [i] =>
    g.output != i &&
      match readers g.nodes [] i with
      | [s] =>
        match g.nodes[s]? with
        | some (.sum _ d) => normDim d 3 == some 1
        | _ => false
      | _ => false
  | _ => false

/-- The tokens of `x` in non-decreasing order. -/
def sortTokens (x : Input) : Input :=
  x.mergeSort

/-- The number of inputs whose sorted version lies in one of the boxes. -/
def sortedCount (space : List Nat) (boxes : List Box) : Nat :=
  (allInputs space).countP fun x => boxes.any fun b => inBox b (sortTokens x)

end CompactCheck
