import CompactCheck.Approx
import CompactCheck.Symmetry

/-!
# The checker

`checkProof` first applies the proof's contractions (`Contract.lean`) and
reads its approximations (`Approx.lean`), then walks the proof's split tree
and checks every leaf on the contracted network:

* `single`: the network is evaluated exactly on the leaf's one input, and
  the input is certified if the label's logit is strictly the largest;
* `interval`: every input of the leaf's box is certified at once if the
  interval rule (`Interval.lean`) proves all their margins positive, with
  the approximation the leaf names, if any;
* `skip`: nothing is certified.

The count is the number of inputs in the certified leaves. With the
symmetry rule (`Symmetry.lean`) it is the number of inputs whose sorted
version lies in a certified leaf.

This file uses only core Lean.
-/

namespace CompactCheck

/-- A proof file, as far as this checker reads it. -/
structure ProofFile where
  network : String
  symmetry : Bool
  /-- The contraction chains, by position in the graph, input side first. -/
  contractions : List (List Nat)
  approximations : List ApproxSpec
  tree : SplitTree

/-- The checker's test for one input: the network's output is a logit
    vector of shape `[1, n]` and the label's logit is strictly larger than
    every other logit. Exact, over the rationals. -/
def singleOk (g : Graph) (w : Weights Rat) (task : Task) (x : Input) : Bool :=
  match evalGraph g w x with
  | some out => out.shape == [1, out.data.size] && strictMaxAt out.data.toList (task.label x)
  | none => false

/-- The input of a box that holds exactly one input. -/
def boxInput : Box → Option Input
  | [] => some []
  | r :: rs => if r.lo = r.hi then (boxInput rs).map (r.lo :: ·) else none

/-- The number of inputs in a box: the product of the range lengths. -/
def boxSize (box : Box) : Nat :=
  box.foldr (fun r n => (r.hi + 1 - r.lo) * n) 1

/-- Whether every input of the leaf is certified, or why the whole proof is
    rejected. An interval leaf may name one of the approximations. -/
def leafOk (g : Graph) (w : Weights Rat) (task : Task) (approxs : List Approx) (leaf : Leaf) :
    Except String Bool :=
  match leaf.rule with
  | .skip => .ok false
  | .single =>
    match boxInput leaf.box with
    | some x => .ok (singleOk g w task x)
    | none => .error "a single leaf must hold exactly one input"
  | .interval none => intervalLeaf g w task leaf.box none
  | .interval (some name) =>
    match approxs.find? (·.name == name) with
    | some a => intervalLeaf g w task leaf.box (some a)
    | none => .error s!"unknown approximation {name}"
  | .tokenInterval =>
    -- as Python: a leaf whose label is not constant is not certified; any
    -- other is refused, since interval leaves already keep each token's row
    match task.constantLabel leaf.box with
    | none => .ok false
    | some _ => .error ("the token_interval rule is for networks beyond linear maps; here interval " ++
        "leaves already use each token's exact row once the maps are contracted")

/-- The number of inputs in the certified leaves. -/
def checkLeaves (g : Graph) (w : Weights Rat) (task : Task) (approxs : List Approx) :
    List Leaf → Except String Nat
  | [] => .ok 0
  | leaf :: rest =>
    match checkLeaves g w task approxs rest with
    | .error e => .error e
    | .ok n =>
      match leafOk g w task approxs leaf with
      | .error e => .error e
      | .ok ok => .ok (if ok then n + boxSize leaf.box else n)

/-- The boxes of the certified leaves. -/
def certifiedBoxes (g : Graph) (w : Weights Rat) (task : Task) (approxs : List Approx) :
    List Leaf → Except String (List Box)
  | [] => .ok []
  | leaf :: rest =>
    match certifiedBoxes g w task approxs rest with
    | .error e => .error e
    | .ok boxes =>
      match leafOk g w task approxs leaf with
      | .error e => .error e
      | .ok ok => .ok (if ok then leaf.box :: boxes else boxes)

/-- Check a proof: the number of inputs it certifies, or why it is
    rejected. -/
def checkProof (g : Graph) (w : Weights Rat) (task : Task) (proof : ProofFile) :
    Except String Nat :=
  if proof.symmetry && !symmetricNet g then
    .error "symmetry does not hold: the input is not used only through a sum over the positions"
  else if proof.symmetry && !task.labelSymmetric then
    .error "symmetry does not hold: the task does not declare that reordering keeps the label"
  else if task.space.any (· == 0) then .error "the input space has a position with no tokens"
  else
    match contractAll g w proof.contractions with
    | .error e => .error e
    | .ok (g', w') =>
      match buildApproxs g' w' proof.approximations with
      | .error e => .error e
      | .ok approxs =>
        match walk proof.tree (rootBox task.space) with
        | .error e => .error e
        | .ok leaves =>
          if proof.symmetry then
            match certifiedBoxes g' w' task approxs leaves with
            | .ok boxes => .ok (sortedCount task.space boxes)
            | .error e => .error e
          else checkLeaves g' w' task approxs leaves

end CompactCheck
