import CompactCheck.Eval

/-!
# The contract rule

Written against `docs/RULES.md`, section "contract": consecutive linear maps
`x ↦ W_k (⋯ (W_1 x + b_1) ⋯) + b_k` compute the same function as one map,
with weight `W_k ⋯ W_1` and bias `W_k ⋯ W_2 b_1 + ⋯ + b_k`, computed
exactly. The chain must be consecutive (each map reads the one before it),
and every map but the last must feed only the next one, as in
`Program.contract` in `core/check/evaluate.py`.

The checker replaces the chain's last map by the product. The other maps of
the chain stay in the graph, unused, so that every operation keeps its
position, and the network computes exactly what it did before. Later
contractions do not count them as readers (`removed`), since the Python
checker deletes them.

This file uses only core Lean.
-/

namespace CompactCheck

/-- The product `A B` of weights `A : [m, k]` and `B : [k, n]`. -/
def Tensor.matMul (A B : Tensor Rat) : Option (Tensor Rat) :=
  let m := A.shape.getD 0 0
  let k := A.shape.getD 1 0
  let n := B.shape.getD 1 0
  if A.shape == [m, k] && B.shape == [k, n] && A.data.size == m * k && B.data.size == k * n then
    some ⟨[m, n], (Array.range (m * n)).map fun j =>
      ((List.range k).map fun i => A.get (j / n * k + i) * B.get (i * n + j % n)).sum⟩
  else none

/-- The product `A v` of a weight `A : [m, k]` and a vector `v : [k]`. -/
def Tensor.matVec (A v : Tensor Rat) : Option (Tensor Rat) :=
  let m := A.shape.getD 0 0
  let k := A.shape.getD 1 0
  if A.shape == [m, k] && v.shape == [k] && A.data.size == m * k && v.data.size == k then
    some ⟨[m], (Array.range m).map fun o =>
      ((List.range k).map fun i => A.get (o * k + i) * v.get i).sum⟩
  else none

/-- The map `x ↦ W2 (W1 x + b1) + b2` as one map: weight `W2 W1`, bias
    `W2 b1 + b2`. -/
def composeLinear (W1 : Tensor Rat) (b1 : Option (Tensor Rat)) (W2 : Tensor Rat)
    (b2 : Option (Tensor Rat)) : Option (Tensor Rat × Option (Tensor Rat)) :=
  match W2.matMul W1 with
  | none => none
  | some M =>
    match b1 with
    | none => some (M, b2)
    | some b1 =>
      match W2.matVec b1, b2 with
      | some c, none => some (M, some c)
      | some c, some b2 => (addOp c b2).map fun d => (M, some d)
      | none, _ => none

/-- The operations an operation reads. -/
def Op.args : Op → List Nat
  | .input => []
  | .linear a _ _ => [a]
  | .sum a _ => [a]
  | .add a b => [a, b]
  | .param _ => []
  | .binary _ a b => [a, b]
  | .neg a => [a]
  | .matmul a b => [a, b]
  | .index a _ => [a]
  | .transpose a => [a]
  | .unsqueeze a _ => [a]
  | .expand a _ => [a]
  | .cat args _ => args
  | .stack args _ => args
  | .exp a => [a]
  | .softmax a _ => [a]
  | .zerosLike a => [a]

/-- The operations reading operation `i`, except removed ones. -/
def readers (nodes : List Op) (removed : List Nat) (i : Nat) : List Nat :=
  (List.range nodes.length).filter fun k =>
    !removed.contains k && nodes[k]?.any fun op => op.args.contains i

/-- Whether some operation of the graph uses the weight name `n`. -/
def usesName (nodes : List Op) (n : String) : Bool :=
  nodes.any fun
    | .linear _ wn bn => wn == n || bn == some n
    | .param wn => wn == n
    | _ => false

/-- The bias of a linear map: `some none` if it has none, `some (some b)`
    if its bias is `b`, and `none` if the bias is missing from the weights. -/
def lookupBias (w : Weights Rat) : Option String → Option (Option (Tensor Rat))
  | none => some none
  | some n => (List.lookup n w).map some

/-- Follow a chain from its second map on, composing. `(M, bM)` is the
    composition of the maps so far, the last of which is operation `prev`.
    Returns the composition of the whole chain and the position of its last
    map. -/
def composeChain (g : Graph) (w : Weights Rat) (removed : List Nat) :
    Nat → Tensor Rat → Option (Tensor Rat) → List Nat →
      Except String (Tensor Rat × Option (Tensor Rat) × Nat)
  | prev, M, bM, [] => .ok (M, bM, prev)
  | prev, M, bM, i :: rest =>
    match g.nodes[i]? with
    | some (.linear a wn bn) =>
      if a == prev && prev < i && !removed.contains i && readers g.nodes removed prev == [i] &&
          g.output != prev then
        match List.lookup wn w, lookupBias w bn with
        | some W, some b =>
          match composeLinear M bM W b with
          | some (M', bM') => composeChain g w removed i M' bM' rest
          | none => .error "the shapes in a contraction chain do not fit"
        | _, _ => .error "the weights of a linear map are missing"
      else .error "only consecutive maps that feed only the next one contract"
    | _ => .error "a contraction chain lists linear maps of the network"

/-- One contraction, with the chain's maps given by position, input side
    first. Returns the graph with the chain's last map replaced by the
    product, the weights with the product added (named `#contract<step>`,
    a name no operation uses), and the positions no longer in use. -/
def contractOne (g : Graph) (w : Weights Rat) (removed : List Nat) (step : Nat) :
    List Nat → Except String (Graph × Weights Rat × List Nat)
  | [] | [_] => .error "a contraction chain lists at least two linear maps"
  | i :: rest =>
    match g.nodes[i]? with
    | some (.linear a wn bn) =>
      if removed.contains i then .error "a contraction chain lists linear maps of the network"
      else
        match List.lookup wn w, lookupBias w bn with
        | some W, some b => finish i rest a W b
        | _, _ => .error "the weights of a linear map are missing"
    | _ => .error "a contraction chain lists linear maps of the network"
where
  /-- Compose the chain `i :: rest`, whose first map reads `a` and has weight
      `W` and bias `b`, and put the product in place of its last map. -/
  finish (i : Nat) (rest : List Nat) (a : Nat) (W : Tensor Rat) (b : Option (Tensor Rat)) :
      Except String (Graph × Weights Rat × List Nat) :=
    let nameW := s!"#contract{step}.weight"
    let nameB := s!"#contract{step}.bias"
    if nameW == nameB || usesName g.nodes nameW || usesName g.nodes nameB then
      .error "the name of a contracted weight is taken"
    else
      match composeChain g w removed i W b rest with
      | .error e => .error e
      | .ok (M, bM, last) =>
        let op := Op.linear a nameW (bM.map fun _ => nameB)
        let w' := match bM with
          | some bv => (nameW, M) :: (nameB, bv) :: w
          | none => (nameW, M) :: w
        .ok ({ g with nodes := g.nodes.set last op }, w', removed ++ (i :: rest).dropLast)

/-- All contractions of a proof, in order. -/
def contractAll (g : Graph) (w : Weights Rat) (chains : List (List Nat)) :
    Except String (Graph × Weights Rat) :=
  go g w [] 0 chains
where
  go (g : Graph) (w : Weights Rat) (removed : List Nat) (step : Nat) :
      List (List Nat) → Except String (Graph × Weights Rat)
    | [] => .ok (g, w)
    | c :: cs =>
      match contractOne g w removed step c with
      | .ok (g', w', removed') => go g' w' removed' (step + 1) cs
      | .error e => .error e

end CompactCheck
