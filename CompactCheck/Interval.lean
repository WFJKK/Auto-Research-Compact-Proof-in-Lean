import CompactCheck.Eval
import CompactCheck.LinAlg

/-!
# The interval rule

An interval leaf certifies every input of its box at once, without
evaluating any of them. Written against `docs/RULES.md`, section
"interval", with the same bounds as `run_interval` in
`core/check/evaluate.py`, so that the two checkers certify the same leaves.

The evaluation follows the network once, keeping for every value what is
known about it for all inputs of the box together (`IVal`):

* The one-hot input stays symbolic until the first linear map: at position
  `p` the token is one of `box[p].lo, ..., box[p].hi`. A linear map then
  picks column `x_p` of its weight, which lies between the smallest and the
  largest of the allowed columns.
* Every later value is known by bounds `lo ≤ value ≤ hi`, entry by entry.
  Linear maps, sums and additions act on bounds by interval arithmetic,
  exactly, over the rationals.
* If the output is a linear map, the margins `logit[l] - logit[j]` are
  bounded directly from the rows `W[l] - W[j]`. This is tighter than
  bounding each logit on its own, since the two logits move together.

The leaf is certified if every margin's lower bound is positive. The task
must first confirm that every input in the box has the same label `l`.

An interval leaf may name an approximation `P` of the output map's weight
`W` (the approximate rule). On the summed one-hot input, a position whose
token ranges over more than one value then contributes a lower bound on
`P[l, t] - P[j, t]` over its tokens, minus twice the largest error
`|W - P|`, instead of the exact smallest difference.

A value the rule cannot follow (adding the one-hot input to something, a
sum over a dimension other than the positions, a shape that does not fit)
makes the whole proof rejected, as in the Python checker.

This file uses only core Lean.
-/

namespace CompactCheck

/-- The smallest of `f lo, f (lo + 1), ..., f hi` (just `f lo` if
    `hi ≤ lo`). -/
def rangeMin (f : Nat → Rat) (lo hi : Nat) : Rat :=
  (List.range (hi - lo)).foldl (fun m k => min m (f (lo + 1 + k))) (f lo)

/-- The largest of `f lo, f (lo + 1), ..., f hi`. -/
def rangeMax (f : Nat → Rat) (lo hi : Nat) : Rat :=
  (List.range (hi - lo)).foldl (fun m k => max m (f (lo + 1 + k))) (f lo)

/-- Entry `o` of an optional bias, 0 if there is none. -/
def biasAt (b : Option (Tensor Rat)) (o : Nat) : Rat :=
  match b with
  | some b => b.get o
  | none => 0

/-- What the interval rule knows about one value of the network, for every
    input of the box at once. -/
inductive IVal where
  /-- The one-hot input (shape `[1, positions, values]`), or with
      `summed = true` its sum over the positions (shape `[1, values]`). -/
  | oneHot (summed : Bool)
  /-- Every entry lies between the entries of `lo` and `hi`, which have the
      value's shape. -/
  | bounds (lo hi : Tensor Rat)
deriving Repr, BEq

/-- One node in interval mode: what is known about its value, and for a
    linear map also what is known about its argument, and the map itself,
    for the margins at the output. -/
structure INode where
  val : IVal
  lin : Option (IVal × Tensor Rat × Option (Tensor Rat))
deriving Repr, BEq

/-- A linear map on the one-hot input. At position `p` the result is column
    `x_p` of `W` (plus the bias), which lies between the smallest and the
    largest of the columns `box[p].lo` to `box[p].hi`. Summed over the
    positions, the bounds add up. -/
def ilinearOneHot (box : Box) (P V : Nat) (summed : Bool) (W : Tensor Rat)
    (b : Option (Tensor Rat)) : Option IVal :=
  let out := W.shape.getD 0 0
  let biasOk := match b with
    | some b => b.shape == [out] && b.data.size == out
    | none => true
  if W.shape == [out, V] && W.data.size == out * V && biasOk then
    let colMin (o : Nat) (r : Range) := rangeMin (fun t => W.get (o * V + t)) r.lo r.hi
    let colMax (o : Nat) (r : Range) := rangeMax (fun t => W.get (o * V + t)) r.lo r.hi
    if summed then
      some (.bounds
        ⟨[1, out], (Array.range out).map fun o => (box.map (colMin o)).sum + biasAt b o⟩
        ⟨[1, out], (Array.range out).map fun o => (box.map (colMax o)).sum + biasAt b o⟩)
    else
      some (.bounds
        ⟨[1, P, out], (Array.range (P * out)).map fun j =>
          colMin (j % out) (box.getD (j / out) ⟨0, 0⟩) + biasAt b (j % out)⟩
        ⟨[1, P, out], (Array.range (P * out)).map fun j =>
          colMax (j % out) (box.getD (j / out) ⟨0, 0⟩) + biasAt b (j % out)⟩)
  else none

/-- A linear map on bounds, by interval arithmetic: each product
    `W[o, i] * v_i` lies between `W[o, i] * lo_i` and `W[o, i] * hi_i`. The
    shape checks are those of `linearOp`. -/
def ilinearBounds (W : Tensor Rat) (b : Option (Tensor Rat)) (lo hi : Tensor Rat) :
    Option IVal :=
  let out := W.shape.getD 0 0
  let inn := W.shape.getD 1 0
  let pre := shapeSize lo.shape.dropLast
  let biasOk := match b with
    | some b => b.shape == [out] && b.data.size == out
    | none => true
  if W.shape == [out, inn] && lo.shape.getLast? == some inn && W.data.size == out * inn &&
      lo.data.size == pre * inn && biasOk && hi.shape == lo.shape &&
      hi.data.size == lo.data.size then
    some (.bounds
      ⟨lo.shape.dropLast ++ [out], (Array.range (pre * out)).map fun j =>
        ((List.range inn).map fun i =>
          min (W.get (j % out * inn + i) * lo.get (j / out * inn + i))
            (W.get (j % out * inn + i) * hi.get (j / out * inn + i))).sum +
          biasAt b (j % out)⟩
      ⟨lo.shape.dropLast ++ [out], (Array.range (pre * out)).map fun j =>
        ((List.range inn).map fun i =>
          max (W.get (j % out * inn + i) * lo.get (j / out * inn + i))
            (W.get (j % out * inn + i) * hi.get (j / out * inn + i))).sum +
          biasAt b (j % out)⟩)
  else none

/-- A linear map in interval mode. -/
def ilinear (box : Box) (P V : Nat) (W : Tensor Rat) (b : Option (Tensor Rat)) :
    IVal → Option IVal
  | .oneHot summed => ilinearOneHot box P V summed W b
  | .bounds lo hi => ilinearBounds W b lo hi

/-- A sum over one dimension in interval mode. The one-hot input may only be
    summed over the positions (dimension 1 of `[1, positions, values]`). -/
def isum (dim : Int) : IVal → Option IVal
  | .oneHot false => if normDim dim 3 == some 1 then some (.oneHot true) else none
  | .oneHot true => none
  | .bounds lo hi =>
    match sumOp dim lo, sumOp dim hi with
    | some lo', some hi' => some (.bounds lo' hi')
    | _, _ => none

/-- An addition in interval mode: the bounds add. -/
def iadd : IVal → IVal → Option IVal
  | .bounds lo1 hi1, .bounds lo2 hi2 =>
    match addOp lo1 lo2, addOp hi1 hi2 with
    | some lo, some hi => some (.bounds lo hi)
    | _, _ => none
  | _, _ => none

/-- One operation in interval mode, given the nodes before it. -/
def ievalOp (g : Graph) (w : Weights Rat) (box : Box) (nodes : Array INode) :
    Op → Option INode
  | .input =>
    if box.length == g.positions && box.all (fun r => r.hi < g.values) then
      some ⟨.oneHot false, none⟩
    else none
  | .linear a wn bn =>
    match nodes[a]?, List.lookup wn w with
    | some n, some W =>
      match bn with
      | none => (ilinear box g.positions g.values W none n.val).map fun v => ⟨v, some (n.val, W, none)⟩
      | some bn =>
        match List.lookup bn w with
        | some b =>
          (ilinear box g.positions g.values W (some b) n.val).map fun v =>
            ⟨v, some (n.val, W, some b)⟩
        | none => none
    | _, _ => none
  | .sum a d =>
    match nodes[a]? with
    | some n => (isum d n.val).map fun v => ⟨v, none⟩
    | none => none
  | .add a b =>
    match nodes[a]?, nodes[b]? with
    | some na, some nb => (iadd na.val nb.val).map fun v => ⟨v, none⟩
    | _, _ => none
  | _ => none

/-- All operations in interval mode, in order. -/
def ievalOps (g : Graph) (w : Weights Rat) (box : Box) :
    List Op → Array INode → Option (Array INode)
  | [], nodes => some nodes
  | op :: ops, nodes =>
    match ievalOp g w box nodes op with
    | some n => ievalOps g w box ops (nodes.push n)
    | none => none

/-! ## Approximations -/

/-- The matrix `P` of an approximation (`core/check/approx.py`). -/
inductive ApproxForm where
  /-- `P` written out, with `W`'s shape. A `row_segments` approximation is
      read as the matrix it describes. -/
  | dense (P : Tensor Rat)
  /-- `P = F G`, with `F` of shape `[out, r]` and `G` of shape `[r, in]`. -/
  | lowRank (F G : Tensor Rat)
deriving Repr, BEq

namespace ApproxForm

/-- Entry `(o, t)` of `P`, for `P` with `inn` columns. -/
def entry (inn : Nat) : ApproxForm → Nat → Nat → Rat
  | .dense P, o, t => P.get (o * inn + t)
  | .lowRank F G, o, t =>
    let r := F.shape.getD 1 0
    ((List.range r).map fun k => F.get (o * r + k) * G.get (k * inn + t)).sum

/-- For every output `j < out`, a lower bound on `P[l, t] - P[j, t]` over
    the tokens `t` from `lo` to `hi` (`row_min_diffs` in
    `core/check/approx.py`):
    * dense: the smallest difference itself;
    * low rank: with `c = F[l] - F[j]`, the sum over `k` of `c_k` times the
      smallest of `G[k, lo], ..., G[k, hi]` if `c_k ≥ 0`, and the largest
      otherwise. -/
def rowBounds (inn out l lo hi : Nat) : ApproxForm → Array Rat
  | .dense P => (Array.range out).map fun j =>
    rangeMin (fun t => P.get (l * inn + t) - P.get (j * inn + t)) lo hi
  | .lowRank F G =>
    let r := F.shape.getD 1 0
    let gmin := (Array.range r).map fun k => rangeMin (fun t => G.get (k * inn + t)) lo hi
    let gmax := (Array.range r).map fun k => rangeMax (fun t => G.get (k * inn + t)) lo hi
    (Array.range out).map fun j => ((List.range r).map fun k =>
      let c := F.get (l * r + k) - F.get (j * r + k)
      if 0 ≤ c then c * gmin.getD k 0 else c * gmax.getD k 0).sum

end ApproxForm

/-- The largest error `|W[o, t] - P[o, t]|` over the entries of `W` (shape
    `[out, in]`). -/
def approxError (W : Tensor Rat) (f : ApproxForm) : Rat :=
  let inn := W.shape.getD 1 0
  (List.range (W.shape.getD 0 0 * inn)).foldl (fun m e =>
    let d := W.get e - f.entry inn (e / inn) (e % inn)
    max m (max d (-d))) 0

/-- An approximation, ready for the interval rule: the position `of` of the
    linear map it approximates in the (contracted) graph, that map's weight
    `W`, the matrix `P`, and the largest error `eps = max |W - P|`. -/
structure Approx where
  name : String
  of : Nat
  W : Tensor Rat
  form : ApproxForm
  eps : Rat

/-- The bounds one position contributes to the margins, for every output
    `j < out`: the exact difference `W[l, t] - W[j, t]` if the position
    holds one token `t`, and otherwise the approximation's bound minus twice
    the error. -/
def approxTerm (W : Tensor Rat) (V out l : Nat) (a : Approx) (r : Range) : Array Rat :=
  if r.lo = r.hi then (Array.range out).map fun j => W.get (l * V + r.lo) - W.get (j * V + r.lo)
  else (a.form.rowBounds V out l r.lo r.hi).map (· - 2 * a.eps)

/-- Lower bounds on the margins at a linear output `W, b` on the summed
    one-hot input, with an approximation of `W` (`_final_margins` in
    `core/check/evaluate.py`). -/
def approxMargins (box : Box) (V : Nat) (W : Tensor Rat) (b : Option (Tensor Rat)) (l : Nat)
    (a : Approx) : List Rat :=
  let out := W.shape.getD 0 0
  let terms := box.map (approxTerm W V out l a)
  (List.range out).map fun j => (terms.map fun t => t.getD j 0).sum + (biasAt b l - biasAt b j)

/-- Lower bounds on the margins `logit[l] - logit[j]`, one for every output
    `j`, when the output is the linear map `W, b` applied to a value known as
    `arg`. The margin is `(W[l] - W[j]) · x + (b[l] - b[j])`.

    * On the summed one-hot input it is the sum over the positions of
      `W[l, x_p] - W[j, x_p]`, at least the smallest such difference over
      the tokens allowed at `p`. This is exact when all but one position
      hold a single token.
    * On bounds, each term `d_i * x_i` is at least the smaller of
      `d_i * lo_i` and `d_i * hi_i`.

    An approximation is used only on the summed one-hot input, and only if
    it is of the output map, the operation at position `output`; on bounds
    it is ignored, as in the Python checker. -/
def linearMargins (box : Box) (V : Nat) (W : Tensor Rat) (b : Option (Tensor Rat)) (l : Nat)
    (approx : Option Approx) (output : Nat) : IVal → Except String (List Rat)
  | .oneHot true =>
    match approx with
    | none =>
      .ok ((List.range (W.shape.getD 0 0)).map fun j =>
        (box.map fun r => rangeMin (fun t => W.get (l * V + t) - W.get (j * V + t)) r.lo r.hi).sum +
          (biasAt b l - biasAt b j))
    | some a =>
      if a.of = output then .ok (approxMargins box V W b l a)
      else .error s!"approximation {a.name} is not of the network's output map"
  | .oneHot false => .error "the network's output is computed per position"
  | .bounds lo hi =>
    let inn := W.shape.getD 1 0
    if lo.shape == [1, inn] then
      .ok ((List.range (W.shape.getD 0 0)).map fun j =>
        ((List.range inn).map fun i =>
          min ((W.get (l * inn + i) - W.get (j * inn + i)) * lo.get i)
            ((W.get (l * inn + i) - W.get (j * inn + i)) * hi.get i)).sum +
          (biasAt b l - biasAt b j))
    else .error "the network's output must be one logit vector"

/-- Lower bounds on the margins when the output is not a linear map:
    `lo[l] - hi[j]`. -/
def valueMargins (l : Nat) : IVal → Except String (List Rat)
  | .bounds lo hi =>
    if lo.shape == [1, lo.data.size] then
      .ok ((List.range lo.data.size).map fun j => lo.get l - hi.get j)
    else .error "the network's output must be one logit vector"
  | .oneHot _ => .error "the network's output must be computed from its input"

/-- The interval rule on one box, with an optional approximation: `true` if
    every input in the box is certified, `false` if the label is not
    constant or a margin bound is not positive, and an error if the rule
    cannot follow the network. -/
def intervalLeaf (g : Graph) (w : Weights Rat) (task : Task) (box : Box)
    (approx : Option Approx) : Except String Bool :=
  match task.constantLabel box with
  | none => .ok false
  | some l =>
    match ievalOps g w box g.nodes #[] with
    | none => .error "the interval rule cannot follow this network"
    | some nodes =>
      match nodes[g.output]? with
      | none => .error "the network's output is not one of its operations"
      | some node =>
        let margins := match node.lin with
          | some (arg, W, b) => linearMargins box g.values W b l approx g.output arg
          | none => valueMargins l node.val
        match margins with
        | .error e => .error e
        | .ok m => if l < m.length then .ok (allPosExcept m l)
          else .error "the label is not one of the network's outputs"

end CompactCheck
