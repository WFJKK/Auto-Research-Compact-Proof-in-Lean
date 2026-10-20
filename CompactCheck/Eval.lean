import CompactCheck.Network
import CompactCheck.Task

/-!
# Evaluating a linear network

What the operations of linear networks compute (`input`, `linear`, `sum`,
`add`), written once for any number type with `0`, `1`, `+` and `*`. With
`α = Rat` this is the checker's exact evaluator. The spec (`Spec.lean`)
uses these same definitions over the reals, through `Semantics.lean`, which
adds the operations of attention networks. Every operation reads entries by
their row-major position, so each definition is the formula in its
docstring.

`evalOp` gives `none` for the other operations: `exp` and `softmax` have no
exact rational values, so the exact evaluator certifies nothing for a
network that uses them.

An operation whose arguments do not fit (a wrong shape, a missing weight,
an argument that is not an earlier operation) gives `none`, and so does the
whole network. The checker certifies nothing for such a network.

This file uses only core Lean.
-/

namespace CompactCheck

variable {α : Type} [Zero α] [One α] [Add α] [Mul α]

/-- The one-hot encoding of `x`, of shape `[1, positions, values]`:
    `out[0, p, v] = 1` if `x[p] = v`, and 0 otherwise. Requires one token
    per position, each below `values`. -/
def oneHotInput (positions values : Nat) (x : Input) : Option (Tensor α) :=
  if x.length == positions && x.all (· < values) then
    some ⟨[1, positions, values], (Array.range (positions * values)).map fun j =>
      if x.getD (j / values) 0 = j % values then 1 else 0⟩
  else none

/-- `torch.nn.Linear` on the last dimension: for every index `p` of the
    leading dimensions and every output `o`,
    `out[p, o] = Σ_i W[o, i] * t[p, i] + b[o]` (with `b = 0` if there is no
    bias). The weight has shape `[out, in]` and the bias `[out]`. -/
def linearOp (W : Tensor α) (b : Option (Tensor α)) (t : Tensor α) : Option (Tensor α) :=
  let out := W.shape.getD 0 0
  let inn := W.shape.getD 1 0
  let pre := shapeSize t.shape.dropLast
  let biasOk := match b with
    | some b => b.shape == [out] && b.data.size == out
    | none => true
  if W.shape == [out, inn] && t.shape.getLast? == some inn && W.data.size == out * inn &&
      t.data.size == pre * inn && biasOk then
    some ⟨t.shape.dropLast ++ [out], (Array.range (pre * out)).map fun j =>
      let p := j / out
      let o := j % out
      ((List.range inn).map fun i => W.get (o * inn + i) * t.get (p * inn + i)).sum +
        (match b with
         | some b => b.get o
         | none => 0)⟩
  else none

/-- Dimension `dim` of a tensor of rank `r`, as PyTorch reads it: `0` to
    `r - 1` from the front, `-1` to `-r` from the end. -/
def normDim (dim : Int) (r : Nat) : Option Nat :=
  if dim < 0 then
    if (-dim).toNat ≤ r then some (r - (-dim).toNat) else none
  else
    if dim.toNat < r then some dim.toNat else none

/-- Sum over dimension `dim` (negative counts from the end):
    `out[o, i] = Σ_k t[o, k, i]`, where `o` runs over the dimensions before
    `dim`, `k` over `dim` itself and `i` over the dimensions after it. -/
def sumOp (dim : Int) (t : Tensor α) : Option (Tensor α) :=
  match normDim dim t.shape.length with
  | none => none
  | some d =>
    let outer := shapeSize (t.shape.take d)
    let n := t.shape.getD d 0
    let inner := shapeSize (t.shape.drop (d + 1))
    if t.data.size == outer * n * inner then
      some ⟨t.shape.eraseIdx d, (Array.range (outer * inner)).map fun j =>
        let o := j / inner
        let i := j % inner
        ((List.range n).map fun k => t.get ((o * n + k) * inner + i)).sum⟩
    else none

/-- Entrywise sum of two tensors of the same shape. -/
def addOp (a b : Tensor α) : Option (Tensor α) :=
  if a.shape == b.shape && a.data.size == b.data.size then
    some ⟨a.shape, (Array.range a.data.size).map fun j => a.get j + b.get j⟩
  else none

/-- One operation, given the results of the operations before it. -/
def evalOp (g : Graph) (w : Weights α) (x : Input) (vals : Array (Tensor α)) :
    Op → Option (Tensor α)
  | .input => oneHotInput g.positions g.values x
  | .linear a wn bn =>
    match vals[a]?, List.lookup wn w with
    | some t, some W =>
      match bn with
      | none => linearOp W none t
      | some bn =>
        match List.lookup bn w with
        | some b => linearOp W (some b) t
        | none => none
    | _, _ => none
  | .sum a d =>
    match vals[a]? with
    | some t => sumOp d t
    | none => none
  | .add a b =>
    match vals[a]?, vals[b]? with
    | some ta, some tb => addOp ta tb
    | _, _ => none
  | _ => none

/-- Run the operations in order, appending each result. An argument can
    only name an earlier operation, since later results do not exist yet. -/
def evalOps (g : Graph) (w : Weights α) (x : Input) :
    List Op → Array (Tensor α) → Option (Array (Tensor α))
  | [], vals => some vals
  | op :: ops, vals =>
    match evalOp g w x vals op with
    | some v => evalOps g w x ops (vals.push v)
    | none => none

/-- The network's output on input `x`. -/
def evalGraph (g : Graph) (w : Weights α) (x : Input) : Option (Tensor α) :=
  match evalOps g w x g.nodes #[] with
  | some vals => vals[g.output]?
  | none => none

end CompactCheck
