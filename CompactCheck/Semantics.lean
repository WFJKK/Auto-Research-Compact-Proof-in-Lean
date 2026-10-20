import CompactCheck.Eval

/-!
# What every operation computes

The semantics of all operations of `Network.lean`, over any number type
with `0`, `1`, `+`, `*`, negation, an exponential and a division. With
`α = ℝ` and `Real.exp` this is the spec (`Spec.lean`). The operations of
linear networks are those of `Eval.lean`; this file adds those of attention
networks (`core/check/general.py`), as PyTorch computes them but exactly.

A tensor is written as a function of its multi-index (`Tensor.ofFn`) and
read by multi-index (`Tensor.entry`), so each definition is the formula in its
docstring, entry by entry. Shapes follow PyTorch: broadcasting aligns the
last dimensions, and a negative dimension counts from the end.

An operation whose arguments do not fit (shapes that do not broadcast, an
index out of range, a missing weight) gives `none`, and so does the whole
network.

This file uses only core Lean.
-/

namespace CompactCheck

/-- The exponential and the division, which softmax and `exp` need. -/
class ExpDiv (α : Type) where
  exp : α → α
  div : α → α → α

/-! ## Multi-indices -/

/-- The strides of a shape in row-major order: the last index moves
    fastest. -/
def strides : List Nat → List Nat
  | [] => []
  | _ :: rest => shapeSize rest :: strides rest

/-- The row-major position of multi-index `i` in a tensor of this shape. -/
def ravel (shape i : List Nat) : Nat :=
  (List.zipWith (· * ·) (strides shape) i).sum

/-- The multi-index of row-major position `j`. -/
def unravel (shape : List Nat) (j : Nat) : List Nat :=
  List.zipWith (fun s d => j / s % d) (strides shape) shape

namespace Tensor

variable {α : Type}

/-- The tensor of this shape whose entry at multi-index `i` is `f i`. -/
def ofFn (shape : List Nat) (f : List Nat → α) : Tensor α :=
  ⟨shape, (Array.range (shapeSize shape)).map fun j => f (unravel shape j)⟩

/-- The entry at multi-index `i`. -/
def entry [Zero α] (t : Tensor α) (i : List Nat) : α :=
  t.get (ravel t.shape i)

end Tensor

/-! ## Broadcasting -/

/-- The shape of an entrywise operation on shapes `s` and `t`, as in
    PyTorch: the shapes are aligned at their last dimensions, missing
    dimensions count as 1, and two sizes must be equal unless one is 1. -/
def broadcastShape (s t : List Nat) : Option (List Nat) :=
  let n := max s.length t.length
  (List.zip (List.replicate (n - s.length) 1 ++ s) (List.replicate (n - t.length) 1 ++ t)).mapM
    fun (a, b) => if a = b then some a else if a = 1 then some b else if b = 1 then some a else none

/-- The multi-index of a tensor of shape `s` that broadcasting reads at
    multi-index `i` of the result: the last `s.length` indices, with 0 along
    the dimensions of size 1. -/
def broadcastIndex (s i : List Nat) : List Nat :=
  List.zipWith (fun d k => if d = 1 then 0 else k) s (i.drop (i.length - s.length))

section ops

variable {α : Type} [Zero α] [One α] [Add α] [Mul α] [Neg α] [ExpDiv α]

/-- `f` entry by entry, with broadcasting:
    `out[i] = f a[broadcastIndex a i] b[broadcastIndex b i]`. -/
def broadcastOp (f : α → α → α) (a b : Tensor α) : Option (Tensor α) :=
  if a.wellFormed && b.wellFormed then
    (broadcastShape a.shape b.shape).map fun s =>
      Tensor.ofFn s fun i =>
        f (a.entry (broadcastIndex a.shape i)) (b.entry (broadcastIndex b.shape i))
  else none

/-- `+`, `-` or `*`. -/
def BinOp.apply : BinOp → α → α → α
  | .add, a, b => a + b
  | .sub, a, b => a + -b
  | .mul, a, b => a * b

/-- The shapes of `torch.matmul` of tensors of shapes `s` and `t`: the
    shapes padded to matrices (a vector `a` is one row, a vector `b` one
    column), the matrix sizes `m × k` and `k × n`, the leading (batch)
    dimensions of each and their broadcast, and the shape of the result,
    without the padded dimensions. -/
structure MatmulShape where
  sa : List Nat
  sb : List Nat
  m : Nat
  k : Nat
  n : Nat
  ba : List Nat
  bb : List Nat
  batch : List Nat
  out : List Nat

/-- A vector as a matrix of one row; other shapes stay. -/
def padRow (s : List Nat) : List Nat := if s.length = 1 then 1 :: s else s

/-- A vector as a matrix of one column; other shapes stay. -/
def padCol (t : List Nat) : List Nat := if t.length = 1 then t ++ [1] else t

/-- The matrix dimension `d` of a product's result, left out where it was
    padded. -/
def keepDim (s : List Nat) (d : Nat) : List Nat := if s.length = 1 then [] else [d]

def matmulShape (s t : List Nat) : Option MatmulShape :=
  if s = [] || t = [] then none else
  let sa := padRow s
  let sb := padCol t
  let m := sa.getD (sa.length - 2) 0
  let k := sa.getD (sa.length - 1) 0
  let n := sb.getD (sb.length - 1) 0
  let ba := sa.take (sa.length - 2)
  let bb := sb.take (sb.length - 2)
  if sb.getD (sb.length - 2) 0 ≠ k then none else
  (broadcastShape ba bb).map fun batch =>
    ⟨sa, sb, m, k, n, ba, bb, batch, batch ++ keepDim s m ++ keepDim t n⟩

/-- `torch.matmul`: `out[..., r, c] = Σ_k a[..., r, k] * b[..., k, c]`,
    with the leading (batch) dimensions broadcast. A vector `a` is one row
    and a vector `b` one column, and that dimension is left out of the
    result. -/
def matmulOp (a b : Tensor α) : Option (Tensor α) :=
  if !a.wellFormed || !b.wellFormed then none else
  (matmulShape a.shape b.shape).map fun p =>
    let a' : Tensor α := ⟨p.sa, a.data⟩
    let b' : Tensor α := ⟨p.sb, b.data⟩
    ⟨p.out, (Tensor.ofFn (p.batch ++ [p.m, p.n]) fun i =>
      let bi := i.take p.batch.length
      ((List.range p.k).map fun t =>
        a'.entry (broadcastIndex p.ba bi ++ [i.getD p.batch.length 0, t]) *
        b'.entry (broadcastIndex p.bb bi ++ [t, i.getD (p.batch.length + 1) 0])).sum).data⟩

/-- Whether an index item fits a dimension of size `d`. -/
def IndexItem.fits (d : Nat) : IndexItem → Bool
  | .all => true
  | .one i => i < d
  | .range a b => a ≤ b && b ≤ d

/-- The dimension an index item leaves of a dimension of size `d`: none for
    one entry. -/
def IndexItem.dims (d : Nat) : IndexItem → List Nat
  | .all => [d]
  | .one _ => []
  | .range a b => [b - a]

/-- The multi-index indexing reads at multi-index `i` of the result. -/
def sourceIndex : List IndexItem → List Nat → List Nat
  | [], i => i
  | .all :: items, i => i.headD 0 :: sourceIndex items i.tail
  | .one j :: items, i => j :: sourceIndex items i
  | .range a _ :: items, i => (a + i.headD 0) :: sourceIndex items i.tail

/-- Indexing `t[items]`, one item for each leading dimension:
    `out[i] = t[sourceIndex items i]`. -/
def indexOp (t : Tensor α) (items : List IndexItem) : Option (Tensor α) :=
  if items.length ≤ t.shape.length && t.wellFormed &&
      (List.zipWith IndexItem.fits (t.shape.take items.length) items).all id then
    some (Tensor.ofFn ((List.zipWith IndexItem.dims (t.shape.take items.length) items).flatten ++
      t.shape.drop items.length) fun i => t.entry (sourceIndex items i))
  else none

/-- The transpose of a matrix (`.T`): `out[r, c] = t[c, r]`. A vector or a
    number is its own transpose. -/
def transposeOp (t : Tensor α) : Option (Tensor α) :=
  match t.shape with
  | [m, n] =>
    if t.wellFormed then some (Tensor.ofFn [n, m] fun i => t.entry [i.getD 1 0, i.getD 0 0]) else none
  | [] => some t
  | [_] => some t
  | _ => none

/-- A new dimension of size 1 at position `dim` of the result (from the end
    if negative). The entries stay in the same order. -/
def unsqueezeOp (t : Tensor α) (dim : Int) : Option (Tensor α) :=
  (normDim dim (t.shape.length + 1)).map fun d => ⟨t.shape.take d ++ [1] ++ t.shape.drop d, t.data⟩

/-- The shape of `t.expand(shape)` for a tensor of shape `ts`: `shape`,
    where `-1` keeps the size of the matching dimension of `ts` (aligned at
    the end). `none` for `-1` at a new leading dimension or another
    negative size. -/
def expandShape (ts : List Nat) (shape : List Int) : Option (List Nat) :=
  (List.range shape.length).mapM fun i =>
    let s := shape.getD i 0
    if s = -1 then
      (if i < shape.length - ts.length then none else some (ts.getD (i - (shape.length - ts.length)) 0))
    else if 0 ≤ s then some s.toNat else none

/-- `t.expand(shape)`: new leading dimensions, and dimensions of size 1
    repeated; `-1` keeps a size. `out[i] = t[broadcastIndex t i]`. -/
def expandOp (t : Tensor α) (shape : List Int) : Option (Tensor α) :=
  if shape.length < t.shape.length || !t.wellFormed then none else
  match expandShape t.shape shape with
  | none => none
  | some full =>
    if (List.zipWith (fun d f => d == f || d == 1) t.shape
        (full.drop (shape.length - t.shape.length))).all id then
      some (Tensor.ofFn full fun i => t.entry (broadcastIndex t.shape i))
    else none

/-- The part a position along the joined dimension falls in, and its first
    position. -/
def locate : List Nat → Nat → Nat → Nat × Nat
  | [], _, start => (0, start)
  | s :: sizes, k, start => if k < start + s then (0, start) else
    let (p, first) := locate sizes k (start + s)
    (p + 1, first)

/-- For `torch.cat` of tensors of these shapes along `dim`: the dimension,
    the sizes along it, and the shape of the result, if the shapes fit (same
    rank, same sizes outside `dim`). -/
def catShape (shapes : List (List Nat)) (dim : Int) : Option (Nat × List Nat × List Nat) :=
  match shapes with
  | [] => none
  | s0 :: _ =>
    match normDim dim s0.length with
    | none => none
    | some d =>
      if shapes.all fun s => s.length == s0.length && s.eraseIdx d == s0.eraseIdx d then
        some (d, shapes.map (·.getD d 0), s0.set d (shapes.map (·.getD d 0)).sum)
      else none

/-- `torch.cat`: the tensors joined along dimension `dim`; their other
    sizes must agree. `out[i]` is entry `i` of the part holding position
    `i[d]`, counted from the part's first position. -/
def catOp (ts : List (Tensor α)) (dim : Int) : Option (Tensor α) :=
  if ts.all (·.wellFormed) then
    match catShape (ts.map (·.shape)) dim with
    | none => none
    | some (d, sizes, shape) =>
      some (Tensor.ofFn shape fun i =>
        let (p, first) := locate sizes (i.getD d 0) 0
        (ts.getD p ⟨[], #[]⟩).entry (i.set d (i.getD d 0 - first)))
  else none

/-- For `torch.stack` of tensors of these shapes along a new dimension
    `dim`: the dimension and the shape of the result, if all shapes are
    equal. -/
def stackShape (shapes : List (List Nat)) (dim : Int) : Option (Nat × List Nat) :=
  match shapes with
  | [] => none
  | s0 :: _ =>
    match normDim dim (s0.length + 1) with
    | none => none
    | some d =>
      if shapes.all (· == s0) then some (d, s0.take d ++ [shapes.length] ++ s0.drop d) else none

/-- `torch.stack`: tensors of one shape along a new dimension `dim`:
    `out[i] = ts[i[d]][i without i[d]]`. -/
def stackOp (ts : List (Tensor α)) (dim : Int) : Option (Tensor α) :=
  if ts.all (·.wellFormed) then
    match stackShape (ts.map (·.shape)) dim with
    | none => none
    | some (d, shape) =>
      some (Tensor.ofFn shape fun i => (ts.getD (i.getD d 0) ⟨[], #[]⟩).entry (i.eraseIdx d))
  else none

/-- Softmax along dimension `dim`:
    `out[i] = exp t[i] / Σ_k exp t[i with k at dimension d]`. -/
def softmaxOp (t : Tensor α) (dim : Int) : Option (Tensor α) :=
  match normDim dim t.shape.length with
  | none => none
  | some d =>
    if t.wellFormed then
      some (Tensor.ofFn t.shape fun i =>
        ExpDiv.div (ExpDiv.exp (t.entry i))
          ((List.range (t.shape.getD d 0)).map fun k => ExpDiv.exp (t.entry (i.set d k))).sum)
    else none

/-! ## The network -/

/-- One operation, given the results of the operations before it. The
    operations of linear networks are those of `evalOp`. -/
def semOp (g : Graph) (w : Weights α) (x : Input) (vals : Array (Tensor α)) :
    Op → Option (Tensor α)
  | .param n => List.lookup n w
  | .binary f a b =>
    match vals[a]?, vals[b]? with
    | some ta, some tb => broadcastOp f.apply ta tb
    | _, _ => none
  | .neg a => vals[a]?.map (Tensor.map Neg.neg)
  | .matmul a b =>
    match vals[a]?, vals[b]? with
    | some ta, some tb => matmulOp ta tb
    | _, _ => none
  | .index a items => vals[a]?.bind (indexOp · items)
  | .transpose a => vals[a]?.bind transposeOp
  | .unsqueeze a d => vals[a]?.bind (unsqueezeOp · d)
  | .expand a shape => vals[a]?.bind (expandOp · shape)
  | .cat args d => (args.mapM (vals[·]?)).bind (catOp · d)
  | .stack args d => (args.mapM (vals[·]?)).bind (stackOp · d)
  | .exp a => vals[a]?.map (Tensor.map ExpDiv.exp)
  | .softmax a d => vals[a]?.bind (softmaxOp · d)
  | .zerosLike a => vals[a]?.map fun t => ⟨t.shape, Array.replicate (shapeSize t.shape) 0⟩
  | op => evalOp g w x vals op

/-- Run the operations in order, appending each result. -/
def semOps (g : Graph) (w : Weights α) (x : Input) :
    List Op → Array (Tensor α) → Option (Array (Tensor α))
  | [], vals => some vals
  | op :: ops, vals =>
    match semOp g w x vals op with
    | some v => semOps g w x ops (vals.push v)
    | none => none

/-- The network's output on input `x`. -/
def semGraph (g : Graph) (w : Weights α) (x : Input) : Option (Tensor α) :=
  match semOps g w x g.nodes #[] with
  | some vals => vals[g.output]?
  | none => none

end ops

end CompactCheck
