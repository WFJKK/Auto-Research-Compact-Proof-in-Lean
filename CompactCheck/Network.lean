import CompactCheck.Tensor

/-!
# Networks as graphs

A network is data, not code: a list of operations, each reading earlier
results by their position in the list, plus named weight tensors. Lean
never mentions a particular model. A trusted Python exporter writes the
graph that PyTorch traces from a model folder's `model.py`, and the
model's weights, exactly.

Every value keeps PyTorch's leading batch dimension, of size 1, so the
dimensions in the graph are exactly those in the PyTorch model. The input
is the one-hot encoding of the tokens, of shape `[1, positions, values]`.

The first four operations are those of linear networks
(`core/check/trace.py`): `input`, `linear`, `sum` and `add`. The others are
those of attention networks (`core/check/general.py`): weights used
directly, entrywise arithmetic with broadcasting, matrix products,
indexing, reshaping, concatenation, `exp` and `softmax`. What each one
computes is in `Eval.lean` and `Semantics.lean`.

This file uses only core Lean.
-/

namespace CompactCheck

/-- Indexing one dimension: all of it, one entry (the dimension
    disappears), or the entries `start, ..., stop - 1`. -/
inductive IndexItem where
  | all
  | one (i : Nat)
  | range (start stop : Nat)
deriving Repr, BEq, DecidableEq

/-- Entrywise arithmetic. -/
inductive BinOp where
  | add
  | sub
  | mul
deriving Repr, BEq, DecidableEq

/-- One operation of a network. Arguments are positions of earlier
    operations in the graph's list. -/
inductive Op where
  /-- The one-hot input, of shape `[1, positions, values]`. -/
  | input
  /-- `torch.nn.Linear` on the last dimension, with the weight `[out, in]`
      and the optional bias `[out]` named here. -/
  | linear (arg : Nat) (weight : String) (bias : Option String)
  /-- Sum over one dimension. A negative `dim` counts from the end, as in
      PyTorch. -/
  | sum (arg : Nat) (dim : Int)
  /-- Entrywise sum of two results of the same shape. -/
  | add (left right : Nat)
  /-- A weight tensor, or a constant of the model, by name. -/
  | param (name : String)
  /-- `+`, `-` or `*` entry by entry, with broadcasting as in PyTorch. -/
  | binary (op : BinOp) (left right : Nat)
  /-- `-x` entry by entry. -/
  | neg (arg : Nat)
  /-- `torch.matmul`. -/
  | matmul (left right : Nat)
  /-- Indexing with integers and ranges, one item per leading dimension. -/
  | index (arg : Nat) (items : List IndexItem)
  /-- The transpose of a matrix (`.T`). -/
  | transpose (arg : Nat)
  /-- A new dimension of size 1 (`unsqueeze`). -/
  | unsqueeze (arg : Nat) (dim : Int)
  /-- `expand`: dimensions of size 1 repeated, new leading dimensions. -/
  | expand (arg : Nat) (shape : List Int)
  /-- `torch.cat` along a dimension. -/
  | cat (args : List Nat) (dim : Int)
  /-- `torch.stack` along a new dimension. -/
  | stack (args : List Nat) (dim : Int)
  /-- `exp` entry by entry. -/
  | exp (arg : Nat)
  /-- `softmax` along a dimension. -/
  | softmax (arg : Nat) (dim : Int)
  /-- Zeros of the same shape (`torch.zeros_like`). -/
  | zerosLike (arg : Nat)
deriving Repr, BEq

/-- A network's graph: the input's shape, the operations in order, and
    which operation gives the output. -/
structure Graph where
  positions : Nat
  values : Nat
  nodes : List Op
  output : Nat
deriving Repr

/-- Named weight tensors. -/
abbrev Weights (α : Type) := List (String × Tensor α)

end CompactCheck
