/-!
# Tensors

A tensor is a shape and its entries in row-major order, over any number
type `α`. The checker uses `α = Rat`, where everything is computable. The
spec in `Spec.lean` uses the same definitions with `α = ℝ`, so the
checker's numbers and the spec's numbers come from one piece of code.

This file uses only core Lean.
-/

namespace CompactCheck

/-- The number of entries of a tensor with this shape: the product of the
    dimensions (1 for a scalar, whose shape is `[]`). -/
def shapeSize (shape : List Nat) : Nat :=
  shape.foldr (· * ·) 1

/-- A tensor: its shape and its entries in row-major order. In a
    well-formed tensor, `data.size = shapeSize shape`. -/
structure Tensor (α : Type) where
  shape : List Nat
  data : Array α
deriving Repr, BEq

namespace Tensor

variable {α β : Type}

/-- Entry `i` in row-major order, or 0 out of range. -/
def get [Zero α] (t : Tensor α) (i : Nat) : α :=
  t.data.getD i 0

/-- The entries match the shape. -/
def wellFormed (t : Tensor α) : Bool :=
  t.data.size == shapeSize t.shape

/-- Apply `f` to every entry; the shape stays the same. -/
def map (f : α → β) (t : Tensor α) : Tensor β :=
  ⟨t.shape, t.data.map f⟩

end Tensor

end CompactCheck
