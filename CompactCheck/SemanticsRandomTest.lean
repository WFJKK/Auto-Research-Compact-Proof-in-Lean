import CompactCheck.Semantics

/-!
# Random tests of the operations of attention networks

Written by `scripts/gen_semantics_tests.py`: each `#guard` compares an
operation of `Semantics.lean` on random integer tensors with PyTorch's
result, or checks that Lean refuses what PyTorch refuses. Softmax uses a
stand-in exponential, `x * x + 1` over the rationals, so that results are
exact.

This file uses only core Lean.
-/

namespace CompactCheck.SemanticsRandomTest

open CompactCheck

/-- A stand-in for the exponential, to test softmax exactly. -/
local instance : ExpDiv Rat := ⟨fun q => q * q + 1, (· / ·)⟩

/-! ## entrywise arithmetic with broadcasting -/

#guard broadcastOp (BinOp.apply .sub) (⟨[2, 2, 1], #[(-5), 0, 1, 5]⟩ : Tensor Int) (⟨[1], #[3]⟩ : Tensor Int) == some (⟨[2, 2, 1], #[(-8), (-3), (-2), 2]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[2], #[4, 3]⟩ : Tensor Int) (⟨[2, 3], #[3, 4, (-4), (-5), 4, (-5)]⟩ : Tensor Int) == none
#guard broadcastOp (BinOp.apply .add) (⟨[], #[(-2)]⟩ : Tensor Int) (⟨[], #[(-5)]⟩ : Tensor Int) == some (⟨[], #[(-7)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[], #[2]⟩ : Tensor Int) (⟨[], #[3]⟩ : Tensor Int) == some (⟨[], #[(-1)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[3], #[5, 2, (-1)]⟩ : Tensor Int) (⟨[3], #[4, (-4), 1]⟩ : Tensor Int) == some (⟨[3], #[20, (-8), (-1)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[1], #[0]⟩ : Tensor Int) (⟨[2, 2, 1], #[2, 1, (-3), (-2)]⟩ : Tensor Int) == some (⟨[2, 2, 1], #[0, 0, 0, 0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[2, 1], #[(-1), (-1)]⟩ : Tensor Int) (⟨[2, 2], #[4, (-1), 3, (-2)]⟩ : Tensor Int) == some (⟨[2, 2], #[3, (-2), 2, (-3)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1, 1], #[(-2)]⟩ : Tensor Int) (⟨[3, 1, 1], #[3, (-5), 1]⟩ : Tensor Int) == some (⟨[3, 1, 1], #[(-5), 3, (-3)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[3, 1, 1], #[5, 2, (-4)]⟩ : Tensor Int) (⟨[1, 3, 1], #[0, 1, 3]⟩ : Tensor Int) == some (⟨[3, 3, 1], #[0, 5, 15, 0, 2, 6, 0, (-4), (-12)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[], #[5]⟩ : Tensor Int) (⟨[2], #[5, 1]⟩ : Tensor Int) == some (⟨[2], #[0, 4]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[2, 3, 1], #[(-3), 3, (-5), (-1), (-2), 3]⟩ : Tensor Int) (⟨[1], #[3]⟩ : Tensor Int) == some (⟨[2, 3, 1], #[(-9), 9, (-15), (-3), (-6), 9]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[3, 1, 1], #[3, 4, (-5)]⟩ : Tensor Int) (⟨[], #[(-4)]⟩ : Tensor Int) == some (⟨[3, 1, 1], #[(-12), (-16), 20]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[5]⟩ : Tensor Int) (⟨[], #[0]⟩ : Tensor Int) == some (⟨[], #[0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[4]⟩ : Tensor Int) (⟨[3], #[4, 3, (-4)]⟩ : Tensor Int) == some (⟨[3], #[16, 12, (-16)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[1, 2, 2], #[(-1), 0, (-5), 5]⟩ : Tensor Int) (⟨[2, 1], #[2, (-2)]⟩ : Tensor Int) == some (⟨[1, 2, 2], #[1, 2, (-7), 3]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[], #[3]⟩ : Tensor Int) (⟨[], #[(-3)]⟩ : Tensor Int) == some (⟨[], #[0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[3], #[(-5), (-4), 1]⟩ : Tensor Int) (⟨[3], #[3, (-3), (-3)]⟩ : Tensor Int) == some (⟨[3], #[(-2), (-7), (-2)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1], #[(-4)]⟩ : Tensor Int) (⟨[], #[3]⟩ : Tensor Int) == some (⟨[1], #[(-7)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[2, 3, 3], #[(-1), 4, 1, 2, 5, 2, (-1), (-5), 1, (-3), 1, (-5), 4, 5, (-4), 4, (-1), (-5)]⟩ : Tensor Int) (⟨[2], #[5, 5]⟩ : Tensor Int) == none
#guard broadcastOp (BinOp.apply .mul) (⟨[3], #[(-1), (-3), 2]⟩ : Tensor Int) (⟨[3, 3], #[0, (-2), 5, 2, 1, 5, 3, (-4), (-5)]⟩ : Tensor Int) == some (⟨[3, 3], #[0, 6, 10, (-2), (-3), 10, (-3), 12, (-10)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[(-1)]⟩ : Tensor Int) (⟨[1], #[0]⟩ : Tensor Int) == some (⟨[1], #[0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[3, 1], #[(-4), 0, 1]⟩ : Tensor Int) (⟨[3], #[(-2), 1, 5]⟩ : Tensor Int) == some (⟨[3, 3], #[8, (-4), (-20), 0, 0, 0, (-2), 1, 5]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1], #[(-2)]⟩ : Tensor Int) (⟨[], #[2]⟩ : Tensor Int) == some (⟨[1], #[(-4)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[2, 3, 3], #[2, 4, (-4), 2, (-1), 4, 5, 1, 1, 2, 1, 3, (-3), 3, 0, 3, 0, (-2)]⟩ : Tensor Int) (⟨[3, 1], #[(-5), 0, 5]⟩ : Tensor Int) == some (⟨[2, 3, 3], #[(-3), (-1), (-9), 2, (-1), 4, 10, 6, 6, (-3), (-4), (-2), (-3), 3, 0, 8, 5, 3]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1], #[3]⟩ : Tensor Int) (⟨[2, 1], #[3, (-3)]⟩ : Tensor Int) == some (⟨[2, 1], #[0, 6]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1], #[1]⟩ : Tensor Int) (⟨[2, 1], #[0, 0]⟩ : Tensor Int) == some (⟨[2, 1], #[1, 1]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[1, 1], #[5]⟩ : Tensor Int) (⟨[1, 1], #[4]⟩ : Tensor Int) == some (⟨[1, 1], #[9]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[2], #[1, (-5)]⟩ : Tensor Int) (⟨[2], #[(-4), (-5)]⟩ : Tensor Int) == some (⟨[2], #[(-3), (-10)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[1], #[(-4)]⟩ : Tensor Int) (⟨[3, 2, 3], #[2, (-5), 0, 3, 0, 2, 3, (-3), (-4), (-5), 1, (-3), (-3), 3, 3, 5, 0, 0]⟩ : Tensor Int) == some (⟨[3, 2, 3], #[(-8), 20, 0, (-12), 0, (-8), (-12), 12, 16, 20, (-4), 12, 12, (-12), (-12), (-20), 0, 0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1, 1], #[3]⟩ : Tensor Int) (⟨[1, 1], #[2]⟩ : Tensor Int) == some (⟨[1, 1], #[1]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[3, 1, 2], #[(-5), (-1), (-5), 4, 5, (-5)]⟩ : Tensor Int) (⟨[3, 1, 2], #[3, 2, (-2), 3, 5, 3]⟩ : Tensor Int) == some (⟨[3, 1, 2], #[(-15), (-2), 10, 12, 25, (-15)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[1], #[(-1)]⟩ : Tensor Int) (⟨[2], #[0, 1]⟩ : Tensor Int) == some (⟨[2], #[(-1), 0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[2, 1, 1], #[2, (-5)]⟩ : Tensor Int) (⟨[2, 1], #[5, (-5)]⟩ : Tensor Int) == some (⟨[2, 2, 1], #[10, (-10), (-25), 25]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[], #[(-1)]⟩ : Tensor Int) (⟨[], #[(-1)]⟩ : Tensor Int) == some (⟨[], #[0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[3, 2], #[(-2), 3, 1, 1, 4, (-4)]⟩ : Tensor Int) (⟨[3, 2], #[(-2), (-1), 5, (-5), (-1), 0]⟩ : Tensor Int) == some (⟨[3, 2], #[(-4), 2, 6, (-4), 3, (-4)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[(-2)]⟩ : Tensor Int) (⟨[2], #[5, (-2)]⟩ : Tensor Int) == some (⟨[2], #[(-10), 4]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[3], #[2, (-4), 4]⟩ : Tensor Int) (⟨[1, 3], #[3, 0, (-3)]⟩ : Tensor Int) == some (⟨[1, 3], #[6, 0, (-12)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[3, 1], #[3, (-1), 1]⟩ : Tensor Int) (⟨[1], #[1]⟩ : Tensor Int) == some (⟨[3, 1], #[3, (-1), 1]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[5]⟩ : Tensor Int) (⟨[], #[(-3)]⟩ : Tensor Int) == some (⟨[], #[(-15)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[1], #[2]⟩ : Tensor Int) (⟨[1, 2, 1], #[1, (-4)]⟩ : Tensor Int) == some (⟨[1, 2, 1], #[2, (-8)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1, 2], #[1, (-5)]⟩ : Tensor Int) (⟨[2], #[2, (-4)]⟩ : Tensor Int) == some (⟨[1, 2], #[(-1), (-1)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1, 3, 1], #[2, 5, 2]⟩ : Tensor Int) (⟨[1, 1], #[3]⟩ : Tensor Int) == some (⟨[1, 3, 1], #[(-1), 2, (-1)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[1], #[(-3)]⟩ : Tensor Int) (⟨[1], #[3]⟩ : Tensor Int) == some (⟨[1], #[(-9)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[], #[(-4)]⟩ : Tensor Int) (⟨[], #[4]⟩ : Tensor Int) == some (⟨[], #[0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[], #[(-2)]⟩ : Tensor Int) (⟨[], #[(-2)]⟩ : Tensor Int) == some (⟨[], #[0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[1], #[4]⟩ : Tensor Int) (⟨[1], #[(-3)]⟩ : Tensor Int) == some (⟨[1], #[1]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1], #[3]⟩ : Tensor Int) (⟨[1, 1], #[(-1)]⟩ : Tensor Int) == some (⟨[1, 1], #[4]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[3], #[(-4), 2, (-2)]⟩ : Tensor Int) (⟨[], #[(-5)]⟩ : Tensor Int) == some (⟨[3], #[(-9), (-3), (-7)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[2], #[(-3), (-4)]⟩ : Tensor Int) (⟨[2], #[(-4), (-1)]⟩ : Tensor Int) == some (⟨[2], #[12, 4]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[4]⟩ : Tensor Int) (⟨[], #[2]⟩ : Tensor Int) == some (⟨[], #[8]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[2]⟩ : Tensor Int) (⟨[], #[4]⟩ : Tensor Int) == some (⟨[], #[8]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1], #[4]⟩ : Tensor Int) (⟨[3], #[4, (-1), 5]⟩ : Tensor Int) == some (⟨[3], #[0, 5, (-1)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[1, 2, 3], #[0, (-4), 5, 1, 3, 5]⟩ : Tensor Int) (⟨[1, 2, 3], #[1, 2, 4, 5, 0, 1]⟩ : Tensor Int) == some (⟨[1, 2, 3], #[0, (-8), 20, 5, 0, 5]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[2, 3, 1], #[(-3), 3, (-3), (-4), (-3), 1]⟩ : Tensor Int) (⟨[2, 3, 1], #[0, 0, (-5), 2, (-2), 3]⟩ : Tensor Int) == some (⟨[2, 3, 1], #[0, 0, 15, (-8), 6, 3]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[(-2)]⟩ : Tensor Int) (⟨[], #[1]⟩ : Tensor Int) == some (⟨[], #[(-2)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[1, 2], #[(-3), 3]⟩ : Tensor Int) (⟨[2, 1, 2], #[2, (-4), (-3), (-1)]⟩ : Tensor Int) == some (⟨[2, 1, 2], #[(-6), (-12), 9, (-3)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[], #[2]⟩ : Tensor Int) (⟨[], #[4]⟩ : Tensor Int) == some (⟨[], #[(-2)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[2, 3, 1], #[(-4), (-3), (-1), (-1), 1, 1]⟩ : Tensor Int) (⟨[1], #[1]⟩ : Tensor Int) == some (⟨[2, 3, 1], #[(-3), (-2), 0, 0, 2, 2]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[3, 2, 2], #[(-5), (-5), 3, (-3), (-3), 1, (-5), 3, (-4), 1, 1, (-3)]⟩ : Tensor Int) (⟨[], #[(-1)]⟩ : Tensor Int) == some (⟨[3, 2, 2], #[(-6), (-6), 2, (-4), (-4), 0, (-6), 2, (-5), 0, 0, (-4)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[1, 3], #[3, 3, 2]⟩ : Tensor Int) (⟨[2, 1, 3], #[4, 3, (-1), (-1), (-2), (-4)]⟩ : Tensor Int) == some (⟨[2, 1, 3], #[7, 6, 1, 2, 1, (-2)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[2, 3], #[4, 2, 1, 1, (-5), (-1)]⟩ : Tensor Int) (⟨[3], #[(-2), 1, (-2)]⟩ : Tensor Int) == some (⟨[2, 3], #[6, 1, 3, 3, (-6), 1]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[2], #[(-2), 4]⟩ : Tensor Int) (⟨[2], #[(-1), (-1)]⟩ : Tensor Int) == some (⟨[2], #[(-1), 5]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[3, 1], #[4, (-4), (-3)]⟩ : Tensor Int) (⟨[1], #[1]⟩ : Tensor Int) == some (⟨[3, 1], #[5, (-3), (-2)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[2], #[(-3), 0]⟩ : Tensor Int) (⟨[], #[5]⟩ : Tensor Int) == some (⟨[2], #[2, 5]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1, 1], #[4]⟩ : Tensor Int) (⟨[1, 2], #[(-3), 3]⟩ : Tensor Int) == some (⟨[1, 2], #[7, 1]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[2, 1], #[(-3), 3]⟩ : Tensor Int) (⟨[2, 1], #[(-2), 1]⟩ : Tensor Int) == some (⟨[2, 1], #[(-5), 4]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[2], #[(-2), 4]⟩ : Tensor Int) (⟨[2], #[1, (-3)]⟩ : Tensor Int) == some (⟨[2], #[(-2), (-12)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[], #[(-1)]⟩ : Tensor Int) (⟨[], #[(-5)]⟩ : Tensor Int) == some (⟨[], #[(-6)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[], #[3]⟩ : Tensor Int) (⟨[], #[(-2)]⟩ : Tensor Int) == some (⟨[], #[5]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[2], #[(-2), 2]⟩ : Tensor Int) (⟨[1], #[1]⟩ : Tensor Int) == some (⟨[2], #[(-2), 2]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[2], #[2, (-2)]⟩ : Tensor Int) (⟨[3, 2, 2], #[4, (-5), (-3), 1, 2, 1, 1, 3, 1, 1, 4, 3]⟩ : Tensor Int) == some (⟨[3, 2, 2], #[6, (-7), (-1), (-1), 4, (-1), 3, 1, 3, (-1), 6, 1]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[1, 1, 1], #[(-1)]⟩ : Tensor Int) (⟨[1, 3, 1], #[0, (-5), (-3)]⟩ : Tensor Int) == some (⟨[1, 3, 1], #[(-1), (-6), (-4)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[], #[5]⟩ : Tensor Int) (⟨[2], #[(-1), (-1)]⟩ : Tensor Int) == some (⟨[2], #[6, 6]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[2, 2], #[2, 2, 1, 4]⟩ : Tensor Int) (⟨[1, 2], #[(-4), 0]⟩ : Tensor Int) == some (⟨[2, 2], #[(-2), 2, (-3), 4]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[1, 3], #[5, 0, (-1)]⟩ : Tensor Int) (⟨[1, 3], #[2, (-3), (-2)]⟩ : Tensor Int) == some (⟨[1, 3], #[7, (-3), (-3)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[2, 1, 2], #[(-4), 2, 2, 2]⟩ : Tensor Int) (⟨[], #[(-4)]⟩ : Tensor Int) == some (⟨[2, 1, 2], #[0, 6, 6, 6]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[3, 1], #[(-1), 5, (-4)]⟩ : Tensor Int) (⟨[1], #[(-4)]⟩ : Tensor Int) == some (⟨[3, 1], #[3, 9, 0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[2, 3], #[(-3), 2, 1, (-1), 0, (-4)]⟩ : Tensor Int) (⟨[1, 3], #[(-2), 2, (-1)]⟩ : Tensor Int) == some (⟨[2, 3], #[6, 4, (-1), 2, 0, 4]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[3], #[(-2), 1, 5]⟩ : Tensor Int) (⟨[1, 1, 3], #[(-3), (-5), 2]⟩ : Tensor Int) == some (⟨[1, 1, 3], #[(-5), (-4), 7]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[], #[0]⟩ : Tensor Int) (⟨[1, 1, 3], #[0, 3, 3]⟩ : Tensor Int) == some (⟨[1, 1, 3], #[0, 3, 3]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[1, 2], #[(-1), (-3)]⟩ : Tensor Int) (⟨[1, 2], #[5, (-2)]⟩ : Tensor Int) == some (⟨[1, 2], #[(-5), 6]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[3], #[0, (-4), (-2)]⟩ : Tensor Int) (⟨[], #[4]⟩ : Tensor Int) == some (⟨[3], #[0, (-16), (-8)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[3, 1, 2], #[5, (-5), (-2), 3, (-2), 0]⟩ : Tensor Int) (⟨[2], #[0, (-4)]⟩ : Tensor Int) == some (⟨[3, 1, 2], #[5, (-1), (-2), 7, (-2), 4]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1], #[(-2)]⟩ : Tensor Int) (⟨[2], #[5, (-3)]⟩ : Tensor Int) == some (⟨[2], #[(-7), 1]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[3, 3, 1], #[3, 3, 5, (-2), 1, (-3), (-5), 2, 0]⟩ : Tensor Int) (⟨[1, 1], #[0]⟩ : Tensor Int) == some (⟨[3, 3, 1], #[3, 3, 5, (-2), 1, (-3), (-5), 2, 0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[3]⟩ : Tensor Int) (⟨[], #[4]⟩ : Tensor Int) == some (⟨[], #[12]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[3], #[(-3), 0, 4]⟩ : Tensor Int) (⟨[], #[4]⟩ : Tensor Int) == some (⟨[3], #[(-7), (-4), 0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1], #[3]⟩ : Tensor Int) (⟨[], #[(-1)]⟩ : Tensor Int) == some (⟨[1], #[4]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[3, 1, 1], #[2, 4, 1]⟩ : Tensor Int) (⟨[3, 1, 1], #[2, 1, 2]⟩ : Tensor Int) == some (⟨[3, 1, 1], #[4, 4, 2]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[0]⟩ : Tensor Int) (⟨[], #[(-3)]⟩ : Tensor Int) == some (⟨[], #[0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[3, 2, 3], #[(-4), 5, (-3), 0, (-1), 2, (-4), 3, 3, 2, 4, 5, (-4), 4, 0, 4, (-1), (-5)]⟩ : Tensor Int) (⟨[1, 3], #[3, (-4), 0]⟩ : Tensor Int) == some (⟨[3, 2, 3], #[(-12), (-20), 0, 0, 4, 0, (-12), (-12), 0, 6, (-16), 0, (-12), (-16), 0, 12, 4, 0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[1, 2], #[5, 3]⟩ : Tensor Int) (⟨[], #[(-1)]⟩ : Tensor Int) == some (⟨[1, 2], #[(-5), (-3)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[], #[0]⟩ : Tensor Int) (⟨[], #[1]⟩ : Tensor Int) == some (⟨[], #[0]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[1], #[(-5)]⟩ : Tensor Int) (⟨[2, 1], #[(-1), 4]⟩ : Tensor Int) == some (⟨[2, 1], #[(-4), (-9)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[3], #[5, 4, 3]⟩ : Tensor Int) (⟨[], #[(-4)]⟩ : Tensor Int) == some (⟨[3], #[9, 8, 7]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[3, 2], #[(-2), 5, (-2), 4, (-4), (-3)]⟩ : Tensor Int) (⟨[], #[5]⟩ : Tensor Int) == some (⟨[3, 2], #[(-7), 0, (-7), (-1), (-9), (-8)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[2, 1, 1], #[(-4), (-2)]⟩ : Tensor Int) (⟨[1, 1, 1, 1], #[2]⟩ : Tensor Int) == some (⟨[1, 2, 1, 1], #[(-8), (-4)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .add) (⟨[3], #[1, (-4), (-4)]⟩ : Tensor Int) (⟨[], #[(-2)]⟩ : Tensor Int) == some (⟨[3], #[(-1), (-6), (-6)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .mul) (⟨[2], #[4, (-1)]⟩ : Tensor Int) (⟨[2], #[(-4), 5]⟩ : Tensor Int) == some (⟨[2], #[(-16), (-5)]⟩ : Tensor Int)
#guard broadcastOp (BinOp.apply .sub) (⟨[], #[5]⟩ : Tensor Int) (⟨[2], #[(-4), (-5)]⟩ : Tensor Int) == some (⟨[2], #[9, 10]⟩ : Tensor Int)

/-! ## torch.matmul -/

#guard matmulOp (⟨[3, 1], #[4, (-1), (-3)]⟩ : Tensor Int) (⟨[1, 2], #[5, 5]⟩ : Tensor Int) == some (⟨[3, 2], #[20, 20, (-5), (-5), (-15), (-15)]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1], #[3, (-4)]⟩ : Tensor Int) (⟨[1, 1], #[(-5)]⟩ : Tensor Int) == some (⟨[2, 1], #[(-15), 20]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 1], #[(-4)]⟩ : Tensor Int) (⟨[1, 1], #[(-1)]⟩ : Tensor Int) == some (⟨[1, 1], #[4]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 1], #[(-5), 4, (-4)]⟩ : Tensor Int) (⟨[2, 1, 1], #[(-1), (-3)]⟩ : Tensor Int) == some (⟨[2, 3, 1], #[5, (-4), 4, 15, (-12), 12]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1], #[4, 4]⟩ : Tensor Int) (⟨[1, 2], #[2, 0]⟩ : Tensor Int) == some (⟨[2, 2], #[8, 0, 8, 0]⟩ : Tensor Int)
#guard matmulOp (⟨[2], #[(-1), (-1)]⟩ : Tensor Int) (⟨[3, 1], #[4, 0, 4]⟩ : Tensor Int) == none
#guard matmulOp (⟨[1], #[(-1)]⟩ : Tensor Int) (⟨[1], #[(-5)]⟩ : Tensor Int) == some (⟨[], #[5]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 1], #[1]⟩ : Tensor Int) (⟨[1, 3], #[3, (-2), (-1)]⟩ : Tensor Int) == some (⟨[1, 3], #[3, (-2), (-1)]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 2], #[3, 4]⟩ : Tensor Int) (⟨[3, 3, 3], #[1, (-5), 0, 2, (-2), 3, 3, (-2), (-2), 4, 2, (-5), (-3), 1, 1, (-2), 4, 1, (-2), (-3), (-1), (-3), (-1), 1, 3, 0, 0]⟩ : Tensor Int) == none
#guard matmulOp (⟨[2], #[2, 4]⟩ : Tensor Int) (⟨[2, 3], #[(-1), 1, 3, (-2), 4, (-2)]⟩ : Tensor Int) == some (⟨[3], #[(-10), 18, (-2)]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 3], #[(-1), 4, 4]⟩ : Tensor Int) (⟨[3, 1], #[(-2), 4, 4]⟩ : Tensor Int) == some (⟨[1, 1], #[34]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 2], #[3, 4, 5, 1]⟩ : Tensor Int) (⟨[2], #[(-3), 0]⟩ : Tensor Int) == some (⟨[2], #[(-9), (-15)]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 3], #[(-1), 0, 1, (-5), (-5), (-1), 1, (-2), 4]⟩ : Tensor Int) (⟨[3, 3], #[0, (-5), 4, 0, (-4), 1, 0, (-5), 1]⟩ : Tensor Int) == some (⟨[3, 3], #[0, 0, (-3), 0, 50, (-26), 0, (-17), 6]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1, 3], #[(-2), 1, 3, (-1), 1, (-2)]⟩ : Tensor Int) (⟨[2, 4, 3], #[(-4), (-1), (-1), 4, (-2), 5, 5, (-4), 2, 2, 4, 5, (-2), 1, (-1), 0, 1, 1, (-2), (-3), 0, 5, 1, 3]⟩ : Tensor Int) == none
#guard matmulOp (⟨[1], #[1]⟩ : Tensor Int) (⟨[1], #[4]⟩ : Tensor Int) == some (⟨[], #[4]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[(-4), (-2), (-2)]⟩ : Tensor Int) (⟨[2, 3, 3], #[2, 5, 1, 4, (-1), 4, 2, 3, (-5), 4, (-4), (-2), (-2), 4, 2, (-4), 2, (-2)]⟩ : Tensor Int) == some (⟨[2, 3], #[(-20), (-24), (-2), (-4), 4, 8]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 3, 3], #[5, (-2), 1, 1, (-5), 0, 0, 1, (-3), (-5), (-5), 3, 2, (-4), 4, 2, (-3), (-1), 5, 0, (-5), 2, 5, (-1), 4, (-5), (-5)]⟩ : Tensor Int) (⟨[3, 1], #[5, (-2), 0]⟩ : Tensor Int) == some (⟨[3, 3, 1], #[29, 15, (-2), (-15), 18, 16, 25, 0, 30]⟩ : Tensor Int)
#guard matmulOp (⟨[2], #[(-4), 5]⟩ : Tensor Int) (⟨[1, 2, 3], #[(-4), (-4), 4, 1, 2, (-2)]⟩ : Tensor Int) == some (⟨[1, 3], #[21, 26, (-26)]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 2, 3], #[(-2), 2, 3, (-2), (-3), 2, (-3), 5, (-5), 2, (-1), (-1), 1, 5, (-4), 4, (-1), 4]⟩ : Tensor Int) (⟨[3, 1], #[3, (-4), (-3)]⟩ : Tensor Int) == some (⟨[3, 2, 1], #[(-23), 0, (-14), 13, (-5), 4]⟩ : Tensor Int)
#guard matmulOp (⟨[2], #[2, 3]⟩ : Tensor Int) (⟨[2], #[3, 1]⟩ : Tensor Int) == some (⟨[], #[9]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1], #[1, 1]⟩ : Tensor Int) (⟨[1], #[4]⟩ : Tensor Int) == some (⟨[2], #[4, 4]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 2], #[3, (-5)]⟩ : Tensor Int) (⟨[2], #[0, 4]⟩ : Tensor Int) == some (⟨[1], #[(-20)]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 1, 2], #[(-2), 1, (-3), 0, (-5), (-3)]⟩ : Tensor Int) (⟨[3, 2], #[(-3), 2, (-5), (-2), (-5), (-3)]⟩ : Tensor Int) == none
#guard matmulOp (⟨[1, 3], #[3, (-4), 0]⟩ : Tensor Int) (⟨[4], #[5, 0, 2, 5]⟩ : Tensor Int) == none
#guard matmulOp (⟨[2, 2, 1], #[(-1), (-1), 4, (-4)]⟩ : Tensor Int) (⟨[1], #[4]⟩ : Tensor Int) == some (⟨[2, 2], #[(-4), (-4), 16, (-16)]⟩ : Tensor Int)
#guard matmulOp (⟨[1], #[1]⟩ : Tensor Int) (⟨[1], #[0]⟩ : Tensor Int) == some (⟨[], #[0]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 2], #[(-2), 0, 1, (-1)]⟩ : Tensor Int) (⟨[2, 2], #[3, (-4), (-1), 2]⟩ : Tensor Int) == some (⟨[2, 2], #[(-6), 8, 4, (-6)]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[3, 1, 2]⟩ : Tensor Int) (⟨[3], #[2, (-3), 0]⟩ : Tensor Int) == some (⟨[], #[3]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 1, 1], #[(-3)]⟩ : Tensor Int) (⟨[1], #[2]⟩ : Tensor Int) == some (⟨[1, 1], #[(-6)]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 3], #[5, 1, (-4), (-1), 3, 0]⟩ : Tensor Int) (⟨[3, 3], #[(-5), (-2), (-3), (-1), 4, (-2), (-2), 4, 5]⟩ : Tensor Int) == some (⟨[2, 3], #[(-18), (-22), (-37), 2, 14, (-3)]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[5, 0, 1]⟩ : Tensor Int) (⟨[4, 1], #[(-4), (-5), 4, 5]⟩ : Tensor Int) == none
#guard matmulOp (⟨[1, 2], #[3, 4]⟩ : Tensor Int) (⟨[2], #[(-3), 1]⟩ : Tensor Int) == some (⟨[1], #[(-5)]⟩ : Tensor Int)
#guard matmulOp (⟨[1], #[(-1)]⟩ : Tensor Int) (⟨[1, 2], #[(-2), 4]⟩ : Tensor Int) == some (⟨[2], #[2, (-4)]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 2], #[4, (-1)]⟩ : Tensor Int) (⟨[2, 1], #[(-2), 5]⟩ : Tensor Int) == some (⟨[1, 1], #[(-13)]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 3], #[(-1), (-5), (-4), (-4), 3, (-3), 1, 4, (-1)]⟩ : Tensor Int) (⟨[3], #[(-2), (-3), 0]⟩ : Tensor Int) == some (⟨[3], #[17, (-1), (-14)]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 2], #[(-2), 3, 1, (-3), 4, (-5)]⟩ : Tensor Int) (⟨[2], #[0, 1]⟩ : Tensor Int) == some (⟨[3], #[3, (-3), (-5)]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 1, 1], #[4]⟩ : Tensor Int) (⟨[1], #[0]⟩ : Tensor Int) == some (⟨[1, 1], #[0]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1, 1], #[2, (-2)]⟩ : Tensor Int) (⟨[1, 1], #[(-3)]⟩ : Tensor Int) == some (⟨[2, 1, 1], #[(-6), 6]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 3], #[3, 0, 2, (-2), 2, 5]⟩ : Tensor Int) (⟨[3, 2], #[3, 4, (-1), 0, (-4), 5]⟩ : Tensor Int) == some (⟨[2, 2], #[1, 22, (-28), 17]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 2], #[2, 5, 4, 1]⟩ : Tensor Int) (⟨[3, 3], #[(-5), (-5), 1, (-4), (-4), 5, 4, (-2), 5]⟩ : Tensor Int) == none
#guard matmulOp (⟨[2, 1], #[5, (-5)]⟩ : Tensor Int) (⟨[1], #[3]⟩ : Tensor Int) == some (⟨[2], #[15, (-15)]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 2], #[(-3), (-1)]⟩ : Tensor Int) (⟨[2, 1], #[5, (-4)]⟩ : Tensor Int) == some (⟨[1, 1], #[(-11)]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 2, 2], #[(-4), 5, 0, (-3), 1, (-2), (-5), 5, 2, 5, 4, (-2)]⟩ : Tensor Int) (⟨[2, 2], #[(-2), 2, 0, (-5)]⟩ : Tensor Int) == some (⟨[3, 2, 2], #[8, (-33), 0, 15, (-2), 12, 10, (-35), (-4), (-21), (-8), 18]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 3, 3], #[2, 4, (-4), (-1), (-4), 3, 0, 5, 0, 4, 3, 3, 3, (-2), (-3), 5, 4, (-4)]⟩ : Tensor Int) (⟨[4, 1], #[(-4), (-3), (-5), 2]⟩ : Tensor Int) == none
#guard matmulOp (⟨[1, 1], #[3]⟩ : Tensor Int) (⟨[1, 3], #[4, 4, (-5)]⟩ : Tensor Int) == some (⟨[1, 3], #[12, 12, (-15)]⟩ : Tensor Int)
#guard matmulOp (⟨[2], #[(-5), 5]⟩ : Tensor Int) (⟨[3, 3, 3], #[(-3), (-4), 2, (-4), 3, (-2), (-3), 1, 4, 3, (-4), 3, 0, 1, (-4), 0, (-2), (-3), (-1), (-5), 2, 2, (-2), 2, 0, 1, 2]⟩ : Tensor Int) == none
#guard matmulOp (⟨[2, 1], #[(-4), 1]⟩ : Tensor Int) (⟨[1, 3], #[0, 4, 2]⟩ : Tensor Int) == some (⟨[2, 3], #[0, (-16), (-8), 0, 4, 2]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 2], #[1, (-2), 1, 5]⟩ : Tensor Int) (⟨[2, 1], #[(-2), (-4)]⟩ : Tensor Int) == some (⟨[2, 1], #[6, (-22)]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 2, 1], #[2, (-1), 2, 5]⟩ : Tensor Int) (⟨[1], #[(-1)]⟩ : Tensor Int) == some (⟨[2, 2], #[(-2), 1, (-2), (-5)]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1], #[(-5), (-5)]⟩ : Tensor Int) (⟨[1, 1, 2], #[1, (-4)]⟩ : Tensor Int) == some (⟨[1, 2, 2], #[(-5), 20, (-5), 20]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 3], #[(-3), 2, (-5), 5, 1, (-1), (-1), 1, 2]⟩ : Tensor Int) (⟨[3, 2], #[3, 0, (-5), (-1), 3, (-2)]⟩ : Tensor Int) == some (⟨[3, 2], #[(-34), 8, 7, 1, (-2), (-5)]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[1, (-3), 1]⟩ : Tensor Int) (⟨[3], #[(-4), (-2), 3]⟩ : Tensor Int) == some (⟨[], #[5]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 2], #[(-2), (-2), (-5), 4, 0, 5]⟩ : Tensor Int) (⟨[3], #[4, 3, 2]⟩ : Tensor Int) == none
#guard matmulOp (⟨[1], #[(-4)]⟩ : Tensor Int) (⟨[3, 1, 3], #[2, (-2), (-2), 5, (-3), 5, 2, 1, (-5)]⟩ : Tensor Int) == some (⟨[3, 3], #[(-8), 8, 8, (-20), 12, (-20), (-8), (-4), 20]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1, 1], #[(-4), (-4)]⟩ : Tensor Int) (⟨[2, 1, 1], #[3, 0]⟩ : Tensor Int) == some (⟨[2, 1, 1], #[(-12), 0]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 3], #[(-5), 1, 4, (-4), 3, 5, (-4), 2, 0]⟩ : Tensor Int) (⟨[3, 3, 3], #[0, 5, 1, (-5), (-5), (-2), (-3), 3, 5, 0, (-5), 3, (-4), 3, 1, (-2), 3, (-5), 4, (-3), 4, (-1), 3, (-3), (-2), 5, 1]⟩ : Tensor Int) == some (⟨[3, 3, 3], #[(-17), (-18), 13, (-30), (-20), 15, (-10), (-30), (-8), (-12), 40, (-34), (-22), 44, (-34), (-8), 26, (-10), (-29), 38, (-19), (-29), 46, (-20), (-18), 18, (-22)]⟩ : Tensor Int)
#guard matmulOp (⟨[1], #[1]⟩ : Tensor Int) (⟨[1, 3], #[(-2), (-2), (-5)]⟩ : Tensor Int) == some (⟨[3], #[(-2), (-2), (-5)]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 3, 2], #[2, 0, 1, (-3), (-2), 1]⟩ : Tensor Int) (⟨[2, 3], #[0, 1, (-1), 1, (-3), (-2)]⟩ : Tensor Int) == some (⟨[1, 3, 3], #[0, 2, (-2), (-3), 10, 5, 1, (-5), 0]⟩ : Tensor Int)
#guard matmulOp (⟨[1], #[(-3)]⟩ : Tensor Int) (⟨[1, 1, 1], #[(-1)]⟩ : Tensor Int) == some (⟨[1, 1], #[3]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 1], #[1, (-3), 3]⟩ : Tensor Int) (⟨[2], #[(-5), (-3)]⟩ : Tensor Int) == none
#guard matmulOp (⟨[2, 1], #[5, 1]⟩ : Tensor Int) (⟨[1, 2], #[(-1), 5]⟩ : Tensor Int) == some (⟨[2, 2], #[(-5), 25, (-1), 5]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1], #[1, 2]⟩ : Tensor Int) (⟨[1, 1], #[(-5)]⟩ : Tensor Int) == some (⟨[2, 1], #[(-5), (-10)]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[(-4), 1, 4]⟩ : Tensor Int) (⟨[1, 3, 3], #[(-5), (-2), (-3), 2, (-1), (-3), 0, 3, (-4)]⟩ : Tensor Int) == some (⟨[1, 3], #[22, 19, (-7)]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[0, 1, 3]⟩ : Tensor Int) (⟨[3, 2], #[4, (-3), 4, (-4), 1, 5]⟩ : Tensor Int) == some (⟨[2], #[7, 11]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 3], #[(-4), 3, 4, 3, (-1), 5]⟩ : Tensor Int) (⟨[3, 2], #[(-2), (-5), (-3), 3, (-5), (-2)]⟩ : Tensor Int) == some (⟨[2, 2], #[(-21), 21, (-28), (-28)]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 3], #[3, (-5), (-5), (-4), (-5), 0]⟩ : Tensor Int) (⟨[4, 3], #[0, 2, (-4), 5, (-5), 4, 0, 5, (-4), (-1), 1, (-1)]⟩ : Tensor Int) == none
#guard matmulOp (⟨[3], #[4, 5, (-1)]⟩ : Tensor Int) (⟨[3, 2], #[(-5), 3, 4, 5, 2, (-5)]⟩ : Tensor Int) == some (⟨[2], #[(-2), 42]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 3, 3], #[(-2), (-2), 0, 4, 5, (-3), (-3), (-3), 2, 3, 3, 3, (-4), (-2), 4, (-5), 0, 4, 5, (-4), 4, (-4), 5, (-4), (-3), (-2), 4]⟩ : Tensor Int) (⟨[3, 4, 3], #[0, 4, (-5), 5, 2, 2, (-2), (-1), (-1), 1, 3, (-4), 4, 5, 2, 2, 4, (-2), (-2), 5, (-4), 2, 3, (-2), (-2), 5, (-3), (-2), 2, (-2), 3, (-5), (-1), 2, 5, (-4)]⟩ : Tensor Int) == none
#guard matmulOp (⟨[1, 2], #[3, (-3)]⟩ : Tensor Int) (⟨[2], #[(-3), 4]⟩ : Tensor Int) == some (⟨[1], #[(-21)]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1, 1], #[(-1), (-4)]⟩ : Tensor Int) (⟨[2], #[2, (-5)]⟩ : Tensor Int) == none
#guard matmulOp (⟨[3, 2, 2], #[(-4), (-2), (-2), (-5), (-5), (-2), 5, 3, (-1), 3, 2, (-4)]⟩ : Tensor Int) (⟨[2, 3], #[(-2), 1, (-4), (-1), (-3), (-4)]⟩ : Tensor Int) == some (⟨[3, 2, 3], #[10, 2, 24, 9, 13, 28, 12, 1, 28, (-13), (-4), (-32), (-1), (-10), (-8), 0, 14, 8]⟩ : Tensor Int)
#guard matmulOp (⟨[2], #[(-4), 0]⟩ : Tensor Int) (⟨[2, 3], #[3, 2, 2, (-3), 5, 5]⟩ : Tensor Int) == some (⟨[3], #[(-12), (-8), (-8)]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1], #[(-1), (-1)]⟩ : Tensor Int) (⟨[1, 1], #[5]⟩ : Tensor Int) == some (⟨[2, 1], #[(-5), (-5)]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 1], #[(-1), 0, 4]⟩ : Tensor Int) (⟨[3, 1, 3], #[1, 5, (-1), (-2), (-5), 5, (-2), (-4), 5]⟩ : Tensor Int) == some (⟨[3, 3, 3], #[(-1), (-5), 1, 0, 0, 0, 4, 20, (-4), 2, 5, (-5), 0, 0, 0, (-8), (-20), 20, 2, 4, (-5), 0, 0, 0, (-8), (-16), 20]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 1], #[3, 5, 1]⟩ : Tensor Int) (⟨[1, 3], #[(-5), (-3), 2]⟩ : Tensor Int) == some (⟨[3, 3], #[(-15), (-9), 6, (-25), (-15), 10, (-5), (-3), 2]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 1, 1], #[1, 3, (-4)]⟩ : Tensor Int) (⟨[1], #[(-1)]⟩ : Tensor Int) == some (⟨[3, 1], #[(-1), (-3), 4]⟩ : Tensor Int)
#guard matmulOp (⟨[2], #[(-2), (-5)]⟩ : Tensor Int) (⟨[2], #[5, 1]⟩ : Tensor Int) == some (⟨[], #[(-15)]⟩ : Tensor Int)
#guard matmulOp (⟨[1], #[(-5)]⟩ : Tensor Int) (⟨[1, 3], #[4, (-5), 2]⟩ : Tensor Int) == some (⟨[3], #[(-20), 25, (-10)]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 2, 3], #[2, (-4), 0, 0, 0, 1]⟩ : Tensor Int) (⟨[3, 3], #[5, 3, 1, (-2), (-1), 4, (-4), 4, (-3)]⟩ : Tensor Int) == some (⟨[1, 2, 3], #[18, 10, (-14), (-4), 4, (-3)]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 3], #[(-4), 2, 5, (-3), 3, 2, 1, (-3), 5]⟩ : Tensor Int) (⟨[3, 2], #[(-1), 0, (-2), 4, (-3), (-3)]⟩ : Tensor Int) == some (⟨[3, 2], #[(-15), (-7), (-9), 6, (-10), (-27)]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 2], #[4, (-5)]⟩ : Tensor Int) (⟨[2, 3], #[(-4), (-5), (-2), (-4), 5, 0]⟩ : Tensor Int) == some (⟨[1, 3], #[4, (-45), (-8)]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[0, (-4), 5]⟩ : Tensor Int) (⟨[3], #[(-1), 0, 0]⟩ : Tensor Int) == some (⟨[], #[0]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 2], #[1, (-5), (-5), 5]⟩ : Tensor Int) (⟨[3, 1], #[5, (-4), 5]⟩ : Tensor Int) == none
#guard matmulOp (⟨[1], #[(-1)]⟩ : Tensor Int) (⟨[1, 1, 3], #[(-3), 5, 4]⟩ : Tensor Int) == some (⟨[1, 3], #[3, (-5), (-4)]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[5, 5, 2]⟩ : Tensor Int) (⟨[3, 3], #[0, 1, (-2), (-1), (-1), (-1), (-5), (-2), (-5)]⟩ : Tensor Int) == some (⟨[3], #[(-15), (-4), (-25)]⟩ : Tensor Int)
#guard matmulOp (⟨[1], #[(-5)]⟩ : Tensor Int) (⟨[1, 2], #[5, 1]⟩ : Tensor Int) == some (⟨[2], #[(-25), (-5)]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1], #[(-2), (-4)]⟩ : Tensor Int) (⟨[1, 3], #[5, (-4), 0]⟩ : Tensor Int) == some (⟨[2, 3], #[(-10), 8, 0, (-20), 16, 0]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[5, 0, 4]⟩ : Tensor Int) (⟨[3, 3], #[(-1), (-1), (-2), 1, (-2), 5, (-1), 2, (-2)]⟩ : Tensor Int) == some (⟨[3], #[(-9), 3, (-18)]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[0, (-5), 3]⟩ : Tensor Int) (⟨[3, 3], #[5, (-1), (-2), 1, 0, (-5), 2, 3, (-2)]⟩ : Tensor Int) == some (⟨[3], #[1, 9, 19]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 3, 3], #[4, 0, 3, (-4), (-2), (-5), (-1), (-2), 3, 4, (-2), 0, 4, (-4), 1, (-5), (-5), 0, 5, (-3), 2, 2, 2, (-2), 1, (-1), (-2)]⟩ : Tensor Int) (⟨[3, 3], #[(-4), (-3), (-1), (-4), 1, 0, 0, (-2), (-4)]⟩ : Tensor Int) == some (⟨[3, 3, 3], #[(-16), (-18), (-16), 24, 20, 24, 12, (-5), (-11), (-8), (-14), (-4), 0, (-18), (-8), 40, 10, 5, (-8), (-22), (-13), (-16), 0, 6, 0, 0, 7]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[(-4), (-4), (-4)]⟩ : Tensor Int) (⟨[3, 3], #[(-1), (-4), (-3), (-1), (-3), (-4), 1, 1, (-4)]⟩ : Tensor Int) == some (⟨[3], #[4, 24, 44]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[1, 4, (-5)]⟩ : Tensor Int) (⟨[3], #[3, 0, (-1)]⟩ : Tensor Int) == some (⟨[], #[8]⟩ : Tensor Int)
#guard matmulOp (⟨[2, 1], #[0, 5]⟩ : Tensor Int) (⟨[1, 1, 2], #[2, 5]⟩ : Tensor Int) == some (⟨[1, 2, 2], #[0, 0, 10, 25]⟩ : Tensor Int)
#guard matmulOp (⟨[3], #[4, 5, (-2)]⟩ : Tensor Int) (⟨[3], #[(-2), (-5), 0]⟩ : Tensor Int) == some (⟨[], #[(-33)]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 2, 3], #[0, 5, 4, 5, (-5), 1]⟩ : Tensor Int) (⟨[3, 1], #[5, 4, 1]⟩ : Tensor Int) == some (⟨[1, 2, 1], #[24, 6]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 3], #[(-3), (-2), 5]⟩ : Tensor Int) (⟨[3], #[(-5), (-5), (-2)]⟩ : Tensor Int) == some (⟨[1], #[15]⟩ : Tensor Int)
#guard matmulOp (⟨[3, 1, 2], #[5, 3, (-3), (-5), (-5), 3]⟩ : Tensor Int) (⟨[2, 2], #[1, 0, 2, 0]⟩ : Tensor Int) == some (⟨[3, 1, 2], #[11, 0, (-13), 0, 1, 0]⟩ : Tensor Int)
#guard matmulOp (⟨[2], #[(-4), (-1)]⟩ : Tensor Int) (⟨[2], #[(-5), 1]⟩ : Tensor Int) == some (⟨[], #[19]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 2, 2], #[0, (-1), (-3), (-1)]⟩ : Tensor Int) (⟨[1, 2, 2], #[1, 3, 1, 3]⟩ : Tensor Int) == some (⟨[1, 2, 2], #[(-1), (-3), (-4), (-12)]⟩ : Tensor Int)
#guard matmulOp (⟨[1, 3], #[5, 2, 1]⟩ : Tensor Int) (⟨[3, 2], #[(-1), 4, (-1), 2, 2, (-4)]⟩ : Tensor Int) == some (⟨[1, 2], #[(-5), 20]⟩ : Tensor Int)

/-! ## indexing -/

#guard indexOp (⟨[2], #[1, 5]⟩ : Tensor Int) [.all] == some (⟨[2], #[1, 5]⟩ : Tensor Int)
#guard indexOp (⟨[3, 4], #[1, 3, 4, 3, 3, 2, 3, 4, 1, (-1), 2, (-2)]⟩ : Tensor Int) [] == some (⟨[3, 4], #[1, 3, 4, 3, 3, 2, 3, 4, 1, (-1), 2, (-2)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 1, 1], #[5, 3, (-4)]⟩ : Tensor Int) [(.range 1 1)] == some (⟨[0, 1, 1], #[]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[(-1), (-5), 2, 4]⟩ : Tensor Int) [] == some (⟨[4], #[(-1), (-5), 2, 4]⟩ : Tensor Int)
#guard indexOp (⟨[4, 3, 2], #[3, 1, (-4), (-2), 5, (-4), 1, (-2), (-4), 3, (-2), (-2), 0, (-2), (-5), 4, 2, 5, 1, 1, 5, (-4), 4, (-3)]⟩ : Tensor Int) [(.one 3), (.one 2), .all] == some (⟨[2], #[4, (-3)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 3], #[3, 3, 2, (-3), 5, (-2), 5, (-1), 0]⟩ : Tensor Int) [(.range 0 2)] == some (⟨[2, 3], #[3, 3, 2, (-3), 5, (-2)]⟩ : Tensor Int)
#guard indexOp (⟨[3], #[2, 5, 0]⟩ : Tensor Int) [] == some (⟨[3], #[2, 5, 0]⟩ : Tensor Int)
#guard indexOp (⟨[3, 4, 1], #[2, 4, 2, (-2), 2, 0, 0, (-5), (-1), (-4), 3, 3]⟩ : Tensor Int) [.all, (.range 3 4), (.range 1 1)] == some (⟨[3, 1, 0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[4, 2], #[(-1), 1, (-4), (-2), (-1), (-2), (-1), 1]⟩ : Tensor Int) [.all] == some (⟨[4, 2], #[(-1), 1, (-4), (-2), (-1), (-2), (-1), 1]⟩ : Tensor Int)
#guard indexOp (⟨[2, 1, 1], #[2, 3]⟩ : Tensor Int) [(.range 0 1), (.range 0 0), .all] == some (⟨[1, 0, 1], #[]⟩ : Tensor Int)
#guard indexOp (⟨[1], #[3]⟩ : Tensor Int) [.all] == some (⟨[1], #[3]⟩ : Tensor Int)
#guard indexOp (⟨[3], #[1, 3, (-5)]⟩ : Tensor Int) [] == some (⟨[3], #[1, 3, (-5)]⟩ : Tensor Int)
#guard indexOp (⟨[1, 1], #[4]⟩ : Tensor Int) [(.one 1)] == none
#guard indexOp (⟨[1], #[1]⟩ : Tensor Int) [] == some (⟨[1], #[1]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[3, (-2), (-1), (-4)]⟩ : Tensor Int) [] == some (⟨[4], #[3, (-2), (-1), (-4)]⟩ : Tensor Int)
#guard indexOp (⟨[4, 4], #[(-5), 0, 1, (-2), (-5), 3, (-1), (-4), (-2), 0, (-5), 0, 3, 0, 1, 2]⟩ : Tensor Int) [] == some (⟨[4, 4], #[(-5), 0, 1, (-2), (-5), 3, (-1), (-4), (-2), 0, (-5), 0, 3, 0, 1, 2]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[(-2), (-4), (-1), 0]⟩ : Tensor Int) [] == some (⟨[4], #[(-2), (-4), (-1), 0]⟩ : Tensor Int)
#guard indexOp (⟨[3], #[(-1), 4, 0]⟩ : Tensor Int) [(.range 3 3)] == some (⟨[0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[2], #[0, (-3)]⟩ : Tensor Int) [(.one 0)] == some (⟨[], #[0]⟩ : Tensor Int)
#guard indexOp (⟨[1], #[(-1)]⟩ : Tensor Int) [.all] == some (⟨[1], #[(-1)]⟩ : Tensor Int)
#guard indexOp (⟨[2, 1, 1], #[4, 5]⟩ : Tensor Int) [.all, (.range 1 1), (.one 0)] == some (⟨[2, 0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[1, 1, 1], #[(-2)]⟩ : Tensor Int) [.all, (.one 0), (.one 0)] == some (⟨[1], #[(-2)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 3, 3], #[(-5), 5, 5, 3, 2, 3, (-3), (-2), (-2), (-2), (-1), 0, (-5), (-2), (-1), (-3), 5, (-3), 5, (-1), (-1), (-2), 4, 5, (-1), 1, (-3)]⟩ : Tensor Int) [.all, .all, (.range 1 2)] == some (⟨[3, 3, 1], #[5, 2, (-2), (-1), (-2), 5, (-1), 4, 1]⟩ : Tensor Int)
#guard indexOp (⟨[3, 2], #[(-3), (-5), (-1), (-4), (-4), (-2)]⟩ : Tensor Int) [(.one 0), (.one 1)] == some (⟨[], #[(-5)]⟩ : Tensor Int)
#guard indexOp (⟨[1, 1], #[(-1)]⟩ : Tensor Int) [] == some (⟨[1, 1], #[(-1)]⟩ : Tensor Int)
#guard indexOp (⟨[1, 2], #[0, 4]⟩ : Tensor Int) [(.one 0), (.one 0)] == some (⟨[], #[0]⟩ : Tensor Int)
#guard indexOp (⟨[2, 3, 1], #[(-2), (-3), (-4), 1, 4, (-3)]⟩ : Tensor Int) [.all] == some (⟨[2, 3, 1], #[(-2), (-3), (-4), 1, 4, (-3)]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[(-4), (-3), (-4), 4]⟩ : Tensor Int) [] == some (⟨[4], #[(-4), (-3), (-4), 4]⟩ : Tensor Int)
#guard indexOp (⟨[4, 2], #[(-3), (-4), 4, (-1), 3, (-4), 5, (-5)]⟩ : Tensor Int) [.all, (.range 1 2)] == some (⟨[4, 1], #[(-4), (-1), (-4), (-5)]⟩ : Tensor Int)
#guard indexOp (⟨[2, 1, 2], #[(-2), (-5), 4, (-3)]⟩ : Tensor Int) [.all, (.range 1 1), .all] == some (⟨[2, 0, 2], #[]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[(-4), (-2), (-4), 0]⟩ : Tensor Int) [.all] == some (⟨[4], #[(-4), (-2), (-4), 0]⟩ : Tensor Int)
#guard indexOp (⟨[1, 1], #[2]⟩ : Tensor Int) [] == some (⟨[1, 1], #[2]⟩ : Tensor Int)
#guard indexOp (⟨[4, 1], #[5, 3, (-4), 2]⟩ : Tensor Int) [(.range 4 4), (.one 1)] == none
#guard indexOp (⟨[3], #[(-1), 5, 0]⟩ : Tensor Int) [.all] == some (⟨[3], #[(-1), 5, 0]⟩ : Tensor Int)
#guard indexOp (⟨[3, 1, 1], #[(-3), 2, (-1)]⟩ : Tensor Int) [(.one 2), (.range 0 1)] == some (⟨[1, 1], #[(-1)]⟩ : Tensor Int)
#guard indexOp (⟨[2, 3, 2], #[(-3), 4, 2, (-3), (-4), (-1), 1, 1, 1, 0, (-2), (-4)]⟩ : Tensor Int) [] == some (⟨[2, 3, 2], #[(-3), 4, 2, (-3), (-4), (-1), 1, 1, 1, 0, (-2), (-4)]⟩ : Tensor Int)
#guard indexOp (⟨[3], #[1, (-4), (-3)]⟩ : Tensor Int) [] == some (⟨[3], #[1, (-4), (-3)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 1], #[2, (-4), (-4)]⟩ : Tensor Int) [.all, (.range 0 0)] == some (⟨[3, 0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[(-2), (-3), (-4), (-3)]⟩ : Tensor Int) [] == some (⟨[4], #[(-2), (-3), (-4), (-3)]⟩ : Tensor Int)
#guard indexOp (⟨[4, 1, 3], #[5, (-2), 1, (-3), 4, 2, 2, 0, (-2), 2, 3, (-5)]⟩ : Tensor Int) [(.one 0)] == some (⟨[1, 3], #[5, (-2), 1]⟩ : Tensor Int)
#guard indexOp (⟨[3], #[2, 1, 0]⟩ : Tensor Int) [(.one 0)] == some (⟨[], #[2]⟩ : Tensor Int)
#guard indexOp (⟨[1], #[0]⟩ : Tensor Int) [] == some (⟨[1], #[0]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[3, (-5), 5, (-1)]⟩ : Tensor Int) [] == some (⟨[4], #[3, (-5), 5, (-1)]⟩ : Tensor Int)
#guard indexOp (⟨[4, 2, 1], #[(-1), (-2), (-2), (-5), 3, 5, (-1), 1]⟩ : Tensor Int) [(.one 0)] == some (⟨[2, 1], #[(-1), (-2)]⟩ : Tensor Int)
#guard indexOp (⟨[1, 4], #[5, (-2), (-2), (-5)]⟩ : Tensor Int) [] == some (⟨[1, 4], #[5, (-2), (-2), (-5)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 1], #[4, 3, (-1)]⟩ : Tensor Int) [.all] == some (⟨[3, 1], #[4, 3, (-1)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 2], #[0, (-5), 4, 0, 4, (-2)]⟩ : Tensor Int) [(.range 0 3)] == some (⟨[3, 2], #[0, (-5), 4, 0, 4, (-2)]⟩ : Tensor Int)
#guard indexOp (⟨[2, 4, 2], #[(-4), (-1), 5, 4, (-1), 4, 5, 4, (-5), (-2), 5, 4, (-4), (-5), 3, (-1)]⟩ : Tensor Int) [(.range 1 1), (.range 1 3)] == some (⟨[0, 2, 2], #[]⟩ : Tensor Int)
#guard indexOp (⟨[1], #[(-1)]⟩ : Tensor Int) [] == some (⟨[1], #[(-1)]⟩ : Tensor Int)
#guard indexOp (⟨[2, 4, 4], #[(-2), (-1), 4, (-2), 5, 0, (-5), (-2), (-4), (-2), 3, (-3), (-1), (-2), 5, (-4), (-3), 1, (-3), (-1), (-4), (-5), 1, (-3), (-4), 0, 0, (-2), (-3), 4, 4, (-5)]⟩ : Tensor Int) [] == some (⟨[2, 4, 4], #[(-2), (-1), 4, (-2), 5, 0, (-5), (-2), (-4), (-2), 3, (-3), (-1), (-2), 5, (-4), (-3), 1, (-3), (-1), (-4), (-5), 1, (-3), (-4), 0, 0, (-2), (-3), 4, 4, (-5)]⟩ : Tensor Int)
#guard indexOp (⟨[4, 4], #[5, 5, 1, 0, (-4), (-1), (-2), (-5), (-3), 0, (-2), 2, (-2), (-2), 5, (-4)]⟩ : Tensor Int) [] == some (⟨[4, 4], #[5, 5, 1, 0, (-4), (-1), (-2), (-5), (-3), 0, (-2), 2, (-2), (-2), 5, (-4)]⟩ : Tensor Int)
#guard indexOp (⟨[4, 1], #[(-1), 1, (-5), 0]⟩ : Tensor Int) [.all] == some (⟨[4, 1], #[(-1), 1, (-5), 0]⟩ : Tensor Int)
#guard indexOp (⟨[3, 3, 4], #[(-3), (-4), (-1), (-5), 3, 5, 0, 2, (-2), 5, 4, 0, 4, (-5), (-1), (-1), (-4), 3, (-2), (-5), (-3), 4, 3, 0, 2, 1, 0, 3, (-5), 3, 5, 0, (-5), 3, 0, (-5)]⟩ : Tensor Int) [.all] == some (⟨[3, 3, 4], #[(-3), (-4), (-1), (-5), 3, 5, 0, 2, (-2), 5, 4, 0, 4, (-5), (-1), (-1), (-4), 3, (-2), (-5), (-3), 4, 3, 0, 2, 1, 0, 3, (-5), 3, 5, 0, (-5), 3, 0, (-5)]⟩ : Tensor Int)
#guard indexOp (⟨[4, 4], #[(-2), (-2), 1, 2, (-4), (-1), (-5), 2, 4, 1, (-4), (-1), (-4), 2, 2, (-1)]⟩ : Tensor Int) [] == some (⟨[4, 4], #[(-2), (-2), 1, 2, (-4), (-1), (-5), 2, 4, 1, (-4), (-1), (-4), 2, 2, (-1)]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[(-3), (-5), 4, (-5)]⟩ : Tensor Int) [(.range 1 4)] == some (⟨[3], #[(-5), 4, (-5)]⟩ : Tensor Int)
#guard indexOp (⟨[3], #[(-5), (-4), 0]⟩ : Tensor Int) [] == some (⟨[3], #[(-5), (-4), 0]⟩ : Tensor Int)
#guard indexOp (⟨[3, 2], #[(-4), (-3), (-4), 2, 3, 4]⟩ : Tensor Int) [(.range 1 1)] == some (⟨[0, 2], #[]⟩ : Tensor Int)
#guard indexOp (⟨[2, 1, 1], #[5, 5]⟩ : Tensor Int) [(.one 1)] == some (⟨[1, 1], #[5]⟩ : Tensor Int)
#guard indexOp (⟨[2, 1], #[4, 2]⟩ : Tensor Int) [(.range 0 0)] == some (⟨[0, 1], #[]⟩ : Tensor Int)
#guard indexOp (⟨[1], #[1]⟩ : Tensor Int) [.all] == some (⟨[1], #[1]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[4, 1, 0, (-4)]⟩ : Tensor Int) [] == some (⟨[4], #[4, 1, 0, (-4)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 4, 2], #[1, (-5), 1, 0, (-3), (-1), 3, 1, (-3), (-1), 4, 1, 1, 2, (-4), 5, 5, 1, (-4), (-1), (-3), 2, 5, 5]⟩ : Tensor Int) [.all, (.range 0 4), .all] == some (⟨[3, 4, 2], #[1, (-5), 1, 0, (-3), (-1), 3, 1, (-3), (-1), 4, 1, 1, 2, (-4), 5, 5, 1, (-4), (-1), (-3), 2, 5, 5]⟩ : Tensor Int)
#guard indexOp (⟨[2, 3], #[(-2), (-4), 0, (-4), 0, (-1)]⟩ : Tensor Int) [(.range 1 1), (.one 2)] == some (⟨[0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[1], #[0]⟩ : Tensor Int) [.all] == some (⟨[1], #[0]⟩ : Tensor Int)
#guard indexOp (⟨[3], #[(-1), 0, 2]⟩ : Tensor Int) [] == some (⟨[3], #[(-1), 0, 2]⟩ : Tensor Int)
#guard indexOp (⟨[1, 3], #[(-2), 0, (-4)]⟩ : Tensor Int) [] == some (⟨[1, 3], #[(-2), 0, (-4)]⟩ : Tensor Int)
#guard indexOp (⟨[4, 2, 1], #[2, 5, 2, (-5), (-5), 1, (-1), (-3)]⟩ : Tensor Int) [(.range 0 4), (.one 1)] == some (⟨[4, 1], #[5, (-5), 1, (-3)]⟩ : Tensor Int)
#guard indexOp (⟨[1, 1, 4], #[5, (-2), 0, (-3)]⟩ : Tensor Int) [.all, (.range 0 1), (.range 4 4)] == some (⟨[1, 1, 0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[(-1), (-5), 1, 0]⟩ : Tensor Int) [] == some (⟨[4], #[(-1), (-5), 1, 0]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[(-5), 1, (-3), (-5)]⟩ : Tensor Int) [] == some (⟨[4], #[(-5), 1, (-3), (-5)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 2, 4], #[(-4), (-1), 2, (-5), 3, (-2), (-2), (-1), 0, 0, 5, (-5), (-1), 2, (-1), (-2), 1, 0, 2, 0, 2, (-4), (-5), (-3)]⟩ : Tensor Int) [(.one 1), .all, (.range 2 2)] == some (⟨[2, 0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[4, 3, 3], #[(-3), 0, (-3), (-4), (-5), 5, 1, 2, (-3), (-5), (-1), (-1), 3, 2, 1, 0, (-2), (-5), (-4), 5, (-2), (-1), (-3), (-5), 0, (-4), (-1), (-5), (-2), 5, (-1), 1, (-1), (-1), (-1), 2]⟩ : Tensor Int) [(.range 4 4)] == some (⟨[0, 3, 3], #[]⟩ : Tensor Int)
#guard indexOp (⟨[3, 1], #[4, (-1), (-4)]⟩ : Tensor Int) [] == some (⟨[3, 1], #[4, (-1), (-4)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 4, 4], #[(-5), 3, (-3), (-4), 4, 0, 1, 0, (-5), (-1), 4, (-1), (-5), 2, 3, (-4), 5, (-5), (-5), 2, (-1), (-3), (-4), (-2), 4, 5, 0, (-4), 2, 4, 3, (-1), 2, (-3), 5, 5, (-2), 1, 2, (-3), 5, 3, 3, (-1), (-5), 0, (-3), (-2)]⟩ : Tensor Int) [(.range 0 2), .all, (.one 3)] == some (⟨[2, 4], #[(-4), 0, (-1), (-4), 2, (-2), (-4), (-1)]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[(-2), (-3), (-5), (-2)]⟩ : Tensor Int) [.all] == some (⟨[4], #[(-2), (-3), (-5), (-2)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 3, 1], #[(-5), 0, 1, (-4), 3, (-5), 1, (-1), 5]⟩ : Tensor Int) [(.one 1)] == some (⟨[3, 1], #[(-4), 3, (-5)]⟩ : Tensor Int)
#guard indexOp (⟨[3, 3, 3], #[4, (-1), (-2), 5, 1, 2, 0, 1, (-4), (-2), 3, 5, (-1), (-3), (-1), 0, 1, 0, (-4), 0, 1, (-2), 5, 2, (-5), 3, 3]⟩ : Tensor Int) [] == some (⟨[3, 3, 3], #[4, (-1), (-2), 5, 1, 2, 0, 1, (-4), (-2), 3, 5, (-1), (-3), (-1), 0, 1, 0, (-4), 0, 1, (-2), 5, 2, (-5), 3, 3]⟩ : Tensor Int)
#guard indexOp (⟨[1, 4, 2], #[4, 5, (-4), 2, (-2), 1, (-2), (-1)]⟩ : Tensor Int) [.all, (.one 3), (.one 1)] == some (⟨[1], #[(-1)]⟩ : Tensor Int)
#guard indexOp (⟨[2], #[0, 2]⟩ : Tensor Int) [.all] == some (⟨[2], #[0, 2]⟩ : Tensor Int)
#guard indexOp (⟨[1, 1], #[0]⟩ : Tensor Int) [.all, (.one 0)] == some (⟨[1], #[0]⟩ : Tensor Int)
#guard indexOp (⟨[1], #[3]⟩ : Tensor Int) [(.range 0 0)] == some (⟨[0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[3, 3, 4], #[(-4), 0, (-1), (-5), (-5), 2, 5, 3, (-4), 0, 4, (-5), 0, 2, (-2), 4, (-5), (-5), 1, (-2), (-1), (-4), (-4), (-3), (-5), (-2), 0, (-4), (-4), (-4), (-3), 1, 5, 3, 2, (-1)]⟩ : Tensor Int) [(.range 0 0), (.range 2 2)] == some (⟨[0, 0, 4], #[]⟩ : Tensor Int)
#guard indexOp (⟨[3, 3], #[(-2), 2, 4, 5, 4, 1, 0, (-5), (-1)]⟩ : Tensor Int) [] == some (⟨[3, 3], #[(-2), 2, 4, 5, 4, 1, 0, (-5), (-1)]⟩ : Tensor Int)
#guard indexOp (⟨[4, 4], #[5, 4, (-3), 4, 2, 2, 3, (-5), 4, (-1), 3, 5, (-2), (-4), 5, (-2)]⟩ : Tensor Int) [.all, (.range 4 4)] == some (⟨[4, 0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[2], #[(-2), (-1)]⟩ : Tensor Int) [] == some (⟨[2], #[(-2), (-1)]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[4, 0, 5, (-2)]⟩ : Tensor Int) [(.range 3 3)] == some (⟨[0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[4], #[(-4), 4, (-2), 2]⟩ : Tensor Int) [] == some (⟨[4], #[(-4), 4, (-2), 2]⟩ : Tensor Int)
#guard indexOp (⟨[1], #[4]⟩ : Tensor Int) [] == some (⟨[1], #[4]⟩ : Tensor Int)
#guard indexOp (⟨[2, 2, 3], #[0, 0, (-5), (-2), (-2), 0, (-1), (-5), (-1), (-2), 3, 0]⟩ : Tensor Int) [(.one 0), .all, (.one 2)] == some (⟨[2], #[(-5), 0]⟩ : Tensor Int)
#guard indexOp (⟨[2, 3], #[(-4), 3, 1, (-4), 5, 4]⟩ : Tensor Int) [] == some (⟨[2, 3], #[(-4), 3, 1, (-4), 5, 4]⟩ : Tensor Int)
#guard indexOp (⟨[4, 2], #[0, (-2), 2, 0, 0, 0, (-4), 4]⟩ : Tensor Int) [] == some (⟨[4, 2], #[0, (-2), 2, 0, 0, 0, (-4), 4]⟩ : Tensor Int)
#guard indexOp (⟨[1], #[(-3)]⟩ : Tensor Int) [] == some (⟨[1], #[(-3)]⟩ : Tensor Int)
#guard indexOp (⟨[2, 2], #[(-2), 0, 2, (-1)]⟩ : Tensor Int) [(.one 0)] == some (⟨[2], #[(-2), 0]⟩ : Tensor Int)
#guard indexOp (⟨[1, 2, 2], #[3, 0, 2, 3]⟩ : Tensor Int) [.all, (.range 0 1)] == some (⟨[1, 1, 2], #[3, 0]⟩ : Tensor Int)
#guard indexOp (⟨[3, 2, 4], #[2, (-3), (-2), 1, 3, 5, 1, 4, (-2), 5, 4, 0, 0, (-5), 0, 2, 5, 4, 0, (-2), 1, 0, (-2), (-2)]⟩ : Tensor Int) [(.range 0 3)] == some (⟨[3, 2, 4], #[2, (-3), (-2), 1, 3, 5, 1, 4, (-2), 5, 4, 0, 0, (-5), 0, 2, 5, 4, 0, (-2), 1, 0, (-2), (-2)]⟩ : Tensor Int)
#guard indexOp (⟨[1, 3, 2], #[4, (-1), (-3), 4, 2, (-4)]⟩ : Tensor Int) [(.range 0 1), (.range 2 2), (.one 1)] == some (⟨[1, 0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[1, 4, 1], #[(-1), (-5), 4, (-5)]⟩ : Tensor Int) [(.range 1 1), (.range 1 1), (.range 1 1)] == some (⟨[0, 0, 0], #[]⟩ : Tensor Int)
#guard indexOp (⟨[1], #[0]⟩ : Tensor Int) [(.one 0)] == some (⟨[], #[0]⟩ : Tensor Int)
#guard indexOp (⟨[1, 3], #[5, 4, (-5)]⟩ : Tensor Int) [(.one 0)] == some (⟨[3], #[5, 4, (-5)]⟩ : Tensor Int)
#guard indexOp (⟨[2, 2, 4], #[2, 2, (-1), 4, (-2), 1, 2, 0, 3, 2, (-4), 1, (-5), 4, (-3), 3]⟩ : Tensor Int) [] == some (⟨[2, 2, 4], #[2, 2, (-1), 4, (-2), 1, 2, 0, 3, 2, (-4), 1, (-5), 4, (-3), 3]⟩ : Tensor Int)

/-! ## transpose -/

#guard transposeOp (⟨[], #[(-3)]⟩ : Tensor Int) == some (⟨[], #[(-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[3], #[5, 4, (-4)]⟩ : Tensor Int) == some (⟨[3], #[5, 4, (-4)]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 3], #[(-5), (-2), 4, (-4), 0, (-1), 3, 4, (-5)]⟩ : Tensor Int) == some (⟨[3, 3], #[(-5), (-4), 3, (-2), 0, 4, 4, (-1), (-5)]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[(-1)]⟩ : Tensor Int) == some (⟨[], #[(-1)]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 2, 3], #[3, 4, 0, (-3), (-5), 5, 3, 2, (-4), (-1), 5, (-4), 0, (-4), 2, 5, (-5), (-2)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[], #[5]⟩ : Tensor Int) == some (⟨[], #[5]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 1, 3], #[(-5), 3, (-5), 0, (-4), (-5), 3, (-4), 2]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3, 2, 3], #[4, (-5), (-5), (-3), 4, 5, (-2), 0, (-1), 2, 2, 5, 1, 5, (-5), 5, 0, (-1)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[2, 1, 1], #[(-3), (-5)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[2], #[(-5), (-3)]⟩ : Tensor Int) == some (⟨[2], #[(-5), (-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[2], #[1, (-3)]⟩ : Tensor Int) == some (⟨[2], #[1, (-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 3, 3], #[1, (-3), (-5), (-5), (-5), 5, 1, 2, (-5), (-1), 2, 0, (-1), (-4), 0, (-2), 2, (-5)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[1, 2], #[0, 3]⟩ : Tensor Int) == some (⟨[2, 1], #[0, 3]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[1]⟩ : Tensor Int) == some (⟨[], #[1]⟩ : Tensor Int)
#guard transposeOp (⟨[1], #[1]⟩ : Tensor Int) == some (⟨[1], #[1]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 3], #[(-3), (-5), (-2), (-1), (-2), 2, (-2), 3, 5]⟩ : Tensor Int) == some (⟨[3, 3], #[(-3), (-1), (-2), (-5), (-2), 3, (-2), 2, 5]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 3], #[3, 0, (-4), (-4), 0, (-5)]⟩ : Tensor Int) == some (⟨[3, 2], #[3, (-4), 0, 0, (-4), (-5)]⟩ : Tensor Int)
#guard transposeOp (⟨[1], #[1]⟩ : Tensor Int) == some (⟨[1], #[1]⟩ : Tensor Int)
#guard transposeOp (⟨[3], #[0, (-1), 2]⟩ : Tensor Int) == some (⟨[3], #[0, (-1), 2]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[(-1)]⟩ : Tensor Int) == some (⟨[], #[(-1)]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 2, 3], #[(-4), (-3), 0, 3, (-3), (-4), 3, (-1), 2, 2, 1, 2]⟩ : Tensor Int) == none
#guard transposeOp (⟨[], #[(-4)]⟩ : Tensor Int) == some (⟨[], #[(-4)]⟩ : Tensor Int)
#guard transposeOp (⟨[3], #[1, (-3), 3]⟩ : Tensor Int) == some (⟨[3], #[1, (-3), 3]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 1], #[5, 3]⟩ : Tensor Int) == some (⟨[1, 2], #[5, 3]⟩ : Tensor Int)
#guard transposeOp (⟨[2], #[(-5), (-5)]⟩ : Tensor Int) == some (⟨[2], #[(-5), (-5)]⟩ : Tensor Int)
#guard transposeOp (⟨[1], #[4]⟩ : Tensor Int) == some (⟨[1], #[4]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[(-3)]⟩ : Tensor Int) == some (⟨[], #[(-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[1], #[0]⟩ : Tensor Int) == some (⟨[1], #[0]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 1, 1], #[(-2), 5]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3], #[0, 3, 1]⟩ : Tensor Int) == some (⟨[3], #[0, 3, 1]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 1], #[(-1), (-3), (-5)]⟩ : Tensor Int) == some (⟨[1, 3], #[(-1), (-3), (-5)]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[(-2)]⟩ : Tensor Int) == some (⟨[], #[(-2)]⟩ : Tensor Int)
#guard transposeOp (⟨[1], #[1]⟩ : Tensor Int) == some (⟨[1], #[1]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 3], #[1, (-5), 2, (-1), (-2), 5]⟩ : Tensor Int) == some (⟨[3, 2], #[1, (-1), (-5), (-2), 2, 5]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 2], #[3, 5, 2, 1, (-5), (-1)]⟩ : Tensor Int) == some (⟨[2, 3], #[3, 2, (-5), 5, 1, (-1)]⟩ : Tensor Int)
#guard transposeOp (⟨[3], #[4, 2, 2]⟩ : Tensor Int) == some (⟨[3], #[4, 2, 2]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[(-2)]⟩ : Tensor Int) == some (⟨[], #[(-2)]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 1, 2], #[2, 4, 0, 1]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3, 1, 3], #[(-5), 5, (-1), (-2), (-1), 0, (-5), 1, (-2)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[], #[1]⟩ : Tensor Int) == some (⟨[], #[1]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 2], #[1, (-2), 5, 1]⟩ : Tensor Int) == some (⟨[2, 2], #[1, 5, (-2), 1]⟩ : Tensor Int)
#guard transposeOp (⟨[3], #[4, 2, (-1)]⟩ : Tensor Int) == some (⟨[3], #[4, 2, (-1)]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 2, 1], #[2, (-4), (-4), (-5)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[1, 1], #[(-3)]⟩ : Tensor Int) == some (⟨[1, 1], #[(-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 3, 1], #[(-4), 0, 5, 3, 0, (-1)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3, 3, 1], #[(-2), (-2), 3, 0, 4, (-5), 5, (-1), (-3)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3, 3, 2], #[5, (-5), (-3), (-2), (-4), (-4), 5, 2, 2, 0, 0, (-4), 0, 1, 3, (-4), (-4), 1]⟩ : Tensor Int) == none
#guard transposeOp (⟨[], #[(-2)]⟩ : Tensor Int) == some (⟨[], #[(-2)]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[3]⟩ : Tensor Int) == some (⟨[], #[3]⟩ : Tensor Int)
#guard transposeOp (⟨[2], #[(-4), 4]⟩ : Tensor Int) == some (⟨[2], #[(-4), 4]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 2, 2], #[(-5), (-2), 2, 2, 3, 5, (-4), (-5)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[2], #[(-1), 0]⟩ : Tensor Int) == some (⟨[2], #[(-1), 0]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[4]⟩ : Tensor Int) == some (⟨[], #[4]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 2, 2], #[1, (-2), 1, 1, 5, 4, (-5), (-4)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3, 2], #[(-4), 1, 3, 0, 0, 3]⟩ : Tensor Int) == some (⟨[2, 3], #[(-4), 3, 0, 1, 0, 3]⟩ : Tensor Int)
#guard transposeOp (⟨[1, 2], #[5, 0]⟩ : Tensor Int) == some (⟨[2, 1], #[5, 0]⟩ : Tensor Int)
#guard transposeOp (⟨[1, 1, 3], #[(-4), (-3), (-2)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3, 3], #[1, (-2), (-2), (-4), 2, (-4), 1, (-4), 3]⟩ : Tensor Int) == some (⟨[3, 3], #[1, (-4), 1, (-2), 2, (-4), (-2), (-4), 3]⟩ : Tensor Int)
#guard transposeOp (⟨[3], #[(-2), (-3), (-4)]⟩ : Tensor Int) == some (⟨[3], #[(-2), (-3), (-4)]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 1], #[(-3), 0, (-5)]⟩ : Tensor Int) == some (⟨[1, 3], #[(-3), 0, (-5)]⟩ : Tensor Int)
#guard transposeOp (⟨[1, 2], #[(-3), (-4)]⟩ : Tensor Int) == some (⟨[2, 1], #[(-3), (-4)]⟩ : Tensor Int)
#guard transposeOp (⟨[1], #[(-3)]⟩ : Tensor Int) == some (⟨[1], #[(-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 1], #[1, (-3)]⟩ : Tensor Int) == some (⟨[1, 2], #[1, (-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[(-1)]⟩ : Tensor Int) == some (⟨[], #[(-1)]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[4]⟩ : Tensor Int) == some (⟨[], #[4]⟩ : Tensor Int)
#guard transposeOp (⟨[2], #[(-1), 0]⟩ : Tensor Int) == some (⟨[2], #[(-1), 0]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 1], #[(-1), (-5), (-3)]⟩ : Tensor Int) == some (⟨[1, 3], #[(-1), (-5), (-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 1, 3], #[0, 2, (-4), 2, (-4), (-5)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3, 1], #[4, 1, (-5)]⟩ : Tensor Int) == some (⟨[1, 3], #[4, 1, (-5)]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 2], #[1, 4, 2, 0]⟩ : Tensor Int) == some (⟨[2, 2], #[1, 2, 4, 0]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 1], #[1, (-5), 3]⟩ : Tensor Int) == some (⟨[1, 3], #[1, (-5), 3]⟩ : Tensor Int)
#guard transposeOp (⟨[2], #[(-3), 1]⟩ : Tensor Int) == some (⟨[2], #[(-3), 1]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 1, 2], #[5, 2, (-5), (-3), 0, (-5)]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3], #[2, (-3), 0]⟩ : Tensor Int) == some (⟨[3], #[2, (-3), 0]⟩ : Tensor Int)
#guard transposeOp (⟨[1], #[(-1)]⟩ : Tensor Int) == some (⟨[1], #[(-1)]⟩ : Tensor Int)
#guard transposeOp (⟨[3], #[3, (-2), 0]⟩ : Tensor Int) == some (⟨[3], #[3, (-2), 0]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[5]⟩ : Tensor Int) == some (⟨[], #[5]⟩ : Tensor Int)
#guard transposeOp (⟨[1], #[4]⟩ : Tensor Int) == some (⟨[1], #[4]⟩ : Tensor Int)
#guard transposeOp (⟨[1, 3], #[0, 2, 2]⟩ : Tensor Int) == some (⟨[3, 1], #[0, 2, 2]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[0]⟩ : Tensor Int) == some (⟨[], #[0]⟩ : Tensor Int)
#guard transposeOp (⟨[3, 3, 2], #[(-5), 2, 0, (-4), 0, (-4), (-3), 1, 1, (-1), 5, 0, (-4), 1, 5, (-2), 3, 0]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3, 3, 1], #[2, 1, (-4), 4, 1, (-5), 4, 2, 3]⟩ : Tensor Int) == none
#guard transposeOp (⟨[], #[(-1)]⟩ : Tensor Int) == some (⟨[], #[(-1)]⟩ : Tensor Int)
#guard transposeOp (⟨[3], #[(-5), (-3), (-2)]⟩ : Tensor Int) == some (⟨[3], #[(-5), (-3), (-2)]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[4]⟩ : Tensor Int) == some (⟨[], #[4]⟩ : Tensor Int)
#guard transposeOp (⟨[1], #[(-3)]⟩ : Tensor Int) == some (⟨[1], #[(-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 2, 3], #[0, 1, (-2), 4, 5, (-4), (-3), 1, 3, 4, 0, 1]⟩ : Tensor Int) == none
#guard transposeOp (⟨[1], #[2]⟩ : Tensor Int) == some (⟨[1], #[2]⟩ : Tensor Int)
#guard transposeOp (⟨[3], #[(-3), 4, 5]⟩ : Tensor Int) == some (⟨[3], #[(-3), 4, 5]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[(-3)]⟩ : Tensor Int) == some (⟨[], #[(-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[(-2)]⟩ : Tensor Int) == some (⟨[], #[(-2)]⟩ : Tensor Int)
#guard transposeOp (⟨[1], #[(-2)]⟩ : Tensor Int) == some (⟨[1], #[(-2)]⟩ : Tensor Int)
#guard transposeOp (⟨[1, 1, 1], #[2]⟩ : Tensor Int) == none
#guard transposeOp (⟨[1], #[3]⟩ : Tensor Int) == some (⟨[1], #[3]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[(-2)]⟩ : Tensor Int) == some (⟨[], #[(-2)]⟩ : Tensor Int)
#guard transposeOp (⟨[2, 1, 2], #[(-2), 3, 3, 2]⟩ : Tensor Int) == none
#guard transposeOp (⟨[3], #[2, 1, (-1)]⟩ : Tensor Int) == some (⟨[3], #[2, 1, (-1)]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[(-4)]⟩ : Tensor Int) == some (⟨[], #[(-4)]⟩ : Tensor Int)
#guard transposeOp (⟨[3], #[(-2), (-4), (-3)]⟩ : Tensor Int) == some (⟨[3], #[(-2), (-4), (-3)]⟩ : Tensor Int)
#guard transposeOp (⟨[], #[2]⟩ : Tensor Int) == some (⟨[], #[2]⟩ : Tensor Int)

/-! ## unsqueeze -/

#guard unsqueezeOp (⟨[3], #[(-1), 3, (-2)]⟩ : Tensor Int) (-2) == some (⟨[1, 3], #[(-1), 3, (-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[(-1)]⟩ : Tensor Int) (0) == some (⟨[1], #[(-1)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2], #[(-1), 5]⟩ : Tensor Int) (-1) == some (⟨[2, 1], #[(-1), 5]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3], #[(-4), (-5), 0]⟩ : Tensor Int) (-1) == some (⟨[3, 1], #[(-4), (-5), 0]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[5]⟩ : Tensor Int) (-2) == none
#guard unsqueezeOp (⟨[1, 2], #[5, 3]⟩ : Tensor Int) (-4) == none
#guard unsqueezeOp (⟨[2, 3, 2], #[5, 4, 1, (-4), (-2), (-2), (-4), (-4), 5, (-5), (-3), 5]⟩ : Tensor Int) (2) == some (⟨[2, 3, 1, 2], #[5, 4, 1, (-4), (-2), (-2), (-4), (-4), 5, (-5), (-3), 5]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[1]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[1], #[(-2)]⟩ : Tensor Int) (-2) == some (⟨[1, 1], #[(-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[0]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[], #[1]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[2, 2, 3], #[4, 0, (-4), (-2), 2, (-5), 2, 4, 0, (-4), (-3), 0]⟩ : Tensor Int) (-1) == some (⟨[2, 2, 3, 1], #[4, 0, (-4), (-2), 2, (-5), 2, 4, 0, (-4), (-3), 0]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[(-5)]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[1, 3], #[0, 4, (-2)]⟩ : Tensor Int) (-1) == some (⟨[1, 3, 1], #[0, 4, (-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[2]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[2], #[(-2), 1]⟩ : Tensor Int) (-1) == some (⟨[2, 1], #[(-2), 1]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3], #[4, (-2), 5]⟩ : Tensor Int) (0) == some (⟨[1, 3], #[4, (-2), 5]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3, 1], #[5, 5, 2]⟩ : Tensor Int) (-1) == some (⟨[3, 1, 1], #[5, 5, 2]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 3], #[(-4), (-1), 1, 0, (-2), 4]⟩ : Tensor Int) (1) == some (⟨[2, 1, 3], #[(-4), (-1), 1, 0, (-2), 4]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[(-2)]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[], #[3]⟩ : Tensor Int) (-2) == none
#guard unsqueezeOp (⟨[1, 1, 1], #[1]⟩ : Tensor Int) (-3) == some (⟨[1, 1, 1, 1], #[1]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 1, 3], #[4, 3, 3, (-4), 2, 1]⟩ : Tensor Int) (0) == some (⟨[1, 2, 1, 3], #[4, 3, 3, (-4), 2, 1]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[5]⟩ : Tensor Int) (-2) == none
#guard unsqueezeOp (⟨[3], #[(-1), (-1), (-2)]⟩ : Tensor Int) (-1) == some (⟨[3, 1], #[(-1), (-1), (-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1, 3], #[5, (-1), 5]⟩ : Tensor Int) (-1) == some (⟨[1, 3, 1], #[5, (-1), 5]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1, 1, 2], #[(-1), (-3)]⟩ : Tensor Int) (1) == some (⟨[1, 1, 1, 2], #[(-1), (-3)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1, 3], #[(-2), (-1), 2]⟩ : Tensor Int) (-3) == some (⟨[1, 1, 3], #[(-2), (-1), 2]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3, 3, 2], #[2, 0, (-5), 4, (-5), 2, 1, 0, (-4), 4, 1, (-3), (-3), (-4), (-4), 2, 1, (-1)]⟩ : Tensor Int) (-1) == some (⟨[3, 3, 2, 1], #[2, 0, (-5), 4, (-5), 2, 1, 0, (-4), 4, 1, (-3), (-3), (-4), (-4), 2, 1, (-1)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1, 3], #[4, 0, 3]⟩ : Tensor Int) (3) == none
#guard unsqueezeOp (⟨[1, 1, 3], #[1, 3, 3]⟩ : Tensor Int) (-4) == some (⟨[1, 1, 1, 3], #[1, 3, 3]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2], #[2, 3]⟩ : Tensor Int) (2) == none
#guard unsqueezeOp (⟨[2], #[0, (-4)]⟩ : Tensor Int) (1) == some (⟨[2, 1], #[0, (-4)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[4]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[3], #[4, (-4), 3]⟩ : Tensor Int) (0) == some (⟨[1, 3], #[4, (-4), 3]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[1]⟩ : Tensor Int) (0) == some (⟨[1], #[1]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3], #[(-2), 4, (-4)]⟩ : Tensor Int) (-1) == some (⟨[3, 1], #[(-2), 4, (-4)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1, 3, 1], #[(-5), 4, 5]⟩ : Tensor Int) (-2) == some (⟨[1, 3, 1, 1], #[(-5), 4, 5]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3, 2, 2], #[(-1), (-3), 5, (-1), (-3), 3, 3, 4, 1, (-2), 0, 3]⟩ : Tensor Int) (1) == some (⟨[3, 1, 2, 2], #[(-1), (-3), 5, (-1), (-3), 3, 3, 4, 1, (-2), 0, 3]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[4]⟩ : Tensor Int) (0) == some (⟨[1], #[4]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1, 3, 3], #[3, 2, 2, (-2), 2, 5, 2, (-4), (-1)]⟩ : Tensor Int) (-1) == some (⟨[1, 3, 3, 1], #[3, 2, 2, (-2), 2, 5, 2, (-4), (-1)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1, 2, 3], #[(-2), (-5), (-3), 0, 5, (-3)]⟩ : Tensor Int) (-3) == some (⟨[1, 1, 2, 3], #[(-2), (-5), (-3), 0, 5, (-3)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3, 2], #[(-3), 4, 1, 2, 5, 3]⟩ : Tensor Int) (-2) == some (⟨[3, 1, 2], #[(-3), 4, 1, 2, 5, 3]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1], #[(-4)]⟩ : Tensor Int) (-2) == some (⟨[1, 1], #[(-4)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2], #[(-5), (-3)]⟩ : Tensor Int) (-2) == some (⟨[1, 2], #[(-5), (-3)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2], #[(-3), (-3)]⟩ : Tensor Int) (0) == some (⟨[1, 2], #[(-3), (-3)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[5]⟩ : Tensor Int) (0) == some (⟨[1], #[5]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3, 1], #[(-3), (-5), 5]⟩ : Tensor Int) (-4) == none
#guard unsqueezeOp (⟨[1], #[0]⟩ : Tensor Int) (-2) == some (⟨[1, 1], #[0]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 2], #[2, 1, 3, (-4)]⟩ : Tensor Int) (-2) == some (⟨[2, 1, 2], #[2, 1, 3, (-4)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 3], #[(-4), (-4), 2, 5, (-4), (-5)]⟩ : Tensor Int) (1) == some (⟨[2, 1, 3], #[(-4), (-4), 2, 5, (-4), (-5)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 2, 3], #[(-2), (-5), 4, 2, 4, (-5), 1, 5, (-1), 2, 3, 3]⟩ : Tensor Int) (-4) == some (⟨[1, 2, 2, 3], #[(-2), (-5), 4, 2, 4, (-5), 1, 5, (-1), 2, 3, 3]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 2, 2], #[3, (-4), (-1), (-1), 5, (-1), 2, (-4)]⟩ : Tensor Int) (1) == some (⟨[2, 1, 2, 2], #[3, (-4), (-1), (-1), 5, (-1), 2, (-4)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[5]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[1], #[(-3)]⟩ : Tensor Int) (-3) == none
#guard unsqueezeOp (⟨[3, 1, 3], #[2, (-2), 1, (-4), 5, 1, 3, (-1), 3]⟩ : Tensor Int) (4) == none
#guard unsqueezeOp (⟨[1, 1, 3], #[(-3), (-5), (-5)]⟩ : Tensor Int) (-3) == some (⟨[1, 1, 1, 3], #[(-3), (-5), (-5)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[(-2)]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[], #[0]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[1, 3, 2], #[(-5), (-4), (-5), 3, (-1), 2]⟩ : Tensor Int) (-5) == none
#guard unsqueezeOp (⟨[], #[5]⟩ : Tensor Int) (-2) == none
#guard unsqueezeOp (⟨[], #[1]⟩ : Tensor Int) (-2) == none
#guard unsqueezeOp (⟨[1], #[(-2)]⟩ : Tensor Int) (0) == some (⟨[1, 1], #[(-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1, 3], #[3, 0, (-3)]⟩ : Tensor Int) (-3) == some (⟨[1, 1, 3], #[3, 0, (-3)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2], #[(-5), 1]⟩ : Tensor Int) (-1) == some (⟨[2, 1], #[(-5), 1]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[5]⟩ : Tensor Int) (0) == some (⟨[1], #[5]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 3], #[2, (-5), (-1), 2, (-1), 3]⟩ : Tensor Int) (-3) == some (⟨[1, 2, 3], #[2, (-5), (-1), 2, (-1), 3]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3], #[(-2), (-3), (-2)]⟩ : Tensor Int) (-2) == some (⟨[1, 3], #[(-2), (-3), (-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 1], #[5, (-4)]⟩ : Tensor Int) (0) == some (⟨[1, 2, 1], #[5, (-4)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1, 3, 3], #[2, (-2), 3, (-5), 1, 3, 0, 5, (-1)]⟩ : Tensor Int) (3) == some (⟨[1, 3, 3, 1], #[2, (-2), 3, (-5), 1, 3, 0, 5, (-1)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[(-5)]⟩ : Tensor Int) (-1) == some (⟨[1], #[(-5)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2], #[(-3), (-4)]⟩ : Tensor Int) (-2) == some (⟨[1, 2], #[(-3), (-4)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1, 3], #[3, (-2), (-2)]⟩ : Tensor Int) (-1) == some (⟨[1, 3, 1], #[3, (-2), (-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 2, 1], #[1, (-3), 3, (-2)]⟩ : Tensor Int) (1) == some (⟨[2, 1, 2, 1], #[1, (-3), 3, (-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3], #[3, (-4), (-3)]⟩ : Tensor Int) (-1) == some (⟨[3, 1], #[3, (-4), (-3)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 2], #[(-4), 2, 3, 0]⟩ : Tensor Int) (-1) == some (⟨[2, 2, 1], #[(-4), 2, 3, 0]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 3], #[4, (-4), 2, 3, 3, (-1)]⟩ : Tensor Int) (-2) == some (⟨[2, 1, 3], #[4, (-4), 2, 3, 3, (-1)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[(-1)]⟩ : Tensor Int) (-2) == none
#guard unsqueezeOp (⟨[3, 2, 1], #[0, (-1), (-4), 0, 2, (-2)]⟩ : Tensor Int) (-3) == some (⟨[3, 1, 2, 1], #[0, (-1), (-4), 0, 2, (-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[1], #[(-3)]⟩ : Tensor Int) (2) == none
#guard unsqueezeOp (⟨[1, 1, 2], #[3, (-3)]⟩ : Tensor Int) (4) == none
#guard unsqueezeOp (⟨[1], #[5]⟩ : Tensor Int) (2) == none
#guard unsqueezeOp (⟨[3, 3, 1], #[(-4), 2, (-4), 1, 3, (-2), 0, 0, 4]⟩ : Tensor Int) (-2) == some (⟨[3, 3, 1, 1], #[(-4), 2, (-4), 1, 3, (-2), 0, 0, 4]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2], #[1, (-2)]⟩ : Tensor Int) (-2) == some (⟨[1, 2], #[1, (-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2], #[(-4), 0]⟩ : Tensor Int) (0) == some (⟨[1, 2], #[(-4), 0]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[(-1)]⟩ : Tensor Int) (-1) == some (⟨[1], #[(-1)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[(-2)]⟩ : Tensor Int) (-2) == none
#guard unsqueezeOp (⟨[], #[(-3)]⟩ : Tensor Int) (1) == none
#guard unsqueezeOp (⟨[2], #[2, (-1)]⟩ : Tensor Int) (1) == some (⟨[2, 1], #[2, (-1)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 2], #[(-4), (-2), (-2), (-3)]⟩ : Tensor Int) (-3) == some (⟨[1, 2, 2], #[(-4), (-2), (-2), (-3)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3, 1], #[(-5), (-4), 4]⟩ : Tensor Int) (0) == some (⟨[1, 3, 1], #[(-5), (-4), 4]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[(-2)]⟩ : Tensor Int) (-2) == none
#guard unsqueezeOp (⟨[2], #[3, 5]⟩ : Tensor Int) (2) == none
#guard unsqueezeOp (⟨[2, 1, 1], #[1, 1]⟩ : Tensor Int) (-1) == some (⟨[2, 1, 1, 1], #[1, 1]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[3, 1, 1], #[(-3), 4, (-3)]⟩ : Tensor Int) (0) == some (⟨[1, 3, 1, 1], #[(-3), 4, (-3)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2, 3, 3], #[3, 4, (-1), 1, 3, 2, 1, (-4), (-1), (-1), 0, 1, (-4), 5, 5, (-1), 4, 4]⟩ : Tensor Int) (-3) == some (⟨[2, 1, 3, 3], #[3, 4, (-1), 1, 3, 2, 1, (-4), (-1), (-1), 0, 1, (-4), 5, 5, (-1), 4, 4]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[2], #[(-5), (-4)]⟩ : Tensor Int) (-1) == some (⟨[2, 1], #[(-5), (-4)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[2]⟩ : Tensor Int) (-2) == none
#guard unsqueezeOp (⟨[2, 3], #[(-2), 5, 4, 5, 1, (-2)]⟩ : Tensor Int) (2) == some (⟨[2, 3, 1], #[(-2), 5, 4, 5, 1, (-2)]⟩ : Tensor Int)
#guard unsqueezeOp (⟨[], #[5]⟩ : Tensor Int) (-2) == none

/-! ## expand -/

#guard expandOp (⟨[], #[(-3)]⟩ : Tensor Int) [] == some (⟨[], #[(-3)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 2], #[2, 3]⟩ : Tensor Int) [3, 2, 2] == some (⟨[3, 2, 2], #[2, 3, 2, 3, 2, 3, 2, 3, 2, 3, 2, 3]⟩ : Tensor Int)
#guard expandOp (⟨[2], #[2, 1]⟩ : Tensor Int) [(-1), 3, (-1)] == none
#guard expandOp (⟨[1], #[1]⟩ : Tensor Int) [2, 1, 1] == some (⟨[2, 1, 1], #[1, 1]⟩ : Tensor Int)
#guard expandOp (⟨[], #[5]⟩ : Tensor Int) [3, 2] == some (⟨[3, 2], #[5, 5, 5, 5, 5, 5]⟩ : Tensor Int)
#guard expandOp (⟨[2], #[(-4), (-4)]⟩ : Tensor Int) [2, 2, 2] == some (⟨[2, 2, 2], #[(-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4)]⟩ : Tensor Int)
#guard expandOp (⟨[], #[1]⟩ : Tensor Int) [] == some (⟨[], #[1]⟩ : Tensor Int)
#guard expandOp (⟨[2, 1], #[3, (-1)]⟩ : Tensor Int) [1, 2, 1] == some (⟨[1, 2, 1], #[3, (-1)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 2, 2], #[(-1), (-3), (-1), (-3)]⟩ : Tensor Int) [3, 2, 2] == some (⟨[3, 2, 2], #[(-1), (-3), (-1), (-3), (-1), (-3), (-1), (-3), (-1), (-3), (-1), (-3)]⟩ : Tensor Int)
#guard expandOp (⟨[], #[(-1)]⟩ : Tensor Int) [] == some (⟨[], #[(-1)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[5]⟩ : Tensor Int) [2, 1, 1] == some (⟨[2, 1, 1], #[5, 5]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[(-3)]⟩ : Tensor Int) [1, 1, 3] == some (⟨[1, 1, 3], #[(-3), (-3), (-3)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[0]⟩ : Tensor Int) [2, 1, 3] == some (⟨[2, 1, 3], #[0, 0, 0, 0, 0, 0]⟩ : Tensor Int)
#guard expandOp (⟨[2, 1, 1], #[4, 3]⟩ : Tensor Int) [(-1), (-1), 3] == some (⟨[2, 1, 3], #[4, 4, 4, 3, 3, 3]⟩ : Tensor Int)
#guard expandOp (⟨[2, 1, 1], #[(-3), 5]⟩ : Tensor Int) [1, 1, (-1), 3, 2] == some (⟨[1, 1, 2, 3, 2], #[(-3), (-3), (-3), (-3), (-3), (-3), 5, 5, 5, 5, 5, 5]⟩ : Tensor Int)
#guard expandOp (⟨[1, 3, 2], #[(-1), (-2), (-4), (-2), (-2), (-4)]⟩ : Tensor Int) [3, 3, 2] == some (⟨[3, 3, 2], #[(-1), (-2), (-4), (-2), (-2), (-4), (-1), (-2), (-4), (-2), (-2), (-4), (-1), (-2), (-4), (-2), (-2), (-4)]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[(-3)]⟩ : Tensor Int) [3] == some (⟨[3], #[(-3), (-3), (-3)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[5]⟩ : Tensor Int) [4, 3, 2, 3] == some (⟨[4, 3, 2, 3], #[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[0]⟩ : Tensor Int) [3, 1, 1] == some (⟨[3, 1, 1], #[0, 0, 0]⟩ : Tensor Int)
#guard expandOp (⟨[], #[2]⟩ : Tensor Int) [4, 1] == some (⟨[4, 1], #[2, 2, 2, 2]⟩ : Tensor Int)
#guard expandOp (⟨[1, 3], #[2, 1, (-5)]⟩ : Tensor Int) [3, (-1)] == some (⟨[3, 3], #[2, 1, (-5), 2, 1, (-5), 2, 1, (-5)]⟩ : Tensor Int)
#guard expandOp (⟨[3], #[1, 0, (-5)]⟩ : Tensor Int) [2, (-1)] == some (⟨[2, 3], #[1, 0, (-5), 1, 0, (-5)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 2], #[(-5), (-2)]⟩ : Tensor Int) [1, 2] == some (⟨[1, 2], #[(-5), (-2)]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[(-1)]⟩ : Tensor Int) [2] == some (⟨[2], #[(-1), (-1)]⟩ : Tensor Int)
#guard expandOp (⟨[2], #[0, 3]⟩ : Tensor Int) [2] == some (⟨[2], #[0, 3]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 1], #[1]⟩ : Tensor Int) [3, 2, (-1), 2] == some (⟨[3, 2, 1, 2], #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 2], #[(-5), 2]⟩ : Tensor Int) [1, 2, 2, 2] == some (⟨[1, 2, 2, 2], #[(-5), 2, (-5), 2, (-5), 2, (-5), 2]⟩ : Tensor Int)
#guard expandOp (⟨[], #[4]⟩ : Tensor Int) [1, 2] == some (⟨[1, 2], #[4, 4]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[5]⟩ : Tensor Int) [3] == some (⟨[3], #[5, 5, 5]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 1], #[5]⟩ : Tensor Int) [3, 1, (-1), 1, (-1)] == some (⟨[3, 1, 1, 1, 1], #[5, 5, 5]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 2], #[0, 4]⟩ : Tensor Int) [1, 1, 1, 2] == some (⟨[1, 1, 1, 2], #[0, 4]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 1], #[(-3)]⟩ : Tensor Int) [3, 1, (-1)] == some (⟨[3, 1, 1], #[(-3), (-3), (-3)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 1], #[3]⟩ : Tensor Int) [(-1), (-1), 3] == some (⟨[1, 1, 3], #[3, 3, 3]⟩ : Tensor Int)
#guard expandOp (⟨[], #[3]⟩ : Tensor Int) [3] == some (⟨[3], #[3, 3, 3]⟩ : Tensor Int)
#guard expandOp (⟨[], #[4]⟩ : Tensor Int) [(-1), 3] == none
#guard expandOp (⟨[1, 1, 2], #[2, (-4)]⟩ : Tensor Int) [1, 3, 3, (-1)] == some (⟨[1, 3, 3, 2], #[2, (-4), 2, (-4), 2, (-4), 2, (-4), 2, (-4), 2, (-4), 2, (-4), 2, (-4), 2, (-4)]⟩ : Tensor Int)
#guard expandOp (⟨[2, 1, 1], #[4, (-5)]⟩ : Tensor Int) [2, 2, (-1), 2] == some (⟨[2, 2, 1, 2], #[4, 4, (-5), (-5), 4, 4, (-5), (-5)]⟩ : Tensor Int)
#guard expandOp (⟨[2, 1, 1], #[3, 5]⟩ : Tensor Int) [2, 2, 1, 2] == some (⟨[2, 2, 1, 2], #[3, 3, 5, 5, 3, 3, 5, 5]⟩ : Tensor Int)
#guard expandOp (⟨[], #[(-2)]⟩ : Tensor Int) [] == some (⟨[], #[(-2)]⟩ : Tensor Int)
#guard expandOp (⟨[], #[(-4)]⟩ : Tensor Int) [3] == some (⟨[3], #[(-4), (-4), (-4)]⟩ : Tensor Int)
#guard expandOp (⟨[3, 2], #[3, 3, (-4), (-5), (-2), (-1)]⟩ : Tensor Int) [3, 3, 3, 2] == some (⟨[3, 3, 3, 2], #[3, 3, (-4), (-5), (-2), (-1), 3, 3, (-4), (-5), (-2), (-1), 3, 3, (-4), (-5), (-2), (-1), 3, 3, (-4), (-5), (-2), (-1), 3, 3, (-4), (-5), (-2), (-1), 3, 3, (-4), (-5), (-2), (-1), 3, 3, (-4), (-5), (-2), (-1), 3, 3, (-4), (-5), (-2), (-1), 3, 3, (-4), (-5), (-2), (-1)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 2], #[(-5), (-4)]⟩ : Tensor Int) [(-1), 3, 2] == some (⟨[1, 3, 2], #[(-5), (-4), (-5), (-4), (-5), (-4)]⟩ : Tensor Int)
#guard expandOp (⟨[], #[(-4)]⟩ : Tensor Int) [(-1), 2] == none
#guard expandOp (⟨[1], #[4]⟩ : Tensor Int) [1, 3] == some (⟨[1, 3], #[4, 4, 4]⟩ : Tensor Int)
#guard expandOp (⟨[2], #[1, (-1)]⟩ : Tensor Int) [2] == some (⟨[2], #[1, (-1)]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[(-1)]⟩ : Tensor Int) [4] == some (⟨[4], #[(-1), (-1), (-1), (-1)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 3], #[1, 4, 5]⟩ : Tensor Int) [1, (-1), 3] == some (⟨[1, 1, 3], #[1, 4, 5]⟩ : Tensor Int)
#guard expandOp (⟨[1, 3], #[0, (-3), (-2)]⟩ : Tensor Int) [2, 1, 2, 3] == some (⟨[2, 1, 2, 3], #[0, (-3), (-2), 0, (-3), (-2), 0, (-3), (-2), 0, (-3), (-2)]⟩ : Tensor Int)
#guard expandOp (⟨[2, 1, 3], #[0, (-2), 2, (-2), 0, 2]⟩ : Tensor Int) [2, 2, (-1), (-1), 3] == some (⟨[2, 2, 2, 1, 3], #[0, (-2), 2, (-2), 0, 2, 0, (-2), 2, (-2), 0, 2, 0, (-2), 2, (-2), 0, 2, 0, (-2), 2, (-2), 0, 2]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 3], #[4, (-2), (-3)]⟩ : Tensor Int) [3, 1, 2, 2, 3] == some (⟨[3, 1, 2, 2, 3], #[4, (-2), (-3), 4, (-2), (-3), 4, (-2), (-3), 4, (-2), (-3), 4, (-2), (-3), 4, (-2), (-3), 4, (-2), (-3), 4, (-2), (-3), 4, (-2), (-3), 4, (-2), (-3), 4, (-2), (-3), 4, (-2), (-3)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 3], #[5, 2, 4]⟩ : Tensor Int) [1, 3, 3, 3] == some (⟨[1, 3, 3, 3], #[5, 2, 4, 5, 2, 4, 5, 2, 4, 5, 2, 4, 5, 2, 4, 5, 2, 4, 5, 2, 4, 5, 2, 4, 5, 2, 4]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[(-3)]⟩ : Tensor Int) [1, 2, 1, (-1)] == some (⟨[1, 2, 1, 1], #[(-3), (-3)]⟩ : Tensor Int)
#guard expandOp (⟨[], #[(-5)]⟩ : Tensor Int) [] == some (⟨[], #[(-5)]⟩ : Tensor Int)
#guard expandOp (⟨[], #[3]⟩ : Tensor Int) [2, 2] == some (⟨[2, 2], #[3, 3, 3, 3]⟩ : Tensor Int)
#guard expandOp (⟨[2, 1, 2], #[5, 1, (-5), 3]⟩ : Tensor Int) [2, (-1), 3, (-1)] == some (⟨[2, 2, 3, 2], #[5, 1, 5, 1, 5, 1, (-5), 3, (-5), 3, (-5), 3, 5, 1, 5, 1, 5, 1, (-5), 3, (-5), 3, (-5), 3]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[5]⟩ : Tensor Int) [3] == some (⟨[3], #[5, 5, 5]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[(-3)]⟩ : Tensor Int) [3, 3] == some (⟨[3, 3], #[(-3), (-3), (-3), (-3), (-3), (-3), (-3), (-3), (-3)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 1], #[(-5)]⟩ : Tensor Int) [3, 3, (-1), 3, 3] == some (⟨[3, 3, 1, 3, 3], #[(-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5), (-5)]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[(-4)]⟩ : Tensor Int) [2, 2] == some (⟨[2, 2], #[(-4), (-4), (-4), (-4)]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[3]⟩ : Tensor Int) [3] == some (⟨[3], #[3, 3, 3]⟩ : Tensor Int)
#guard expandOp (⟨[], #[3]⟩ : Tensor Int) [] == some (⟨[], #[3]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 1], #[1]⟩ : Tensor Int) [2, 2, 3] == some (⟨[2, 2, 3], #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 3], #[(-2), (-1), (-1)]⟩ : Tensor Int) [1, 3, 1, 2, 3] == some (⟨[1, 3, 1, 2, 3], #[(-2), (-1), (-1), (-2), (-1), (-1), (-2), (-1), (-1), (-2), (-1), (-1), (-2), (-1), (-1), (-2), (-1), (-1)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[3]⟩ : Tensor Int) [2, (-1), 2] == some (⟨[2, 1, 2], #[3, 3, 3, 3]⟩ : Tensor Int)
#guard expandOp (⟨[2, 3, 1], #[(-3), (-2), (-1), (-5), 1, (-2)]⟩ : Tensor Int) [2, 3, (-1), 0, 2] == none
#guard expandOp (⟨[1, 2, 2], #[4, 1, (-4), (-2)]⟩ : Tensor Int) [2, (-1), 2] == some (⟨[2, 2, 2], #[4, 1, (-4), (-2), 4, 1, (-4), (-2)]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[(-5)]⟩ : Tensor Int) [1, 2, 1] == some (⟨[1, 2, 1], #[(-5), (-5)]⟩ : Tensor Int)
#guard expandOp (⟨[3], #[1, 2, (-5)]⟩ : Tensor Int) [3, 1, (-1)] == some (⟨[3, 1, 3], #[1, 2, (-5), 1, 2, (-5), 1, 2, (-5)]⟩ : Tensor Int)
#guard expandOp (⟨[2], #[3, (-2)]⟩ : Tensor Int) [2] == some (⟨[2], #[3, (-2)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[(-3)]⟩ : Tensor Int) [1, 1, 1, 1] == some (⟨[1, 1, 1, 1], #[(-3)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 3], #[(-4), 1, 4]⟩ : Tensor Int) [1, (-1), 1, 3] == some (⟨[1, 1, 1, 3], #[(-4), 1, 4]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[0]⟩ : Tensor Int) [1, 1, 2, 2] == some (⟨[1, 1, 2, 2], #[0, 0, 0, 0]⟩ : Tensor Int)
#guard expandOp (⟨[1, 2], #[4, 5]⟩ : Tensor Int) [3, 2] == some (⟨[3, 2], #[4, 5, 4, 5, 4, 5]⟩ : Tensor Int)
#guard expandOp (⟨[], #[4]⟩ : Tensor Int) [2, 2] == some (⟨[2, 2], #[4, 4, 4, 4]⟩ : Tensor Int)
#guard expandOp (⟨[1, 2, 1], #[1, 3]⟩ : Tensor Int) [2, 1, 2, 1] == some (⟨[2, 1, 2, 1], #[1, 3, 1, 3]⟩ : Tensor Int)
#guard expandOp (⟨[2, 3], #[2, (-2), 4, (-4), 5, 1]⟩ : Tensor Int) [(-1), 2, 2, 3] == none
#guard expandOp (⟨[1, 3, 2], #[(-3), 1, 2, (-5), (-5), (-1)]⟩ : Tensor Int) [1, (-1), (-1), 2] == some (⟨[1, 1, 3, 2], #[(-3), 1, 2, (-5), (-5), (-1)]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[2]⟩ : Tensor Int) [(-1)] == some (⟨[1], #[2]⟩ : Tensor Int)
#guard expandOp (⟨[1, 2, 3], #[(-5), 2, 1, 3, (-2), 2]⟩ : Tensor Int) [1, (-1), 2, 3] == some (⟨[1, 1, 2, 3], #[(-5), 2, 1, 3, (-2), 2]⟩ : Tensor Int)
#guard expandOp (⟨[], #[2]⟩ : Tensor Int) [2] == some (⟨[2], #[2, 2]⟩ : Tensor Int)
#guard expandOp (⟨[1, 3], #[(-3), 3, 5]⟩ : Tensor Int) [2, 2, (-1), 3] == some (⟨[2, 2, 1, 3], #[(-3), 3, 5, (-3), 3, 5, (-3), 3, 5, (-3), 3, 5]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[3]⟩ : Tensor Int) [3, (-1)] == some (⟨[3, 1], #[3, 3, 3]⟩ : Tensor Int)
#guard expandOp (⟨[3], #[5, (-5), 5]⟩ : Tensor Int) [3] == some (⟨[3], #[5, (-5), 5]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[(-4)]⟩ : Tensor Int) [3, 3, 2, 3] == some (⟨[3, 3, 2, 3], #[(-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4), (-4)]⟩ : Tensor Int)
#guard expandOp (⟨[], #[(-3)]⟩ : Tensor Int) [] == some (⟨[], #[(-3)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[(-3)]⟩ : Tensor Int) [3, 1, 1, (-1)] == some (⟨[3, 1, 1, 1], #[(-3), (-3), (-3)]⟩ : Tensor Int)
#guard expandOp (⟨[], #[1]⟩ : Tensor Int) [1] == some (⟨[1], #[1]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[5]⟩ : Tensor Int) [3, 1, 3] == some (⟨[3, 1, 3], #[5, 5, 5, 5, 5, 5, 5, 5, 5]⟩ : Tensor Int)
#guard expandOp (⟨[1, 3, 3], #[1, 2, (-1), 5, 2, 1, 1, (-5), (-2)]⟩ : Tensor Int) [1, 3, 3] == some (⟨[1, 3, 3], #[1, 2, (-1), 5, 2, 1, 1, (-5), (-2)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[0]⟩ : Tensor Int) [1, 2, 3] == some (⟨[1, 2, 3], #[0, 0, 0, 0, 0, 0]⟩ : Tensor Int)
#guard expandOp (⟨[2], #[(-1), (-1)]⟩ : Tensor Int) [2, (-1)] == some (⟨[2, 2], #[(-1), (-1), (-1), (-1)]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[(-5)]⟩ : Tensor Int) [2] == some (⟨[2], #[(-5), (-5)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[4]⟩ : Tensor Int) [1, 3, (-1), 0] == some (⟨[1, 3, 1, 0], #[]⟩ : Tensor Int)
#guard expandOp (⟨[3, 1, 1], #[4, 3, (-3)]⟩ : Tensor Int) [3, (-1), (-1), 3] == some (⟨[3, 3, 1, 3], #[4, 4, 4, 3, 3, 3, (-3), (-3), (-3), 4, 4, 4, 3, 3, 3, (-3), (-3), (-3), 4, 4, 4, 3, 3, 3, (-3), (-3), (-3)]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[1]⟩ : Tensor Int) [3, 3, 1] == some (⟨[3, 3, 1], #[1, 1, 1, 1, 1, 1, 1, 1, 1]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[3]⟩ : Tensor Int) [1, 3, (-1), 3] == some (⟨[1, 3, 1, 3], #[3, 3, 3, 3, 3, 3, 3, 3, 3]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1, 3], #[(-2), 0, 2]⟩ : Tensor Int) [(-1), 3, 3] == some (⟨[1, 3, 3], #[(-2), 0, 2, (-2), 0, 2, (-2), 0, 2]⟩ : Tensor Int)
#guard expandOp (⟨[1, 1], #[(-5)]⟩ : Tensor Int) [1, (-1), 2] == some (⟨[1, 1, 2], #[(-5), (-5)]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[(-1)]⟩ : Tensor Int) [1] == some (⟨[1], #[(-1)]⟩ : Tensor Int)
#guard expandOp (⟨[1], #[4]⟩ : Tensor Int) [3] == some (⟨[3], #[4, 4, 4]⟩ : Tensor Int)

/-! ## torch.cat -/

#guard catOp [(⟨[3, 3, 2], #[(-4), (-5), 2, (-1), (-1), (-2), (-2), (-2), (-5), 0, 4, (-1), 1, 5, 3, (-4), 4, (-4)]⟩ : Tensor Int), (⟨[2, 3, 2], #[(-3), (-4), 0, (-1), (-4), 2, (-2), (-4), 0, (-2), 2, (-3)]⟩ : Tensor Int), (⟨[3, 3, 3], #[(-3), (-1), 5, 4, (-2), 3, (-3), 1, 4, 5, 3, (-1), (-1), (-2), (-1), 1, (-2), 1, 4, 2, (-4), 3, 0, (-2), (-2), 0, (-5)]⟩ : Tensor Int)] (0) == none
#guard catOp [(⟨[3, 1, 2], #[(-4), (-2), 0, 0, 3, (-4)]⟩ : Tensor Int), (⟨[4, 1, 2], #[(-3), 4, (-4), (-3), (-5), (-1), 2, 0]⟩ : Tensor Int), (⟨[1, 1, 2], #[2, (-1)]⟩ : Tensor Int)] (0) == some (⟨[8, 1, 2], #[(-4), (-2), 0, 0, 3, (-4), (-3), 4, (-4), (-3), (-5), (-1), 2, 0, 2, (-1)]⟩ : Tensor Int)
#guard catOp [(⟨[2, 1, 2], #[0, 1, 1, 4]⟩ : Tensor Int)] (-3) == some (⟨[2, 1, 2], #[0, 1, 1, 4]⟩ : Tensor Int)
#guard catOp [(⟨[3, 3], #[4, 4, (-5), 1, (-5), 0, (-3), 3, 0]⟩ : Tensor Int), (⟨[3, 3], #[0, 0, (-1), 2, 0, (-2), (-4), 4, 1]⟩ : Tensor Int)] (0) == some (⟨[6, 3], #[4, 4, (-5), 1, (-5), 0, (-3), 3, 0, 0, 0, (-1), 2, 0, (-2), (-4), 4, 1]⟩ : Tensor Int)
#guard catOp [(⟨[3], #[(-5), (-5), 3]⟩ : Tensor Int), (⟨[2], #[4, 4]⟩ : Tensor Int)] (-1) == some (⟨[5], #[(-5), (-5), 3, 4, 4]⟩ : Tensor Int)
#guard catOp [(⟨[2, 3], #[(-1), (-3), (-3), (-2), (-4), 4]⟩ : Tensor Int), (⟨[2, 1], #[(-4), 3]⟩ : Tensor Int)] (1) == some (⟨[2, 4], #[(-1), (-3), (-3), (-4), (-2), (-4), 4, 3]⟩ : Tensor Int)
#guard catOp [(⟨[1, 3, 3], #[2, (-2), (-2), 3, (-5), (-2), (-2), (-5), (-5)]⟩ : Tensor Int), (⟨[2, 3, 2], #[(-5), (-4), 5, 5, 3, 2, 3, 5, (-3), 5, (-4), (-3)]⟩ : Tensor Int), (⟨[1, 3, 2], #[5, 4, (-2), 4, (-1), (-1)]⟩ : Tensor Int)] (0) == none
#guard catOp [(⟨[3, 2], #[(-4), 3, 0, 1, 3, (-2)]⟩ : Tensor Int)] (-3) == none
#guard catOp [(⟨[1, 1, 3], #[4, (-2), 3]⟩ : Tensor Int), (⟨[3, 1, 3], #[(-3), 2, 4, 3, 3, 4, (-4), 1, 1]⟩ : Tensor Int)] (0) == some (⟨[4, 1, 3], #[4, (-2), 3, (-3), 2, 4, 3, 3, 4, (-4), 1, 1]⟩ : Tensor Int)
#guard catOp [(⟨[1], #[1]⟩ : Tensor Int), (⟨[1], #[(-1)]⟩ : Tensor Int)] (-2) == none
#guard catOp [(⟨[2], #[5, 4]⟩ : Tensor Int), (⟨[3], #[(-3), 5, (-4)]⟩ : Tensor Int)] (-1) == some (⟨[5], #[5, 4, (-3), 5, (-4)]⟩ : Tensor Int)
#guard catOp [(⟨[3], #[5, 5, (-5)]⟩ : Tensor Int)] (-2) == none
#guard catOp [(⟨[3], #[2, (-1), 1]⟩ : Tensor Int)] (-1) == some (⟨[3], #[2, (-1), 1]⟩ : Tensor Int)
#guard catOp [(⟨[1, 2, 1], #[(-4), 5]⟩ : Tensor Int)] (1) == some (⟨[1, 2, 1], #[(-4), 5]⟩ : Tensor Int)
#guard catOp [(⟨[3], #[(-3), 5, (-5)]⟩ : Tensor Int), (⟨[3], #[3, 5, 5]⟩ : Tensor Int), (⟨[1], #[1]⟩ : Tensor Int)] (-2) == none
#guard catOp [(⟨[1], #[3]⟩ : Tensor Int), (⟨[3], #[2, 0, (-3)]⟩ : Tensor Int)] (0) == some (⟨[4], #[3, 2, 0, (-3)]⟩ : Tensor Int)
#guard catOp [(⟨[2, 2, 1], #[2, (-5), 2, (-1)]⟩ : Tensor Int), (⟨[2, 2, 1], #[(-2), (-3), (-5), 5]⟩ : Tensor Int), (⟨[2, 2, 1], #[(-4), (-4), (-3), 1]⟩ : Tensor Int)] (-4) == none
#guard catOp [(⟨[3, 3, 3], #[(-2), 3, 1, 1, 4, 2, 2, 5, 2, 2, (-1), (-5), (-2), 0, (-4), 3, 3, (-4), 2, (-5), (-5), 4, 0, (-5), 2, (-4), (-3)]⟩ : Tensor Int)] (3) == none
#guard catOp [(⟨[2, 3], #[(-5), (-3), 2, 2, 5, (-4)]⟩ : Tensor Int)] (1) == some (⟨[2, 3], #[(-5), (-3), 2, 2, 5, (-4)]⟩ : Tensor Int)
#guard catOp [(⟨[3, 3, 2], #[(-5), 1, 1, 2, (-1), 5, 5, 3, 0, (-3), (-3), (-5), 5, (-2), (-3), 2, (-2), (-5)]⟩ : Tensor Int)] (-1) == some (⟨[3, 3, 2], #[(-5), 1, 1, 2, (-1), 5, 5, 3, 0, (-3), (-3), (-5), 5, (-2), (-3), 2, (-2), (-5)]⟩ : Tensor Int)
#guard catOp [(⟨[3, 1], #[(-2), (-4), 0]⟩ : Tensor Int), (⟨[1, 1], #[0]⟩ : Tensor Int)] (2) == none
#guard catOp [(⟨[3, 3], #[(-4), 4, 1, 2, (-2), (-4), (-2), 3, 5]⟩ : Tensor Int), (⟨[3, 3], #[2, 2, 5, (-1), (-3), (-5), 1, (-4), (-1)]⟩ : Tensor Int), (⟨[2, 2], #[3, 4, 4, (-2)]⟩ : Tensor Int)] (2) == none
#guard catOp [(⟨[1, 3], #[1, (-1), 0]⟩ : Tensor Int), (⟨[1, 1], #[0]⟩ : Tensor Int), (⟨[1, 1], #[5]⟩ : Tensor Int)] (-1) == some (⟨[1, 5], #[1, (-1), 0, 0, 5]⟩ : Tensor Int)
#guard catOp [(⟨[1], #[(-2)]⟩ : Tensor Int), (⟨[1], #[(-1)]⟩ : Tensor Int), (⟨[2], #[5, (-4)]⟩ : Tensor Int)] (0) == some (⟨[4], #[(-2), (-1), 5, (-4)]⟩ : Tensor Int)
#guard catOp [(⟨[3, 2, 2], #[3, 1, (-5), (-3), 3, (-3), (-4), 1, (-5), (-2), (-1), (-4)]⟩ : Tensor Int), (⟨[3, 2, 2], #[(-5), (-3), 2, (-5), (-3), (-5), 3, (-2), 5, (-1), 5, 4]⟩ : Tensor Int), (⟨[4, 2, 2], #[5, (-5), 3, (-2), (-3), (-3), 3, 5, (-5), (-5), 5, 4, (-4), 4, (-4), (-3)]⟩ : Tensor Int)] (-1) == none
#guard catOp [(⟨[1, 1, 2], #[(-4), 1]⟩ : Tensor Int)] (0) == some (⟨[1, 1, 2], #[(-4), 1]⟩ : Tensor Int)
#guard catOp [(⟨[1, 3, 3], #[1, (-1), (-4), 4, 1, 5, 3, 2, 2]⟩ : Tensor Int), (⟨[2, 3, 4], #[3, (-4), (-2), (-3), (-3), 2, 1, 0, (-3), (-5), (-4), (-2), (-4), (-3), (-5), 2, 0, 4, (-4), 4, (-1), (-4), 1, (-2)]⟩ : Tensor Int)] (3) == none
#guard catOp [(⟨[2, 1, 3], #[2, 4, 4, 1, (-5), (-2)]⟩ : Tensor Int)] (3) == none
#guard catOp [(⟨[1, 2, 3], #[4, 2, (-1), 0, (-5), (-1)]⟩ : Tensor Int), (⟨[1, 2, 2], #[(-3), (-3), 5, 0]⟩ : Tensor Int)] (-1) == some (⟨[1, 2, 5], #[4, 2, (-1), (-3), (-3), 0, (-5), (-1), 5, 0]⟩ : Tensor Int)
#guard catOp [(⟨[1, 1, 2], #[5, 0]⟩ : Tensor Int), (⟨[1, 1, 3], #[2, 1, 4]⟩ : Tensor Int)] (-1) == some (⟨[1, 1, 5], #[5, 0, 2, 1, 4]⟩ : Tensor Int)
#guard catOp [(⟨[2, 1], #[5, (-3)]⟩ : Tensor Int), (⟨[1, 1], #[5]⟩ : Tensor Int), (⟨[2, 2], #[(-5), (-4), 1, 5]⟩ : Tensor Int)] (0) == none
#guard catOp [(⟨[2], #[(-5), 3]⟩ : Tensor Int), (⟨[3], #[(-5), (-4), (-1)]⟩ : Tensor Int), (⟨[1], #[1]⟩ : Tensor Int)] (1) == none
#guard catOp [(⟨[2, 2, 1], #[0, 4, 5, 0]⟩ : Tensor Int), (⟨[2, 2, 1], #[(-2), 3, (-5), (-4)]⟩ : Tensor Int), (⟨[2, 2, 1], #[4, 4, (-2), 1]⟩ : Tensor Int)] (2) == some (⟨[2, 2, 3], #[0, (-2), 4, 4, 3, 4, 5, (-5), (-2), 0, (-4), 1]⟩ : Tensor Int)
#guard catOp [(⟨[2, 3, 3], #[2, (-5), (-5), (-3), 2, 1, 0, 4, 0, 2, 1, 1, 0, (-4), (-2), 1, 1, (-2)]⟩ : Tensor Int), (⟨[2, 1, 3], #[0, 4, 4, (-2), (-5), 0]⟩ : Tensor Int), (⟨[2, 2, 3], #[1, 3, (-1), (-5), (-3), (-4), 1, 0, (-5), (-5), (-3), 2]⟩ : Tensor Int)] (1) == some (⟨[2, 6, 3], #[2, (-5), (-5), (-3), 2, 1, 0, 4, 0, 0, 4, 4, 1, 3, (-1), (-5), (-3), (-4), 2, 1, 1, 0, (-4), (-2), 1, 1, (-2), (-2), (-5), 0, 1, 0, (-5), (-5), (-3), 2]⟩ : Tensor Int)
#guard catOp [(⟨[3], #[5, (-5), 2]⟩ : Tensor Int)] (1) == none
#guard catOp [(⟨[3, 1], #[4, 3, (-4)]⟩ : Tensor Int)] (2) == none
#guard catOp [(⟨[3], #[(-2), (-2), 4]⟩ : Tensor Int), (⟨[2], #[3, (-1)]⟩ : Tensor Int)] (1) == none
#guard catOp [(⟨[3, 3], #[3, 4, 0, (-2), (-5), 5, (-1), 4, (-5)]⟩ : Tensor Int), (⟨[1, 3], #[5, (-5), 5]⟩ : Tensor Int)] (-3) == none
#guard catOp [(⟨[3], #[(-2), (-3), (-5)]⟩ : Tensor Int), (⟨[2], #[5, 5]⟩ : Tensor Int), (⟨[2], #[3, 3]⟩ : Tensor Int)] (0) == some (⟨[7], #[(-2), (-3), (-5), 5, 5, 3, 3]⟩ : Tensor Int)
#guard catOp [(⟨[1], #[5]⟩ : Tensor Int), (⟨[3], #[(-5), (-4), (-3)]⟩ : Tensor Int)] (0) == some (⟨[4], #[5, (-5), (-4), (-3)]⟩ : Tensor Int)
#guard catOp [(⟨[2, 1, 2], #[3, 3, (-5), 4]⟩ : Tensor Int), (⟨[2, 1, 1], #[0, 1]⟩ : Tensor Int), (⟨[2, 1, 1], #[(-3), 4]⟩ : Tensor Int)] (-1) == some (⟨[2, 1, 4], #[3, 3, 0, (-3), (-5), 4, 1, 4]⟩ : Tensor Int)
#guard catOp [(⟨[2], #[5, 1]⟩ : Tensor Int)] (-1) == some (⟨[2], #[5, 1]⟩ : Tensor Int)
#guard catOp [(⟨[1, 1, 1], #[3]⟩ : Tensor Int)] (3) == none
#guard catOp [(⟨[3, 2], #[(-3), 4, (-2), 1, (-5), 4]⟩ : Tensor Int), (⟨[3, 2], #[(-3), 5, 5, (-5), (-5), 3]⟩ : Tensor Int)] (-1) == some (⟨[3, 4], #[(-3), 4, (-3), 5, (-2), 1, 5, (-5), (-5), 4, (-5), 3]⟩ : Tensor Int)
#guard catOp [(⟨[1], #[2]⟩ : Tensor Int), (⟨[2], #[(-5), 1]⟩ : Tensor Int), (⟨[1], #[(-1)]⟩ : Tensor Int)] (0) == some (⟨[4], #[2, (-5), 1, (-1)]⟩ : Tensor Int)
#guard catOp [(⟨[2, 2], #[0, 3, 4, 3]⟩ : Tensor Int)] (0) == some (⟨[2, 2], #[0, 3, 4, 3]⟩ : Tensor Int)
#guard catOp [(⟨[2, 1], #[(-5), 1]⟩ : Tensor Int)] (0) == some (⟨[2, 1], #[(-5), 1]⟩ : Tensor Int)
#guard catOp [(⟨[1, 2, 2], #[4, 3, (-2), (-1)]⟩ : Tensor Int), (⟨[1, 2, 2], #[2, (-4), (-2), (-4)]⟩ : Tensor Int)] (1) == some (⟨[1, 4, 2], #[4, 3, (-2), (-1), 2, (-4), (-2), (-4)]⟩ : Tensor Int)
#guard catOp [(⟨[3, 4], #[0, 1, (-2), (-4), (-5), 1, (-4), (-2), 1, 2, (-5), 1]⟩ : Tensor Int), (⟨[3, 3], #[(-4), (-1), 1, (-3), (-3), 2, 0, 5, 5]⟩ : Tensor Int)] (-3) == none
#guard catOp [(⟨[1], #[2]⟩ : Tensor Int)] (1) == none
#guard catOp [(⟨[1], #[(-1)]⟩ : Tensor Int), (⟨[2], #[3, (-4)]⟩ : Tensor Int)] (-1) == some (⟨[3], #[(-1), 3, (-4)]⟩ : Tensor Int)
#guard catOp [(⟨[1], #[0]⟩ : Tensor Int)] (-2) == none
#guard catOp [(⟨[2], #[(-1), 1]⟩ : Tensor Int), (⟨[3], #[(-3), 0, (-1)]⟩ : Tensor Int), (⟨[4], #[1, (-3), 5, (-3)]⟩ : Tensor Int)] (0) == some (⟨[9], #[(-1), 1, (-3), 0, (-1), 1, (-3), 5, (-3)]⟩ : Tensor Int)
#guard catOp [(⟨[2, 1], #[(-2), 4]⟩ : Tensor Int), (⟨[2, 1], #[1, 5]⟩ : Tensor Int)] (-2) == some (⟨[4, 1], #[(-2), 4, 1, 5]⟩ : Tensor Int)
#guard catOp [(⟨[2, 3], #[4, (-3), (-1), 4, 2, (-1)]⟩ : Tensor Int)] (-2) == some (⟨[2, 3], #[4, (-3), (-1), 4, 2, (-1)]⟩ : Tensor Int)
#guard catOp [(⟨[3, 3], #[2, (-4), 5, 5, 3, 2, (-1), 2, 0]⟩ : Tensor Int), (⟨[1, 3], #[(-4), (-5), 0]⟩ : Tensor Int)] (-2) == some (⟨[4, 3], #[2, (-4), 5, 5, 3, 2, (-1), 2, 0, (-4), (-5), 0]⟩ : Tensor Int)
#guard catOp [(⟨[1, 2, 2], #[2, 4, (-1), (-2)]⟩ : Tensor Int), (⟨[1, 2, 2], #[(-3), (-5), (-1), 3]⟩ : Tensor Int)] (1) == some (⟨[1, 4, 2], #[2, 4, (-1), (-2), (-3), (-5), (-1), 3]⟩ : Tensor Int)
#guard catOp [(⟨[3, 2], #[(-3), 4, (-5), (-4), 5, (-3)]⟩ : Tensor Int), (⟨[3, 2], #[(-4), 3, (-2), 1, (-5), 4]⟩ : Tensor Int), (⟨[3, 2], #[4, 3, (-1), (-5), 0, (-4)]⟩ : Tensor Int)] (-1) == some (⟨[3, 6], #[(-3), 4, (-4), 3, 4, 3, (-5), (-4), (-2), 1, (-1), (-5), 5, (-3), (-5), 4, 0, (-4)]⟩ : Tensor Int)
#guard catOp [(⟨[3], #[4, 5, 2]⟩ : Tensor Int), (⟨[3], #[5, 0, 2]⟩ : Tensor Int), (⟨[3], #[2, 2, (-2)]⟩ : Tensor Int)] (-1) == some (⟨[9], #[4, 5, 2, 5, 0, 2, 2, 2, (-2)]⟩ : Tensor Int)
#guard catOp [(⟨[2], #[(-1), 3]⟩ : Tensor Int)] (-1) == some (⟨[2], #[(-1), 3]⟩ : Tensor Int)
#guard catOp [(⟨[2], #[(-1), 4]⟩ : Tensor Int), (⟨[3], #[5, 5, 0]⟩ : Tensor Int)] (-2) == none
#guard catOp [(⟨[3, 1], #[2, 5, (-5)]⟩ : Tensor Int), (⟨[3, 1], #[(-4), 3, (-5)]⟩ : Tensor Int), (⟨[3, 1], #[1, 2, 5]⟩ : Tensor Int)] (-1) == some (⟨[3, 3], #[2, (-4), 1, 5, 3, 2, (-5), (-5), 5]⟩ : Tensor Int)
#guard catOp [(⟨[1, 3], #[5, 2, (-4)]⟩ : Tensor Int)] (2) == none
#guard catOp [(⟨[3], #[(-2), (-1), 5]⟩ : Tensor Int), (⟨[2], #[5, (-4)]⟩ : Tensor Int), (⟨[3], #[(-5), 1, 2]⟩ : Tensor Int)] (0) == some (⟨[8], #[(-2), (-1), 5, 5, (-4), (-5), 1, 2]⟩ : Tensor Int)
#guard catOp [(⟨[2, 3, 3], #[1, 0, 1, (-4), 5, (-2), 3, (-3), (-3), 1, (-1), 4, (-2), (-3), (-1), 5, (-5), 1]⟩ : Tensor Int), (⟨[2, 3, 3], #[(-4), (-2), 2, 5, 1, 5, (-2), (-1), 5, 3, 0, 3, 2, 1, 0, 0, 4, (-1)]⟩ : Tensor Int)] (-2) == some (⟨[2, 6, 3], #[1, 0, 1, (-4), 5, (-2), 3, (-3), (-3), (-4), (-2), 2, 5, 1, 5, (-2), (-1), 5, 1, (-1), 4, (-2), (-3), (-1), 5, (-5), 1, 3, 0, 3, 2, 1, 0, 0, 4, (-1)]⟩ : Tensor Int)
#guard catOp [(⟨[2, 3], #[0, 2, 4, (-2), (-5), 1]⟩ : Tensor Int)] (0) == some (⟨[2, 3], #[0, 2, 4, (-2), (-5), 1]⟩ : Tensor Int)
#guard catOp [(⟨[2, 1, 1], #[(-3), (-1)]⟩ : Tensor Int)] (-2) == some (⟨[2, 1, 1], #[(-3), (-1)]⟩ : Tensor Int)
#guard catOp [(⟨[3, 2, 1], #[5, 3, 1, 5, 0, 3]⟩ : Tensor Int), (⟨[3, 2, 1], #[(-4), 2, (-4), (-3), (-3), (-5)]⟩ : Tensor Int)] (1) == some (⟨[3, 4, 1], #[5, 3, (-4), 2, 1, 5, (-4), (-3), 0, 3, (-3), (-5)]⟩ : Tensor Int)
#guard catOp [(⟨[1], #[(-3)]⟩ : Tensor Int), (⟨[2], #[(-4), 0]⟩ : Tensor Int)] (-2) == none
#guard catOp [(⟨[3], #[4, 0, (-3)]⟩ : Tensor Int), (⟨[3], #[0, 0, 0]⟩ : Tensor Int)] (0) == some (⟨[6], #[4, 0, (-3), 0, 0, 0]⟩ : Tensor Int)
#guard catOp [(⟨[3, 2], #[4, 2, 3, 5, 5, (-2)]⟩ : Tensor Int), (⟨[1, 2], #[(-1), (-1)]⟩ : Tensor Int), (⟨[2, 2], #[(-5), (-3), (-1), 3]⟩ : Tensor Int)] (-2) == some (⟨[6, 2], #[4, 2, 3, 5, 5, (-2), (-1), (-1), (-5), (-3), (-1), 3]⟩ : Tensor Int)
#guard catOp [(⟨[3, 1, 1], #[(-2), (-2), (-2)]⟩ : Tensor Int)] (1) == some (⟨[3, 1, 1], #[(-2), (-2), (-2)]⟩ : Tensor Int)
#guard catOp [(⟨[2, 2, 2], #[5, 3, (-4), 4, 3, 5, (-2), (-1)]⟩ : Tensor Int)] (-3) == some (⟨[2, 2, 2], #[5, 3, (-4), 4, 3, 5, (-2), (-1)]⟩ : Tensor Int)
#guard catOp [(⟨[1, 3], #[0, (-4), (-4)]⟩ : Tensor Int)] (-1) == some (⟨[1, 3], #[0, (-4), (-4)]⟩ : Tensor Int)
#guard catOp [(⟨[3, 2], #[(-5), (-4), (-4), 5, 3, (-5)]⟩ : Tensor Int)] (-2) == some (⟨[3, 2], #[(-5), (-4), (-4), 5, 3, (-5)]⟩ : Tensor Int)
#guard catOp [(⟨[2, 2], #[(-1), 2, (-1), 4]⟩ : Tensor Int)] (-3) == none
#guard catOp [(⟨[3], #[1, 1, 2]⟩ : Tensor Int)] (0) == some (⟨[3], #[1, 1, 2]⟩ : Tensor Int)
#guard catOp [(⟨[4, 2], #[0, 0, 5, (-1), (-1), 0, 5, (-3)]⟩ : Tensor Int), (⟨[2, 2], #[1, (-3), 5, 1]⟩ : Tensor Int)] (0) == some (⟨[6, 2], #[0, 0, 5, (-1), (-1), 0, 5, (-3), 1, (-3), 5, 1]⟩ : Tensor Int)
#guard catOp [(⟨[3, 3, 2], #[2, 2, (-1), (-4), (-5), (-1), 3, 0, 4, (-4), 3, (-1), (-2), (-2), 0, 5, (-2), 1]⟩ : Tensor Int)] (3) == none
#guard catOp [(⟨[1, 2, 3], #[(-5), 0, 2, 3, 0, (-5)]⟩ : Tensor Int), (⟨[1, 2, 3], #[2, (-4), 2, (-1), 1, 0]⟩ : Tensor Int), (⟨[2, 2, 3], #[0, 0, 0, 1, (-5), 1, (-4), (-3), 4, (-4), 4, 1]⟩ : Tensor Int)] (3) == none
#guard catOp [(⟨[1, 3, 1], #[(-3), 0, (-3)]⟩ : Tensor Int), (⟨[3, 3, 1], #[3, 1, (-3), 4, 3, 5, (-1), 4, (-1)]⟩ : Tensor Int)] (0) == some (⟨[4, 3, 1], #[(-3), 0, (-3), 3, 1, (-3), 4, 3, 5, (-1), 4, (-1)]⟩ : Tensor Int)
#guard catOp [(⟨[1], #[(-4)]⟩ : Tensor Int), (⟨[1], #[(-4)]⟩ : Tensor Int), (⟨[2], #[(-2), 1]⟩ : Tensor Int)] (0) == some (⟨[4], #[(-4), (-4), (-2), 1]⟩ : Tensor Int)
#guard catOp [(⟨[2, 2, 1], #[3, 2, (-1), 1]⟩ : Tensor Int), (⟨[2, 1, 1], #[1, 0]⟩ : Tensor Int), (⟨[2, 3, 1], #[5, 5, 5, 3, (-4), 5]⟩ : Tensor Int)] (-2) == some (⟨[2, 6, 1], #[3, 2, 1, 5, 5, 5, (-1), 1, 0, 3, (-4), 5]⟩ : Tensor Int)
#guard catOp [(⟨[3, 2, 3], #[1, (-2), (-1), 0, 3, 0, 3, (-4), 5, (-3), 2, (-5), (-3), 4, 5, (-5), 4, (-4)]⟩ : Tensor Int), (⟨[2, 2, 3], #[4, (-1), 2, 4, (-1), (-1), 3, (-4), 3, 0, (-2), 3]⟩ : Tensor Int), (⟨[3, 2, 3], #[2, (-1), 0, 1, 2, (-5), 2, (-1), (-3), 3, 0, 4, (-5), (-2), (-4), (-5), 0, (-4)]⟩ : Tensor Int)] (3) == none
#guard catOp [(⟨[2, 2], #[(-1), 4, 2, (-1)]⟩ : Tensor Int), (⟨[2, 2], #[1, (-3), 3, 4]⟩ : Tensor Int)] (-2) == some (⟨[4, 2], #[(-1), 4, 2, (-1), 1, (-3), 3, 4]⟩ : Tensor Int)
#guard catOp [(⟨[1, 3, 3], #[(-1), 1, 1, (-1), 0, 3, 5, (-4), (-4)]⟩ : Tensor Int), (⟨[1, 3, 1], #[(-4), (-2), 1]⟩ : Tensor Int), (⟨[1, 3, 1], #[(-2), 4, (-5)]⟩ : Tensor Int)] (-1) == some (⟨[1, 3, 5], #[(-1), 1, 1, (-4), (-2), (-1), 0, 3, (-2), 4, 5, (-4), (-4), 1, (-5)]⟩ : Tensor Int)
#guard catOp [(⟨[3, 3], #[(-5), 5, (-2), (-5), (-5), (-4), 4, 3, 4]⟩ : Tensor Int), (⟨[2, 3], #[(-4), (-1), (-1), 3, 2, (-2)]⟩ : Tensor Int)] (-3) == none
#guard catOp [(⟨[2, 2], #[5, 3, 4, (-2)]⟩ : Tensor Int), (⟨[2, 2], #[5, (-4), 2, (-4)]⟩ : Tensor Int)] (-1) == some (⟨[2, 4], #[5, 3, 5, (-4), 4, (-2), 2, (-4)]⟩ : Tensor Int)
#guard catOp [(⟨[1], #[2]⟩ : Tensor Int)] (1) == none
#guard catOp [(⟨[2, 2, 1], #[0, 3, (-2), (-2)]⟩ : Tensor Int)] (2) == some (⟨[2, 2, 1], #[0, 3, (-2), (-2)]⟩ : Tensor Int)
#guard catOp [(⟨[1, 2], #[(-5), (-1)]⟩ : Tensor Int), (⟨[1, 2], #[2, 2]⟩ : Tensor Int), (⟨[2, 2], #[0, (-3), 3, (-5)]⟩ : Tensor Int)] (-2) == some (⟨[4, 2], #[(-5), (-1), 2, 2, 0, (-3), 3, (-5)]⟩ : Tensor Int)
#guard catOp [(⟨[3], #[0, 5, (-1)]⟩ : Tensor Int), (⟨[3], #[(-1), 1, 0]⟩ : Tensor Int)] (-2) == none
#guard catOp [(⟨[4, 2], #[(-2), 1, 1, 4, 0, (-2), (-4), (-2)]⟩ : Tensor Int), (⟨[3, 2], #[(-3), (-2), (-2), 2, 2, 2]⟩ : Tensor Int), (⟨[3, 2], #[(-3), 5, (-5), 5, 3, 0]⟩ : Tensor Int)] (1) == none
#guard catOp [(⟨[1, 1, 3], #[5, (-2), 3]⟩ : Tensor Int), (⟨[1, 1, 2], #[0, 4]⟩ : Tensor Int), (⟨[1, 1, 3], #[(-5), (-2), 0]⟩ : Tensor Int)] (-1) == some (⟨[1, 1, 8], #[5, (-2), 3, 0, 4, (-5), (-2), 0]⟩ : Tensor Int)
#guard catOp [(⟨[2], #[(-4), 5]⟩ : Tensor Int), (⟨[2], #[4, (-3)]⟩ : Tensor Int)] (-1) == some (⟨[4], #[(-4), 5, 4, (-3)]⟩ : Tensor Int)
#guard catOp [(⟨[1, 4, 1], #[3, (-2), 5, (-3)]⟩ : Tensor Int), (⟨[3, 3, 1], #[5, 5, (-1), 0, (-4), (-4), 3, 1, 2]⟩ : Tensor Int)] (3) == none
#guard catOp [(⟨[1, 2, 1], #[(-2), (-4)]⟩ : Tensor Int), (⟨[1, 3, 1], #[(-2), 2, 3]⟩ : Tensor Int), (⟨[1, 3, 1], #[(-1), 2, (-4)]⟩ : Tensor Int)] (-2) == some (⟨[1, 8, 1], #[(-2), (-4), (-2), 2, 3, (-1), 2, (-4)]⟩ : Tensor Int)
#guard catOp [(⟨[3, 3], #[1, 4, (-5), 4, 4, 2, 4, 1, 4]⟩ : Tensor Int)] (2) == none
#guard catOp [(⟨[1, 3], #[(-1), (-1), (-4)]⟩ : Tensor Int), (⟨[1, 3], #[3, (-1), 3]⟩ : Tensor Int), (⟨[2, 3], #[1, 4, (-4), (-1), 0, 3]⟩ : Tensor Int)] (-1) == none
#guard catOp [(⟨[1, 2, 3], #[4, (-1), 4, 1, 2, 1]⟩ : Tensor Int), (⟨[1, 1, 3], #[0, 5, 4]⟩ : Tensor Int), (⟨[1, 2, 3], #[2, 5, 1, 4, 3, 1]⟩ : Tensor Int)] (-2) == some (⟨[1, 5, 3], #[4, (-1), 4, 1, 2, 1, 0, 5, 4, 2, 5, 1, 4, 3, 1]⟩ : Tensor Int)

/-! ## torch.stack -/

#guard stackOp [(⟨[], #[(-5)]⟩ : Tensor Int)] (0) == some (⟨[1], #[(-5)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 1, 2], #[5, 0, (-3), (-2), (-1), (-1)]⟩ : Tensor Int), (⟨[3, 1, 2], #[3, (-4), 0, 5, 1, 1]⟩ : Tensor Int)] (-3) == some (⟨[3, 2, 1, 2], #[5, 0, 3, (-4), (-3), (-2), 0, 5, (-1), (-1), 1, 1]⟩ : Tensor Int)
#guard stackOp [(⟨[1, 2, 3], #[(-4), 2, 4, 1, (-1), 5]⟩ : Tensor Int), (⟨[1, 2, 3], #[(-2), 0, (-1), (-2), 5, 4]⟩ : Tensor Int)] (-4) == some (⟨[2, 1, 2, 3], #[(-4), 2, 4, 1, (-1), 5, (-2), 0, (-1), (-2), 5, 4]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 2], #[3, (-2), (-3), (-3)]⟩ : Tensor Int), (⟨[2, 2], #[(-3), 3, 4, 1]⟩ : Tensor Int), (⟨[2, 2], #[(-5), 4, (-4), 1]⟩ : Tensor Int)] (-3) == some (⟨[3, 2, 2], #[3, (-2), (-3), (-3), (-3), 3, 4, 1, (-5), 4, (-4), 1]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[(-1)]⟩ : Tensor Int), (⟨[], #[1]⟩ : Tensor Int)] (0) == some (⟨[2], #[(-1), 1]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[2, (-5)]⟩ : Tensor Int), (⟨[2], #[5, (-5)]⟩ : Tensor Int)] (-2) == some (⟨[2, 2], #[2, (-5), 5, (-5)]⟩ : Tensor Int)
#guard stackOp [(⟨[1, 1], #[(-4)]⟩ : Tensor Int), (⟨[1, 1], #[1]⟩ : Tensor Int), (⟨[2, 1], #[2, 1]⟩ : Tensor Int)] (2) == none
#guard stackOp [(⟨[1, 3, 1], #[1, (-4), 4]⟩ : Tensor Int), (⟨[1, 3, 1], #[(-3), 2, 3]⟩ : Tensor Int), (⟨[1, 3, 1], #[(-5), 3, 0]⟩ : Tensor Int)] (1) == some (⟨[1, 3, 3, 1], #[1, (-4), 4, (-3), 2, 3, (-5), 3, 0]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 1, 1], #[(-2), (-4), 2]⟩ : Tensor Int)] (-3) == some (⟨[3, 1, 1, 1], #[(-2), (-4), 2]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[1]⟩ : Tensor Int)] (0) == some (⟨[1], #[1]⟩ : Tensor Int)
#guard stackOp [(⟨[1, 2], #[(-5), (-2)]⟩ : Tensor Int), (⟨[1, 2], #[(-1), 3]⟩ : Tensor Int)] (-3) == some (⟨[2, 1, 2], #[(-5), (-2), (-1), 3]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 2], #[(-2), 4, 2, 3, (-3), 2]⟩ : Tensor Int)] (1) == some (⟨[3, 1, 2], #[(-2), 4, 2, 3, (-3), 2]⟩ : Tensor Int)
#guard stackOp [(⟨[1, 2, 3], #[1, 5, (-4), (-1), (-1), (-1)]⟩ : Tensor Int), (⟨[1, 2, 3], #[(-3), 0, 4, (-1), 5, (-2)]⟩ : Tensor Int)] (-4) == some (⟨[2, 1, 2, 3], #[1, 5, (-4), (-1), (-1), (-1), (-3), 0, 4, (-1), 5, (-2)]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[0]⟩ : Tensor Int)] (-1) == some (⟨[1], #[0]⟩ : Tensor Int)
#guard stackOp [(⟨[1], #[5]⟩ : Tensor Int), (⟨[1], #[3]⟩ : Tensor Int)] (1) == some (⟨[1, 2], #[5, 3]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[3]⟩ : Tensor Int)] (0) == some (⟨[1], #[3]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[1]⟩ : Tensor Int)] (-1) == some (⟨[1], #[1]⟩ : Tensor Int)
#guard stackOp [(⟨[1, 3], #[2, 3, 5]⟩ : Tensor Int), (⟨[1, 3], #[0, (-4), (-4)]⟩ : Tensor Int), (⟨[1, 3], #[1, (-2), (-5)]⟩ : Tensor Int)] (2) == some (⟨[1, 3, 3], #[2, 0, 1, 3, (-4), (-2), 5, (-4), (-5)]⟩ : Tensor Int)
#guard stackOp [(⟨[3], #[1, (-3), (-3)]⟩ : Tensor Int), (⟨[3], #[3, (-2), (-1)]⟩ : Tensor Int)] (0) == some (⟨[2, 3], #[1, (-3), (-3), 3, (-2), (-1)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 1, 2], #[(-3), 2, 2, 1, (-5), 1]⟩ : Tensor Int), (⟨[3, 1, 2], #[5, 0, 5, 5, 4, (-4)]⟩ : Tensor Int)] (-3) == some (⟨[3, 2, 1, 2], #[(-3), 2, 5, 0, 2, 1, 5, 5, (-5), 1, 4, (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 3], #[3, (-2), (-4), 3, 4, 1]⟩ : Tensor Int)] (1) == some (⟨[2, 1, 3], #[3, (-2), (-4), 3, 4, 1]⟩ : Tensor Int)
#guard stackOp [(⟨[1, 1], #[5]⟩ : Tensor Int), (⟨[1, 1], #[(-5)]⟩ : Tensor Int), (⟨[1, 1], #[(-4)]⟩ : Tensor Int)] (1) == some (⟨[1, 3, 1], #[5, (-5), (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 1, 1], #[4, 3, (-3)]⟩ : Tensor Int), (⟨[3, 1, 1], #[4, (-5), 4]⟩ : Tensor Int), (⟨[3, 1, 1], #[(-4), (-2), (-5)]⟩ : Tensor Int)] (3) == some (⟨[3, 1, 1, 3], #[4, 4, (-4), 3, (-5), (-2), (-3), 4, (-5)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 2], #[1, 5, (-4), (-5), 1, (-1)]⟩ : Tensor Int), (⟨[3, 2], #[(-5), 4, 1, 1, 2, 4]⟩ : Tensor Int)] (-2) == some (⟨[3, 2, 2], #[1, 5, (-5), 4, (-4), (-5), 1, 1, 1, (-1), 2, 4]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[(-2)]⟩ : Tensor Int), (⟨[], #[0]⟩ : Tensor Int)] (-1) == some (⟨[2], #[(-2), 0]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[(-4), (-3)]⟩ : Tensor Int), (⟨[2], #[(-4), 3]⟩ : Tensor Int)] (0) == some (⟨[2, 2], #[(-4), (-3), (-4), 3]⟩ : Tensor Int)
#guard stackOp [(⟨[1], #[(-5)]⟩ : Tensor Int)] (-2) == some (⟨[1, 1], #[(-5)]⟩ : Tensor Int)
#guard stackOp [(⟨[1], #[5]⟩ : Tensor Int)] (0) == some (⟨[1, 1], #[5]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 2, 3], #[0, 2, (-5), 0, (-4), (-5), 3, 0, (-1), 5, (-5), (-4)]⟩ : Tensor Int), (⟨[1, 2, 3], #[1, 1, (-4), (-4), 0, (-5)]⟩ : Tensor Int)] (1) == none
#guard stackOp [(⟨[2], #[(-5), (-2)]⟩ : Tensor Int), (⟨[1], #[5]⟩ : Tensor Int), (⟨[1], #[(-5)]⟩ : Tensor Int)] (-1) == none
#guard stackOp [(⟨[2, 2, 3], #[1, 4, (-4), 3, (-2), 3, (-4), 4, 2, (-5), 2, (-1)]⟩ : Tensor Int), (⟨[2, 2, 3], #[(-1), 5, 3, 3, 1, (-1), 0, (-3), 4, (-3), (-1), (-5)]⟩ : Tensor Int), (⟨[2, 2, 3], #[(-1), (-4), (-1), 3, 2, 4, 3, 5, 2, 2, 2, (-4)]⟩ : Tensor Int)] (-2) == some (⟨[2, 2, 3, 3], #[1, 4, (-4), (-1), 5, 3, (-1), (-4), (-1), 3, (-2), 3, 3, 1, (-1), 3, 2, 4, (-4), 4, 2, 0, (-3), 4, 3, 5, 2, (-5), 2, (-1), (-3), (-1), (-5), 2, 2, (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 2, 3], #[3, 2, (-3), 3, (-2), (-3), (-4), (-4), 2, 2, (-5), (-2), (-2), 3, 4, (-5), (-5), (-2)]⟩ : Tensor Int)] (-2) == some (⟨[3, 2, 1, 3], #[3, 2, (-3), 3, (-2), (-3), (-4), (-4), 2, 2, (-5), (-2), (-2), 3, 4, (-5), (-5), (-2)]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[(-5)]⟩ : Tensor Int), (⟨[], #[(-2)]⟩ : Tensor Int), (⟨[], #[(-4)]⟩ : Tensor Int)] (-1) == some (⟨[3], #[(-5), (-2), (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[(-4), (-1)]⟩ : Tensor Int), (⟨[2], #[(-4), (-5)]⟩ : Tensor Int), (⟨[2], #[4, 2]⟩ : Tensor Int)] (-2) == some (⟨[3, 2], #[(-4), (-1), (-4), (-5), 4, 2]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 2], #[3, 2, (-3), 5]⟩ : Tensor Int), (⟨[1, 2], #[(-5), (-4)]⟩ : Tensor Int), (⟨[1, 2], #[5, (-3)]⟩ : Tensor Int)] (1) == none
#guard stackOp [(⟨[1, 3, 3], #[(-4), 0, 3, (-3), 0, 2, (-5), 4, 0]⟩ : Tensor Int)] (-1) == some (⟨[1, 3, 3, 1], #[(-4), 0, 3, (-3), 0, 2, (-5), 4, 0]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[4]⟩ : Tensor Int), (⟨[], #[2]⟩ : Tensor Int)] (0) == some (⟨[2], #[4, 2]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[(-2), 5]⟩ : Tensor Int), (⟨[2], #[0, 0]⟩ : Tensor Int), (⟨[2], #[(-3), (-5)]⟩ : Tensor Int)] (0) == some (⟨[3, 2], #[(-2), 5, 0, 0, (-3), (-5)]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[(-4)]⟩ : Tensor Int), (⟨[], #[(-4)]⟩ : Tensor Int), (⟨[], #[(-2)]⟩ : Tensor Int)] (-1) == some (⟨[3], #[(-4), (-4), (-2)]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[1]⟩ : Tensor Int)] (0) == some (⟨[1], #[1]⟩ : Tensor Int)
#guard stackOp [(⟨[3], #[2, (-1), 3]⟩ : Tensor Int), (⟨[3], #[(-5), (-4), (-4)]⟩ : Tensor Int), (⟨[4], #[(-1), 1, 3, 3]⟩ : Tensor Int)] (-2) == none
#guard stackOp [(⟨[], #[(-2)]⟩ : Tensor Int), (⟨[], #[(-5)]⟩ : Tensor Int), (⟨[], #[(-1)]⟩ : Tensor Int)] (0) == some (⟨[3], #[(-2), (-5), (-1)]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[3, 2]⟩ : Tensor Int), (⟨[2], #[(-3), (-1)]⟩ : Tensor Int)] (-1) == some (⟨[2, 2], #[3, (-3), 2, (-1)]⟩ : Tensor Int)
#guard stackOp [(⟨[3], #[(-2), 1, 0]⟩ : Tensor Int)] (0) == some (⟨[1, 3], #[(-2), 1, 0]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 3, 1], #[2, (-1), (-4), 4, (-5), 2]⟩ : Tensor Int), (⟨[2, 3, 1], #[0, 4, (-2), 5, (-1), 2]⟩ : Tensor Int), (⟨[2, 3, 1], #[(-3), (-3), 0, 0, (-1), 0]⟩ : Tensor Int)] (1) == some (⟨[2, 3, 3, 1], #[2, (-1), (-4), 0, 4, (-2), (-3), (-3), 0, 4, (-5), 2, 5, (-1), 2, 0, (-1), 0]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[(-3), 0]⟩ : Tensor Int)] (0) == some (⟨[1, 2], #[(-3), 0]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[1]⟩ : Tensor Int), (⟨[], #[4]⟩ : Tensor Int), (⟨[], #[3]⟩ : Tensor Int)] (-1) == some (⟨[3], #[1, 4, 3]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 2], #[4, 2, 2, (-5), (-3), (-4)]⟩ : Tensor Int), (⟨[4, 1], #[3, (-5), 5, (-1)]⟩ : Tensor Int), (⟨[3, 1], #[(-3), (-1), (-2)]⟩ : Tensor Int)] (1) == none
#guard stackOp [(⟨[4], #[1, (-4), 1, 1]⟩ : Tensor Int), (⟨[4], #[(-2), (-4), (-5), (-1)]⟩ : Tensor Int)] (0) == some (⟨[2, 4], #[1, (-4), 1, 1, (-2), (-4), (-5), (-1)]⟩ : Tensor Int)
#guard stackOp [(⟨[3], #[(-5), 3, (-2)]⟩ : Tensor Int), (⟨[3], #[(-1), 0, 1]⟩ : Tensor Int), (⟨[3], #[(-5), 2, 3]⟩ : Tensor Int)] (-1) == some (⟨[3, 3], #[(-5), (-1), (-5), 3, 0, 2, (-2), 1, 3]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[(-1)]⟩ : Tensor Int), (⟨[], #[(-4)]⟩ : Tensor Int)] (-1) == some (⟨[2], #[(-1), (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 2], #[2, 3, 0, 4, 5, 3]⟩ : Tensor Int), (⟨[2, 2], #[4, (-2), 1, (-3)]⟩ : Tensor Int)] (0) == none
#guard stackOp [(⟨[1], #[(-2)]⟩ : Tensor Int), (⟨[2], #[(-2), 1]⟩ : Tensor Int)] (0) == none
#guard stackOp [(⟨[2, 2, 1], #[(-3), 0, (-1), 5]⟩ : Tensor Int)] (2) == some (⟨[2, 2, 1, 1], #[(-3), 0, (-1), 5]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 1], #[2, (-2)]⟩ : Tensor Int), (⟨[2, 1], #[(-2), (-5)]⟩ : Tensor Int)] (-3) == some (⟨[2, 2, 1], #[2, (-2), (-2), (-5)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 1, 1], #[2, (-2), (-4)]⟩ : Tensor Int)] (0) == some (⟨[1, 3, 1, 1], #[2, (-2), (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[(-4), 3]⟩ : Tensor Int), (⟨[2], #[(-4), 2]⟩ : Tensor Int)] (-1) == some (⟨[2, 2], #[(-4), (-4), 3, 2]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[1, (-4)]⟩ : Tensor Int)] (0) == some (⟨[1, 2], #[1, (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[(-1)]⟩ : Tensor Int), (⟨[], #[(-4)]⟩ : Tensor Int)] (0) == some (⟨[2], #[(-1), (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[(-5)]⟩ : Tensor Int), (⟨[], #[(-3)]⟩ : Tensor Int)] (0) == some (⟨[2], #[(-5), (-3)]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[4]⟩ : Tensor Int)] (0) == some (⟨[1], #[4]⟩ : Tensor Int)
#guard stackOp [(⟨[3], #[(-2), 1, (-4)]⟩ : Tensor Int)] (1) == some (⟨[3, 1], #[(-2), 1, (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[1, 3], #[1, (-1), (-2)]⟩ : Tensor Int), (⟨[1, 3], #[(-1), (-5), 3]⟩ : Tensor Int), (⟨[1, 2], #[3, (-4)]⟩ : Tensor Int)] (0) == none
#guard stackOp [(⟨[], #[(-1)]⟩ : Tensor Int)] (0) == some (⟨[1], #[(-1)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 2], #[3, (-4), (-5), 2, 5, (-4)]⟩ : Tensor Int), (⟨[3, 2], #[(-5), 5, (-1), (-5), (-1), 1]⟩ : Tensor Int)] (-2) == some (⟨[3, 2, 2], #[3, (-4), (-5), 5, (-5), 2, (-1), (-5), 5, (-4), (-1), 1]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 3, 2], #[5, (-2), 0, 3, 2, (-3), (-3), (-3), 0, (-2), 5, (-1)]⟩ : Tensor Int), (⟨[1, 3, 2], #[(-2), (-4), 4, (-1), (-3), 2]⟩ : Tensor Int), (⟨[1, 3, 2], #[2, (-1), (-4), (-4), 1, (-3)]⟩ : Tensor Int)] (-4) == none
#guard stackOp [(⟨[2, 2], #[(-1), 4, (-4), 5]⟩ : Tensor Int), (⟨[2, 2], #[1, (-1), (-4), (-2)]⟩ : Tensor Int)] (-1) == some (⟨[2, 2, 2], #[(-1), 1, 4, (-1), (-4), (-4), 5, (-2)]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[(-3), (-5)]⟩ : Tensor Int)] (1) == some (⟨[2, 1], #[(-3), (-5)]⟩ : Tensor Int)
#guard stackOp [(⟨[1, 3, 3], #[3, (-1), (-4), 5, 0, (-5), 0, 0, 1]⟩ : Tensor Int), (⟨[1, 3, 3], #[1, (-2), 2, (-2), 1, 5, (-2), (-5), 5]⟩ : Tensor Int)] (3) == some (⟨[1, 3, 3, 2], #[3, 1, (-1), (-2), (-4), 2, 5, (-2), 0, 1, (-5), 5, 0, (-2), 0, (-5), 1, 5]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 2], #[5, 4, 2, (-2)]⟩ : Tensor Int), (⟨[2, 2], #[0, (-4), (-2), 3]⟩ : Tensor Int), (⟨[2, 3], #[(-4), 4, (-2), 5, 0, 1]⟩ : Tensor Int)] (-2) == none
#guard stackOp [(⟨[2, 1], #[(-4), (-2)]⟩ : Tensor Int), (⟨[2, 1], #[2, (-2)]⟩ : Tensor Int)] (1) == some (⟨[2, 2, 1], #[(-4), 2, (-2), (-2)]⟩ : Tensor Int)
#guard stackOp [(⟨[4], #[3, 3, (-1), (-2)]⟩ : Tensor Int)] (-1) == some (⟨[4, 1], #[3, 3, (-1), (-2)]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 2, 3], #[(-3), 4, 0, 0, (-4), (-2), 2, 1, 5, 3, (-5), (-3)]⟩ : Tensor Int), (⟨[2, 2, 3], #[(-2), 3, (-5), (-5), 3, (-1), 2, 0, 4, (-2), (-2), 5]⟩ : Tensor Int), (⟨[2, 2, 3], #[2, 4, (-5), (-4), 4, 0, 2, 0, (-1), 2, 0, (-1)]⟩ : Tensor Int)] (-4) == some (⟨[3, 2, 2, 3], #[(-3), 4, 0, 0, (-4), (-2), 2, 1, 5, 3, (-5), (-3), (-2), 3, (-5), (-5), 3, (-1), 2, 0, 4, (-2), (-2), 5, 2, 4, (-5), (-4), 4, 0, 2, 0, (-1), 2, 0, (-1)]⟩ : Tensor Int)
#guard stackOp [(⟨[3], #[(-5), (-2), 1]⟩ : Tensor Int), (⟨[3], #[(-3), (-1), 3]⟩ : Tensor Int)] (1) == some (⟨[3, 2], #[(-5), (-3), (-2), (-1), 1, 3]⟩ : Tensor Int)
#guard stackOp [(⟨[1, 3], #[1, 1, (-4)]⟩ : Tensor Int)] (-2) == some (⟨[1, 1, 3], #[1, 1, (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 2], #[(-5), 0, 3, 0, (-5), 0]⟩ : Tensor Int)] (1) == some (⟨[3, 1, 2], #[(-5), 0, 3, 0, (-5), 0]⟩ : Tensor Int)
#guard stackOp [(⟨[1], #[0]⟩ : Tensor Int)] (-1) == some (⟨[1, 1], #[0]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[(-3)]⟩ : Tensor Int), (⟨[], #[(-1)]⟩ : Tensor Int)] (0) == some (⟨[2], #[(-3), (-1)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 2, 1], #[(-1), 2, 5, (-2), 3, 2]⟩ : Tensor Int), (⟨[3, 2, 1], #[(-5), 5, 0, (-1), (-5), 0]⟩ : Tensor Int)] (-2) == some (⟨[3, 2, 2, 1], #[(-1), (-5), 2, 5, 5, 0, (-2), (-1), 3, (-5), 2, 0]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 2, 1], #[(-3), (-3), (-2), 3, 2, 4]⟩ : Tensor Int), (⟨[3, 2, 1], #[(-2), (-5), (-5), (-4), 4, 4]⟩ : Tensor Int), (⟨[3, 2, 1], #[1, 5, (-4), 3, (-2), (-2)]⟩ : Tensor Int)] (2) == some (⟨[3, 2, 3, 1], #[(-3), (-2), 1, (-3), (-5), 5, (-2), (-5), (-4), 3, (-4), 3, 2, 4, (-2), 4, 4, (-2)]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 2], #[3, (-5), (-4), 0]⟩ : Tensor Int), (⟨[2, 2], #[(-3), (-5), (-4), (-4)]⟩ : Tensor Int)] (-1) == some (⟨[2, 2, 2], #[3, (-3), (-5), (-5), (-4), (-4), 0, (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 2, 3], #[(-2), 3, 4, (-2), (-4), 1, (-2), 5, (-1), (-2), 3, 1, (-5), 3, 5, 1, (-4), 1]⟩ : Tensor Int), (⟨[3, 2, 3], #[(-5), 1, 2, (-3), (-2), (-3), 1, (-4), 4, 2, 2, (-1), 5, 4, 1, (-4), (-2), (-5)]⟩ : Tensor Int), (⟨[3, 2, 3], #[(-1), (-2), 0, 2, 4, (-3), 3, 4, (-1), 2, (-1), 5, 0, 5, (-5), 3, 1, 4]⟩ : Tensor Int)] (2) == some (⟨[3, 2, 3, 3], #[(-2), 3, 4, (-5), 1, 2, (-1), (-2), 0, (-2), (-4), 1, (-3), (-2), (-3), 2, 4, (-3), (-2), 5, (-1), 1, (-4), 4, 3, 4, (-1), (-2), 3, 1, 2, 2, (-1), 2, (-1), 5, (-5), 3, 5, 5, 4, 1, 0, 5, (-5), 1, (-4), 1, (-4), (-2), (-5), 3, 1, 4]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[(-4), 0]⟩ : Tensor Int), (⟨[2], #[(-4), (-5)]⟩ : Tensor Int), (⟨[2], #[3, (-3)]⟩ : Tensor Int)] (-1) == some (⟨[2, 3], #[(-4), (-4), 3, 0, (-5), (-3)]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[3, 0]⟩ : Tensor Int), (⟨[2], #[1, (-4)]⟩ : Tensor Int), (⟨[2], #[1, (-4)]⟩ : Tensor Int)] (0) == some (⟨[3, 2], #[3, 0, 1, (-4), 1, (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 3], #[0, 4, 4, 4, (-5), (-1), (-4), 5, (-2)]⟩ : Tensor Int)] (0) == some (⟨[1, 3, 3], #[0, 4, 4, 4, (-5), (-1), (-4), 5, (-2)]⟩ : Tensor Int)
#guard stackOp [(⟨[4, 3], #[(-2), (-2), (-1), 2, (-1), 4, 3, 3, 5, 3, (-3), (-5)]⟩ : Tensor Int)] (-2) == some (⟨[4, 1, 3], #[(-2), (-2), (-1), 2, (-1), 4, 3, 3, 5, 3, (-3), (-5)]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 1, 2], #[(-2), 2, 5, 4, 0, (-5)]⟩ : Tensor Int), (⟨[3, 1, 2], #[(-3), 5, 3, 5, 2, (-1)]⟩ : Tensor Int), (⟨[3, 1, 2], #[4, (-5), (-5), 1, 2, (-4)]⟩ : Tensor Int)] (-3) == some (⟨[3, 3, 1, 2], #[(-2), 2, (-3), 5, 4, (-5), 5, 4, 3, 5, (-5), 1, 0, (-5), 2, (-1), 2, (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 1], #[3, 1]⟩ : Tensor Int)] (2) == some (⟨[2, 1, 1], #[3, 1]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 1, 3], #[(-5), 1, 2, 4, 1, 1]⟩ : Tensor Int), (⟨[2, 1, 3], #[(-3), (-2), (-5), (-1), 4, (-3)]⟩ : Tensor Int), (⟨[2, 1, 3], #[5, (-4), 2, (-1), 4, 3]⟩ : Tensor Int)] (-3) == some (⟨[2, 3, 1, 3], #[(-5), 1, 2, (-3), (-2), (-5), 5, (-4), 2, 4, 1, 1, (-1), 4, (-3), (-1), 4, 3]⟩ : Tensor Int)
#guard stackOp [(⟨[3, 1], #[0, (-4), 2]⟩ : Tensor Int), (⟨[3, 1], #[(-5), 2, (-5)]⟩ : Tensor Int)] (-2) == some (⟨[3, 2, 1], #[0, (-5), (-4), 2, 2, (-5)]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 2, 1], #[2, 1, 4, (-5)]⟩ : Tensor Int), (⟨[1, 2, 1], #[4, 4]⟩ : Tensor Int)] (1) == none
#guard stackOp [(⟨[], #[(-2)]⟩ : Tensor Int), (⟨[], #[4]⟩ : Tensor Int)] (-1) == some (⟨[2], #[(-2), 4]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 1], #[1, (-4)]⟩ : Tensor Int), (⟨[2, 1], #[1, 5]⟩ : Tensor Int)] (-1) == some (⟨[2, 1, 2], #[1, 1, (-4), 5]⟩ : Tensor Int)
#guard stackOp [(⟨[2, 1], #[0, (-3)]⟩ : Tensor Int)] (-3) == some (⟨[1, 2, 1], #[0, (-3)]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[3]⟩ : Tensor Int), (⟨[], #[0]⟩ : Tensor Int)] (-1) == some (⟨[2], #[3, 0]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[(-2)]⟩ : Tensor Int), (⟨[], #[(-4)]⟩ : Tensor Int), (⟨[], #[3]⟩ : Tensor Int)] (-1) == some (⟨[3], #[(-2), (-4), 3]⟩ : Tensor Int)
#guard stackOp [(⟨[1], #[(-3)]⟩ : Tensor Int)] (0) == some (⟨[1, 1], #[(-3)]⟩ : Tensor Int)
#guard stackOp [(⟨[1, 1, 3], #[2, (-4), (-4)]⟩ : Tensor Int)] (-2) == some (⟨[1, 1, 1, 3], #[2, (-4), (-4)]⟩ : Tensor Int)
#guard stackOp [(⟨[2], #[2, 0]⟩ : Tensor Int), (⟨[2], #[(-1), (-3)]⟩ : Tensor Int)] (-1) == some (⟨[2, 2], #[2, (-1), 0, (-3)]⟩ : Tensor Int)
#guard stackOp [(⟨[], #[(-2)]⟩ : Tensor Int)] (-1) == some (⟨[1], #[(-2)]⟩ : Tensor Int)

/-! ## softmax -/

#guard softmaxOp (⟨[2], #[(-3 : Rat), (-3 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[3], #[(4 : Rat), (-1 : Rat), (0 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[3], #[(-5 : Rat), (5 : Rat), (4 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[3], #[(26 / 69 : Rat), (26 / 69 : Rat), (17 / 69 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[1, 2, 3], #[(1 : Rat), (4 : Rat), (3 : Rat), (2 : Rat), (4 : Rat), (5 : Rat)]⟩ : Tensor Rat) (-3) == some (⟨[1, 2, 3], #[(1 : Rat), (1 : Rat), (1 : Rat), (1 : Rat), (1 : Rat), (1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2], #[(-1 : Rat), (0 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[], #[(-2 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[3, 3, 1], #[(2 : Rat), (3 : Rat), (4 : Rat), (3 : Rat), (-4 : Rat), (-2 : Rat), (2 : Rat), (4 : Rat), (3 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[3, 3, 1], #[(1 / 4 : Rat), (5 / 22 : Rat), (17 / 32 : Rat), (1 / 2 : Rat), (17 / 44 : Rat), (5 / 32 : Rat), (1 / 4 : Rat), (17 / 44 : Rat), (5 / 16 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3], #[(-4 : Rat), (-5 : Rat), (-5 : Rat)]⟩ : Tensor Rat) (-2) == none
#guard softmaxOp (⟨[3], #[(1 : Rat), (-2 : Rat), (1 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[3], #[(2 / 9 : Rat), (5 / 9 : Rat), (2 / 9 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(4 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[], #[(-2 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[1, 2, 3], #[(5 : Rat), (1 : Rat), (-1 : Rat), (4 : Rat), (-3 : Rat), (-2 : Rat)]⟩ : Tensor Rat) (1) == some (⟨[1, 2, 3], #[(26 / 43 : Rat), (1 / 6 : Rat), (2 / 7 : Rat), (17 / 43 : Rat), (5 / 6 : Rat), (5 / 7 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3, 3], #[(2 : Rat), (4 : Rat), (-3 : Rat), (3 : Rat), (-4 : Rat), (-2 : Rat), (2 : Rat), (0 : Rat), (-5 : Rat)]⟩ : Tensor Rat) (2) == none
#guard softmaxOp (⟨[3], #[(-1 : Rat), (-4 : Rat), (5 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[3], #[(2 / 45 : Rat), (17 / 45 : Rat), (26 / 45 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2], #[(3 : Rat), (-4 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[2], #[(10 / 27 : Rat), (17 / 27 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2, 3], #[(0 : Rat), (3 : Rat), (2 : Rat), (2 : Rat), (4 : Rat), (4 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[2, 3], #[(1 / 6 : Rat), (10 / 27 : Rat), (5 / 22 : Rat), (5 / 6 : Rat), (17 / 27 : Rat), (17 / 22 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2, 2], #[(-5 : Rat), (-5 : Rat), (-4 : Rat), (4 : Rat)]⟩ : Tensor Rat) (-2) == some (⟨[2, 2], #[(26 / 43 : Rat), (26 / 43 : Rat), (17 / 43 : Rat), (17 / 43 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(4 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[1, 1, 2], #[(2 : Rat), (5 : Rat)]⟩ : Tensor Rat) (-3) == some (⟨[1, 1, 2], #[(1 : Rat), (1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3], #[(5 : Rat), (-4 : Rat), (-5 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[3], #[(26 / 69 : Rat), (17 / 69 : Rat), (26 / 69 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2], #[(2 : Rat), (4 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[3, 2], #[(-1 : Rat), (5 : Rat), (-4 : Rat), (0 : Rat), (2 : Rat), (-2 : Rat)]⟩ : Tensor Rat) (1) == some (⟨[3, 2], #[(1 / 14 : Rat), (13 / 14 : Rat), (17 / 18 : Rat), (1 / 18 : Rat), (1 / 2 : Rat), (1 / 2 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(-2 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[1, 2], #[(4 : Rat), (-2 : Rat)]⟩ : Tensor Rat) (1) == some (⟨[1, 2], #[(17 / 22 : Rat), (5 / 22 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(2 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[1], #[(-4 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[], #[(1 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[2], #[(5 : Rat), (2 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[3, 2], #[(0 : Rat), (0 : Rat), (-4 : Rat), (-3 : Rat), (3 : Rat), (-4 : Rat)]⟩ : Tensor Rat) (2) == none
#guard softmaxOp (⟨[2, 3], #[(-4 : Rat), (-3 : Rat), (-5 : Rat), (-3 : Rat), (-5 : Rat), (0 : Rat)]⟩ : Tensor Rat) (-3) == none
#guard softmaxOp (⟨[], #[(-5 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[1, 3, 3], #[(-2 : Rat), (5 : Rat), (1 : Rat), (-2 : Rat), (3 : Rat), (-1 : Rat), (4 : Rat), (3 : Rat), (2 : Rat)]⟩ : Tensor Rat) (-4) == none
#guard softmaxOp (⟨[2, 2, 3], #[(-1 : Rat), (2 : Rat), (2 : Rat), (2 : Rat), (1 : Rat), (-5 : Rat), (-2 : Rat), (-1 : Rat), (1 : Rat), (2 : Rat), (4 : Rat), (5 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[2, 2, 3], #[(1 / 6 : Rat), (5 / 12 : Rat), (5 / 12 : Rat), (5 / 33 : Rat), (2 / 33 : Rat), (26 / 33 : Rat), (5 / 9 : Rat), (2 / 9 : Rat), (2 / 9 : Rat), (5 / 48 : Rat), (17 / 48 : Rat), (13 / 24 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3, 2], #[(-1 : Rat), (4 : Rat), (-3 : Rat), (-4 : Rat), (3 : Rat), (2 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[3, 2], #[(2 / 19 : Rat), (17 / 19 : Rat), (10 / 27 : Rat), (17 / 27 : Rat), (2 / 3 : Rat), (1 / 3 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(-3 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[2, 2], #[(-3 : Rat), (-5 : Rat), (1 : Rat), (-1 : Rat)]⟩ : Tensor Rat) (-2) == some (⟨[2, 2], #[(5 / 6 : Rat), (13 / 14 : Rat), (1 / 6 : Rat), (1 / 14 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[1, 2, 3], #[(2 : Rat), (4 : Rat), (-2 : Rat), (0 : Rat), (2 : Rat), (-4 : Rat)]⟩ : Tensor Rat) (3) == none
#guard softmaxOp (⟨[3], #[(3 : Rat), (-2 : Rat), (-4 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[], #[(3 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[3, 3], #[(2 : Rat), (4 : Rat), (5 : Rat), (2 : Rat), (3 : Rat), (-4 : Rat), (-4 : Rat), (0 : Rat), (5 : Rat)]⟩ : Tensor Rat) (2) == none
#guard softmaxOp (⟨[3, 1, 1], #[(2 : Rat), (4 : Rat), (-3 : Rat)]⟩ : Tensor Rat) (-3) == some (⟨[3, 1, 1], #[(5 / 32 : Rat), (17 / 32 : Rat), (5 / 16 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3], #[(3 : Rat), (0 : Rat), (-5 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[3], #[(10 / 37 : Rat), (1 / 37 : Rat), (26 / 37 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3, 3], #[(1 : Rat), (2 : Rat), (-5 : Rat), (-2 : Rat), (2 : Rat), (5 : Rat), (-3 : Rat), (-2 : Rat), (1 : Rat)]⟩ : Tensor Rat) (-2) == some (⟨[3, 3], #[(2 / 17 : Rat), (1 / 3 : Rat), (13 / 27 : Rat), (5 / 17 : Rat), (1 / 3 : Rat), (13 / 27 : Rat), (10 / 17 : Rat), (1 / 3 : Rat), (1 / 27 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[1], #[(3 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[1], #[(1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[1], #[(-1 : Rat)]⟩ : Tensor Rat) (-2) == none
#guard softmaxOp (⟨[3], #[(2 : Rat), (-4 : Rat), (4 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[3], #[(5 / 39 : Rat), (17 / 39 : Rat), (17 / 39 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(-4 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[2, 2, 3], #[(1 : Rat), (-3 : Rat), (2 : Rat), (4 : Rat), (3 : Rat), (2 : Rat), (5 : Rat), (-3 : Rat), (-3 : Rat), (-3 : Rat), (-1 : Rat), (3 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[2, 2, 3], #[(2 / 17 : Rat), (10 / 17 : Rat), (5 / 17 : Rat), (17 / 32 : Rat), (5 / 16 : Rat), (5 / 32 : Rat), (13 / 23 : Rat), (5 / 23 : Rat), (5 / 23 : Rat), (5 / 11 : Rat), (1 / 11 : Rat), (5 / 11 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2, 2, 3], #[(-2 : Rat), (1 : Rat), (-5 : Rat), (4 : Rat), (2 : Rat), (3 : Rat), (0 : Rat), (4 : Rat), (0 : Rat), (4 : Rat), (4 : Rat), (4 : Rat)]⟩ : Tensor Rat) (-4) == none
#guard softmaxOp (⟨[], #[(-2 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[], #[(-2 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[], #[(3 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[1, 1, 2], #[(4 : Rat), (-2 : Rat)]⟩ : Tensor Rat) (-3) == some (⟨[1, 1, 2], #[(1 : Rat), (1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(-3 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[], #[(2 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[], #[(-1 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[], #[(1 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[1, 1], #[(-1 : Rat)]⟩ : Tensor Rat) (-3) == none
#guard softmaxOp (⟨[1], #[(5 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[1], #[(1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2, 1], #[(0 : Rat), (3 : Rat)]⟩ : Tensor Rat) (1) == some (⟨[2, 1], #[(1 : Rat), (1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(-4 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[1, 3], #[(2 : Rat), (-5 : Rat), (2 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[1, 3], #[(1 : Rat), (1 : Rat), (1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[1], #[(3 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[1], #[(0 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[1], #[(1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[1], #[(5 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[1], #[(1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(3 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[], #[(-5 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[3, 2, 1], #[(4 : Rat), (4 : Rat), (1 : Rat), (-5 : Rat), (4 : Rat), (-4 : Rat)]⟩ : Tensor Rat) (1) == some (⟨[3, 2, 1], #[(1 / 2 : Rat), (1 / 2 : Rat), (1 / 14 : Rat), (13 / 14 : Rat), (1 / 2 : Rat), (1 / 2 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3, 1, 1], #[(-4 : Rat), (-4 : Rat), (0 : Rat)]⟩ : Tensor Rat) (2) == some (⟨[3, 1, 1], #[(1 : Rat), (1 : Rat), (1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[1], #[(-2 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[], #[(0 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[2, 3], #[(-1 : Rat), (2 : Rat), (-5 : Rat), (-3 : Rat), (-2 : Rat), (0 : Rat)]⟩ : Tensor Rat) (2) == none
#guard softmaxOp (⟨[], #[(0 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[3], #[(3 : Rat), (3 : Rat), (2 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[3], #[(2 / 5 : Rat), (2 / 5 : Rat), (1 / 5 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[1, 2, 2], #[(-5 : Rat), (3 : Rat), (-5 : Rat), (-3 : Rat)]⟩ : Tensor Rat) (2) == some (⟨[1, 2, 2], #[(13 / 18 : Rat), (5 / 18 : Rat), (13 / 18 : Rat), (5 / 18 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3, 2, 2], #[(-2 : Rat), (5 : Rat), (-3 : Rat), (2 : Rat), (3 : Rat), (3 : Rat), (3 : Rat), (0 : Rat), (-3 : Rat), (-1 : Rat), (0 : Rat), (-1 : Rat)]⟩ : Tensor Rat) (2) == some (⟨[3, 2, 2], #[(5 / 31 : Rat), (26 / 31 : Rat), (2 / 3 : Rat), (1 / 3 : Rat), (1 / 2 : Rat), (1 / 2 : Rat), (10 / 11 : Rat), (1 / 11 : Rat), (5 / 6 : Rat), (1 / 6 : Rat), (1 / 3 : Rat), (2 / 3 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[1], #[(-2 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[2, 1, 3], #[(-1 : Rat), (2 : Rat), (0 : Rat), (-2 : Rat), (0 : Rat), (3 : Rat)]⟩ : Tensor Rat) (-3) == some (⟨[2, 1, 3], #[(2 / 7 : Rat), (5 / 6 : Rat), (1 / 11 : Rat), (5 / 7 : Rat), (1 / 6 : Rat), (10 / 11 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2, 3, 2], #[(0 : Rat), (-1 : Rat), (-4 : Rat), (-4 : Rat), (-2 : Rat), (-5 : Rat), (-3 : Rat), (4 : Rat), (1 : Rat), (-3 : Rat), (-5 : Rat), (-2 : Rat)]⟩ : Tensor Rat) (-3) == some (⟨[2, 3, 2], #[(1 / 11 : Rat), (2 / 19 : Rat), (17 / 19 : Rat), (17 / 27 : Rat), (5 / 31 : Rat), (26 / 31 : Rat), (10 / 11 : Rat), (17 / 19 : Rat), (2 / 19 : Rat), (10 / 27 : Rat), (26 / 31 : Rat), (5 / 31 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2, 2, 3], #[(-2 : Rat), (-4 : Rat), (-3 : Rat), (-3 : Rat), (0 : Rat), (2 : Rat), (2 : Rat), (-5 : Rat), (1 : Rat), (1 : Rat), (0 : Rat), (4 : Rat)]⟩ : Tensor Rat) (-4) == none
#guard softmaxOp (⟨[2, 3], #[(-3 : Rat), (4 : Rat), (3 : Rat), (-5 : Rat), (5 : Rat), (-4 : Rat)]⟩ : Tensor Rat) (2) == none
#guard softmaxOp (⟨[1, 3, 2], #[(-2 : Rat), (-3 : Rat), (-4 : Rat), (-5 : Rat), (4 : Rat), (5 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[1, 3, 2], #[(1 / 3 : Rat), (2 / 3 : Rat), (17 / 43 : Rat), (26 / 43 : Rat), (17 / 43 : Rat), (26 / 43 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(1 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[2, 3], #[(-4 : Rat), (-4 : Rat), (-3 : Rat), (4 : Rat), (-5 : Rat), (1 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[2, 3], #[(1 / 2 : Rat), (17 / 43 : Rat), (5 / 6 : Rat), (1 / 2 : Rat), (26 / 43 : Rat), (1 / 6 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[], #[(2 : Rat)]⟩ : Tensor Rat) (-1) == none
#guard softmaxOp (⟨[1, 1], #[(-4 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[1, 1], #[(1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3, 1], #[(-3 : Rat), (5 : Rat), (-3 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[3, 1], #[(1 : Rat), (1 : Rat), (1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3, 1, 3], #[(4 : Rat), (-2 : Rat), (3 : Rat), (-4 : Rat), (-4 : Rat), (2 : Rat), (-5 : Rat), (2 : Rat), (3 : Rat)]⟩ : Tensor Rat) (1) == some (⟨[3, 1, 3], #[(1 : Rat), (1 : Rat), (1 : Rat), (1 : Rat), (1 : Rat), (1 : Rat), (1 : Rat), (1 : Rat), (1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[1], #[(-5 : Rat)]⟩ : Tensor Rat) (-2) == none
#guard softmaxOp (⟨[2, 1, 3], #[(2 : Rat), (5 : Rat), (0 : Rat), (0 : Rat), (0 : Rat), (2 : Rat)]⟩ : Tensor Rat) (2) == some (⟨[2, 1, 3], #[(5 / 32 : Rat), (13 / 16 : Rat), (1 / 32 : Rat), (1 / 7 : Rat), (1 / 7 : Rat), (5 / 7 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2], #[(1 : Rat), (1 : Rat)]⟩ : Tensor Rat) (1) == none
#guard softmaxOp (⟨[2, 3, 3], #[(1 : Rat), (5 : Rat), (4 : Rat), (0 : Rat), (0 : Rat), (-5 : Rat), (-4 : Rat), (-3 : Rat), (-5 : Rat), (-1 : Rat), (-5 : Rat), (-5 : Rat), (5 : Rat), (1 : Rat), (-4 : Rat), (-1 : Rat), (-5 : Rat), (4 : Rat)]⟩ : Tensor Rat) (3) == none
#guard softmaxOp (⟨[2], #[(2 : Rat), (5 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[2], #[(5 / 31 : Rat), (26 / 31 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2, 1], #[(-5 : Rat), (0 : Rat)]⟩ : Tensor Rat) (-2) == some (⟨[2, 1], #[(26 / 27 : Rat), (1 / 27 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[3], #[(5 : Rat), (-1 : Rat), (-1 : Rat)]⟩ : Tensor Rat) (0) == some (⟨[3], #[(13 / 15 : Rat), (1 / 15 : Rat), (1 / 15 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2, 1], #[(5 : Rat), (-5 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[2, 1], #[(1 : Rat), (1 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2], #[(-3 : Rat), (3 : Rat)]⟩ : Tensor Rat) (-1) == some (⟨[2], #[(1 / 2 : Rat), (1 / 2 : Rat)]⟩ : Tensor Rat)
#guard softmaxOp (⟨[2], #[(-3 : Rat), (2 : Rat)]⟩ : Tensor Rat) (-2) == none
#guard softmaxOp (⟨[], #[(3 : Rat)]⟩ : Tensor Rat) (0) == none
#guard softmaxOp (⟨[1], #[(-3 : Rat)]⟩ : Tensor Rat) (-2) == none

end CompactCheck.SemanticsRandomTest
