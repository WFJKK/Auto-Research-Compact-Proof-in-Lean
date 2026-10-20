import CompactCheck.Walk

/-!
# Tasks

A task says which inputs exist and what the correct answer to each one is,
like `task.py` in a model folder. The `space` and the `label` are part of
the spec: the theorems count inputs the network answers correctly, and
"correctly" means "matching `label`". Each task is written once here and
reviewed by hand.

A task also has a test for boxes whose inputs all have the same label,
which the interval rule needs (`constant_label` in `task.py`), and says
whether reordering an input's tokens keeps its label, which the symmetry
rule needs (`LABEL_SYMMETRIC` in `task.py`). Neither is part of the spec,
and neither needs review: every task comes with proofs that both are right
(`constantLabel_spec`, `labelSymmetric_spec`).

This file uses only core Lean.
-/

namespace CompactCheck

/-- `x` and `y` have the same length, and every token of `x` is at most the
    token of `y` at the same position. -/
def tokensLE : Input → Input → Bool
  | [], [] => true
  | a :: x, b :: y => a ≤ b && tokensLE x y
  | _, _ => false

/-- A task: the input space (position `p` takes the tokens
    `0, ..., space[p] - 1`), the correct output for every input, and a test
    for boxes in which every input has the same label. -/
structure Task where
  name : String
  space : List Nat
  label : Input → Nat
  /-- `some l` if every input in the box has the label `l`; `none` if the
      test cannot tell. -/
  constantLabel : Box → Option Nat
  /-- The test is right. -/
  constantLabel_spec : ∀ box l x, constantLabel box = some l → inBox box x = true → label x = l
  /-- `true` if reordering the tokens of an input never changes its label. -/
  labelSymmetric : Bool
  /-- It is right. -/
  labelSymmetric_spec : labelSymmetric = true → ∀ x y, x.Perm y → label x = label y

/-! ## Boxes with a constant label

For a label that never decreases when a token increases, the smallest label
in a box is at the corner of lower ends and the largest at the corner of
upper ends. If the two corners have the same label, so does every input in
the box. -/

/-- Every input in a box lies between its two corners. -/
theorem inBox_corners : ∀ (box : Box) (x : Input), inBox box x = true →
    tokensLE (box.map Range.lo) x = true ∧ tokensLE x (box.map Range.hi) = true
  | [], [], _ => ⟨rfl, rfl⟩
  | r :: rs, t :: ts, h => by
    simp only [inBox, inRange, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := inBox_corners rs ts h.2
    simp only [List.map_cons, tokensLE, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨h.1.1, ih.1⟩, ⟨h.1.2, ih.2⟩⟩
  | [], _ :: _, h => by simp [inBox] at h
  | _ :: _, [], h => by simp [inBox] at h

/-- The test for a label that never decreases when a token increases: the
    label of the lower corner, if it equals the label of the upper corner. -/
def cornerLabel (label : Input → Nat) (box : Box) : Option Nat :=
  if label (box.map Range.lo) = label (box.map Range.hi) then some (label (box.map Range.lo))
  else none

theorem cornerLabel_spec (label : Input → Nat)
    (mono : ∀ x y, tokensLE x y = true → label x ≤ label y) :
    ∀ box l x, cornerLabel label box = some l → inBox box x = true → label x = l := by
  intro box l x h hx
  unfold cornerLabel at h
  split at h
  · cases h
    have h1 := mono _ _ (inBox_corners box x hx).1
    have h2 := mono _ _ (inBox_corners box x hx).2
    omega
  · cases h

/-- Folding with a function that grows with both arguments. -/
theorem foldl_mono (f : Nat → Nat → Nat) (hf : ∀ a b c d, a ≤ b → c ≤ d → f a c ≤ f b d) :
    ∀ (x y : Input) (a b : Nat), a ≤ b → tokensLE x y = true → x.foldl f a ≤ y.foldl f b
  | [], [], _, _, hab, _ => hab
  | s :: x, t :: y, a, b, hab, h => by
    simp only [tokensLE, Bool.and_eq_true, decide_eq_true_eq] at h
    exact foldl_mono f hf x y _ _ (hf a b s t hab h.1) h.2
  | [], _ :: _, _, _, _, h => by simp [tokensLE] at h
  | _ :: _, [], _, _, _, h => by simp [tokensLE] at h

/-! ## Labels that do not depend on the order of the tokens -/

/-- Folding with a function whose last two arguments can be swapped gives
    the same result for every reordering of the list. -/
theorem foldl_perm (f : Nat → Nat → Nat) (hf : ∀ a b c, f (f a b) c = f (f a c) b) (a : Nat)
    {x y : Input} (h : x.Perm y) : x.foldl f a = y.foldl f a :=
  h.foldl_eq' (fun _ _ _ _ z => hf z _ _) a

/-! ## The tasks

Each label is written the way `label` in the model folder's `task.py`
computes it; `scripts/export_network.py` checks that the two agree on every
input before it writes a network file. -/

/-- The largest of `positions` tokens, each in `0, ..., values - 1`
    (max2, attn-max2, attn-max4). -/
def maxTask (positions values : Nat) : Task where
  name := "max"
  space := List.replicate positions values
  label x := x.foldl max 0
  constantLabel := cornerLabel fun x => x.foldl max 0
  constantLabel_spec := cornerLabel_spec _ fun x y h =>
    foldl_mono max (fun _ _ _ _ _ _ => by omega) x y 0 0 (Nat.le_refl 0) h
  labelSymmetric := true
  labelSymmetric_spec _ _ _ h := foldl_perm max (fun _ _ _ => by omega) 0 h

/-- The smallest of `positions` tokens, each in `0, ..., values - 1`
    (attn-min2, attn-min4). Every token is at most `values - 1`, so that is
    a safe starting value. -/
def minTask (positions values : Nat) : Task where
  name := "min"
  space := List.replicate positions values
  label x := x.foldl min (values - 1)
  constantLabel := cornerLabel fun x => x.foldl min (values - 1)
  constantLabel_spec := cornerLabel_spec _ fun x y h =>
    foldl_mono min (fun _ _ _ _ _ _ => by omega) x y _ _ (Nat.le_refl _) h
  labelSymmetric := true
  labelSymmetric_spec _ _ _ h := foldl_perm min (fun _ _ _ => by omega) _ h

/-- The label of majority: 1 if the tokens add up to more than half of
    `positions`, that is to at least `positions / 2 + 1`, else 0. -/
def majorityLabel (positions : Nat) (x : Input) : Nat :=
  if positions / 2 + 1 ≤ x.foldl (· + ·) 0 then 1 else 0

/-- Majority on `positions` bits, the tokens 0 and 1 (xorformer-majority):
    1 exactly when more than half of the bits are 1. With 12 bits, at least
    7 of them. -/
def majorityTask (positions : Nat) : Task where
  name := "majority"
  space := List.replicate positions 2
  label := majorityLabel positions
  constantLabel := cornerLabel (majorityLabel positions)
  constantLabel_spec := cornerLabel_spec _ fun x y h => by
    have := foldl_mono (· + ·) (fun _ _ _ _ h1 h2 => Nat.add_le_add h1 h2) x y 0 0 (Nat.le_refl 0) h
    unfold majorityLabel
    split <;> split <;> omega
  labelSymmetric := true
  labelSymmetric_spec _ x y h := by
    unfold majorityLabel
    rw [foldl_perm (· + ·) (fun _ _ _ => by omega) 0 h]

/-- The task with this name, for this input shape. -/
def taskByName (name : String) (positions values : Nat) : Option Task :=
  match name with
  | "max" => some (maxTask positions values)
  | "min" => some (minTask positions values)
  | "majority" => if values = 2 then some (majorityTask positions) else none
  | _ => none

end CompactCheck
