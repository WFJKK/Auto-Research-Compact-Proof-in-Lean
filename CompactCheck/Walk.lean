/-
  Step 1 of docs/LEAN.md: the split tree and the walk.

  Written against docs/RULES.md, section "Split tree": a split divides the
  current range [lo, hi] of one position at strictly increasing cuts inside
  (lo, hi]. The pieces are [lo, c1-1], ..., [ck, hi], and the number of
  children must equal the number of pieces.

  Not here yet: reading JSON. A later file turns a proof file into a
  `SplitTree`; until then the tests below write trees by hand.
-/

namespace CompactCheck

/-! ## Types -/

/-- An inclusive range of tokens, `lo ≤ t ≤ hi`. -/
structure Range where
  lo : Nat
  hi : Nat
deriving Repr, DecidableEq

/-- One range per position. -/
abbrev Box := List Range

/-- An input: one token per position. -/
abbrev Input := List Nat

/-- The leaf rules. Only an interval leaf can name an approximation. The
    type makes every other combination impossible, so no runtime check is
    needed for it (the Python walk does one). -/
inductive Rule where
  | single
  | skip
  | interval (approx : Option String)
deriving Repr, DecidableEq

/-- A split tree, as in the proof file. -/
inductive SplitTree where
  | leaf  (rule : Rule)
  | split (position : Nat) (cuts : List Nat) (children : List SplitTree)

/-- A leaf of the walked tree: its box and its rule. -/
structure Leaf where
  box  : Box
  rule : Rule
deriving Repr

/-! ## The walk -/

/-- The pieces `[lo, c1-1], [c1, c2-1], ..., [ck, hi]` of a split. -/
def pieces (lo hi : Nat) : List Nat → List Range
  | []      => [⟨lo, hi⟩]
  | c :: cs => ⟨lo, c - 1⟩ :: pieces c hi cs

/-- The cuts increase strictly inside `(lo, hi]`: `lo < c1 < ... < ck ≤ hi`. -/
def cutsOk (lo hi : Nat) : List Nat → Bool
  | []      => true
  | c :: cs => lo < c && c ≤ hi && cutsOk c hi cs

-- Two functions that call each other, because a tree holds a list of trees.
mutual

/-- Validate the tree and list its leaves with their boxes. -/
def walk : SplitTree → Box → Except String (List Leaf)
  | .leaf rule, box => pure [Leaf.mk box rule]
  | .split p cuts children, box => do
      let some r := box[p]? | throw s!"split position {p} out of range"
      if cuts.isEmpty then throw "cuts must be a non-empty list"
      unless cutsOk r.lo r.hi cuts do
        throw s!"cuts must increase strictly inside ({r.lo}, {r.hi}]"
      unless children.length == cuts.length + 1 do
        throw s!"a split with {cuts.length} cuts needs {cuts.length + 1} children"
      walkChildren children (pieces r.lo r.hi cuts) box p

/-- Walk each child, with position `p` restricted to that child's piece. -/
def walkChildren : List SplitTree → List Range → Box → Nat → Except String (List Leaf)
  | [], [], _, _ => pure []
  | t :: ts, r :: rs, box, p => do
      let first ← walk t (List.set box p r)
      let rest ← walkChildren ts rs box p
      return first ++ rest
  | _, _, _, _ => throw "children and pieces do not match"

end

/-- The root box covers every input: position `p` takes the values
    `0, ..., space[p] - 1`. -/
def rootBox (space : List Nat) : Box :=
  space.map fun v => Range.mk 0 (v - 1)

/-- The tree that splits every position into single tokens (brute force),
    like `full_tree` in `core/check/proof.py`. -/
def fullTree (space : List Nat) : SplitTree :=
  go 0 space
where
  go (p : Nat) : List Nat → SplitTree
    | [] => .leaf .single
    | v :: vs =>
      if v ≤ 1 then go (p + 1) vs
      else .split p ((List.range v).drop 1) (List.replicate v (go (p + 1) vs))

/-! ## Running it -/

-- Splitting position 0 of [0, 3] at 2 gives the pieces [0, 1] and [2, 3].
#eval walk (.split 0 [2] [.leaf .skip, .leaf (.interval none)]) (rootBox [4, 4])

/-- The number of leaves, or `none` if the walk rejects the tree. -/
def leafCount (t : SplitTree) (space : List Nat) : Option Nat :=
  match walk t (rootBox space) with
  | .ok leaves => some leaves.length
  | .error _   => none

-- `#guard` fails the build if its test is false, so these are real tests.
-- Brute force on max2 v64 and v128: one leaf per input.
#guard leafCount (fullTree [64, 64]) [64, 64] == some 4096
#guard leafCount (fullTree [128, 128]) [128, 128] == some 16384

-- The rejections in tests/test_checker.py, where the vocabulary is 5.
#guard leafCount (.split 0 [0] [.leaf .skip, .leaf .skip]) [5, 5] == none
#guard leafCount (.split 0 [2, 2] [.leaf .skip, .leaf .skip, .leaf .skip]) [5, 5] == none
#guard leafCount (.split 0 [5] [.leaf .skip, .leaf .skip]) [5, 5] == none
#guard leafCount (.split 2 [1] [.leaf .skip, .leaf .skip]) [5, 5] == none
#guard leafCount (.split 0 [1] [.leaf .skip]) [5, 5] == none
-- and the overlapping pieces from tests/test_adversarial.py
#guard leafCount (.split 0 [2, 1] [.leaf .skip, .leaf .skip, .leaf .skip]) [5, 5] == none

/-! ## The partition theorem -/

/-- Whether token `t` lies in range `r`. -/
def inRange (r : Range) (t : Nat) : Bool :=
  r.lo ≤ t && t ≤ r.hi

/-- Whether input `x` lies in `box`: the same length, and each token inside
    its range. -/
def inBox : Box → Input → Bool
  | [], [] => true
  | r :: rs, t :: ts => inRange r t && inBox rs ts
  | _, _ => false

/-- Every input of a space, for testing on small spaces. -/
def allInputs : List Nat → List Input
  | [] => [[]]
  | v :: vs => (List.range v).flatMap fun t => (allInputs vs).map (t :: ·)

/-- The partition statement below, checked by brute force on one tree.
    Tokens one past the end are included, to test that every leaf stays
    inside the root box. -/
def partitionHolds (t : SplitTree) (space : List Nat) : Bool :=
  match walk t (rootBox space) with
  | .error _ => true
  | .ok leaves =>
    (allInputs (space.map (· + 1))).all fun x =>
      leaves.countP (fun l => inBox l.box x) == (if inBox (rootBox space) x then 1 else 0)

-- Test the statement before trying to prove it.
#guard partitionHolds (fullTree [4, 4]) [4, 4]
#guard partitionHolds
  (.split 0 [1, 3] [.leaf .skip, .split 1 [2] [.leaf .skip, .leaf (.interval none)], .leaf .single])
  [4, 4]

/-- A first lemma: a split with k cuts has k + 1 pieces. `generalizing lo`
    is needed because the recursive call starts from `c` instead of `lo`. -/
theorem pieces_length (lo hi : Nat) (cuts : List Nat) :
    (pieces lo hi cuts).length = cuts.length + 1 := by
  induction cuts generalizing lo with
  | nil => simp [pieces]
  | cons c cs ih => simp [pieces, ih]

/-! ### Lemmas for the proof -/

/-- If `walk` accepts a split, then the split position exists, its cuts are
    valid, and the children were walked over the pieces. -/
theorem walk_split_ok {p : Nat} {cuts : List Nat} {children : List SplitTree} {box : Box}
    {leaves : List Leaf} (h : walk (.split p cuts children) box = .ok leaves) :
    ∃ r, box[p]? = some r ∧ cutsOk r.lo r.hi cuts = true ∧
      walkChildren children (pieces r.lo r.hi cuts) box p = .ok leaves := by
  rw [walk.eq_2] at h
  split at h
  · rename_i r hr
    refine ⟨r, hr, ?_⟩
    simp only at h
    split at h
    · contradiction
    · split at h
      · split at h
        · exact ⟨by assumption, h⟩
        · contradiction
      · contradiction
  · contradiction

/-- If `walkChildren` accepts a list of children, then it walked the first
    child and the rest, and appended their leaves. -/
theorem walkChildren_cons_ok {t : SplitTree} {ts : List SplitTree} {r : Range}
    {rs : List Range} {box : Box} {p : Nat} {leaves : List Leaf}
    (h : walkChildren (t :: ts) (r :: rs) box p = .ok leaves) :
    ∃ l1 l2, walk t (box.set p r) = .ok l1 ∧ walkChildren ts rs box p = .ok l2 ∧
      leaves = l1 ++ l2 := by
  rw [walkChildren.eq_2] at h
  cases h1 : walk t (box.set p r) with
  | error e => simp [h1] at h; contradiction
  | ok l1 =>
    cases h2 : walkChildren ts rs box p with
    | error e => simp [h1, h2] at h; contradiction
    | ok l2 =>
      rw [h1, h2] at h
      have h' : (Except.ok (l1 ++ l2) : Except String (List Leaf)) = .ok leaves := h
      injection h' with h''
      exact ⟨l1, l2, rfl, rfl, h''.symm⟩

/-- The pieces of a valid split cover `[lo, hi]` exactly once: every token
    in `[lo, hi]` lies in exactly one piece, and every other token in none. -/
theorem pieces_partition (lo hi : Nat) (cuts : List Nat) (h : cutsOk lo hi cuts = true)
    (t : Nat) :
    (pieces lo hi cuts).countP (fun r => inRange r t) = if lo ≤ t ∧ t ≤ hi then 1 else 0 := by
  induction cuts generalizing lo with
  | nil => simp [pieces, inRange]
  | cons c cs ih =>
    simp only [cutsOk, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [pieces, List.countP_cons]
    rw [ih c h3]
    simp only [inRange, Bool.and_eq_true, decide_eq_true_eq]
    split <;> split <;> split <;> omega

/-- Whether `x` lies in `box` at every position except `p`. (Position `p`
    gets the range `[0, x_p]`, which always contains `x_p`.) -/
def inBoxExcept (box : Box) (p : Nat) (x : Input) : Bool :=
  inBox (box.set p ⟨0, x.getD p 0⟩) x

/-- Changing the range at position `p`: `x` lies in the new box exactly when
    it matches the other positions and its token `x_p` lies in the new range. -/
theorem inBox_set (box : Box) (x : Input) (p : Nat) (hp : p < box.length) (r : Range) :
    inBox (box.set p r) x = (inBoxExcept box p x && inRange r (x.getD p 0)) := by
  unfold inBoxExcept
  induction box generalizing p x with
  | nil => simp at hp
  | cons b bs ih =>
    cases x with
    | nil => cases p <;> simp [inBox]
    | cons t ts =>
      cases p with
      | zero =>
        simp only [List.set_cons_zero, List.getD_cons_zero, inBox]
        cases inBox bs ts <;> simp [inRange]
      | succ q =>
        simp only [List.set_cons_succ, List.getD_cons_succ, inBox]
        rw [ih ts q (by simpa using hp)]
        cases inRange b t <;> simp

/-- Counting with a condition `b` that does not depend on the element. -/
theorem countP_const_and {α : Type} (l : List α) (b : Bool) (f : α → Bool) :
    l.countP (fun a => b && f a) = if b then l.countP f else 0 := by
  cases b <;> simp

/-! ### The theorem -/

mutual

/-- Step 1's theorem: the leaves of an accepted tree partition its box.
    Every input in the box lies in exactly one leaf, and every other input
    in none. This is what lets the checker add up leaf counts without
    counting an input twice. It is stated for any box, not just the root,
    because the proof goes by induction and a child's box is not the root. -/
theorem walk_partition (t : SplitTree) (box : Box) (leaves : List Leaf)
    (h : walk t box = .ok leaves) (x : Input) :
    leaves.countP (fun l => inBox l.box x) = if inBox box x then 1 else 0 := by
  match t with
  | .leaf rule =>
    rw [walk.eq_1] at h
    have h' : (Except.ok [Leaf.mk box rule] : Except String (List Leaf)) = .ok leaves := h
    injection h' with h''
    subst h''
    simp
  | .split p cuts children =>
    obtain ⟨r, hr, hcuts, hw⟩ := walk_split_ok h
    obtain ⟨hp, hpr⟩ := List.getElem?_eq_some_iff.mp hr
    -- The leaves come from the children, one child per piece.
    rw [walkChildren_partition children (pieces r.lo r.hi cuts) box p leaves hw x]
    -- Across the pieces, only position `p` changes.
    simp only [inBox_set box x p hp]
    rw [countP_const_and, pieces_partition r.lo r.hi cuts hcuts]
    -- The original box is the box with the range `r` at position `p`.
    have hbox : inBox box x = (inBoxExcept box p x && inRange r (x.getD p 0)) := by
      rw [← inBox_set box x p hp r, ← hpr, List.set_getElem_self hp]
    rw [hbox]
    cases inBoxExcept box p x <;> simp [inRange]

/-- The same for a list of children, one per piece: an input is counted
    once for each piece whose box contains it. -/
theorem walkChildren_partition (ts : List SplitTree) (rs : List Range) (box : Box) (p : Nat)
    (leaves : List Leaf) (h : walkChildren ts rs box p = .ok leaves) (x : Input) :
    leaves.countP (fun l => inBox l.box x) = rs.countP (fun r => inBox (box.set p r) x) := by
  match ts, rs with
  | [], [] =>
    rw [walkChildren.eq_1] at h
    have h' : (Except.ok [] : Except String (List Leaf)) = .ok leaves := h
    injection h' with h''
    subst h''
    simp
  | t :: ts, r :: rs =>
    obtain ⟨l1, l2, h1, h2, rfl⟩ := walkChildren_cons_ok h
    simp only [List.countP_append, List.countP_cons, walk_partition t _ l1 h1 x,
      walkChildren_partition ts rs box p l2 h2 x]
    omega
  | [], _ :: _ => rw [walkChildren.eq_def] at h; simp only at h; contradiction
  | _ :: _, [] => rw [walkChildren.eq_def] at h; simp only at h; contradiction

end

/-! ## Exercises -/

-- W1. Add a `#guard` showing that an interval leaf with an approximation
--     name, `.leaf (.interval (some "A"))`, is accepted.

-- W2. Write a tree with three levels of splits on [5, 5] and check it with
--     `partitionHolds`.

-- W3. A first proof of your own. Hint: `cases cuts <;> simp [pieces]`.
theorem pieces_ne_nil (lo hi : Nat) (cuts : List Nat) : pieces lo hi cuts ≠ [] := by
  cases cuts <;> simp [pieces]

end CompactCheck
