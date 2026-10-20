/-
  Lean basics, with examples shaped like the checker.

  Open this file in VS Code with the Lean 4 extension. The panel on the
  right (the "infoview") shows the output of every `#eval`, and inside a
  proof it shows what is still to be proved at the cursor. Move the cursor
  through the proofs line by line and watch the goal change.
-/
import Mathlib

namespace Tutorial

/-! ## 1. Definitions and evaluation -/

/-- A function: name, arguments with types, result type, body. -/
def double (n : Nat) : Nat := 2 * n

#eval double 21              -- 42

/-! Subtraction on `Nat` stops at zero. This matters for range sizes. -/
#eval (3 : Nat) - 5          -- 0, not -2
#eval (3 : Int) - 5          -- -2

/-! ## 2. Structures: records with named fields -/

structure Range where
  lo : Nat
  hi : Nat
deriving Repr

/-- The number of tokens in `[lo, hi]`, which is zero if `hi < lo`. -/
def Range.size (r : Range) : Nat := r.hi + 1 - r.lo

#eval (Range.mk 3 7).size                   -- 5
#eval ({ lo := 3, hi := 7 } : Range).size   -- the same, with field names

/-! ## 3. Inductive types: a value is one of several cases -/

inductive Rule where
  | single
  | skip
  | interval
deriving Repr, DecidableEq

/-- Pattern matching: one line per case. Lean refuses the definition if a
    case is missing. -/
def Rule.canCertify : Rule → Bool
  | .single   => true
  | .interval => true
  | .skip     => false

#eval Rule.skip.canCertify   -- false

/-! ## 4. Recursion on lists -/

/-- `[]` is the empty list, and `x :: xs` is `x` in front of the list `xs`. -/
def total : List Nat → Nat
  | []      => 0
  | x :: xs => x + total xs

#eval total [1, 2, 3]        -- 6

/-! ## 5. Failure: `Except`

A checker must be able to reject. A value of type `Except String α` is
either `.ok a` or `.error message`. Inside `do`, `throw` stops with an
error and `return` finishes with a result. -/

def safeDiv (a b : Nat) : Except String Nat := do
  if b = 0 then throw "division by zero"
  return a / b

#eval safeDiv 7 2            -- Except.ok 3
#eval safeDiv 7 0            -- Except.error "division by zero"

/-! ## 6. `Bool` versus `Prop`

A `Bool` is a value a program computes: `true` or `false`.
A `Prop` is a mathematical statement: it can be proved, not run.
The checker computes `Bool`s; theorems are `Prop`s. A decidable
statement such as `a ≤ b` becomes a `Bool` through `decide`, which Lean
inserts automatically here: -/

def ordered (a b : Nat) : Bool := a ≤ b

#eval ordered 2 5            -- true

/-! ## 7. Theorems and tactics

A theorem is a statement plus a proof. After `by` come tactics. Each one
changes the goal shown in the infoview, until no goal is left. -/

theorem double_add (a b : Nat) : double (a + b) = double a + double b := by
  unfold double   -- goal is now: 2 * (a + b) = 2 * a + 2 * b
  omega           -- decides linear arithmetic over Nat and Int

/-- `simp` rewrites with known lemmas, here `decide_eq_true_eq`. -/
theorem ordered_iff (a b : Nat) : ordered a b = true ↔ a ≤ b := by
  simp [ordered]

/-- Induction on a list: prove the empty case, then the case `x :: xs`
    using the statement for `xs` (called `ih`, the induction hypothesis). -/
theorem total_append (xs ys : List Nat) :
    total (xs ++ ys) = total xs + total ys := by
  induction xs with
  | nil => simp [total]
  | cons x xs ih => simp [total, ih, Nat.add_assoc]

/-- A statement about concrete numbers can be proved by computing it. -/
example : total [1, 2, 3] = 6 := by decide

/-- `sorry` marks a missing proof. Lean accepts it with a warning, so you
    can state theorems first and prove them later. -/
theorem later (n : Nat) : n + 0 = n := by
  sorry

/-! ## 8. The whole project in miniature

A checker, its soundness theorem proved once, and a concrete result
obtained by running the checker. The real project has the same three
parts, with weights in place of `n` and a proof file in place of `d`. -/

/-- The checker: `d` is a certificate that `n` is not prime. -/
def checkFactor (n d : Nat) : Bool := decide (1 < d ∧ d < n ∧ n % d = 0)

#eval checkFactor 91 7       -- true

/-- Soundness, proved once for every `n` and `d`. -/
theorem checkFactor_sound (n d : Nat) (h : checkFactor n d = true) :
    ¬ Nat.Prime n := by
  simp only [checkFactor, decide_eq_true_eq] at h
  -- h : 1 < d ∧ d < n ∧ n % d = 0
  obtain ⟨h1, h2, h3⟩ := h
  intro hp
  have hd : d ∣ n := Nat.dvd_of_mod_eq_zero h3
  rcases hp.eq_one_or_self_of_dvd d hd with h4 | h4 <;> omega

/-- A concrete result: run the checker (`by decide`), then apply soundness. -/
theorem not_prime_91 : ¬ Nat.Prime 91 := checkFactor_sound 91 7 (by decide)

/-! ## Exercises: replace each `sorry` -/

-- E1. Use `unfold` and `omega`, as in `double_add`.
theorem double_pos (n : Nat) (h : 0 < n) : 0 < double n := by
  sorry

-- E2. What is the size of an empty range? Prove it by computing.
example : (Range.mk 7 3).size = 0 := by
  sorry

-- E3. Induction, using `total_append` and `List.reverse_cons`.
theorem total_reverse (xs : List Nat) : total xs.reverse = total xs := by
  sorry

end Tutorial
