import CompactCheck.Network
import CompactCheck.Exp

/-!
# The counted language: a monad whose every operation on a number is charged

A scored open-lane proof's checker `D : CostM Nat` is written here. `CostM` holds the weights and
the certificate, and a bill; the only way for `D` to make or use a number of the network is one of the
primitives below, each with a fixed charge from `cost-v3`. Loops, conditionals and arithmetic on `Nat`
and `Bool` are ordinary Lean and free, as the Python checker's bookkeeping is. The acceptance service
checks that `D` uses nothing else (`docs/COUNTED.md`): in `D`, `Q` and `CostM` are sealed; in theorems
about `D`, `Q.val` and `CostM.run` are plain projections.

Nothing here is trusted for soundness: a proof about a checker written in `CostM` is a theorem about
these definitions. What the service trusts is the charge of each primitive, as the number cost-v3 gives
the operation.

This file uses only core Lean.
-/

namespace CompactCheck

/-- A number of the network, sealed inside `D`. -/
structure Q where
  val : Rat
deriving Repr

/-- A certificate: the numbers a proof hands the checker, read once (charged `read`, 1 each). -/
abbrev Cert := Array Rat

/-- What a checker runs against. -/
structure Env where
  weights : Weights Rat
  cert : Cert

/-- The bill: operations by category, as `core/check/cost.py` keeps them. -/
abbrev Cost := List (String × Nat)

namespace Cost

def add (c : Cost) (cat : String) (n : Nat) : Cost :=
  match c with
  | [] => [(cat, n)]
  | (k, m) :: rest => if k == cat then (k, m + n) :: rest else (k, m) :: add rest cat n

def total (c : Cost) : Nat := (c.map (·.2)).sum

def get (c : Cost) (cat : String) : Nat :=
  match c.find? (·.1 == cat) with
  | some (_, n) => n
  | none => 0

end Cost

/-- A counted computation: from the environment and the bill so far to a result and the new bill, or
    `none` when a primitive is misused (a weight that does not exist, say). A structure, not a function
    type, so that a checker cannot be written as a bare function of the environment: inside `D`, neither
    `CostM.mk` nor `CostM.run` is available. -/
structure CostM (α : Type) where
  run : Env → Cost → Option (α × Cost)

namespace CostM

protected def pure (a : α) : CostM α := ⟨fun _ c => some (a, c)⟩

protected def bind (x : CostM α) (f : α → CostM β) : CostM β := ⟨fun env c =>
  match x.run env c with
  | some (a, c') => (f a).run env c'
  | none => none⟩

instance : Monad CostM where
  pure := CostM.pure
  bind := CostM.bind

/-- Run a checker from an empty bill: the result and the bill, if every primitive was used properly. -/
def exec (x : CostM α) (env : Env) : Option (α × Cost) := x.run env []

/-- The result and the bill's total: what a scored submission's instance theorem states,
    `CostM.billed D ⟨weights, cert⟩ = some (n, L)`. -/
def billed (x : CostM α) (env : Env) : Option (α × Nat) :=
  (x.exec env).map fun p => (p.1, p.2.total)

/-- Fail: the checker certifies nothing. -/
def fail : CostM α := ⟨fun _ _ => none⟩

/-! ## Primitives, with their charges -/

/-- Add to the bill. A program can only make itself longer. -/
def charge (cat : String) (n : Nat) : CostM Unit := ⟨fun _ c => some ((), c.add cat n)⟩

/-- Entry `i` of the weight `name`, in row-major order. Free: the weights are charged once per proof
    (`extract`, E). -/
def weight (name : String) (i : Nat) : CostM Q := ⟨fun env c =>
  match List.lookup name env.weights with
  | some t => if i < t.data.size then some (⟨t.data[i]!⟩, c) else none
  | none => none⟩

/-- The shape of a weight, for loops. Free. -/
def weightShape (name : String) : CostM (List Nat) := ⟨fun env c =>
  match List.lookup name env.weights with
  | some t => some (t.shape, c)
  | none => none⟩

/-- The number of entries of the weight `name` (its data length, which may differ from the product of its
    shape in an ill-formed network file). Free, like `weightShape`: structural metadata, not a number of
    the network. Before version 4.1 (cost-v4) a checker could bound a tensor's length from above only by
    running a whole forward pass (`single`), which every proof paid once. -/
def weightSize (name : String) : CostM Nat := ⟨fun env c =>
  match List.lookup name env.weights with
  | some t => some (t.data.size, c)
  | none => none⟩

theorem weightSize_spec {name : String} {env : Env} {c c' : Cost} {n : Nat}
    (h : (weightSize name).run env c = some (n, c')) :
    ∃ t, List.lookup name env.weights = some t ∧ t.data.size = n ∧ c' = c := by
  simp only [weightSize] at h
  split at h
  · rename_i t ht
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨t, ht, h.1, h.2.symm⟩
  · cases h

/-- Number `i` of the certificate. Free: the certificate is charged once per proof (`read`). -/
def cert (i : Nat) : CostM Q := ⟨fun env c =>
  if i < env.cert.size then some (⟨env.cert[i]!⟩, c) else none⟩

/-- How many numbers the certificate holds. Free. -/
def certSize : CostM Nat := ⟨fun env c => some (env.cert.size, c)⟩

/-- A numeral, as a number read from the proof file: 1. -/
def lit (cat : String) (n : Nat) : CostM Q := ⟨fun _ c => some (⟨(n : Rat)⟩, c.add cat 1)⟩

/-- Zero, free: the Python checker starts its sums at 0 without charge. -/
def zero : CostM Q := ⟨fun _ c => some (⟨0⟩, c)⟩

def qadd (cat : String) (a b : Q) : CostM Q := ⟨fun _ c => some (⟨a.val + b.val⟩, c.add cat 1)⟩
def qsub (cat : String) (a b : Q) : CostM Q := ⟨fun _ c => some (⟨a.val - b.val⟩, c.add cat 1)⟩
/-- A multiply-add, `acc + a * b`: 1. -/
def qmuladd (cat : String) (acc a b : Q) : CostM Q :=
  ⟨fun _ c => some (⟨acc.val + a.val * b.val⟩, c.add cat 1)⟩
def qneg (cat : String) (a : Q) : CostM Q := ⟨fun _ c => some (⟨-a.val⟩, c.add cat 1)⟩
def qmin (cat : String) (a b : Q) : CostM Q := ⟨fun _ c => some (⟨min a.val b.val⟩, c.add cat 1)⟩
def qmax (cat : String) (a b : Q) : CostM Q := ⟨fun _ c => some (⟨max a.val b.val⟩, c.add cat 1)⟩
def qlt (cat : String) (a b : Q) : CostM Bool := ⟨fun _ c => some (decide (a.val < b.val), c.add cat 1)⟩
def qle (cat : String) (a b : Q) : CostM Bool := ⟨fun _ c => some (decide (a.val ≤ b.val), c.add cat 1)⟩
def qeq (cat : String) (a b : Q) : CostM Bool := ⟨fun _ c => some (decide (a.val = b.val), c.add cat 1)⟩

/-- Bounds on `exp a` (`Exp.lean`, as the Python checker computes them), charged 3 as a softmax entry
    of `cost-v3`'s general networks; `none` if the argument is out of the bounds' range. -/
def qexp (cat : String) (a : Q) : CostM (Q × Q) := ⟨fun _ c =>
  match expInterval a.val with
  | some (lo, hi) => some ((⟨lo⟩, ⟨hi⟩), c.add cat 3)
  | none => none⟩

end CostM

end CompactCheck
