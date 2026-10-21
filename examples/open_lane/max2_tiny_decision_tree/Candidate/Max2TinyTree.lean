import Protected.N_max2_tiny_v8_s0_c0
import CompactCheck.Soundness
import CompactCheck.CountedOps

/-!
# A decision tree over truth values, written in the counted language (version 4)

A reviewer's counterexample to version 3 (21 October 2026): with a free mask `nmask : B → N → N`,

    decode [] acc = nofNat (f acc)
    decode ((b, nb) :: rest) acc = nadd (nmask b (decode rest (2 acc + 1))) (nmask nb (decode rest (2 acc)))

selects `f` of the number the bits spell, for nothing: a conditional on counts, and `f` is any Lean
function. Version 4 has no mask on a count. This is the same decoder written in version 4: the path
indicator `p` goes through a charged gate at every node (`p && b`, `p && !b`), and the leaves are
`nscale (f acc) p`, a concrete multiple of one truth value. So a tree over `k` truth values bills
`3 (2^k - 1)` gates, every node of it, whatever its leaves compute: the bill is the tree. Here `f` is the
zero function and the tree certifies nothing (the claim is 0); what the service records is its bill.
-/

namespace Candidate.Max2TinyTree

open CompactCheck Protected.N_max2_tiny_v8_s0_c0

abbrev K := Interp.counting

def cat : String := "m"
def nE : String := "embedding.weight"
def k4 : Nat := 4

/-- Any function of the decoded number; the zero function here. -/
def leaf (_ : Nat) : Nat := 0

/-- `k` truth values about one weight: `w < t` for `t = 1 .. k`, each a numeral and a comparison. -/
def bitsOf (I : Interp) (w : I.V) : Nat → I.M (List I.B)
  | 0 => pure []
  | Nat.succ j => do
    let t ← I.lit cat (Nat.succ j)
    let b ← I.lt cat w t
    let bs ← bitsOf I w j
    pure (b :: bs)

/-- The decoder: a path indicator through a charged gate at every node, a concrete multiple of it at
    every leaf. -/
def decode (I : Interp) : List I.B → Nat → I.B → I.M I.N
  | [], acc, p => pure (I.nscale (leaf acc) p)
  | b :: rest, acc, p => do
    let nb ← I.bnot cat b
    let p1 ← I.band cat p b
    let p0 ← I.band cat p nb
    let x ← decode I rest (2 * acc + 1) p1
    let y ← decode I rest (2 * acc) p0
    pure (I.nadd x y)

def D : Checker := fun I => do
  let w ← I.weight nE 0
  let bs ← bitsOf I w k4
  decode I bs 0 I.btrue

theorem bind_some {α β : Type} {x : CostM α} {f : α → CostM β} {env : Env} {c c' : Cost} {b : β}
    (h : (x >>= f).run env c = some (b, c')) :
    ∃ a c1, x.run env c = some (a, c1) ∧ (f a).run env c1 = some (b, c') := by
  rw [CostM.run_bind] at h
  split at h
  · rename_i a c1 ha; exact ⟨a, c1, ha, h⟩
  · cases h

theorem pure_some {α : Type} {a b : α} {env : Env} {c c' : Cost}
    (h : (pure a : CostM α).run env c = some (b, c')) : b = a ∧ c' = c := by
  rw [CostM.run_pure] at h
  simp only [Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- Every leaf is a multiple of zero, so the tree's count is zero. -/
theorem decode_zero {env : Env} : ∀ (bs : List Bool) (acc : Nat) (p : Bool) {c c' : Cost} {n : Nat},
    (decode K bs acc p).run env c = some (n, c') → n = 0
  | [], acc, p, c, c', n, h => by
    simp only [decode] at h
    rw [(pure_some h).1]
    cases p <;> rfl
  | b :: rest, acc, p, c, c', n, h => by
    simp only [decode] at h
    obtain ⟨nb, c1, -, h⟩ := bind_some h
    obtain ⟨p1, c2, -, h⟩ := bind_some h
    obtain ⟨p0, c3, -, h⟩ := bind_some h
    obtain ⟨x, c4, hx, h⟩ := bind_some h
    obtain ⟨y, c5, hy, h⟩ := bind_some h
    rw [(pure_some h).1, decode_zero rest _ p1 hx, decode_zero rest _ p0 hy]

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  have h' : (D K).run ⟨w, c⟩ [] = some (n, cost) := h
  simp only [D] at h'
  obtain ⟨wq, c1, -, h'⟩ := bind_some h'
  obtain ⟨bs, c2, -, h'⟩ := bind_some h'
  rw [decode_zero bs 0 true h']
  exact Nat.zero_le _

/-- 4 numerals and 4 comparisons, then 15 nodes at 3 gates each. -/
theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (0, 53) := by
  decide +kernel

theorem performance : Target := by
  show claimedCount ≤ numCorrect graph weights task
  exact Nat.zero_le _

end Candidate.Max2TinyTree
