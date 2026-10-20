# The counted language (step 2 of the open lane)

How a scored open-lane proof gets a length: its checker `D` is written against a monad whose only way to
touch a number of the network is a charged primitive, a mechanical check of `D`'s definition makes sure of
it, and the kernel evaluates `D` on the protected weights.

## The problem

Length must be the operation count of `cost-v3`, not time, and the service must control the bill: `D` must
not be an arbitrary Lean function that reports how much work it did. A plain monad does not do it: a
`StateM Nat` computation can call any pure Lean function for free, including one that inspects the weights.

## The design (`Counted.lean`, `CountedOps.lean`)

- `Q`: a structure around `ℚ`. In theorems it is transparent (`Q.val`); in `D` it is sealed by the check
  below, so `D` can only make and combine `Q` values through the primitives.
- `CostM α`: a structure around `Env → Cost → Option (α × Cost)`, with its own `Monad` instance. `Env`
  holds the weights and the certificate; `Cost` is the bill, by category. `D : CostM Nat` takes no
  argument: it reaches the weights and the certificate only through the primitives. (A structure, not a
  function type, so that `D` cannot be written as `fun env cost => ...`: `CostM.mk` and `CostM.run` are
  not on the allowlist.)
- Primitives, each with a fixed charge from `cost-v3`:
  - `qadd`, `qsub`, `qmuladd`, `qneg`, `qmin`, `qmax`: 1 each; `qlt`, `qle`, `qeq`: 1 each, returning `Bool`;
  - `weight name i : CostM Q`: free (the weights are charged once per proof, as `extract`, E);
  - `cert i : CostM Q`: free (the certificate is charged once per proof, as `read`, 1 per number);
  - `lit n : CostM Q` for a numeral: 1 (as a number read from the proof file);
  - `qexp`: the exponential's enclosure (`Exp.lean`), charged 3, as `cost-v3` charges a softmax entry;
  - `charge category n`: adds to the bill (a program can only make itself longer).
  - loops, conditionals, `Nat`, `Bool`, lists and arrays: ordinary Lean, free, as the Python checker's
    bookkeeping is free. There is no bridge from `Q` to `Nat` except a charged comparison to `Bool`.
- Counted operations (`CountedOps.lean`): the checker's own rules as charged calls, each with a
  specification lemma. `CostM.single graph task x` runs the single-input rule and charges `singleCost`
  (one exact forward pass and the comparison, exactly what `cost-v3` charges a `single` leaf);
  `CostM.interval graph task box` runs the interval rule on a box and charges `intervalCost`. A scored
  checker composes these; a checker written from the arithmetic primitives alone is possible but has to
  reproduce the rules' arithmetic itself.
- `exec D env : Option (Nat × Cost)`: the result and the bill; `billed D env : Option (Nat × Nat)`: the
  result and the bill's total, which is what the instance theorem states.

## The check (`acceptcheck closure`)

The service walks the constants `D` uses, transitively through the candidate's own definitions (not into
proofs: a theorem computes nothing), and requires every other constant to be on an allowlist
(`accept/allowlist.txt`, part of the trusted base and of the policy digest). The allowlist holds the
primitives, the counted operations, `CostM`'s `bind` and `pure`, the structural functions of core Lean on
`Nat`, `Bool`, `List`, `Array`, `Option`, `Prod`, `Fin` and `String`, and the checker's own structural
types (inputs, boxes, the task's shape). The protected module's `graph` and `task` are allowed (the
soundness statement mentions them); its `weights`, `cert`, `claimedCount` and `Target` are not. Not on
the list: `Q.val`, `Q.mk`, `CostM.mk`, `CostM.run`, anything of `ℚ` or `ℝ`. A `D` that uses anything
else is refused scoring, with the names listed; the proof stays verified.

Why this is enough: every number of the network enters `D` as a `Q` from `weight` or through a counted
operation, every number of the certificate as a `Q` from `cert`, every constant through `lit`, and `Q`
values can only be combined by the charged primitives or turned into a `Bool` by a charged comparison.
Free computation on `Nat` and `Bool` cannot read a `Q`. So every operation on a value of the network is
on the bill. The `Monad` instance is ours, so `do` notation desugars to our `bind`.

## The two statements (`acceptcheck score`)

The service builds both statements itself and asks the kernel to accept the candidate's theorems at
exactly these types, as it does for the target:

    Challenge.sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
        CostM.exec D ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task

    Challenge.instance : CostM.billed D ⟨weights, cert⟩ = some (claimedCount, claimedBill)

The instance is always kernel-checked (`decide +kernel` in the candidate; the service never runs
candidate code). Proofs about `D` use `run_bind`, `run_pure`, the operations' specification lemmas
(`single_spec`, `interval_spec`) and `exec_of_billed`, which turns the instance into the hypothesis of
soundness, so the target follows inside the candidate.

## Why the reported cost is the cost

Proving that a checker's count is right says nothing about its bill, so the bill is never reported by the
candidate: the instance theorem `CostM.billed D ⟨weights, cert⟩ = some (n, L)` is accepted by the kernel at
a statement the service builds, so `L` is what the monad's semantics charges on the protected weights, as
the kernel computes it. What makes that charge the whole cost is the closure check above: every number of
the network or the certificate reaches `D` as a sealed `Q` through a charged primitive or a counted
operation, nothing on the allowlist can open a `Q`, and free computation on `Nat` and `Bool` cannot read
one, so no chargeable work can happen outside the bill. The general-layer budgets bound what the free part
can carry. A receipt's `execution_assurance` is `kernel_checked_instance` for this reason: the count and the
bill are both kernel-checked for the exact checker, certificate and weights; nothing of a candidate is ever
executed by the service.

## The manifest and the receipt

A scored submission adds to its manifest

    "scored": {"checker": ..., "sound": ..., "instance": ..., "certificate": [numbers], "claimed_bill": L}

The certificate (integers, floats, or `[p, q]` pairs) becomes the protected module's `cert`, and its hash
becomes part of the module's name. The receipt's `claim_kind` is `performance` (a proof of Target) or
`auxiliary` (a lemma with any statement, accepted with no count and no score: `"kind": "auxiliary"` in the
manifest), `score_eligible` says whether it was scored, and the `scoring` block says `scored` or `refused`
(with the reason) and gives the length in `cost-v3` units:

    length = claimed_bill + extract + read,  extract = number of weight entries,  read = certificate size

The mapping to `cost-v3`'s categories: `single` and `interval` through the counted operations, `extract`
and `read` as above, the arithmetic categories through the primitives. `tree` has no counterpart: the
structure of a scored proof is its program, bounded by the literal budget below rather than charged.

## General-layer safeguards

The general layer is the checker, its soundness proof and everything they depend on. Beyond the closure
check, the service enforces, as policy (recorded in the receipt's policy digest):

- no reference to a protected constant other than `graph` and `task` from the general layer
  (`acceptcheck score` rejects it; the closure check catches it in `D` first);
- a literal budget: the literal weight of the general layer (1 per 16 bits of a natural number literal,
  1 per 2 bytes of a string literal, over the statements of all its constants and the bodies of its
  definitions, not of its proofs) is at most `32 + E / 8`. A copy of the weights costs at least about
  `2 E`, so it cannot fit, while a general checker needs a handful;
- a kernel budget: replaying the general layer (timed on its own, before the rest) takes at most 120 s.

These bound what the general layer can hide; they do not prove that nothing is hidden. The adversarial
tests in `scripts/test_accept.py` say so in their names.

## Reproduction (`CountedCheck.lean`, `compactcheck cost`)

`checkProofCounted` walks a split-tree proof file as `checkProof` does and bills it with `cost-v3`'s
formulas, category by category: `extract`, `read`, `tree`, `single`, `interval`, `contract`,
`approximate`, `symmetry`. The gate: on the four max2 baselines and every proof of the recorded max2 runs,
the bill equals the Python length to the unit and the count equals the Python count
(`scripts/test_cost.py`). Its soundness comes from the count being `checkProof`'s, which is proved sound.

## What stays open

`token_interval` and `token_convex` as counted operations (needed to reproduce the attention
frontiers, not for this slice); the `interval` operation with an approximation; a literal budget
calibrated on more than the brute-force example.
