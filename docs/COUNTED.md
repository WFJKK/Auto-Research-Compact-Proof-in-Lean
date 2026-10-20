# The counted language (design, step 2 of the open lane)

How a scored open-lane proof gets a length: its checker `D` is written against a monad whose only way to
touch a number is a charged primitive, and a mechanical check of `D`'s definition makes sure of it.

## The problem

Length must be the operation count of `cost-v3`, not time, and the interpreter must control the bill: `D`
must not be an arbitrary Lean function that reports how much work it did. A deep embedding (an inductive
`Prog` with an interpreter) does that but makes every `D` and every proof about it painful. A plain monad does
not do it: a `StateM Nat` computation can call any pure Lean function for free, including one that inspects
the weights.

## The design

- `Q`: a structure around `ℚ`. In theorems it is transparent (`Q.val`); in `D` it is sealed by the check
  below, so `D` can only make and combine `Q` values through the primitives.
- `CostM α`: a structure around `Env → Cost → Option (α × Cost)`, with its own `Monad` instance. `Env`
  holds the weights and the certificate; `Cost` is the bill, by category. `D : CostM Nat` takes no
  argument: it reaches the weights and the certificate only through the primitives. (A structure, not a
  function type, so that `D` cannot be written as `fun env cost => ...`.)
- Primitives, each with a fixed charge from `cost-v3`:
  - `qadd`, `qsub`, `qmuladd`, `qneg`, `qmin`, `qmax`: 1 each; `qlt`, `qle`, `qeq`: 1 each, returning `Bool`;
  - `weight name i : CostM Q`: free (the weights are charged once per proof, as `extract`, E);
  - `cert i : CostM Q`: free (the certificate is charged once per proof, as `read`, 1 per number);
  - `lit n : CostM Q` for a numeral: 1 (as a number read from the proof file);
  - `expLo`, `expHi`: the exponential's enclosure (`Exp.lean`), charged as `cost-v3` charges `exp`;
  - `charge category n`: adds to the bill (a program can only make itself longer; this is how a port
    mirrors structural charges such as `tree`).
  - loops, conditionals, `Nat`, `Bool`, lists and arrays: ordinary Lean, free, as the Python checker's
    bookkeeping is free. There is no bridge from `Q` to `Nat` except a charged comparison to `Bool`.
- `exec D env : Option (Nat × Cost)`: the result and the bill, plus E and the certificate's size.

## The check

The service walks the constants `D` uses, transitively through the candidate's own definitions (not into
proofs: a theorem computes nothing), and requires every other constant to be on an allowlist
(`accept/allowlist.txt`, part of the trusted base). The allowlist holds the primitives, `CostM`'s `bind` and
`pure`, and the pure structural functions of core Lean on `Nat`, `Bool`, `List`, `Array`, `Option`, `Prod`,
`Fin` and `String` that the ported rules use. Not on it, so not available to `D`: `Q.val`, `Q.mk`, `Q.rec`,
`CostM.mk`, `CostM.run`, anything of `ℚ` or `ℝ`, `StateT`'s `get` and `set`, `ReaderT.read`. A `D` that uses
anything else is refused scoring, with the names listed; the proof may still be accepted as mathematically
verified.

Why this is enough: every number of the network enters `D` as a `Q` from `weight`, every number of the
certificate as a `Q` from `cert`, every constant through `lit`, and `Q` values can only be combined by the
charged primitives or turned into a `Bool` by a charged comparison. Free computation on `Nat` and `Bool`
cannot read a `Q`. So every operation on a value of the network is on the bill. The `Monad` instance is
ours, so `do` notation desugars to our `bind`.

## Soundness, the fixed shape

    theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
        CostM.exec D ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task

The service builds this statement itself from `D`, `graph` and `task` and asks the kernel to accept the
candidate's theorem at that type, as it does for the target. Proofs about `D` use `run_bind`, `run_pure` and
one lemma per primitive (`(qadd a b).val = a.val + b.val`, and so on), which the library proves once.

## The instance, two tiers

- `compiled`: the service runs `exec D ⟨weights, cert⟩` with the compiled interpreter (`acceptcheck run`) and
  records `n` and the bill. The trust is the Lean compiler's, as for `compactcheck`.
- `kernel`: the candidate proves `exec D ⟨weights, cert⟩ = some (n, cost)` by `decide +kernel`, and the target
  follows inside Lean. Feasible on small networks; the receipt says which tier was reached.

## Reproduction

`single`, `skip`, `interval`, `contract`, `symmetry` and `approximate` are ported as `CostM` programs that
mirror the Python checker's loops, with a program `checkProofCounted : Cert → CostM Nat` that walks a
split-tree proof file. The gate: on the four max2 baselines and every proof of the recorded max2 runs, the
bill equals the Python length to the unit and the count equals the Python count. Their soundness comes from
equivalence with `checkProof` (`Check.lean`), which is proved sound already.

## What stays open

The general-layer safeguards (no reference to the protected constants outside the instance, a literal
budget, a kernel budget over the new dependency closure) and the adversarial tests are part of the same
step; the anti-hiding property itself is an obligation, not a theorem.
