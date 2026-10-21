# The counted language (step 2 of the open lane; version 4, 21 October)

How a scored open-lane proof gets a length: its checker `D` is written against an abstract interpreter
whose operations are the only way to touch a number of the network, the service runs it with the
interpreter that charges `cost-v3`'s prices, a mechanical check of `D`'s definition makes sure it reaches
no other interpreter, and the kernel evaluates the result on the protected weights.

## The problem

Length must be the operation count of `cost-v3`, not time, and the service must control the bill: `D` must
not be an arbitrary Lean function that reports how much work it did. A plain monad does not do it: a
`StateM Nat` computation can call any pure Lean function for free, including one that inspects the weights.

## The design (`Counted.lean`, `CountedOps.lean`)

A checker is a function of an interpreter:

    abbrev Checker := (I : Interp) → I.M I.N

`Interp` (CountedOps.lean) is a structure of abstract types and operations: a monad `M`, numbers `V`,
truth values `B`, counts `N`; `weight`, `cert`, `lit`, `zero`; `add`, `sub`, `muladd`, `neg`, `min`,
`max`; `lt`, `le`, `eq`; `exp`; `charge`, `fail`; `btrue`, `bfalse`, `countB`, `nscale`, `selectV`,
`bnot`, `band`, `bor`; `nzero`, `nsucc`, `nadd`, `nofNat`; and the checker's own rules as operations,
`single` and `interval`. The checker's own code is ordinary Lean on lists, `Nat` indices and strings
around these calls, and it has to typecheck for every `I`: so it can never look inside a value of `I.V`,
`I.B` or `I.N`. There is no branching on a truth value: it can only become a count (`countB`, or
`nscale k`: a concrete `k` if true), a choice between two numbers (`selectV`, charged) or another truth
value through a charged gate. So nothing learned about the network ever decides what the checker's own
code does next, and the bill the interpreter keeps is the whole cost of the computation. The shapes of
the weights (`weightShape`) and the certificate's size are concrete and may be branched on: they are
public structure, not the network's numbers.

Counts are terminal. The operations that make an `N` are `nzero`, `nsucc`, `nadd`, `nofNat` (concrete
numbers) and `countB`, `nscale` (a concrete multiple of one truth value); none takes a count together
with a truth value or a number, and none takes a count and returns anything but a count. So every count
is a sum of concrete numbers and concrete multiples of truth values that charged operations produced, and
a count never encodes a computation on the network: a product of two truth values exists only through a
charged gate. The full list of signatures is the structure itself (CountedOps.lean); the test
`test_a_decision_tree_over_truth_values_bills_every_node` shows what the rule costs.

`Interp.counting` is the interpreter the service runs: `M` is `CostM` (Counted.lean, a structure around
`Env → Cost → Option (α × Cost)` with the weights and the certificate in `Env` and the bill in `Cost`),
`V` is `Q` (a structure around `ℚ`), `B` is `Bool`, `N` is `Nat`. Its charges are `cost-v3`'s:

- `add`, `sub`, `muladd`, `neg`, `min`, `max`: 1 each; `lt`, `le`, `eq`: 1 each;
- `weight name i`: free (the weights are charged once per proof, as `extract`, E);
- `cert i`: free (the certificate is charged once per proof, as `read`, 1 per number);
- `lit n` for a numeral: 1 (as a number read from the proof file);
- `exp`: the exponential's enclosure (`Exp.lean`), charged 3, as `cost-v3` charges a softmax entry;
- `charge category n`: adds to the bill (a program can only make itself longer);
- `single graph task x`: the single-input rule, charged `singleCost` (one exact forward pass and the
  comparison, exactly what `cost-v3` charges a `single` leaf); `interval graph task box`: the interval
  rule on a box, charged `intervalCost`;
- loops, conditionals on `Nat`, lists and arrays, `nsucc`, `nadd`: free, as the Python checker's
  bookkeeping is free.

`CostM.exec (D Interp.counting) env : Option (Nat × Cost)` is the result and the bill; `CostM.billed`
the result and the bill's total, which is what the instance theorem states. Every operation of the
counting interpreter is a `CostM` function with a specification lemma (`CostM.single_spec`,
`CostM.interval_spec`, `run_bind`, `run_pure`, `exec_of_billed`), and `Interp.counting` is reducible, so a
soundness proof unfolds `D Interp.counting` to those functions and never looks inside the monad.

### Why this shape, after three reviews

The first version (20 October, morning) was a concrete monad, `D : CostM Nat`, with `Bool` results from
the charged comparisons and free `Nat` arithmetic: a reviewer showed that bits from comparisons can be
turned back into numbers by free arithmetic, so a checker could binary-search every weight at about 50
charged operations each and then run the network for nothing. The second version (that evening) made
numbers, truth values and counts abstract but kept `ifN : B → M N → M N → M N` and free gates: the
reviewer showed that `I.ifN bit (k 1) (k 0)` hands the bit to the checker's own code `k` through which
branch runs, whatever the branch returns, and that gates alone give bit-level arithmetic. Version 3 (21
October) removed branching and charged the gates, but kept a free mask `nmask : B → N → N`: the reviewer
showed that `nadd (nmask b (k 1)) (nmask nb (k 0))` is a conditional on counts, so a recursive decoder
selects `f` of the number a list of truth values spells, for nothing, with `f` any Lean function. Hence
version 4: no operation takes a count and a truth value; a truth value becomes a count only as a concrete
multiple (`nscale`), and a product of truth values costs a gate. The decoder written in version 4
(`examples/open_lane/max2_tiny_decision_tree`) bills every node of its tree. This is the shape of the
split-tree checker too, whose structure comes from the certificate and whose results only become counts.

## The check (`acceptcheck closure`)

The service walks the constants `D` uses, transitively through the candidate's own definitions (not into
proofs: a theorem computes nothing), and requires every other constant to be on an allowlist
(`accept/allowlist.txt`, part of the trusted base and of the policy digest). The allowlist holds the
interface (`Interp` and its fields, `instMonadInterp`, `Checker`), the monad classes, the structural
functions of core Lean on `Nat`, `Bool`, `List`, `Array`, `Option`, `Prod`, `Fin` and `String`, and the
checker's own structural types (inputs, boxes, the task's shape). The protected module's `graph` and
`task` are allowed (the soundness statement mentions them); its `weights`, `cert`, `claimedCount` and
`Target` are not. Not on the list: `Interp.counting`, anything of `CostM` or `Q`, anything of `ℚ` or
`ℝ`, `Classical.*`, `cast`, `Eq.mpr` and the other ways to decide or rewrite an abstract equation. A
`D` that uses anything else is refused scoring, with the names listed; the proof stays verified.

Why this is enough: the abstraction does the work (above); the allowlist makes sure the checker does not
reach the counting interpreter or a classical decision by name, which are the only ways around it.

## The two statements (`acceptcheck score`)

The service builds both statements itself and asks the kernel to accept the candidate's theorems at
exactly these types, as it does for the target:

    Challenge.sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
        CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task

    Challenge.instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (claimedCount, claimedBill)

The instance is always kernel-checked (`decide +kernel` in the candidate; the service never runs
candidate code). Proofs about `D` use `run_bind`, `run_pure`, the operations' specification lemmas
(`single_spec`, `interval_spec`) and `exec_of_billed`, which turns the instance into the hypothesis of
soundness, so the target follows inside the candidate.

## Why the reported cost is the cost

Proving that a checker's count is right says nothing about its bill, so the bill is never reported by the
candidate: the instance theorem `CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (n, L)` is
accepted by the kernel at a statement the service builds, so `L` is what the counting interpreter charges
on the protected weights, as the kernel computes it. What makes that charge the whole cost is the
interface: every number reaches `D` as an abstract `I.V`, every truth value is an abstract `I.B`, and
neither can decide what `D`'s own code does next or be turned into anything but counts, numbers and
truth values through charged operations. So no work on a value of the network can happen outside the
bill. The description-size budget bounds the free structure around it; it is a bound, not a proof. A receipt's `execution_assurance` is `kernel_checked_instance` for this reason: the count and the
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
- a description-size budget: the size of the checker's computational closure (the checker and the
  definitions it uses, transitively through definitions and never through theorems: what it computes is
  a function of these bodies and of the interpreter), every node of every body counted 1, a numeral 1 per
  bit, a string 8 per byte, measured as a tree (a repeated subterm counts each time), with no exemption by name, is at most `8192 + 4 E`. A
  reviewer showed that data can live in constructors (`[true, false, ...]`) and in the shape of
  applications alone (`fun c0 c1 z => c0 (c1 (c0 z))`), so the whole term is measured, and the rates make
  a number of `b` bits cost at least `b` however it is written (a numeral or a string `b`, constructors
  or applications at least `2 b`). An exported weight has 23 to 35 bits (its mantissa over the tensor's
  common exponent), so a copy of the weights costs at least about `24 E`, against `4 E` plus the base: on
  every size setting of the pipeline's zoo a copy is over the budget (max2 v64, E = 1,088: at least
  34,044 against 12,544; `scripts/test_accept.py` checks the arithmetic on the zoo and refuses an actual
  copy on max2 v64 under the default policy), while the pilot's column checker is under 8,000. This
  bounds description length; it does not show the absence of compressed information, and on the tiny
  test network (E = 80) the whole set of weights is smaller than any checker, so the budget separates
  nothing there (its tests use a smaller base through an environment hook, recorded in the policy
  digest);
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
