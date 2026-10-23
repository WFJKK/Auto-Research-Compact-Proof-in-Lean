import CompactCheck.General
import CompactCheck.Counted

/-!
# The single rule on general networks (attention), as a counted operation

`CostM.single` (CountedOps.lean) runs the linear checker; on a network with attention its cost function
has no price for the operations and the rule fails. This file gives the general checker of `General.lean`
(exact dyadic arithmetic, `generalSingle`) the same role: `CostM.gsingle g task x` runs the network on
one input and charges what cost-v3 charges a single leaf of a general network (`core/check/general.py`,
`GeneralProgram._eval` and `run_singles`, at batch size 1):

- a product with the one-hot input (a lookup): the output's size; any other matrix product: the output's
  size times the inner dimension;
- a sum, difference, product, addition or negation, and an `exp`: the output's size;
- a sum over a dimension: the output's size times (the summed length - 1);
- a softmax: 3 per entry;
- indexing, transposing, unsqueezing, expanding, concatenating, stacking, parameters: nothing;
- the final comparison of the label's logit with every other logit: (outputs - 1).

Only the operations that depend on the input are charged here; cost-v3 computes the others once per
proof and charges them to `extract`, which the acceptance service adds to its own `extract` (they are
none in the zoo's attention networks). The network is evaluated once per call: `gsingleRun` returns the
verdict and the charge together, and `gsingleRun_generalSingle` relates the verdict to `generalSingle`,
whose soundness theorem (`generalSingle_correct`) gives `CostM.gsingle_correct` in
`CountedGeneralSound.lean`.

This file uses only core Lean.
-/

namespace CompactCheck

/-- What cost-v3 charges for one operation of a general network on one input: `vals` holds the values of
    the operations before it, `out` its own value. -/
def gopCost (g : Graph) (vals : Array GVal) (out : DT) : Op → Nat
  | .matmul a _ =>
    if g.nodes[a]? == some .input then shapeSize out.shape
    else
      match vals[a]?.bind GVal.tensor with
      | some x => shapeSize out.shape * x.shape.getLast?.getD 1
      | none => shapeSize out.shape
  | .add _ _ => shapeSize out.shape
  | .binary _ _ _ => shapeSize out.shape
  | .neg _ => shapeSize out.shape
  | .sum a d =>
    match vals[a]?.bind GVal.tensor with
    | some x =>
      match normDim d x.shape.length with
      | some k => shapeSize out.shape * (x.shape.getD k 1 - 1)
      | none => 0
    | none => 0
  | .exp _ => shapeSize out.shape
  | .softmax _ _ => 3 * shapeSize out.shape
  | _ => 0

/-- Run the operations in order, as `gevalOps` does, and add up the charge of those that depend on the
    input (`deps`, indexed from `i`). -/
def gcostOps (g : Graph) (w : DWeights) (input : GVal) (deps : Array Bool) :
    List Op → Nat → Array GVal → Nat → Option (Array GVal × Nat)
  | [], _, vals, acc => some (vals, acc)
  | op :: ops, i, vals, acc =>
    match gevalOp g w input vals op with
    | some v =>
      let c := match v.tensor with
        | some t => if deps.getD i true then gopCost g vals t op else 0
        | none => 0
      gcostOps g w input deps ops (i + 1) (vals.push v) (acc + c)
    | none => none

theorem gcostOps_fst (g : Graph) (w : DWeights) (input : GVal) (deps : Array Bool) :
    ∀ (ops : List Op) (i : Nat) (vals : Array GVal) (acc : Nat),
      (gcostOps g w input deps ops i vals acc).map Prod.fst = gevalOps g w input ops vals
  | [], _, _, _ => rfl
  | op :: ops, i, vals, acc => by
    simp only [gcostOps, gevalOps]
    cases hv : gevalOp g w input vals op with
    | none => rfl
    | some v => exact gcostOps_fst g w input deps ops _ _ _

/-- The output's number of logits, for the final comparison. -/
def logitCount (out : DT) : Nat :=
  match out.shape with
  | [1, n] => n
  | _ => 0

/-- The single rule on a general network, with its cost-v3 charge: the verdict of `generalSingle` and the
    charge of the operations that depend on the input plus the final comparison, from one evaluation. -/
def gsingleRun (g : Graph) (w : DWeights) (task : Task) (x : Input) : Option (Bool × Nat) :=
  match oneHotDT g x with
  | none => none
  | some input =>
    match gcostOps g w input (dependsOnInput g) g.nodes 0 #[] 0 with
    | none => none
    | some (vals, cost) =>
      match vals[g.output]?.bind GVal.tensor with
      | none => none
      | some out =>
        match marginTest out (task.label x) with
        | none => none
        | some ok => some (ok, cost + (logitCount out - 1))

theorem gsingleRun_generalSingle {g : Graph} {w : DWeights} {task : Task} {x : Input} {b : Bool} {k : Nat}
    (h : gsingleRun g w task x = some (b, k)) : generalSingle g w task x = some b := by
  unfold gsingleRun at h
  unfold generalSingle gevalGraph
  cases hi : oneHotDT g x with
  | none => simp [hi] at h
  | some input =>
    simp only [hi] at h
    have hfst := gcostOps_fst g w input (dependsOnInput g) g.nodes 0 #[] 0
    cases hc : gcostOps g w input (dependsOnInput g) g.nodes 0 #[] 0 with
    | none => simp [hc] at h
    | some p =>
      obtain ⟨vals, cost⟩ := p
      simp only [hc] at h
      rw [hc] at hfst
      simp only [Option.map_some] at hfst
      simp only [Option.bind_eq_bind, Option.bind_some, ← hfst]
      cases ho : vals[g.output]?.bind GVal.tensor with
      | none => simp [ho] at h
      | some out =>
        simp only [ho] at h
        cases hm : marginTest out (task.label x) with
        | none => simp [hm] at h
        | some ok =>
          simp only [hm, Option.some.injEq, Prod.mk.injEq] at h
          simp only [ho, Option.bind_some, hm, h.1]

namespace CostM

/-- The single rule on a general network (attention): runs the network on one input exactly, with the
    general checker's dyadic arithmetic, and charges what cost-v3 charges a single leaf. `none` if the
    weights are not dyadic or the general checker cannot follow the network. -/
def gsingle (g : Graph) (task : Task) (x : Input) : CostM Bool := ⟨fun env c =>
  match dweights env.weights with
  | none => none
  | some dw =>
    match gsingleRun g dw task x with
    | some (b, k) => some (b, c.add "single" k)
    | none => none⟩

/-- How an instance proof splits: one fact per call, `gsingleRun` on the protected weights, each decided by
    the kernel on its own (a single `decide` over many forward passes runs out of memory), and this lemma
    to put each fact in place of the call. -/
theorem gsingle_run_of {g : Graph} {task : Task} {x : Input} {env : Env} {c : Cost} {b : Bool} {k : Nat}
    (h : ((dweights env.weights).bind fun dw => gsingleRun g dw task x) = some (b, k)) :
    (gsingle g task x).run env c = some (b, c.add "single" k) := by
  show (match dweights env.weights with
    | none => none
    | some dw =>
      match gsingleRun g dw task x with
      | some (b, k) => some (b, c.add "single" k)
      | none => none) = _
  cases hdw : dweights env.weights with
  | none => simp [hdw] at h
  | some dw =>
    simp only [hdw, Option.bind_some] at h
    simp only [h]

end CostM

/-- Adding to one category twice is adding the sum. -/
theorem Cost.add_add (c : Cost) (cat : String) (m n : Nat) : (c.add cat m).add cat n = c.add cat (m + n) := by
  induction c with
  | nil => simp [Cost.add]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : (k == cat) = true
    · simp [Cost.add, hk, Nat.add_assoc]
    · simp [Cost.add, hk, ih]

theorem Cost.total_add (c : Cost) (cat : String) (n : Nat) : (c.add cat n).total = c.total + n := by
  induction c with
  | nil => simp [Cost.add, Cost.total]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    by_cases hk : (k == cat) = true
    · simp [Cost.add, hk, Cost.total, List.sum_cons]; omega
    · have hk' : (k == cat) = false := by simpa using hk
      have e1 : Cost.add ((k, v) :: rest) cat n = (k, v) :: Cost.add rest cat n := by
        simp [Cost.add, hk']
      rw [e1]
      have e2 : Cost.total ((k, v) :: Cost.add rest cat n) = v + Cost.total (Cost.add rest cat n) := by
        simp [Cost.total]
      have e3 : Cost.total ((k, v) :: rest) = v + Cost.total rest := by
        simp [Cost.total]
      rw [e2, e3, ih]
      omega

end CompactCheck
