import CompactCheck.Json
import CompactCheck.Semantics

/-!
# The `compactcheck` program

    compactcheck <network.json> <proof.json>
        Check a proof. The last line is {"certified": n}, as the pipeline's
        lean_check hook expects; a rejected proof gives n = 0 and a reason.

    compactcheck brute <network.json>
        Check every input on its own: the number the single-input test
        certifies, and a mask with one 0 or 1 per input, in the order of
        itertools.product over the input space. Exact for linear networks;
        for general networks with the bounds of `General.lean`.

    compactcheck logits <network.json> <inputs.json>
        The exact logits for each input in a JSON list of token lists, as
        fractions. For comparing with PyTorch and the Python checker. Linear
        networks only.

    compactcheck leaves <network.json> <proof.json>
        The outcome of every leaf of the proof's split tree, in the tree's
        order: its box, its rule, and whether it is certified. For comparing
        with the Python checker leaf by leaf.

    compactcheck floats <network.json> <inputs.json>
        The logits for each input computed in floats with the spec's
        definitions (`semGraph` in Semantics.lean), for any network. Each
        float is printed as its 64 bits, so Python reads it exactly. For
        comparing the network Lean reads with PyTorch's.
-/

open Lean (Json)
open CompactCheck

def loadNetwork (path : String) : IO NetworkFile := do
  match parseNetwork (← readJson path) with
  | .ok net => pure net
  | .error e => throw (IO.userError s!"{path}: {e}")

def runCheck (netPath proofPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let proofJson ← readJson proofPath
  match checkProofFile net proofJson with
  | .ok n => IO.println (Json.mkObj [("certified", Lean.toJson n)]).compress
  | .error e =>
    IO.println (Json.mkObj [("certified", Lean.toJson (0 : Nat)), ("status", Json.str "rejected"),
      ("reason", Json.str e)]).compress
  return 0

def runBrute (netPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let test ← if net.general then
      match dweights net.weights with
      | some dw => pure fun x => (generalSingle net.graph dw net.task x).getD false
      | none => throw (IO.userError "a weight is not a tensor of dyadic numbers")
    else pure fun x => singleOk net.graph net.weights net.task x
  let mask := (allInputs net.task.space).map fun x => if test x then '1' else '0'
  let n := mask.count '1'
  IO.println (Json.mkObj [("correct", Lean.toJson n), ("mask", Json.str (String.ofList mask))]).compress
  return 0

def readInputs (path : String) : IO (List Input) := do
  match (← readJson path).getArr? with
  | .ok a => a.toList.mapM fun j => match Lean.fromJson? (α := List Nat) j with
    | .ok x => pure x
    | .error e => throw (IO.userError e)
  | .error e => throw (IO.userError e)

def runLogits (netPath inputsPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let inputs ← readInputs inputsPath
  let rows := inputs.map fun x =>
    match evalGraph net.graph net.weights x with
    | some out => Json.arr (out.data.map fun q => Json.str (toString q))
    | none => Json.null
  IO.println (Json.arr rows.toArray).compress
  return 0

def ruleName : Rule → String
  | .single => "single"
  | .skip => "skip"
  | .interval _ => "interval"

def runLeaves (netPath proofPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let fail (e : String) : IO UInt32 := do
    IO.println (Json.mkObj [("status", Json.str "rejected"), ("reason", Json.str e)]).compress
    return 0
  match parseProof (← readJson proofPath) net.names with
  | .error e => fail e
  | .ok proof =>
    match walk proof.tree (rootBox net.task.space) with
    | .error e => fail e
    | .ok leaves =>
      let outcome? : Except String (Leaf → Except String Bool) :=
        if net.general then
          match dweights net.weights with
          | some dw => .ok (generalLeafOk net.graph dw net.task)
          | none => .error "a weight is not a tensor of dyadic numbers"
        else do
          let (g', w') ← contractAll net.graph net.weights proof.contractions
          let approxs ← buildApproxs g' w' proof.approximations
          pure (leafOk g' w' net.task approxs)
      match outcome? with
      | .error e => fail e
      | .ok outcome =>
        let rows := leaves.map fun l =>
          let res := match outcome l with
            | .ok b => Lean.toJson b
            | .error e => Json.str ("error: " ++ e)
          Json.mkObj [("ranges", Lean.toJson (l.box.map fun r => [r.lo, r.hi])),
            ("rule", Json.str (ruleName l.rule)), ("accepted", res)]
        IO.println (Json.arr rows.toArray).compress
        return 0

instance : Zero Float := ⟨0⟩
instance : One Float := ⟨1⟩
instance : ExpDiv Float := ⟨Float.exp, (· / ·)⟩

/-- A weight as a float (numerator and denominator rounded separately). -/
def ratToFloat (q : Rat) : Float := Float.ofInt q.num / Float.ofNat q.den

def runFloats (netPath inputsPath : String) : IO UInt32 := do
  let net ← loadNetwork netPath
  let inputs ← readInputs inputsPath
  let w : Weights Float := net.weights.map fun p => (p.1, p.2.map ratToFloat)
  let rows := inputs.map fun x =>
    match semGraph net.graph w x with
    | some out => Json.mkObj [("shape", Lean.toJson out.shape),
        ("bits", Json.arr (out.data.map fun f => Lean.toJson f.toBits.toNat))]
    | none => Json.null
  IO.println (Json.arr rows.toArray).compress
  return 0

def main (args : List String) : IO UInt32 := do
  match args with
  | ["brute", net] => runBrute net
  | ["logits", net, inputs] => runLogits net inputs
  | ["floats", net, inputs] => runFloats net inputs
  | ["leaves", net, proof] => runLeaves net proof
  | [net, proof] => runCheck net proof
  | _ =>
    IO.eprintln ("usage: compactcheck <network.json> <proof.json> | brute <network.json> | " ++
      "logits <network.json> <inputs.json> | leaves <network.json> <proof.json> | " ++
      "floats <network.json> <inputs.json>")
    return 2
