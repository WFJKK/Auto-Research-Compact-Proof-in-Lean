import Lean.Data.Json
import CompactCheck.Tokens

/-!
# Reading networks and proof files

Network files come from `scripts/export_network.py`; proof files are the
pipeline's `split-tree-v1` JSON. Reading is not part of any theorem: the
theorems are about the `Graph`, `Weights`, `Task` and `ProofFile` values
read here. A file that cannot be read is rejected, and so is everything the
Python checker rejects while reading (unknown keys, a `contract` that is not
a list, and so on), so that the two checkers agree on what they accept.

This file uses only core Lean.
-/

namespace CompactCheck

open Lean (Json)

/-- The format written by `scripts/export_network.py`. -/
def networkFormat : String := "compactcheck-network-v1"

/-- The rational `m * 2^e`. -/
def dyadic (m e : Int) : Rat :=
  if e ≥ 0 then ((m * 2 ^ e.toNat : Int) : Rat)
  else (m : Rat) / ((2 ^ (-e).toNat : Nat) : Rat)

/-- The keys of a JSON object. -/
def objKeys (j : Json) : Except String (List String) := do
  return (← j.getObj?).keys

/-- Every key of the object is one of `allowed`. -/
def onlyKeys (j : Json) (allowed : List String) : Except String Bool := do
  return (← objKeys j).all (allowed.contains ·)

/-- The object has exactly the keys `keys`. -/
def exactKeys (j : Json) (keys : List String) : Except String Bool := do
  let ks ← objKeys j
  return ks.length == keys.length && keys.all (ks.contains ·)

/-- One index item: `"all"`, `{"one": i}` or `{"range": [start, stop]}`. -/
def parseIndexItem (j : Json) : Except String IndexItem :=
  match j with
  | .str "all" => .ok .all
  | _ =>
    match j.getObjValAs? Nat "one", j.getObjValAs? (List Nat) "range" with
    | .ok i, _ => .ok (.one i)
    | _, .ok [a, b] => .ok (.range a b)
    | _, _ => .error "an index item is \"all\", {\"one\": i} or {\"range\": [start, stop]}"

/-- One operation of the graph, and its name in the Python checker's graph
    (empty if the file gives none). -/
def parseOp (j : Json) : Except String (Op × String) := do
  let name := (j.getObjValAs? String "name").toOption.getD ""
  let arg := j.getObjValAs? Nat "arg"
  let dim := j.getObjValAs? Int "dim"
  let op ← match ← j.getObjValAs? String "op" with
    | "input" => pure Op.input
    | "linear" =>
      let bias ← match j.getObjValD "bias" with
        | Json.null => pure none
        | b => some <$> b.getStr?
      pure (Op.linear (← arg) (← j.getObjValAs? String "weight") bias)
    | "sum" => pure (Op.sum (← arg) (← dim))
    | "add" => pure (Op.add (← j.getObjValAs? Nat "left") (← j.getObjValAs? Nat "right"))
    | "param" => pure (Op.param (← j.getObjValAs? String "weight"))
    | "binary" =>
      let f ← match ← j.getObjValAs? String "fn" with
        | "add" => pure BinOp.add
        | "sub" => pure BinOp.sub
        | "mul" => pure BinOp.mul
        | other => throw s!"unknown entrywise operation {other}"
      pure (Op.binary f (← j.getObjValAs? Nat "left") (← j.getObjValAs? Nat "right"))
    | "neg" => pure (Op.neg (← arg))
    | "matmul" => pure (Op.matmul (← j.getObjValAs? Nat "left") (← j.getObjValAs? Nat "right"))
    | "index" =>
      pure (Op.index (← arg) (← (← j.getObjValAs? (Array Json) "items").toList.mapM parseIndexItem))
    | "transpose" => pure (Op.transpose (← arg))
    | "unsqueeze" => pure (Op.unsqueeze (← arg) (← dim))
    | "expand" => pure (Op.expand (← arg) (← j.getObjValAs? (List Int) "shape"))
    | "cat" => pure (Op.cat (← j.getObjValAs? (List Nat) "args") (← dim))
    | "stack" => pure (Op.stack (← j.getObjValAs? (List Nat) "args") (← dim))
    | "exp" => pure (Op.exp (← arg))
    | "softmax" => pure (Op.softmax (← arg) (← dim))
    | "zeros_like" => pure (Op.zerosLike (← arg))
    | other => throw s!"operation {other} is not supported by the Lean checker yet"
  return (op, name)

/-- The graph, and the names of its operations. -/
def parseGraph (j : Json) : Except String (Graph × List String) := do
  let ops ← (← j.getObjValAs? (Array Json) "nodes").toList.mapM parseOp
  let g : Graph := {
    positions := ← j.getObjValAs? Nat "positions"
    values := ← j.getObjValAs? Nat "values"
    nodes := ops.map (·.1)
    output := ← j.getObjValAs? Nat "output" }
  return (g, ops.map (·.2))

/-- One weight tensor, `ints[i] * 2^exp` in row-major order. -/
def parseWeight (j : Json) : Except String (String × Tensor Rat) := do
  let name ← j.getObjValAs? String "name"
  let shape ← j.getObjValAs? (List Nat) "shape"
  let e ← j.getObjValAs? Int "exp"
  let ints ← j.getObjValAs? (Array Int) "ints"
  let t : Tensor Rat := ⟨shape, ints.map (dyadic · e)⟩
  unless t.wellFormed do throw s!"weight {name}: {ints.size} entries for shape {shape}"
  return (name, t)

/-- A network file: its id, graph, the names of its operations, weights and
    task, and whether the Python checker checks it as a general network
    (`core/check/general.py`) rather than as a linear one. -/
structure NetworkFile where
  network : String
  graph : Graph
  names : List String
  weights : Weights Rat
  task : Task
  general : Bool := false

def parseNetwork (j : Json) : Except String NetworkFile := do
  let fmt ← j.getObjValAs? String "format"
  unless fmt == networkFormat do throw s!"network file format {fmt}, expected {networkFormat}"
  let (graph, names) ← parseGraph (← j.getObjVal? "graph")
  let weights ← (← j.getObjValAs? (Array Json) "weights").toList.mapM parseWeight
  let taskName ← j.getObjValAs? String "task"
  let some task := taskByName taskName graph.positions graph.values
    | throw s!"unknown task {taskName}"
  let general ← match j.getObjValD "general" with
    | Json.null => pure false
    | b => b.getBool?
  return { network := ← j.getObjValAs? String "network", graph, names, weights, task, general }

/-- One node of a split tree. -/
partial def parseTree (j : Json) : Except String SplitTree := do
  match j.getObjVal? "leaf" with
  | .ok rule =>
    unless ← onlyKeys j ["leaf", "approx"] do throw "unknown leaf keys"
    let approx ← match j.getObjValD "approx" with
      | Json.null => pure none
      | a => some <$> a.getStr?
    match ← rule.getStr?, approx with
    | "single", none => pure (.leaf .single)
    | "skip", none => pure (.leaf .skip)
    | "interval", a => pure (.leaf (.interval a))
    | "token_interval", none => pure (.leaf .tokenInterval)
    | "single", some _ | "skip", some _ | "token_interval", some _ =>
      throw "only interval leaves take an approximation name"
    | other, _ => throw s!"leaf rule {other} is not allowed"
  | .error _ =>
    unless ← exactKeys j ["split", "children"] do throw "a node is a leaf or a split with children"
    let sp ← j.getObjVal? "split"
    unless ← exactKeys sp ["position", "cuts"] do throw "split needs exactly position and cuts"
    let children ← j.getObjValAs? (Array Json) "children"
    return .split (← sp.getObjValAs? Nat "position") (← sp.getObjValAs? (List Nat) "cuts")
      (← children.toList.mapM parseTree)

/-- The contract entries `{"name": N, "chain": [a, b, ...]}`, as names. -/
def parseContractions (c : Json) : Except String (List (String × List String)) := do
  (← c.getArr?).toList.mapM fun e => do
    unless ← exactKeys e ["name", "chain"] do
      throw "each contraction is {\"name\": ..., \"chain\": [...]}"
    return (← e.getObjValAs? String "name", ← e.getObjValAs? (List String) "chain")

/-- The chains as positions in the graph, and the names of the operations
    after the contractions. Names change as the contractions are applied, as
    in the Python checker: a contraction's last map takes the contraction's
    name, and its other maps disappear (`none`). -/
def resolveContractions (names : List String) (cs : List (String × List String)) :
    Except String (List (List Nat) × Array (Option String)) := do
  let mut cur : Array (Option String) := (names.map some).toArray
  let mut out : Array (List Nat) := #[]
  for (cname, chain) in cs do
    if cname.isEmpty || cur.contains (some cname) then
      throw s!"contraction name {cname} is empty or already used"
    let idx ← chain.mapM fun n =>
      match cur.findIdx? (· == some n) with
      | some i => pure i
      | none => throw s!"{n} is not a linear map of the network"
    if let some last := idx.getLast? then
      cur := (idx.dropLast.foldl (fun a i => a.set! i none) cur).set! last (some cname)
    out := out.push idx
  return (out.toList, cur)

/-! ## Numbers

As `parse_number` in `core/check/arith.py`: an integer, a string like
`"-3/4"` or `"1.25"`, or a finite float. The value must be dyadic,
`p / 2^k` with `|p| < 2^160` and `k ≤ 1100`, like the float weights.

Python reads a JSON number with a fraction part or an exponent as the
nearest binary64 float, and Lean's reader gives its exact decimal value
`m / 10^e`; `nearestFloat` rounds it the same way. A number with an exponent
and no fraction digits (`1e20`) is read as the integer it denotes, which is
also the float's value unless the integer needs more than 53 bits. -/

def maxNumberBits : Nat := 160
def maxDyadicExp : Nat := 1100
def maxNumberChars : Nat := 200

/-- The number of bits of `n` (`int.bit_length` in Python). -/
def bitLength (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1

/-- The value, if it is `p / 2^k` with `|p| < 2^160` and `k ≤ 1100`. -/
def checkDyadic (q : Rat) : Except String Rat :=
  let d := q.den
  if d &&& (d - 1) != 0 then
    .error "numbers must be dyadic (denominator a power of two), like the float weights"
  else if d.log2 > maxDyadicExp || bitLength q.num.natAbs > maxNumberBits then
    .error "number too large"
  else .ok q

/-- The binary64 float nearest to `n / d` (ties to even), or `none` if it
    is too large for a float. Requires `d > 0`. -/
def nearestFloat (n d : Nat) : Option Rat :=
  if n = 0 then some 0 else
  -- e0 = ⌊log2 (n / d)⌋
  let k : Int := (n.log2 : Int) - (d.log2 : Int)
  let atLeast : Bool := if k ≥ 0 then n ≥ d * 2 ^ k.toNat else n * 2 ^ (-k).toNat ≥ d
  let e0 := if atLeast then k else k - 1
  -- 53 significant bits; below 2^-1022 the floats are 2^-1074 apart
  let E := max (e0 - 52) (-1074)
  let num := if E ≥ 0 then n else n * 2 ^ (-E).toNat
  let den := if E ≥ 0 then d * 2 ^ E.toNat else d
  let m0 := num / den
  let r := num % den
  let m := if 2 * r > den then m0 + 1 else if 2 * r < den then m0 else m0 + m0 % 2
  if E ≥ 0 then
    if m * 2 ^ E.toNat ≥ 2 ^ 1024 then none else some ((m * 2 ^ E.toNat : Nat) : Rat)
  else some ((m : Rat) / ((2 ^ (-E).toNat : Nat) : Rat))

/-- Python's whitespace (`str.isspace`). -/
def isPySpace (c : Char) : Bool :=
  c == ' ' || ('\t' ≤ c && c ≤ '\r') || ('\x1c' ≤ c && c ≤ '\x1f') || c == '\x85' ||
    c == '\xa0' || c == '\u1680' || ('\u2000' ≤ c && c ≤ '\u200a') || c == '\u2028' ||
    c == '\u2029' || c == '\u202f' || c == '\u205f' || c == '\u3000'

/-- The digits at the start of `cs`: their value, how many there are, and
    what follows them. -/
def spanDigits : List Char → Nat → Nat → Nat × Nat × List Char
  | c :: rest, v, n =>
    if c.isDigit then spanDigits rest (10 * v + (c.toNat - '0'.toNat)) (n + 1)
    else (v, n, c :: rest)
  | [], v, n => (v, n, [])

/-- An unsigned number string: digits, digits `/` digits, or a decimal with
    at least one digit (the regular expression of `parse_number`). -/
def parseUnsigned (body : List Char) : Option Rat :=
  let (a, na, rest) := spanDigits body 0 0
  match rest with
  | [] => if na > 0 then some (a : Rat) else none
  | '/' :: rest' =>
    let (b, nb, rest'') := spanDigits rest' 0 0
    if na > 0 && nb > 0 && rest''.isEmpty && b != 0 then some ((a : Rat) / (b : Rat)) else none
  | '.' :: rest' =>
    let (f, nf, rest'') := spanDigits rest' 0 0
    if na + nf > 0 && rest''.isEmpty then some ((a : Rat) + (f : Rat) / ((10 ^ nf : Nat) : Rat))
    else none
  | _ => none

/-- A number written as a string. -/
def parseNumberString (v : String) : Except String Rat := do
  let cs := ((v.toList.dropWhile isPySpace).reverse.dropWhile isPySpace).reverse
  if cs.length > maxNumberChars then throw "number string too long"
  let (neg, body) := match cs with
    | '+' :: rest => (false, rest)
    | '-' :: rest => (true, rest)
    | _ => (false, cs)
  match parseUnsigned body with
  | some q => checkDyadic (if neg then -q else q)
  | none => throw s!"not a number (integers, p/q or decimals only, no exponents): {v}"

/-- A number of a proof file. -/
def parseNumber : Json → Except String Rat
  | .num ⟨m, 0⟩ =>
    if bitLength m.natAbs > maxNumberBits then .error "number too large" else .ok (m : Rat)
  | .num ⟨m, e⟩ =>
    match nearestFloat m.natAbs (10 ^ e) with
    | some v => checkDyadic (if m < 0 then -v else v)
    | none => .error "numbers must be finite"
  | .str s => parseNumberString s
  | .bool _ => .error "booleans are not numbers"
  | _ => .error "not a number"

/-! ## Approximations -/

/-- A JSON integer, without a fraction part (`isinstance(v, int)`). -/
def jsonInt? : Json → Option Int
  | .num ⟨m, 0⟩ => some m
  | _ => none

/-- A matrix as a list of rows of numbers. -/
def parseRows (what : String) (j : Json) : Except String (List (List Rat)) := do
  let .arr rows := j | throw s!"{what} must be a list of rows"
  rows.toList.mapM fun r => do
    let .arr r := r | throw s!"{what} must be a list of rows"
    r.toList.mapM parseNumber

/-- The rows of a `row_segments` approximation: `[start, end, value]`
    triples. -/
def parseSegments (j : Json) : Except String (List (List (Int × Int × Rat))) := do
  let .arr rows := j | throw "rows needs one list of segments per output"
  rows.toList.mapM fun r => do
    let .arr segs := r | throw "each row is a list of segments"
    segs.toList.mapM fun s => do
      let .arr parts := s | throw "segments are [start, end, value]"
      match parts.toList with
      | [a, b, v] =>
        match jsonInt? a, jsonInt? b with
        | some a, some b => return (a, b, ← parseNumber v)
        | _, _ => throw "segments are [start, end, value]"
      | _ => throw "segments are [start, end, value]"

/-- One entry of `approximate`, for a graph whose operations now have these
    names. Keys other than those of its form are ignored, as in Python. -/
def parseApprox (names : Array (Option String)) (j : Json) : Except String ApproxSpec := do
  let (name, of) ← match j.getObjVal? "name", j.getObjVal? "of" with
    | .ok (.str n), .ok (.str o) => pure (n, o)
    | _, _ => throw "each approximation has a \"name\" and an \"of\""
  let some idx := names.findIdx? (· == some of)
    | throw s!"approximation of unknown linear map {of}"
  let form ← match j.getObjVal? "form" with
    | .ok (.str "dense") => RawForm.dense <$> parseRows "values" (j.getObjValD "values")
    | .ok (.str "low_rank") =>
      pure (RawForm.lowRank (← parseRows "left" (j.getObjValD "left"))
        (← parseRows "right" (j.getObjValD "right")))
    | .ok (.str "row_segments") => RawForm.rowSegments <$> parseSegments (j.getObjValD "rows")
    | _ => throw "unknown form; use dense, low_rank or row_segments"
  return { name, of := idx, form }

/-- The value of an optional key: `none` if it is absent. -/
def optVal (j : Json) (key : String) : Option Json :=
  (j.getObjVal? key).toOption

/-- The top-level keys a proof file may have. -/
def proofKeys : List String :=
  ["schema", "network", "symmetry", "contract", "approximate", "tree", "notes"]

/-- A proof file, for a network whose operations have these names. -/
def parseProof (j : Json) (names : List String) : Except String ProofFile := do
  unless ← onlyKeys j proofKeys do throw "unknown top-level keys"
  let schema ← j.getObjValAs? String "schema"
  unless schema == "split-tree-v1" do throw s!"schema must be split-tree-v1, not {schema}"
  let symmetry ← match optVal j "symmetry" with
    | none => pure false
    | some s => match s.getBool? with
      | .ok b => pure b
      | .error _ => throw "symmetry must be true or false"
  let (contractions, cur) ← match optVal j "contract" with
    | none => pure ([], (names.map some).toArray)
    | some c => match c.getArr? with
      | .ok _ => resolveContractions names (← parseContractions c)
      | .error _ => throw "contract must be a list"
  let approximations ← match optVal j "approximate" with
    | none => pure []
    | some a => match a.getArr? with
      | .ok arr => arr.toList.mapM (parseApprox cur)
      | .error _ => throw "approximate must be a list"
  return {
    network := ← j.getObjValAs? String "network"
    symmetry
    contractions
    approximations
    tree := ← parseTree (← j.getObjVal? "tree") }

/-! ## Checking a proof file -/

/-- The numbers, strings and booleans in a JSON value (`count_scalars` in
    `core/check/cost.py`). -/
partial def countScalars : Json → Nat
  | .null => 0
  | .arr a => a.foldl (fun n v => n + countScalars v) 0
  | .obj kvs => kvs.foldl (fun n _ v => n + countScalars v) 0
  | _ => 1

/-- The Python checker rejects a proof file with more numbers, strings and
    booleans than this, for `n` inputs, so that a file cannot make it slow
    (`limits` in `core/check/checker.py`). Its limit on the number of tree
    nodes is never reached by a valid tree, which has fewer than `2 n`. -/
def maxScalars (n : Nat) : Nat := 50 * n + 10 ^ 6

/-- Check a proof file for a network: the number of inputs it certifies, or
    why it is rejected. -/
def checkProofFile (net : NetworkFile) (j : Json) : Except String Nat := do
  let limit := maxScalars (shapeSize net.task.space)
  if countScalars j > limit then throw s!"the proof file has more than {limit} numbers and strings"
  let proof ← parseProof j net.names
  unless proof.network == net.network do
    throw s!"the proof names network {proof.network}, not {net.network}"
  if net.general then checkProofGeneral net.graph net.weights net.task proof
  else checkProof net.graph net.weights net.task proof

/-- Read and parse a JSON file. -/
def readJson (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{path}: {e}")

end CompactCheck
