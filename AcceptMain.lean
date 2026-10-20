import Lean
import CompactCheck.Json
import CompactCheck.Spec
import CompactCheck.Counted

set_option linter.style.longLine false

/-!
# The `acceptcheck` program: the open lane's trusted check

The acceptance service (scripts/accept.py) compiles a candidate's modules with `lean` in a box, then runs
this program, which never elaborates candidate source. It trusts the toolchain, the `.olean` files of the
trusted modules (CompactCheck, its dependencies and the generated `Protected` module), and the kernel.

    acceptcheck check <target const> <candidate const> <trusted modules...> -- <candidate .olean files...>

Imports the trusted modules, replays every constant of the candidate's `.olean` files through the kernel
(`Lean.Kernel.Environment.replay`, as lean4checker does: every definition and theorem is type-checked again,
in a fresh environment, so nothing the candidate's compilation produced is trusted), then asks the kernel to
accept the theorem `Challenge.proof : <target const> := <candidate const>`. That succeeds exactly when the
candidate's constant has the target's type. The last line of output is a JSON object:

    {"status": "accepted" | "rejected", "reason": ..., "axioms": [...], "replayed": n}

`axioms` are the axioms the challenge depends on; the service allows only `propext`, `Classical.choice` and
`Quot.sound`. `sorryAx` and `Lean.ofReduceBool` (native_decide) are among what it rejects.

    acceptcheck score <protected module> <checker> <sound> <instance> <claimed count> <claimed bill>
                      <trusted modules...> -- <candidate .olean files...>

The scored path (docs/COUNTED.md): after the same replay, asks the kernel to accept two theorems whose
statements this program builds itself, `Challenge.sound` at the fixed soundness shape of the checker
`D = <checker>` (for all weights `w`, certificates `c`, counts `n` and bills `cost`: if `CostM.exec D ⟨w, c⟩ =
some (n, cost)` then `n ≤ numCorrect graph w task`), proved by `<sound>`, and `Challenge.instance`,
`CostM.billed D ⟨weights, cert⟩ = some (<claimed count>, <claimed bill>)`, proved by `<instance>`. The
general layer (the checker, its soundness proof and everything they depend on) may use the protected
module's `graph` and `task` but no other protected constant; it is replayed first and timed on its own,
and its literal weight is counted, for the service's budgets. The last line is
`{"status": "accepted" | "rejected", "reason": ..., "axioms": [...], "replayed": n,
  "general": {"constants": k, "literals": l, "kernel_ms": ms}, "rest": {...}, "challenge_ms": ms}`.

    acceptcheck closure <checker const> <allowlist file> <protected module> <trusted modules...> -- <candidate .olean files...>

Walks the constants the checker uses, transitively through the candidate's own definitions (not into
theorems, which compute nothing), and lists every other constant that is not on the allowlist; the
protected module's `graph` and `task` are allowed, its weights and certificate are not. The last line is
`{"status": "ok" | "refused", "offending": [...], "visited": n}`. This is the check that a scored checker
touches numbers only through the counted primitives (docs/COUNTED.md).

    acceptcheck protected <network.json> <protected module> <protected .olean>

Checks that the constants of a generated `Protected` module are the network of the file: the file is read
with the checker's own reader (parseNetwork in Json.lean) and compared with the module's `graph`, `weights`
and `task`. The last line is `{"status": "ok"}` or `{"status": "mismatch", "reason": ...}`.
-/

open Lean

namespace Accept

def standardAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms a constant depends on, found by walking the constants it uses. -/
partial def axiomsOf (env : Kernel.Environment) (root : Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut axioms : Array Name := #[]
  let mut stack : List Name := [root]
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if visited.contains n then continue
      visited := visited.insert n
      match env.find? n with
      | none => continue
      | some ci =>
        if ci matches .axiomInfo _ then axioms := axioms.push n
        for m in ci.getUsedConstantsAsSet.toList do
          if !visited.contains m then stack := m :: stack
  return axioms.qsort Name.lt

def jsonOut (fields : List (String × Json)) : IO Unit :=
  IO.println (Json.mkObj fields).compress

def rejected (reason : String) : IO UInt32 := do
  jsonOut [("status", "rejected"), ("reason", reason)]
  return 0

/-- The constants of an `.olean` file, by name. -/
def oleanConstants (path : System.FilePath) : IO (Array ConstantInfo) := do
  let (data, _region) ← readModuleData path
  return data.constants

def runCheck (target cand : Name) (trusted : List Name) (oleans : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let imports := trusted.toArray.map fun m => { module := m : Import }
  let env ← importModules imports {} (trustLevel := 0)
  let kenv := env.toKernelEnv
  if kenv.find? target |>.isNone then
    return ← rejected s!"the target {target} is not a constant of the trusted modules"
  -- the candidate's constants, replayed through the kernel
  let mut newConstants : Std.HashMap Name ConstantInfo := {}
  let mut count : Nat := 0
  for path in oleans do
    for ci in ← oleanConstants path do
      if (kenv.find? ci.name).isSome then
        return ← rejected s!"the candidate redeclares {ci.name}, a constant of the trusted modules"
      if ci.name.getRoot == `Challenge then
        return ← rejected s!"the candidate declares {ci.name}; the Challenge namespace is the service's"
      if newConstants.contains ci.name then
        return ← rejected s!"the candidate declares {ci.name} twice"
      newConstants := newConstants.insert ci.name ci
      count := count + 1
  let kenv ← try Kernel.Environment.replay newConstants kenv
    catch e => return ← rejected s!"the kernel rejects the candidate: {e}"
  if (kenv.find? cand).isNone then
    return ← rejected s!"the candidate has no constant {cand}"
  -- the challenge: the candidate's constant has the target's type
  let decl := Declaration.thmDecl {
    name := `Challenge.proof, levelParams := [], type := mkConst target, value := mkConst cand }
  match kenv.addDeclCore 0 0 decl (cancelTk? := none) with
  | .error e =>
    let msg ← (e.toMessageData {}).toString
    return ← rejected s!"the kernel rejects Challenge.proof : {target} := {cand}: {msg}"
  | .ok kenv' =>
    let axioms := axiomsOf kenv' `Challenge.proof
    jsonOut [("status", "accepted"), ("reason", Json.null),
      ("axioms", Json.arr (axioms.map fun a => Json.str a.toString)), ("replayed", Lean.toJson count)]
    return 0

/-! ## The scored path: the soundness shape, the instance, and the general-layer measures -/

def natT : Expr := mkConst ``Nat
def costT : Expr := mkConst ``CompactCheck.Cost
def certT : Expr := mkConst ``CompactCheck.Cert
def weightsT : Expr := mkApp (mkConst ``CompactCheck.Weights) (mkConst ``Rat)
def prodT (a b : Expr) : Expr := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b
def optionT (a : Expr) : Expr := mkApp (mkConst ``Option [Level.zero]) a
def someE (a v : Expr) : Expr := mkApp2 (mkConst ``Option.some [Level.zero]) a v
def pairE (a b x y : Expr) : Expr := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) a b x y
def eqE (ty a b : Expr) : Expr := mkApp3 (mkConst ``Eq [Level.one]) ty a b
def envE (w c : Expr) : Expr := mkApp2 (mkConst ``CompactCheck.Env.mk) w c

/-- The soundness shape of a checker `D`:
    `∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
      CostM.exec D ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task`. -/
def soundType (D graph task : Name) : Expr :=
  -- inside the hypothesis: w = bvar 3, c = bvar 2, n = bvar 1, cost = bvar 0
  let hyp := eqE (optionT (prodT natT costT))
    (mkApp3 (mkConst ``CompactCheck.CostM.exec) natT (mkConst D) (envE (mkBVar 3) (mkBVar 2)))
    (someE (prodT natT costT) (pairE natT costT (mkBVar 1) (mkBVar 0)))
  -- inside the conclusion: w = bvar 4, c = bvar 3, n = bvar 2, cost = bvar 1, h = bvar 0
  let concl := mkApp4 (mkConst ``LE.le [Level.zero]) natT (mkConst ``instLENat) (mkBVar 2)
    (mkApp3 (mkConst ``CompactCheck.numCorrect) (mkConst graph) (mkBVar 4) (mkConst task))
  mkForall `w .default weightsT (mkForall `c .default certT (mkForall `n .default natT
    (mkForall `cost .default costT (mkForall `h .default hyp concl))))

/-- The instance: `CostM.billed D ⟨weights, cert⟩ = some (n, bill)`. -/
def instanceType (D weights cert : Name) (n bill : Nat) : Expr :=
  eqE (optionT (prodT natT natT))
    (mkApp3 (mkConst ``CompactCheck.CostM.billed) natT (mkConst D) (envE (mkConst weights) (mkConst cert)))
    (someE (prodT natT natT) (pairE natT natT (mkNatLit n) (mkNatLit bill)))

/-- The candidate's constants, by name: `none` with a reason if one is a trusted constant's name, is in
    the `Challenge` namespace, or is declared twice. -/
def candidateConstants (kenv : Kernel.Environment) (oleans : List String) :
    IO (Except String (Std.HashMap Name ConstantInfo)) := do
  let mut cs : Std.HashMap Name ConstantInfo := {}
  for path in oleans do
    for ci in ← oleanConstants path do
      if (kenv.find? ci.name).isSome then
        return .error s!"the candidate redeclares {ci.name}, a constant of the trusted modules"
      if ci.name.getRoot == `Challenge then
        return .error s!"the candidate declares {ci.name}; the Challenge namespace is the service's"
      if cs.contains ci.name then
        return .error s!"the candidate declares {ci.name} twice"
      cs := cs.insert ci.name ci
  return .ok cs

/-- The constants of the candidate that `roots` use, transitively through the candidate's constants
    (theorems included: this is a dependency closure, not the computational one of `runClosure`),
    completed so that every inductive type comes with its whole mutual block, constructors and recursors,
    as `Kernel.Environment.replay` needs them together. -/
partial def dependencyClosure (cs : Std.HashMap Name ConstantInfo) (roots : List Name) : NameSet := Id.run do
  let mut visited : NameSet := {}
  let mut stack : List Name := roots
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if visited.contains n then continue
      let some ci := cs.get? n | continue
      visited := visited.insert n
      for m in ci.getUsedConstantsAsSet.toList do
        if !visited.contains m && cs.contains m then stack := m :: stack
      -- the inductive block
      let block : List Name := match ci with
        | .inductInfo info => info.all
        | .ctorInfo info => [info.induct]
        | .recInfo info => info.all
        | _ => []
      for i in block do
        if let some (.inductInfo info) := cs.get? i then
          for m in i :: info.ctors do
            if !visited.contains m then stack := m :: stack
          -- the recursors of the block are the candidate's recInfo constants pointing at it
          for (r, rci) in cs.toList do
            if let .recInfo rinfo := rci then
              if rinfo.all.contains i && !visited.contains r then stack := r :: stack
  return visited

/-- The literal weight of an expression: per natural number literal, 1 per 16 bits (so a weight's mantissa
    costs about 2 and a packed word costs more); per string literal, 1 per 2 bytes; a numeral
    `OfNat.ofNat _ n _` counted once. This is what the general layer's literal budget bounds: free data in
    the layer's statements and definitions, a copy of the weights above all. -/
partial def litWeight (e : Expr) : Nat :=
  go e |>.run' {}
where
  go (e : Expr) : StateM (Std.HashMap Expr Nat) Nat := do
    if let some n := (← get).get? e then return n
    let n ← match e with
      | .lit (.natVal n) => pure (max 1 ((Nat.log2 n + 1 + 15) / 16))
      | .lit (.strVal s) => pure (max 1 ((s.utf8ByteSize + 1) / 2))
      | .app .. =>
        let f := e.getAppFn
        let args := e.getAppArgs
        if f.isConstOf ``OfNat.ofNat && args.size == 3 then
          -- the type, the raw literal, the instance (which repeats the literal)
          pure ((← go args[0]!) + (← go args[1]!))
        else
          let mut s ← go f
          for a in args do s := s + (← go a)
          pure s
      | .lam _ ty b _ => pure ((← go ty) + (← go b))
      | .forallE _ ty b _ => pure ((← go ty) + (← go b))
      | .letE _ ty v b _ => pure ((← go ty) + (← go v) + (← go b))
      | .mdata _ b => go b
      | .proj _ _ b => go b
      | _ => pure 0
    modify (·.insert e n)
    return n

/-- Whether a constant of the environment is a proof: its type is a proposition, by the kernel's own
    type checker (a recursive theorem's auxiliary definitions are proofs too, though not `theorem`s). -/
def isProof (env : Environment) (ci : ConstantInfo) : Bool :=
  match Kernel.check env {} ci.type with
  | .ok sort => match Kernel.whnf env {} sort with
    | .ok (.sort u) => u.isZero
    | _ => false
  | .error _ => false

/-- The literal weight of a constant: its statement, and its body unless it is a proof (a proof term
    proves its statement and nothing else; what it computes is bounded by the kernel budget). -/
def constLitWeight (env : Environment) (ci : ConstantInfo) : Nat :=
  litWeight ci.type + (if isProof env ci then 0 else match ci.value? with | some v => litWeight v | none => 0)

/-- Replay a set of the candidate's constants into the kernel environment, timed. -/
def replayTimed (kenv : Kernel.Environment) (cs : Std.HashMap Name ConstantInfo) :
    IO (Except String (Kernel.Environment × Nat)) := do
  let t0 ← IO.monoMsNow
  try
    let kenv' ← Kernel.Environment.replay cs kenv
    return .ok (kenv', (← IO.monoMsNow) - t0)
  catch e => return .error s!"the kernel rejects the candidate: {e}"

/-- Ask the kernel to accept `name : type := value`. -/
def challenge (kenv : Kernel.Environment) (name : Name) (type : Expr) (value : Name) :
    IO (Except String Kernel.Environment) := do
  if (kenv.find? value).isNone then return .error s!"the candidate has no constant {value}"
  let decl := Declaration.thmDecl { name, levelParams := [], type, value := mkConst value }
  match kenv.addDeclCore 0 0 decl (cancelTk? := none) with
  | .error e => return .error s!"the kernel rejects {name} := {value}: {← (e.toMessageData {}).toString}"
  | .ok kenv' => return .ok kenv'

/-- The protected constants the general layer may use: the graph and the task (the statement of
    soundness mentions them); not the weights, the certificate, the claim or the target. -/
def generalMayUse (prot : Name) (n : Name) : Bool :=
  !(prot.isPrefixOf n) || n == prot ++ `graph || n == prot ++ `task

def runScore (prot D sound inst : Name) (n bill : Nat) (trusted : List Name) (oleans : List String) :
    IO UInt32 := do
  initSearchPath (← findSysroot)
  let env ← importModules (trusted.toArray.map fun m => { module := m : Import }) {} (trustLevel := 0)
  let kenv := env.toKernelEnv
  for c in [prot ++ `graph, prot ++ `weights, prot ++ `task, prot ++ `cert] do
    if (kenv.find? c).isNone then
      return ← rejected s!"the protected module has no constant {c}"
  let cs ← match ← candidateConstants kenv oleans with
    | .ok cs => pure cs
    | .error e => return ← rejected e
  for c in [D, sound, inst] do
    if !cs.contains c then return ← rejected s!"the candidate has no constant {c}"
  -- the general layer: the checker and its soundness proof, with everything they depend on
  let general := dependencyClosure cs [D, sound]
  for g in general do
    let some ci := cs.get? g | continue
    for m in ci.getUsedConstantsAsSet.toList do
      if !generalMayUse prot m then
        return ← rejected s!"the general layer ({g}) uses the protected constant {m}; only {prot}.graph and {prot}.task may appear outside the instance"
  let generalMap : Std.HashMap Name ConstantInfo := general.foldl (fun m g => match cs.get? g with
    | some ci => m.insert g ci | none => m) {}
  let restMap : Std.HashMap Name ConstantInfo := cs.fold (fun m k v => if general.contains k then m else m.insert k v) {}
  let (kenv, generalMs) ← match ← replayTimed kenv generalMap with
    | .ok r => pure r
    | .error e => return ← rejected e
  let genv := Environment.ofKernelEnv kenv
  let mut lits : Nat := 0
  let mut litsBy : Array (String × Json) := #[]
  for g in general do
    let some ci := cs.get? g | continue
    let w := constLitWeight genv ci
    lits := lits + w
    if w > 0 then litsBy := litsBy.push (g.toString, Lean.toJson w)
  let (kenv, restMs) ← match ← replayTimed kenv restMap with
    | .ok r => pure r
    | .error e => return ← rejected e
  let t0 ← IO.monoMsNow
  let kenv ← match ← challenge kenv `Challenge.sound (soundType D (prot ++ `graph) (prot ++ `task)) sound with
    | .ok k => pure k
    | .error e => return ← rejected e
  let kenv ← match ← challenge kenv `Challenge.instance (instanceType D (prot ++ `weights) (prot ++ `cert) n bill) inst with
    | .ok k => pure k
    | .error e => return ← rejected e
  let challengeMs := (← IO.monoMsNow) - t0
  let axioms := (axiomsOf kenv `Challenge.sound ++ axiomsOf kenv `Challenge.instance).toList.eraseDups.toArray.qsort Name.lt
  jsonOut [("status", "accepted"), ("reason", Json.null),
    ("axioms", Json.arr (axioms.map fun a => Json.str a.toString)), ("replayed", Lean.toJson cs.size),
    ("general", Json.mkObj [("constants", Lean.toJson general.size), ("literals", Lean.toJson lits),
      ("literals_by", Json.mkObj litsBy.toList), ("kernel_ms", Lean.toJson generalMs)]),
    ("rest", Json.mkObj [("constants", Lean.toJson restMap.size), ("kernel_ms", Lean.toJson restMs)]),
    ("challenge_ms", Lean.toJson challengeMs)]
  return 0

/-! ## The closure of a checker against the allowlist -/

def runClosure (root : Name) (allowPath : String) (prot : Name) (trusted : List Name) (oleans : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let imports := trusted.toArray.map fun m => { module := m : Import }
  let env ← importModules imports {} (trustLevel := 0)
  let kenv := env.toKernelEnv
  let allow : NameSet := (← IO.FS.lines allowPath).foldl (fun s (line : String) =>
    let l : String := line.toSlice.trimAscii.toString
    if l.isEmpty || l.startsWith "#" then s else s.insert l.toName) {}
  let mut cand : Std.HashMap Name ConstantInfo := {}
  for path in oleans do
    for ci in ← oleanConstants path do
      cand := cand.insert ci.name ci
  let mut visited : NameSet := {}
  let mut offending : Array Name := #[]
  let mut stack : List Name := [root]
  if !cand.contains root then
    jsonOut [("status", "refused"), ("offending", Json.arr #[Json.str root.toString]),
      ("reason", s!"{root} is not a constant of the candidate")]
    return 0
  while true do
    match stack with
    | [] => break
    | n :: rest =>
      stack := rest
      if visited.contains n then continue
      visited := visited.insert n
      match cand.get? n with
      | some ci =>
        -- the candidate's own constant: a proof computes nothing; a definition is followed
        if ci matches .thmInfo _ then continue
        for m in ci.getUsedConstantsAsSet.toList do
          if !visited.contains m then stack := m :: stack
      | none =>
        match kenv.find? n with
        | some (.thmInfo _) => continue
        | _ =>
          if !allow.contains n && n != prot ++ `graph && n != prot ++ `task then
            offending := offending.push n
  let sorted := offending.qsort Name.lt
  jsonOut [("status", if sorted.isEmpty then "ok" else "refused"),
    ("offending", Json.arr (sorted.map fun a => Json.str a.toString)), ("visited", Lean.toJson visited.size)]
  return 0

/-! ## The protected module against the network file -/

unsafe def evalProtected (mod : Name) :
    IO (Except String (CompactCheck.Graph × CompactCheck.Weights Rat × String × List Nat)) := do
  -- trusted modules only here (the generated module and what it imports), so their initializers may run
  enableInitializersExecution
  let env ← importModules #[{ module := mod }] {} (trustLevel := 0) (loadExts := true)
  return do
    let g ← env.evalConst CompactCheck.Graph {} (mod ++ `graph)
    let w ← env.evalConst (CompactCheck.Weights Rat) {} (mod ++ `weights)
    let t ← env.evalConst CompactCheck.Task {} (mod ++ `task)
    return (g, w, t.name, t.space)

@[implemented_by evalProtected]
opaque evalProtectedSafe (mod : Name) :
    IO (Except String (CompactCheck.Graph × CompactCheck.Weights Rat × String × List Nat))

/-- Two graphs are the same: the same sizes, operations and output. -/
def sameGraph (a b : CompactCheck.Graph) : Bool :=
  a.positions == b.positions && a.values == b.values && a.nodes == b.nodes && a.output == b.output

def runProtected (netPath : String) (mod : Name) (olean : String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  -- the module we evaluate must be the file the service compiled
  let (data, _) ← readModuleData olean
  unless data.constants.any (·.name == mod ++ `Target) do
    jsonOut [("status", "mismatch"), ("reason", s!"{olean} does not define {mod}.Target")]
    return 0
  let net ← match CompactCheck.parseNetwork (← CompactCheck.readJson netPath) with
    | .ok n => pure n
    | .error e => do
      jsonOut [("status", "mismatch"), ("reason", s!"cannot read {netPath}: {e}")]
      return 0
  match ← evalProtectedSafe mod with
  | .error e =>
    jsonOut [("status", "mismatch"), ("reason", s!"cannot evaluate the module's constants: {e}")]
  | .ok (g, w, tname, tspace) =>
    if !sameGraph g net.graph then
      jsonOut [("status", "mismatch"), ("reason", "the graph differs from the network file's")]
    else if !(w == net.weights) then
      jsonOut [("status", "mismatch"), ("reason", "the weights differ from the network file's")]
    else if tname != net.task.name || tspace != net.task.space then
      jsonOut [("status", "mismatch"), ("reason", "the task differs from the network file's")]
    else
      jsonOut [("status", "ok"), ("network", net.network),
        ("domain", Lean.toJson (CompactCheck.shapeSize net.task.space))]
  return 0

end Accept

def usage : String :=
  "usage: acceptcheck check <target> <candidate const> <trusted modules...> -- <candidate oleans...>\n" ++
  "       acceptcheck score <protected module> <checker> <sound> <instance> <count> <bill> <trusted modules...> -- <candidate oleans...>\n" ++
  "       acceptcheck closure <checker const> <allowlist> <protected module> <trusted modules...> -- <candidate oleans...>\n" ++
  "       acceptcheck protected <network.json> <protected module> <protected olean>"

def main (args : List String) : IO UInt32 := do
  match args with
  | "check" :: target :: cand :: rest =>
    let (trusted, oleans) := rest.span (· != "--")
    let oleans := oleans.drop 1
    if oleans.isEmpty then
      IO.eprintln usage
      return 2
    Accept.runCheck target.toName cand.toName (trusted.map String.toName) oleans
  | "score" :: prot :: D :: sound :: inst :: n :: bill :: rest =>
    let (trusted, oleans) := rest.span (· != "--")
    let oleans := oleans.drop 1
    match n.toNat?, bill.toNat? with
    | some n, some bill =>
      if oleans.isEmpty then
        IO.eprintln usage
        return 2
      Accept.runScore prot.toName D.toName sound.toName inst.toName n bill (trusted.map String.toName) oleans
    | _, _ =>
      IO.eprintln usage
      return 2
  | "closure" :: root :: allow :: prot :: rest =>
    let (trusted, oleans) := rest.span (· != "--")
    let oleans := oleans.drop 1
    if oleans.isEmpty then
      IO.eprintln usage
      return 2
    Accept.runClosure root.toName allow prot.toName (trusted.map String.toName) oleans
  | ["protected", net, mod, olean] => Accept.runProtected net mod.toName olean
  | _ =>
    IO.eprintln usage
    return 2
