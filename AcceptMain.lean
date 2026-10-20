import Lean
import CompactCheck.Json
import CompactCheck.Spec

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

    acceptcheck closure <checker const> <allowlist file> <trusted modules...> -- <candidate .olean files...>

Walks the constants the checker uses, transitively through the candidate's own definitions (not into
theorems, which compute nothing), and lists every other constant that is not on the allowlist. The last
line is `{"status": "ok" | "refused", "offending": [...], "visited": n}`. This is the check that a scored
checker touches numbers only through the counted primitives (docs/COUNTED.md).

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

/-! ## The closure of a checker against the allowlist -/

def runClosure (root : Name) (allowPath : String) (trusted : List Name) (oleans : List String) : IO UInt32 := do
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
        | _ => if !allow.contains n then offending := offending.push n
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
  "       acceptcheck closure <checker const> <allowlist> <trusted modules...> -- <candidate oleans...>\n" ++
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
  | "closure" :: root :: allow :: rest =>
    let (trusted, oleans) := rest.span (· != "--")
    let oleans := oleans.drop 1
    if oleans.isEmpty then
      IO.eprintln usage
      return 2
    Accept.runClosure root.toName allow (trusted.map String.toName) oleans
  | ["protected", net, mod, olean] => Accept.runProtected net mod.toName olean
  | _ =>
    IO.eprintln usage
    return 2
