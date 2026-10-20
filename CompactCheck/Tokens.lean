import CompactCheck.General

/-!
# token_interval leaves

A `token_interval` leaf is checked as `core/check/tokens.py` checks it. An
interval leaf turns each position's tokens into a box at the first lookup;
a token_interval leaf keeps the tokens apart for as long as the graph
allows. Next to interval tensors it uses these values:

* `Sep`: a value of shape `[1, positions, ...]` whose row `p` depends only
  on the token at position `p`, kept exactly for every token the leaf
  allows there. The lookup `x @ W` makes one; adding a constant, a product
  with a constant (entrywise or as a matrix) and a sum over a non-position
  dimension keep it one.
* `Mix`: a constant plus a sum of terms, each a weight times an exact row
  of one position's tokens. Selecting one position of a `Sep`, or summing a
  weighted `Sep` over the positions, makes one; products with a constant
  matrix act on each term's rows exactly.
* `WSep`: a `Sep` times one weight per position (an attention weight),
  waiting for its sum over the positions.
* `Var`, only in leaves where at most one position holds more than one
  token: one value per input of the leaf. Python keeps them as one tensor
  with an extra first axis; here they are a list, one per input, which has
  the same values (Python's operations act on each input's slice alike).

An operation the rules do not cover sees its arguments leave the domain:
as `Var` values if at most one position varies, as interval tensors
otherwise. Python returns `None` from a rule that does not apply (`decline`
here) and raises where the proof is rejected (`fail`).

Python keeps the rows that depend on their token alone for the whole proof;
that only saves work and does not change a value, so this file recomputes
them in each leaf.

This file uses only core Lean.
-/

namespace CompactCheck

/-! ## Outcomes -/

/-- A rule's outcome: a value; `decline`, where Python's rule returns
    `None`; `fail`, where Python raises and rejects the proof. -/
inductive Step (α : Type) where
  | val (a : α)
  | decline
  | fail

namespace Step

def bind {α β : Type} : Step α → (α → Step β) → Step β
  | .val a, f => f a
  | .decline, _ => .decline
  | .fail, _ => .fail

instance : Monad Step where
  pure := .val
  bind := bind

/-- An operation that can only fail (Python raises). -/
def ofOption {α : Type} : Option α → Step α
  | some a => .val a
  | none => .fail

end Step

/-! ## Values -/

/-- Rows that depend on one position's token: per position, an exact
    interval tensor whose first axis runs over the allowed tokens. The
    value has shape `[1, positions] ++ rest`. -/
structure Sep where
  rows : List DT
  rest : List Nat

/-- `w * rows[t]` for the token `t` at position `pos`; `w` has shape `[]`,
    or `[k]` for one weight per input of the leaf. -/
structure Term where
  w : DT
  pos : Nat
  rows : DT

/-- `const` plus the sum of the terms; shape `const.shape`. -/
structure Mix where
  const : DT
  terms : List Term

/-- A value of a token_interval leaf. -/
inductive TV where
  /-- The input of the leaf. -/
  | box
  | sep (s : Sep)
  | mix (m : Mix)
  /-- A `Sep` times one weight per position, an interval tensor of shape
      `[1, positions, 1, ..., 1]`. -/
  | wsep (w : DT) (s : Sep)
  /-- The same with one weight tensor per input of the leaf. -/
  | wsepv (w : Array DT) (s : Sep)
  /-- One value per input of the leaf. -/
  | var (vs : Array DT)
  | dt (v : DT)

def TV.isDomain : TV → Bool
  | .dt _ => false
  | _ => true

def TV.isVar : TV → Bool
  | .var _ => true
  | _ => false

def Sep.shape (s : Sep) : List Nat := 1 :: s.rows.length :: s.rest

/-- The leaf: its box, the number of values per position, the varying
    position if exactly one varies, and the number of inputs per value. -/
structure TCtx where
  box : Box
  values : Nat
  pstar : Option Nat
  aligned : Bool
  k : Nat

def TCtx.ofBox (box : Box) (values : Nat) : TCtx :=
  let varying := (List.range box.length).filter fun p =>
    (box.getD p ⟨0, 0⟩).lo < (box.getD p ⟨0, 0⟩).hi
  let pstar := if varying.length == 1 then varying.head? else none
  { box, values, pstar, aligned := varying.length ≤ 1,
    k := match pstar with
      | some p => (box.getD p ⟨0, 0⟩).hi + 1 - (box.getD p ⟨0, 0⟩).lo
      | none => 1 }

def emptyDT : DT := ⟨[], #[], #[], 0, true⟩

def TV.shape (ctx : TCtx) : TV → List Nat
  | .box => [1, ctx.box.length, ctx.values]
  | .sep s => s.shape
  | .mix m => m.const.shape
  | .wsep _ s => s.shape
  | .wsepv _ s => s.shape
  | .var vs => (vs.getD 0 emptyDT).shape
  | .dt v => v.shape

/-! ## Interval tensors: helpers -/

/-- An exact number. -/
def dtScalar (m : Int) : DT := ⟨[], #[m], #[m], 0, true⟩

/-- Exact zeros. -/
def dtZeros (shape : List Nat) : DT := DT.ofInts shape (Array.replicate (shapeSize shape) 0) 0

/-- The same values at the smaller exponent `e`. -/
def DT.at (v : DT) (e : Int) : DT := v.shift (v.e - e).toNat

def dtIndex (items : List IndexItem) (v : DT) : Option DT := dmove (indexOp · items) v

def dtBroadcastTo (v : DT) (s : List Nat) : Option DT := dmove (expandOp · (s.map Int.ofNat)) v

def dtUnsqueeze (d : Int) (v : DT) : Option DT := dmove (unsqueezeOp · d) v

/-- Python's `_min_max`: the box of the entries over the first axis, which
    keeps length 1; the tensor itself if that axis has length 1. -/
def dtMinMax (r : DT) : Option DT :=
  if !r.ok then none else
  match r.shape with
  | 1 :: _ => some r
  | (n + 1) :: tail =>
    let inner := shapeSize tail
    let lo := (Array.range inner).map fun j =>
      (List.range n).foldl (fun m i => min m (mget r.lo ((i + 1) * inner + j))) (mget r.lo j)
    let hi := (Array.range inner).map fun j =>
      (List.range n).foldl (fun m i => max m (mget r.hi ((i + 1) * inner + j))) (mget r.hi j)
    some ⟨1 :: tail, lo, hi, r.e, false⟩
  | _ => none

/-- The rows of a `Sep` at its smallest exponent. -/
def Sep.minExp (s : Sep) : Int := (s.rows.map (·.e)).foldl min ((s.rows.headD emptyDT).e)

/-- Index items selecting `[:, :, 0:1, ..., 0:1]` of a value of shape
    `[1, positions] ++ rest`. -/
def firstItems (rest : List Nat) : List IndexItem := [.all, .all] ++ rest.map fun _ => .range 0 1

/-! ## Rules that keep the tokens apart -/

/-- The lookup `x @ W` on the leaf's tokens: row `t` of `W` for each
    allowed token `t` of each position. -/
def tLookup (ctx : TCtx) (w : DT) : Option Sep :=
  match w.shape with
  | [v, d] =>
    if w.exact && w.ok && v == ctx.values && boxFits ctx.values ctx.box && 0 < ctx.box.length then
      some ⟨ctx.box.map fun r =>
        let n := r.hi + 1 - r.lo
        let lo := (Array.range (n * d)).map fun j => mget w.lo ((r.lo + j / d) * d + j % d)
        ⟨[n, d], lo, lo, w.e, true⟩, [d]⟩
    else none
  | _ => none

/-- A `Sep` plus a constant: exact constants only. -/
def addConst (s : Sep) (c : DT) : Step Sep :=
  if !c.exact then .decline else
  match dtBroadcastTo c s.shape with
  | none => .decline
  | some b => do
    let rows ← Step.ofOption ((List.range s.rows.length).zip s.rows |>.mapM fun (p, r) => do
      let cp ← dtIndex [.one 0, .one p] b
      dbinary .add r cp)
    pure ⟨rows, s.rest⟩

/-- Whether `v` (of shape `s`) equals its first entries along `rest`,
    repeated: one value per position. -/
def onePerPosition (v : DT) (rest : List Nat) (s : List Nat) : Option (Option DT) := do
  let w ← dtIndex (firstItems rest) v
  let back ← dtBroadcastTo w s
  pure (if back.lo == v.lo && back.hi == v.hi then some w else none)

/-- The shape of one weight per position of a value of shape
    `[1, P] ++ rest`: `[1, P, 1, ..., 1]`. -/
def weightShape (P : Nat) (rest : List Nat) : List Nat := 1 :: P :: List.replicate rest.length 1

/-- A `Sep` times a constant: one weight per position gives a `WSep`;
    otherwise an exact constant multiplies each row.

    One weight per position needs the same real number along `rest`, not
    only the same interval: an exact constant, or one of the shape
    `[1, positions, 1, ..., 1]` (an attention weight). Python checks only
    the intervals; an inexact constant whose intervals agree but whose real
    values differ along `rest` makes a `WSep` there, which is not sound.
    Here every other inexact constant declines, as Python declines an
    inexact constant that is not one weight per position. -/
def mulSep (s : Sep) (c : DT) : Step TV :=
  match dtBroadcastTo c s.shape with
  | none => .decline
  | some b =>
    match onePerPosition b s.rest s.shape with
    | none => .fail
    | some (some w) =>
      if c.exact || c.shape == weightShape s.rows.length s.rest then .val (.wsep w s)
      else .decline
    | some none =>
      if !c.exact then .decline else do
      let rows ← Step.ofOption ((List.range s.rows.length).zip s.rows |>.mapM fun (p, r) => do
        let cp ← dtIndex [.one 0, .one p] b
        dbinary .mul r cp)
      pure (.sep ⟨rows, s.rest⟩)

/-- Per-input weights times a `Sep`: kept apart if they are one weight per
    position (in the same sense as `mulSep`). -/
def mulVarSep (ws : Array DT) (s : Sep) : Step TV :=
  match ws.toList.mapM (dtBroadcastTo · s.shape) with
  | none => .decline
  | some bs =>
    match bs.mapM (onePerPosition · s.rest s.shape) with
    | none => .fail
    | some ws' =>
      match ws'.mapM id with
      | some ws'' =>
        if ws.all fun w => w.exact || w.shape == weightShape s.rows.length s.rest then
          .val (.wsepv ws''.toArray s)
        else .decline
      | none => .decline

/-- A sum over a dimension of the rows (`dim ≥ 2` of the value). -/
def sumRows (s : Sep) (dim : Nat) : Step Sep := do
  let rows ← Step.ofOption (s.rows.mapM (dsum (dim - 1 : Nat)))
  pure ⟨rows, (rows.headD emptyDT).shape.drop 1⟩

/-- The scalar weight of position `p` in a weight tensor of shape
    `[1, positions, 1, ..., 1]`. -/
def weightAt (w : DT) (p : Nat) (rest : List Nat) : Option DT :=
  dtIndex ([.one 0, .one p] ++ rest.map fun _ => .one 0) w

/-- One weight per input, from per-input weight tensors: shape `[k]`. -/
def weightsAt (ws : Array DT) (p : Nat) (rest : List Nat) : Option DT := do
  let xs ← ws.toList.mapM (weightAt · p rest)
  djoin (stackOp · 0) xs

/-- The sum over the positions: one term per position. -/
def sumPositions (s : Sep) (w : Option (Sum DT (Array DT))) : Step Mix := do
  let terms ← Step.ofOption ((List.range s.rows.length).zip s.rows |>.mapM fun (p, r) => do
    let wp ← match w with
      | none => some (dtScalar 1)
      | some (.inl w) => weightAt w p s.rest
      | some (.inr ws) => weightsAt ws p s.rest
    pure ⟨wp, p, r⟩)
  pure ⟨dtZeros (1 :: s.rest), terms⟩

/-- A matrix product with an exact matrix on the right. -/
def matmulSep (s : Sep) (b : DT) : Step Sep := do
  let rows ← Step.ofOption (s.rows.mapM (dmatmul · b))
  pure ⟨rows, (rows.headD emptyDT).shape.drop 1⟩

def matmulMix (m : Mix) (b : DT) : Step Mix := do
  let terms ← Step.ofOption (m.terms.mapM fun t => do
    let rows ← dmatmul t.rows b
    pure ⟨t.w, t.pos, rows⟩)
  let const ← if m.const.exact && m.const.lo.all (· == 0) then
      pure (dtZeros (m.const.shape.dropLast ++ [b.shape.getD 1 0]))
    else Step.ofOption (dmatmul m.const b)
  pure ⟨const, terms⟩

/-- A `Mix` plus a constant of a shape that keeps the `Mix`'s shape (the
    rows of its terms have that shape). -/
def addMix (m : Mix) (c : DT) : Step Mix :=
  match dbinary .add m.const c with
  | none => .fail
  | some const => if const.shape == m.const.shape then .val ⟨const, m.terms⟩ else .decline

/-- Two `Mix`es of the same shape. -/
def addMixes (x y : Mix) : Step Mix :=
  if x.const.shape != y.const.shape then .decline else
  match dbinary .add x.const y.const with
  | none => .fail
  | some const => .val ⟨const, x.terms ++ y.terms⟩

def scaleMix (m : Mix) (s : DT) : Step Mix := do
  let terms ← Step.ofOption (m.terms.mapM fun t => do
    let w ← dbinary .mul t.w s
    pure ⟨w, t.pos, t.rows⟩)
  let const ← Step.ofOption (dbinary .mul m.const s)
  pure ⟨const, terms⟩

/-! ## Leaving the token domain -/

/-- The value per input of a `Sep`, in a leaf where at most one position
    varies. -/
def toVarSep (ctx : TCtx) (s : Sep) : Option (Array DT) := do
  if s.rows.isEmpty then none
  let e := s.minExp
  let rows := s.rows.map (·.at e)
  (Array.range ctx.k).mapM fun i => do
    let parts ← rows.mapM fun r =>
      let n := r.shape.headD 0
      if n == 1 then dtIndex [.one 0] r else if n == ctx.k then dtIndex [.one i] r else none
    let st ← djoin (stackOp · 0) parts
    dtUnsqueeze 0 st

/-- Entry `i` (or the only one) of a list of `k` values. -/
def pick (n i : Nat) (k : Nat) : Option Nat :=
  if n == 1 then some 0 else if n == k then some i else none

/-- A term's weight for input `i`: its only entry, or entry `i`. -/
def varWeight (ctx : TCtx) (i : Nat) (w : DT) : Option DT :=
  match w.shape with
  | [] => some w
  | [n] => do
    let j ← pick n i ctx.k
    dtIndex [.one j] w
  | _ => none

/-- Input `i`'s value so far plus one term. -/
def varMixStep (ctx : TCtx) (i : Nat) (out : DT) (t : Term) : Option DT := do
  let r ← pick (t.rows.shape.headD 0) i ctx.k
  let row ← dtIndex [.range r (r + 1)] t.rows
  let w ← varWeight ctx i t.w
  let prod ← dbinary .mul w row
  dbinary .add out prod

def toVarMix (ctx : TCtx) (m : Mix) : Option (Array DT) :=
  (Array.range ctx.k).mapM fun i => m.terms.foldlM (varMixStep ctx i) m.const

def toVarWSep (ctx : TCtx) (w : Sum DT (Array DT)) (s : Sep) : Option (Array DT) := do
  let xs ← toVarSep ctx s
  (Array.range xs.size).mapM fun i => do
    let wi ← match w with
      | .inl w => some w
      | .inr ws => ws[i]?
    dbinary .mul wi (xs.getD i emptyDT)

/-- The box over the inputs of per-input values (their slices' entrywise
    minimum and maximum); the value itself for one input. -/
def collapseVar (vs : Array DT) : Option DT :=
  if vs.size == 1 then vs[0]? else
  if vs.size == 0 then none else
  let e := (vs.toList.map (·.e)).foldl min (vs.getD 0 emptyDT).e
  let vs := vs.map (·.at e)
  let v0 := vs.getD 0 emptyDT
  if !(vs.all fun v => v.ok && v.shape == v0.shape) then none else
  let size := shapeSize v0.shape
  some ⟨v0.shape,
    (Array.range size).map fun j => vs.foldl (fun m v => min m (mget v.lo j)) (mget v0.lo j),
    (Array.range size).map fun j => vs.foldl (fun m v => max m (mget v.hi j)) (mget v0.hi j),
    e, false⟩

def collapseSep (s : Sep) : Option DT := do
  if s.rows.isEmpty then none
  let e := s.minExp
  let boxes ← s.rows.mapM fun r => dtMinMax (r.at e)
  let c ← djoin (catOp · 0) boxes
  dtUnsqueeze 0 c

/-- The value so far plus a term of one row and an exact scalar weight. -/
def concreteStep (out : DT) (t : Term) : Option DT := do
  let row ← dtIndex [.range 0 1] t.rows
  let prod ← dbinary .mul t.w row
  dbinary .add out prod

/-- A `Mix` whose terms each hold one row with an exact scalar weight is one
    exact value (`some none` if not; `none` if Python raises). -/
def concretize (m : Mix) : Option (Option DT) :=
  if !(m.const.exact && m.terms.all fun t =>
      t.rows.shape.headD 0 == 1 && t.w.exact && t.w.shape == []) then some none else
  (m.terms.foldlM concreteStep m.const).map some

/-- A term's weight as one interval: the weight, or the box of its entries. -/
def boxWeight (w : DT) : Option DT :=
  if w.shape == [] then some w else
  if !w.ok || w.lo.isEmpty then none else
  some ⟨[], #[w.lo.foldl min (w.lo.getD 0 0)], #[w.hi.foldl max (w.hi.getD 0 0)], w.e, false⟩

/-- The box so far plus the box of a term. -/
def boxMixStep (out : DT) (t : Term) : Option DT := do
  let box ← dtMinMax t.rows
  let w ← boxWeight t.w
  let prod ← dbinary .mul w box
  dbinary .add out prod

def collapseMix (m : Mix) : Option DT := do
  match concretize m with
  | none => none
  | some (some d) => some d
  | some none => m.terms.foldlM boxMixStep m.const

def collapseWSep (w : Sum DT (Array DT)) (s : Sep) : Option DT := do
  let w ← match w with
    | .inl w => some w
    | .inr ws => collapseVar ws
  let box ← collapseSep s
  dbinary .mul w box

/-- What a value becomes for an operation the token rules do not cover:
    per-input values if at most one position varies, an interval tensor
    otherwise (a `Mix` that is exact becomes that value). -/
def tLeave (ctx : TCtx) : TV → Option TV
  | .box => none
  | .var vs => some (.var vs)
  | .dt v => some (.dt v)
  | .mix m =>
    match concretize m with
    | none => none
    | some (some d) => some (.dt d)
    | some none => if ctx.aligned then (toVarMix ctx m).map .var else (collapseMix m).map .dt
  | .sep s => if ctx.aligned then (toVarSep ctx s).map .var else (collapseSep s).map .dt
  | .wsep w s =>
    if ctx.aligned then (toVarWSep ctx (.inl w) s).map .var else (collapseWSep (.inl w) s).map .dt
  | .wsepv ws s =>
    if ctx.aligned then (toVarWSep ctx (.inr ws) s).map .var else (collapseWSep (.inr ws) s).map .dt

/-- A domain value as per-input values (Python's `to_var`). -/
def tToVar (ctx : TCtx) : TV → Option (Array DT)
  | .box => none
  | .var vs => some vs
  | .dt v => some #[v]
  | .mix m => toVarMix ctx m
  | .sep s => toVarSep ctx s
  | .wsep w s => toVarWSep ctx (.inl w) s
  | .wsepv ws s => toVarWSep ctx (.inr ws) s

/-! ## Operations on per-input values -/

/-- An argument of an operation on per-input values, input by input: an
    interval tensor is the same for every input. -/
def varSlices (ctx : TCtx) (a : TV) : Option (Nat → DT) :=
  match a with
  | .dt v => some fun _ => v
  | a => (tToVar ctx a).map fun vs i => vs.getD i emptyDT

/-- The values per input given by `f` for each input. -/
def varEach (ctx : TCtx) (f : Nat → Option DT) : Step TV :=
  Step.ofOption (((Array.range ctx.k).mapM f).map .var)

/-- The operation on each input's value (Python's `var_op`); `decline` for
    the operations it does not cover. The arguments that are not domain
    values are the same for every input. -/
def tVarOp (ctx : TCtx) (op : Op) (args : List TV) : Step TV :=
  if !ctx.aligned then .fail else
  let slices := varSlices ctx
  let each := varEach ctx
  match op, args with
  | .binary f _ _, [x, y] =>
    match slices x, slices y with
    | some xs, some ys => each fun i => dbinary f (xs i) (ys i)
    | _, _ => .fail
  | .neg _, [x] =>
    match slices x with
    | some xs => each fun i => some (dneg (xs i))
    | none => .fail
  | .matmul _ _, [x, y] =>
    if y.isDomain then .decline else
    match slices x, y with
    | some xs, .dt b => each fun i => dmatmul (xs i) b
    | _, _ => .fail
  | .unsqueeze _ d, [x] =>
    match slices x with
    | some xs => each fun i => dtUnsqueeze d (xs i)
    | none => .fail
  | .sum _ d, [x] =>
    match slices x with
    | some xs => each fun i => dsum d (xs i)
    | none => .fail
  | .softmax _ d, [x] =>
    match slices x with
    | some xs => each fun i => dsoftmax d (xs i)
    | none => .fail
  | .exp _, [x] =>
    match slices x with
    | some xs => each fun i => dexp (xs i)
    | none => .fail
  | .index _ items, [x] =>
    match slices x with
    | some xs => each fun i => dtIndex items (xs i)
    | none => .fail
  | _, _ => .decline

/-! ## The token rules -/

/-- `x + y` with a domain value. -/
def tAdd (x y : TV) : Step TV :=
  match x, y with
  | .mix a, .mix b => (addMixes a b).bind fun m => .val (.mix m)
  | .mix a, .dt c => (addMix a c).bind fun m => .val (.mix m)
  | .dt c, .mix a => (addMix a c).bind fun m => .val (.mix m)
  | .sep s, .dt c => (addConst s c).bind fun s => .val (.sep s)
  | .dt c, .sep s => (addConst s c).bind fun s => .val (.sep s)
  | _, _ => .decline

/-- `x * y` with one domain value. -/
def tMul (x y : TV) : Step TV :=
  if x.isDomain && y.isDomain then .decline else
  let (v, c) := if x.isDomain then (x, y) else (y, x)
  match v, c with
  | .mix m, .dt c =>
    -- one number, which keeps the shape (Python's `Mix` keeps it even when
    -- the number has more dimensions than the `Mix`; then the product has
    -- more dimensions too, so that case declines here)
    if shapeSize c.shape == 1 && c.ok && c.shape.length ≤ m.const.shape.length then
      (scaleMix m ⟨[], #[c.lo.getD 0 0], #[c.hi.getD 0 0], c.e, c.exact⟩).bind fun m =>
        .val (.mix m)
    else .decline
  | .sep s, .dt c => mulSep s c
  | _, _ => .decline

/-- A sum over dimension `dim` of a `Sep` or `WSep`. -/
def tSum (ctx : TCtx) (x : TV) (dim : Int) : Step TV :=
  let nd : Int := (x.shape ctx).length
  let d := if dim ≥ 0 then dim else nd + dim
  match x with
  | .sep s =>
    if d == 1 then (sumPositions s none).bind fun m => .val (.mix m)
    else if d ≥ 2 && d < nd then (sumRows s d.toNat).bind fun s => .val (.sep s)
    else .decline
  | .wsep w s =>
    if d == 1 then (sumPositions s (some (.inl w))).bind fun m => .val (.mix m) else .decline
  | .wsepv ws s =>
    if d == 1 then (sumPositions s (some (.inr ws))).bind fun m => .val (.mix m) else .decline
  | _ => .decline

/-- `x[:, p]` of a `Sep`: one term. -/
def tGetitem (s : Sep) (items : List IndexItem) : Step TV :=
  match items with
  | [.all, .one p] =>
    if p < s.rows.length then
      .val (.mix ⟨dtZeros (1 :: s.rest), [⟨dtScalar 1, p, s.rows.getD p emptyDT⟩]⟩)
    else .fail
  | _ => .decline

/-- The node's value in the token domain (Python's `evaluate`); `decline`
    to leave the domain. `free b` says whether argument `b` does not depend
    on the input. -/
def tEvaluate (ctx : TCtx) (free : Nat → Bool) (op : Op) (args : List TV) : Step TV :=
  match op, args with
  | .matmul _ b, [.box, y] =>
    match y with
    | .dt w => if free b then Step.ofOption ((tLookup ctx w).map .sep) else .fail
    | _ => .fail
  | _, .box :: _ => .fail
  | .binary .mul _ _, [.var ws, .sep s] => mulVarSep ws s
  | .binary .mul _ _, [.sep s, .var ws] => mulVarSep ws s
  | op, args =>
    if args.any TV.isVar then tVarOp ctx op args else
    match op, args with
    -- products with matrices of rows of one dimension (Python's rules also
    -- take other shapes, where a product of rows is not the rows of the
    -- product; no model has them)
    | .matmul _ _, [.sep s, .dt b] =>
      if b.shape.length == 2 && b.exact && s.rest.length == 1 && b.shape.head? == s.rest.head? then
        (matmulSep s b).bind fun s => .val (.sep s)
      else .decline
    | .matmul _ _, [.mix m, .dt b] =>
      if b.shape.length == 2 && b.exact && m.const.shape.length == 2 &&
          b.shape.head? == m.const.shape.getLast? then
        (matmulMix m b).bind fun m => .val (.mix m)
      else .decline
    | .binary .add _ _, [x, y] => tAdd x y
    | .binary .mul _ _, [x, y] => tMul x y
    | .neg _, [.mix m] => (scaleMix m (dtScalar (-1))).bind fun m => .val (.mix m)
    | .sum _ d, [x] => tSum ctx x d
    | .index _ items, [.sep s] => tGetitem s items
    | _, _ => .decline

/-- The interpreter's values for the operations the token rules do not
    see: interval tensors, the leaf's box, and nothing else. -/
def TV.toGVal (ctx : TCtx) : TV → GVal
  | .dt v => .dt v
  | .box => .box ctx.box
  | _ => .box [⟨1, 0⟩]

/-- One operation of a token_interval leaf (Python's `_eval_token`). -/
def tevalOp (g : Graph) (w : DWeights) (ctx : TCtx) (deps : Array Bool) (vals : Array TV)
    (op : Op) : Option TV :=
  match op with
  | .input =>
    if ctx.box.length == g.positions && ctx.box.all (·.hi < g.values) then some .box else none
  | op =>
    match op.args.mapM (vals[·]?) with
    | none => none
    | some args =>
      let plain := fun (vals : Array TV) =>
        ((gevalOp g w (.box ctx.box) (vals.map (·.toGVal ctx)) op).bind GVal.tensor).map TV.dt
      if !(args.any TV.isDomain) then plain vals else
      match tEvaluate ctx (fun b => !deps.getD b true) op args with
      | .val v => some v
      | .fail => none
      | .decline =>
        -- the arguments leave the domain
        let left := op.args.mapM fun a => (vals[a]?).bind fun v =>
          if v.isDomain then tLeave ctx v else some v
        match left with
        | none => none
        | some left =>
          let set := fun (vs : List TV) =>
            (op.args.zip vs).foldl (fun acc (a, v) => acc.set! a v) vals
          if left.any TV.isVar then
            match tVarOp ctx op left with
            | .val v => some v
            | .fail => none
            | .decline =>
              match left.mapM fun v => match v with
                  | .var vs => (collapseVar vs).map TV.dt
                  | v => some v with
              | none => none
              | some boxed => plain (set boxed)
          else plain (set left)

/-- Run the operations in order. -/
def tevalOps (g : Graph) (w : DWeights) (ctx : TCtx) (deps : Array Bool) :
    List Op → Array TV → Option (Array TV)
  | [], vals => some vals
  | op :: ops, vals =>
    match tevalOp g w ctx deps vals op with
    | some v => tevalOps g w ctx deps ops (vals.push v)
    | none => none

/-! ## The decision -/

/-- One term's lowest weighted differences of rows, added to the margin
    bounds so far: one row of bounds per input if at most one position
    varies, else one row for the whole box. -/
def marginStep (ctx : TCtx) (n label : Nat) (e0 : Int) (rowsN : Nat) (acc : List (List Int))
    (t : Term) : Option (List (List Int)) := do
  let R := t.rows
  let tokens := R.shape.headD 0
  if R.shape.length != 2 then none
  let sh := (t.w.e + R.e - e0).toNat
  let D := fun (r o : Nat) => mget R.lo (r * n + label) - mget R.lo (r * n + o)
  if ctx.aligned then
    let nw := shapeSize t.w.shape
    if !(tokens == ctx.k || tokens == 1) || !(nw == ctx.k || nw == 1) then none
    pure ((List.range rowsN).zip acc |>.map fun (i, row) =>
      let r := if tokens == 1 then 0 else i
      let wi := if nw == 1 then 0 else i
      let wl := mget t.w.lo wi
      let wh := mget t.w.hi wi
      (List.range n).zip row |>.map fun (o, a) =>
        let d := D r o
        a + (if t.w.exact then wl * d else min (wl * d) (wh * d)) * 2 ^ sh)
  else
    if tokens == 0 then none
    let dmin := fun o => (List.range tokens).foldl (fun m r => min m (D r o)) (D 0 o)
    let dmax := fun o => (List.range tokens).foldl (fun m r => max m (D r o)) (D 0 o)
    if t.w.lo.isEmpty then none
    let wlo := t.w.lo.foldl min (t.w.lo.getD 0 0)
    let whi := t.w.hi.foldl max (t.w.hi.getD 0 0)
    pure (acc.map fun row => (List.range n).zip row |>.map fun (o, a) =>
      a + min (min (wlo * dmin o) (wlo * dmax o)) (min (whi * dmin o) (whi * dmax o)) * 2 ^ sh)

/-- Per-input values: the label's lower end minus every other output's upper
    end, for every input, at the lowest exponent. -/
def varMargin (vs : Array DT) (label : Nat) : Option (Option (Int × Int)) := do
  if vs.isEmpty then none
  if !(vs.all fun x => x.shape == (vs.getD 0 emptyDT).shape) then none
  let e := (vs.toList.map (·.e)).foldl min (vs.getD 0 emptyDT).e
  let ms := vs.toList.map fun x =>
    let x := x.at e
    let n := shapeSize x.shape
    ((List.range n).filter (· != label)).map fun o => mget x.lo label - mget x.hi o
  let all := ms.flatten
  pure (all.min?.map fun m => (m, e))

/-- An interval value: the label's lower end minus every other output's
    upper end. -/
def dtMargin (x : DT) (label : Nat) : Option (Int × Int) :=
  let n := shapeSize x.shape
  let all := ((List.range n).filter (· != label)).map fun o => mget x.lo label - mget x.hi o
  all.min?.map fun m => (m, x.e)

/-- A `Mix`: the constant's margin plus, per term, the lowest weighted
    difference of rows (input by input if at most one position varies). -/
def mixMargin (ctx : TCtx) (m : Mix) (label : Nat) : Option (Option (Int × Int)) := do
  let n := m.const.shape.getD 1 0
  if label ≥ n then none
  let c := m.const
  let e0 := (m.terms.map fun t => t.w.e + t.rows.e).foldl min c.e
  let shiftC := (c.e - e0).toNat
  let cm := (List.range n).map fun o => (mget c.lo label - mget c.hi o) * 2 ^ shiftC
  let rowsN := if ctx.aligned then ctx.k else 1
  let acc₀ : List (List Int) := (List.range rowsN).map fun _ => cm
  let acc ← m.terms.foldlM (marginStep ctx n label e0 rowsN) acc₀
  let all := acc.flatMap fun row => ((List.range n).zip row).filter (·.1 != label) |>.map (·.2)
  pure (all.min?.map fun m => (m, e0))

/-- The lowest margin bound over the leaf's inputs, at the exponent given:
    `some none` if the network has one output, `none` where Python raises.
    Values leave the domain first unless they are interval tensors or
    `Mix`es. -/
def lowestMargin (ctx : TCtx) (v : TV) (label : Nat) : Option (Option (Int × Int)) := do
  let v ← match v with
    | .sep _ | .wsep _ _ | .wsepv _ _ => tLeave ctx v
    | v => some v
  match v with
  | .var vs => varMargin vs label
  | .dt x => some (dtMargin x label)
  | .mix m => mixMargin ctx m label
  | _ => none

/-- The output of a token_interval leaf and its lowest margin bound, for the
    label `l`: `none` where Python rejects the proof. -/
def tokenLeafBound (g : Graph) (w : DWeights) (box : Box) (l : Nat) :
    Option (Option (Int × Int)) := do
  let ctx := TCtx.ofBox box g.values
  let vals ← tevalOps g w ctx (dependsOnInput g) g.nodes #[]
  let out ← vals[g.output]?
  match out.shape ctx with
  | [1, n] => if l < n then lowestMargin ctx out l else none
  | _ => none

/-- A token_interval leaf: `some false` if the label is not constant on the
    box or the margin bound is not positive. -/
def generalTokenInterval (g : Graph) (w : DWeights) (task : Task) (box : Box) : Option Bool :=
  match task.constantLabel box with
  | none => some false
  | some l =>
    (tokenLeafBound g w box l).map fun b =>
      match b with
      | none => true
      | some (m, _) => decide (0 < m)

/-! ## Leaves and proofs -/

/-- Whether every input of the leaf is certified, or why the whole proof is
    rejected. -/
def generalLeafOk (g : Graph) (w : DWeights) (task : Task) (leaf : Leaf) :
    Except String Bool :=
  match leaf.rule with
  | .skip => .ok false
  | .single =>
    match boxInput leaf.box with
    | some x =>
      match generalSingle g w task x with
      | some ok => .ok ok
      | none => .error "the checker cannot run the network on this input"
    | none => .error "a single leaf must hold exactly one input"
  | .interval none =>
    match generalInterval g w task leaf.box with
    | some ok => .ok ok
    | none => .error ("the interval rule cannot follow this network " ++
        "(in interval leaves the input may only be multiplied by a weight matrix)")
  | .interval (some name) => .error s!"unknown approximation {name}"
  | .tokenInterval =>
    match generalTokenInterval g w task leaf.box with
    | some ok => .ok ok
    | none => .error ("the token_interval rule cannot follow this network " ++
        "(in token_interval leaves the input may only be multiplied by a weight matrix)")

/-- The number of inputs in the certified leaves. -/
def generalCheckLeaves (g : Graph) (w : DWeights) (task : Task) :
    List Leaf → Except String Nat
  | [] => .ok 0
  | leaf :: rest =>
    match generalCheckLeaves g w task rest with
    | .error e => .error e
    | .ok n =>
      match generalLeafOk g w task leaf with
      | .error e => .error e
      | .ok ok => .ok (if ok then n + boxSize leaf.box else n)

/-- Check a proof on a general network: the number of inputs it certifies,
    or why it is rejected. -/
def checkProofGeneral (g : Graph) (w : Weights Rat) (task : Task) (proof : ProofFile) :
    Except String Nat :=
  if proof.symmetry then
    .error "symmetry does not hold: the input is not used only through a sum over positions"
  else if !proof.contractions.isEmpty then
    .error "the contract rule needs a network built only from linear maps, sums and additions"
  else if !proof.approximations.isEmpty then
    .error "the approximate rule needs a network built only from linear maps"
  else if task.space.any (· == 0) then .error "the input space has a position with no tokens"
  else
    match dweights w with
    | none => .error "a weight is not a tensor of dyadic numbers"
    | some dw =>
      if !constPassOk g dw then .error "the network's operations on its weights fail"
      else
        match walk proof.tree (rootBox task.space) with
        | .error e => .error e
        | .ok leaves => generalCheckLeaves g dw task leaves

end CompactCheck
