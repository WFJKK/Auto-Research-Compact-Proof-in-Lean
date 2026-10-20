import CompactCheck.Semantics
import CompactCheck.Exp
import CompactCheck.Check

/-!
# The checker on attention networks

A network that is not built only from linear maps, sums and additions (an
attention network, the xorformer) is checked as `core/check/general.py`
checks it: every value is a tensor of intervals, and every operation is
computed on intervals. Sums, differences and products are exact; `exp` and
`softmax` are enclosed by the bounds of `Exp.lean`. So the true value of
every operation lies in its interval (`GeneralSound.lean`).

* A `single` leaf runs the network on its one input, exactly one-hot, and
  certifies the input if the lower bound of the label's logit is above the
  upper bound of every other logit.
* An `interval` leaf runs the network on all inputs of its box at once.
  The input may only be multiplied by a weight matrix: that gives, at each
  position, the smallest and largest entry of the matrix's rows over the
  allowed tokens (a lookup). Everything after that is interval arithmetic.

The contract, approximate and symmetry rules need a linear network; Python
refuses them here, and so does this checker. So does any use of the input
other than a lookup in an interval leaf. `torch.nn.Linear` modules are not
supported in these networks yet (no model uses them); the checker refuses
them.

Numbers are stored as Python's interval tensors store them (`IT` in
`core/check/interval.py`): integers with one power of two per tensor, so
sums and products need no fractions. Every bound has the value Python's
has, operation by operation, so both checkers accept the same leaves.

This file uses only core Lean.
-/

namespace CompactCheck

/-! ## Interval tensors of dyadic numbers -/

/-- Python's interval tensor: entry `j` (row-major) lies between
    `lo[j] * 2^e` and `hi[j] * 2^e`. `exact` says whether Python holds the
    tensor as exact (`lo` the same array as `hi`): it chooses Python's
    formula for products, which has the same value as the general one, and
    decides where Python refuses a lookup. -/
structure DT where
  shape : List Nat
  lo : Array Int
  hi : Array Int
  e : Int
  exact : Bool

/-- Both arrays have the tensor's number of entries. -/
def DT.ok (v : DT) : Bool :=
  v.lo.size == shapeSize v.shape && v.hi.size == shapeSize v.shape

/-- The same values, written at the exponent `e - k`. -/
def DT.shift (v : DT) (k : Nat) : DT :=
  if k = 0 then v else
  let lo := v.lo.map (· * 2 ^ k)
  ⟨v.shape, lo, if v.exact then lo else v.hi.map (· * 2 ^ k), v.e - k, v.exact⟩

/-- An exact tensor of integers times `2^e`. -/
def DT.ofInts (shape : List Nat) (m : Array Int) (e : Int) : DT := ⟨shape, m, m, e, true⟩

/-- A tensor of dyadic rationals as one integer array and a power of two, or
    `none` if an entry is not dyadic or the entries do not match the shape. -/
def DT.ofRat (t : Tensor Rat) : Option DT :=
  if t.wellFormed && t.data.all fun q => q.den == 2 ^ q.den.log2 then
    let k := t.data.foldl (fun k q => max k q.den.log2) 0
    some (DT.ofInts t.shape (t.data.map fun q => q.num * 2 ^ (k - q.den.log2)) (-(k : Int)))
  else none

/-- `unravel` and `ravel` with the strides computed once. -/
def unravelWith (st s : List Nat) (j : Nat) : List Nat :=
  List.zipWith (fun st d => j / st % d) st s

def ravelWith (st i : List Nat) : Nat :=
  (List.zipWith (· * ·) st i).sum

/-- Entry `j`, 0 outside. -/
@[inline] def mget (a : Array Int) (j : Nat) : Int := a.getD j 0

/-! ## Products, as Python computes them -/

/-- The lower bound of a product of `[al, ah]` and `[bl, bh]`. With an exact
    factor, Python picks the end by its sign; otherwise it takes the
    smallest of the four products. -/
@[inline] def prodLo (ea eb : Bool) (al ah bl bh : Int) : Int :=
  if ea && eb then al * bl
  else if eb then (if bl ≥ 0 then al * bl else ah * bl)
  else if ea then (if al ≥ 0 then al * bl else al * bh)
  else min (min (al * bl) (al * bh)) (min (ah * bl) (ah * bh))

/-- The upper bound of the product. -/
@[inline] def prodHi (ea eb : Bool) (al ah bl bh : Int) : Int :=
  if ea && eb then al * bl
  else if eb then (if bl ≥ 0 then ah * bl else al * bl)
  else if ea then (if al ≥ 0 then al * bh else al * bl)
  else max (max (al * bl) (al * bh)) (max (ah * bl) (ah * bh))

/-! ## Operations -/

/-- The lower bound of `x + y`, `x - y` or `x * y` from bounds on `x` and
    `y` (for sums and differences, at a common exponent). -/
@[inline] def binLo (f : BinOp) (ea eb : Bool) (al ah bl bh : Int) : Int :=
  match f with
  | .add => al + bl
  | .sub => al - bh
  | .mul => prodLo ea eb al ah bl bh

/-- The upper bound. -/
@[inline] def binHi (f : BinOp) (ea eb : Bool) (al ah bl bh : Int) : Int :=
  match f with
  | .add => ah + bh
  | .sub => ah - bl
  | .mul => prodHi ea eb al ah bl bh

/-- The flat position in a tensor of shape `sh` that broadcasting reads for
    entry `j` of the shape `s` (`st`, `sth` their strides). -/
@[inline] def bcastPos (st s sth sh : List Nat) (j : Nat) : Nat :=
  ravelWith sth (broadcastIndex sh (unravelWith st s j))

/-- The lower ends of entrywise `f` with broadcasting to the shape `s`. -/
def dbinLo (f : BinOp) (a b : DT) (s : List Nat) : Array Int :=
  let st := strides s
  let sta := strides a.shape
  let stb := strides b.shape
  (Array.range (shapeSize s)).map fun j =>
    let ia := bcastPos st s sta a.shape j
    let ib := bcastPos st s stb b.shape j
    binLo f a.exact b.exact (mget a.lo ia) (mget a.hi ia) (mget b.lo ib) (mget b.hi ib)

/-- The upper ends; the lower ends again if both arguments are exact. -/
def dbinHi (f : BinOp) (a b : DT) (s : List Nat) : Array Int :=
  if a.exact && b.exact then dbinLo f a b s else
  let st := strides s
  let sta := strides a.shape
  let stb := strides b.shape
  (Array.range (shapeSize s)).map fun j =>
    let ia := bcastPos st s sta a.shape j
    let ib := bcastPos st s stb b.shape j
    binHi f a.exact b.exact (mget a.lo ia) (mget a.hi ia) (mget b.lo ib) (mget b.hi ib)

/-- Entrywise `f` with broadcasting to the shape `s`, at exponent `e`. -/
def dbinaryAt (f : BinOp) (a b : DT) (s : List Nat) (e : Int) : DT :=
  ⟨s, dbinLo f a b s, dbinHi f a b s, e, a.exact && b.exact⟩

/-- Entrywise `+`, `-` or `*` with broadcasting. Sums and differences are
    taken at the smaller exponent; products at the sum of the exponents. -/
def dbinary (f : BinOp) (a b : DT) : Option DT :=
  if !(a.ok && b.ok) then none else
  (broadcastShape a.shape b.shape).map fun s =>
    match f with
    | .mul => dbinaryAt .mul a b s (a.e + b.e)
    | f =>
      let e := min a.e b.e
      dbinaryAt f (a.shift (a.e - e).toNat) (b.shift (b.e - e).toNat) s e

/-- `-x`. -/
def dneg (a : DT) : DT :=
  let lo := a.hi.map (- ·)
  ⟨a.shape, lo, if a.exact then lo else a.lo.map (- ·), a.e, a.exact⟩

/-- The lower ends of a matrix product: entry `j` sums the products of row
    `pa` of `a` (positions `pa + t`) and column `pb` of `b` (positions
    `pb + t * n`), as Python bounds them. -/
def matmulEnd (lower : Bool) (p : MatmulShape) (a b : DT) : Array Int :=
  let s := p.batch ++ [p.m, p.n]
  let st := strides s
  let sta := strides p.ba
  let stb := strides p.bb
  (Array.range (shapeSize s)).map fun j =>
    let i := unravelWith st s j
    let bi := i.take p.batch.length
    let pa := (ravelWith sta (broadcastIndex p.ba bi) * p.m + i.getD p.batch.length 0) * p.k
    let pb := ravelWith stb (broadcastIndex p.bb bi) * p.k * p.n + i.getD (p.batch.length + 1) 0
    ((List.range p.k).map fun t =>
      (if lower then prodLo else prodHi) a.exact b.exact (mget a.lo (pa + t)) (mget a.hi (pa + t))
        (mget b.lo (pb + t * p.n)) (mget b.hi (pb + t * p.n))).sum

/-- `torch.matmul`, with the shapes of `matmulOp` (`Semantics.lean`); each
    product enclosed as Python does, at the sum of the exponents. -/
def dmatmul (a b : DT) : Option DT :=
  if !(a.ok && b.ok) then none else
  (matmulShape a.shape b.shape).map fun p =>
    let lo := matmulEnd true p a b
    ⟨p.out, lo, if a.exact && b.exact then lo else matmulEnd false p a b, a.e + b.e,
      a.exact && b.exact⟩

/-- Sum over one dimension. -/
def dsum (dim : Int) (a : DT) : Option DT :=
  if !a.ok then none else
  match sumOp dim (⟨a.shape, a.lo⟩ : Tensor Int) with
  | none => none
  | some lo =>
    let hi := if a.exact then lo else (sumOp dim (⟨a.shape, a.hi⟩ : Tensor Int)).getD lo
    some ⟨lo.shape, lo.data, hi.data, a.e, a.exact⟩

/-- An operation that only moves entries (indexing, transposing,
    `unsqueeze`, `expand`), applied to both arrays. -/
def dmove (f : Tensor Int → Option (Tensor Int)) (a : DT) : Option DT :=
  if !a.ok then none else
  match f ⟨a.shape, a.lo⟩ with
  | none => none
  | some lo =>
    if a.exact then some ⟨lo.shape, lo.data, lo.data, a.e, true⟩ else
    match f ⟨a.shape, a.hi⟩ with
    | some hi => some ⟨lo.shape, lo.data, hi.data, a.e, false⟩
    | none => none

/-- The smallest exponent of the tensors, and the tensors written at it. -/
def alignAll (as : List DT) : Int × List DT :=
  let e := (as.map (·.e)).foldl min ((as.headD ⟨[], #[], #[], 0, true⟩).e)
  (e, as.map fun a => a.shift (a.e - e).toNat)

/-- `torch.cat` or `torch.stack`, at the smallest exponent. -/
def djoin (f : List (Tensor Int) → Option (Tensor Int)) (as : List DT) : Option DT :=
  if !(as.all DT.ok) || as.isEmpty then none else
  match alignAll as with
  | (e, as) =>
    match f (as.map fun a => ⟨a.shape, a.lo⟩), f (as.map fun a => ⟨a.shape, a.hi⟩) with
    | some lo, some hi => some ⟨lo.shape, lo.data, hi.data, e, as.all (·.exact)⟩
    | _, _ => none

/-- Bounds on `exp` at `2^-120` of `X * 2^e`: the lower bound if `!upper`. -/
def expEnd (X e : Int) (upper : Bool) : Option Int :=
  (expBoundsParts (decide (X < 0)) X.natAbs e).map fun p => if upper then p.2 else p.1

/-- `exp` entry by entry, at `2^-120`: the lower bound of `exp` at the lower
    end, the upper bound at the upper end. -/
def dexp (a : DT) : Option DT :=
  if !a.ok then none else
  match a.lo.toList.mapM (expEnd · a.e false), a.hi.toList.mapM (expEnd · a.e true) with
  | some lo, some hi => some ⟨a.shape, lo.toArray, hi.toArray, -(expPrecision : Int), false⟩
  | _, _ => none

/-- The flat position of entry `k` of the row, along a dimension of size
    `n` and stride `sd`, of the entry at flat position `j`. -/
def rowPosition (sd n j k : Nat) : Nat := j - (j / sd % n) * sd + k * sd

/-- The shift of the row of entry `j`: its largest upper end. -/
def rowShift (a : DT) (sd n j : Nat) : Int :=
  ((List.range n).map fun k => mget a.hi (rowPosition sd n j k)).foldl max
    (mget a.hi (rowPosition sd n j 0))

/-- The sum of `E` over the row of entry `j`. -/
def rowSum (E : Array Int) (sd n j : Nat) : Int :=
  ((List.range n).map fun k => mget E (rowPosition sd n j k)).sum

/-- `softmax` along dimension `dim`, as interval.py encloses it, at
    `2^-120`. Each row is shifted by its largest upper end; `El`, `Eh` are
    the bounds on `exp` of the shifted lower and upper ends, entry by entry;
    the bounds of an entry use the sums of its row (`softmaxLower`,
    `softmaxUpper` of `Exp.lean`). -/
def dsoftmax (dim : Int) (a : DT) : Option DT :=
  if !a.ok then none else
  match normDim dim a.shape.length with
  | none => none
  | some d =>
    let size := shapeSize a.shape
    let n := a.shape.getD d 0
    let sd := (strides a.shape).getD d 0
    if n = 0 then none else
    match (List.range size).mapM (fun j => expEnd (mget a.lo j - rowShift a sd n j) a.e false),
        (List.range size).mapM (fun j => expEnd (mget a.hi j - rowShift a sd n j) a.e true) with
    | some El, some Eh =>
      let El := El.toArray
      let Eh := Eh.toArray
      some ⟨a.shape,
        (Array.range size).map (fun j => softmaxLower (mget El j) (mget Eh j) (rowSum Eh sd n j)),
        (Array.range size).map (fun j => softmaxUpper (mget El j) (mget Eh j) (rowSum El sd n j)),
        -(expPrecision : Int), false⟩
    | _, _ => none

/-! ## The one-hot input in an interval leaf -/

/-- The smallest of `f lo, ..., f hi`. -/
def irangeMin (f : Nat → Int) (lo hi : Nat) : Int :=
  (List.range (hi - lo)).foldl (fun m k => min m (f (lo + 1 + k))) (f lo)

/-- The largest of `f lo, ..., f hi`. -/
def irangeMax (f : Nat → Int) (lo hi : Nat) : Int :=
  (List.range (hi - lo)).foldl (fun m k => max m (f (lo + 1 + k))) (f lo)

/-- Every range of the box is a nonempty range of tokens below `values`. -/
def boxFits (values : Nat) (box : Box) : Bool :=
  box.all fun r => r.lo ≤ r.hi && r.hi < values

/-- `x @ B` for every one-hot `x` of the box, with `B` an exact matrix
    `[values, d]`: at each position, the smallest and largest entry of each
    column over the rows of the allowed tokens (`_onehot_lookup`). -/
def lookupMatmul (values : Nat) (box : Box) (B : DT) : Option DT :=
  match B.shape with
  | [v, d] =>
    if B.exact && B.ok && v == values && boxFits values box then
      let P := box.length
      let r (j : Nat) : Range := box.getD (j / d % P) ⟨0, 0⟩
      some ⟨[1, P, d], (Array.range (P * d)).map (fun j =>
          irangeMin (fun t => mget B.lo (t * d + j % d)) (r j).lo (r j).hi),
        (Array.range (P * d)).map (fun j =>
          irangeMax (fun t => mget B.lo (t * d + j % d)) (r j).lo (r j).hi),
        B.e, false⟩
    else none
  | _ => none

/-! ## The network -/

/-- A value of the interpreter: the one-hot inputs of the box of an interval
    leaf, or an interval tensor. -/
inductive GVal where
  | box (b : Box)
  | dt (v : DT)

/-- The interval tensor, or `none` for the input of an interval leaf. -/
def GVal.tensor : GVal → Option DT
  | .dt v => some v
  | .box _ => none

/-- The weights as interval tensors, converted once. -/
abbrev DWeights := List (String × DT)

def dweights (w : Weights Rat) : Option DWeights :=
  w.mapM fun p => (DT.ofRat p.2).map fun v => (p.1, v)

/-- One operation, given the values of the operations before it. `none`
    where the Python checker raises. -/
def gevalOp (g : Graph) (w : DWeights) (input : GVal) (vals : Array GVal) : Op → Option GVal
  | .input =>
    match input with
    | .box b => if b.length == g.positions && b.all (·.hi < g.values) then some input else none
    | .dt _ => some input
  | .param n => (List.lookup n w).map .dt
  | .linear _ _ _ => none
  | .sum a d => ((vals[a]?.bind GVal.tensor).bind (dsum d)).map .dt
  | .add a b =>
    match vals[a]?.bind GVal.tensor, vals[b]?.bind GVal.tensor with
    | some x, some y => if x.shape == y.shape then (dbinary .add x y).map .dt else none
    | _, _ => none
  | .binary f a b =>
    match vals[a]?.bind GVal.tensor, vals[b]?.bind GVal.tensor with
    | some x, some y => (dbinary f x y).map .dt
    | _, _ => none
  | .neg a => (vals[a]?.bind GVal.tensor).map fun x => .dt (dneg x)
  | .matmul a b =>
    match vals[a]?, vals[b]?.bind GVal.tensor with
    | some (.box bx), some y => (lookupMatmul g.values bx y).map .dt
    | some (.dt x), some y => (dmatmul x y).map .dt
    | _, _ => none
  | .index a items => ((vals[a]?.bind GVal.tensor).bind (dmove (indexOp · items))).map .dt
  | .transpose a => ((vals[a]?.bind GVal.tensor).bind (dmove transposeOp)).map .dt
  | .unsqueeze a d => ((vals[a]?.bind GVal.tensor).bind (dmove (unsqueezeOp · d))).map .dt
  | .expand a s => ((vals[a]?.bind GVal.tensor).bind (dmove (expandOp · s))).map .dt
  | .cat args d => ((args.mapM fun a => vals[a]?.bind GVal.tensor).bind (djoin (catOp · d))).map .dt
  | .stack args d =>
    ((args.mapM fun a => vals[a]?.bind GVal.tensor).bind (djoin (stackOp · d))).map .dt
  | .exp a => ((vals[a]?.bind GVal.tensor).bind dexp).map .dt
  | .softmax a d => ((vals[a]?.bind GVal.tensor).bind (dsoftmax d)).map .dt
  | .zerosLike a =>
    (vals[a]?.bind GVal.tensor).map fun x =>
      .dt (DT.ofInts x.shape (Array.replicate (shapeSize x.shape) 0) 0)

/-- Run the operations in order, appending each value. -/
def gevalOps (g : Graph) (w : DWeights) (input : GVal) :
    List Op → Array GVal → Option (Array GVal)
  | [], vals => some vals
  | op :: ops, vals =>
    match gevalOp g w input vals op with
    | some v => gevalOps g w input ops (vals.push v)
    | none => none

/-- The interval tensor of the network's output, with this input. -/
def gevalGraph (g : Graph) (w : DWeights) (input : GVal) : Option DT :=
  match gevalOps g w input g.nodes #[] with
  | some vals => vals[g.output]?.bind GVal.tensor
  | none => none

/-- The exact one-hot input of `x`. -/
def oneHotDT (g : Graph) (x : Input) : Option GVal :=
  (oneHotInput g.positions g.values x).map fun (t : Tensor Int) => .dt (DT.ofInts t.shape t.data 0)

/-- The final test of both rules, on the logits (shape `[1, n]`): the lower
    bound of the label's logit is above the upper bound of every other
    logit. `none` if the output is not a vector of logits or the label is
    not one of them (the Python checker raises). -/
def marginTest (out : DT) (l : Nat) : Option Bool :=
  match out.shape with
  | [1, n] =>
    if out.ok && l < n then
      some ((List.range n).all fun j => j == l || decide (mget out.hi j < mget out.lo l))
    else none
  | _ => none

/-- A single leaf of a general network: the network on the input, exactly. -/
def generalSingle (g : Graph) (w : DWeights) (task : Task) (x : Input) : Option Bool := do
  let input ← oneHotDT g x
  let out ← gevalGraph g w input
  marginTest out (task.label x)

/-- An interval leaf of a general network. `some false` if the label is not
    constant on the box or a margin bound is not positive. -/
def generalInterval (g : Graph) (w : DWeights) (task : Task) (box : Box) : Option Bool :=
  match task.constantLabel box with
  | none => some false
  | some l => do
    let out ← gevalGraph g w (.box box)
    marginTest out l

/-! ## The operations that do not depend on the input

The Python checker computes them once, before any leaf, and rejects the
proof if one of them fails. So does this checker. -/

/-- The operations that depend on the input. -/
def dependsOnInput (g : Graph) : Array Bool :=
  g.nodes.foldl (fun deps op =>
    deps.push (match op with
      | .input => true
      | op => op.args.any fun a => deps.getD a false)) #[]

/-- Whether every operation that does not depend on the input succeeds. -/
def constPassOk (g : Graph) (w : DWeights) : Bool :=
  let deps := dependsOnInput g
  let r := g.nodes.foldl (fun (acc : Option (Array GVal) × Nat) op =>
    match acc with
    | (none, k) => (none, k + 1)
    | (some vals, k) =>
      if deps.getD k true then (some (vals.push (.box [])), k + 1)
      else (((gevalOp g w (.box []) vals op).map vals.push), k + 1)) (some #[], 0)
  r.1.isSome

end CompactCheck
