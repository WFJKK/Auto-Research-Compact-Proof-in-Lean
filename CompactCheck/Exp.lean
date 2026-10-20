/-!
# Bounds on `exp` and `softmax`

The exponential of a rational number is not rational, so the checker
encloses it: `expBounds x` gives integers `L` and `H` with
`L ≤ exp x * 2^120 ≤ H` (`expBounds_spec` in `ExpSound.lean`). Softmax is
enclosed from these bounds (`softmaxBounds`). Both follow `exp_bounds` and
`softmax` in `core/check/interval.py` step by step, so the two checkers
compute the same bounds.

For `exp`: write `|x| = y * 2^m` with `y ≤ 2^-8`. The series
`exp y = Σ y^k / k!` has positive terms, each at most `y` times the one
before, so after the terms up to `k` the rest is at most twice the next
term. All terms are integers at `2^-W`, rounded down for the lower bound
and up for the upper bound. For `x < 0`, `exp x = 1 / exp |x|`. Then `m`
squarings, rounded outwards, give `exp x = exp (±y) ^ (2^m)`.

This file uses only core Lean.
-/

namespace CompactCheck

/-- Results of `exp` and `softmax` are multiples of `2^-expPrecision`. -/
def expPrecision : Nat := 120

/-- `exp` is refused for arguments of `2^maxExpLog2` or more, and enclosed by
    `[0, 2^-120]` below `-2^maxExpLog2`. -/
def maxExpLog2 : Int := 12

/-- `⌈a / b⌉` for `b > 0`. -/
def ceilDiv (a b : Int) : Int := -((-a) / b)

/-- A dyadic rational `x = ±A * 2^e` as `(A, e)` with `A = |numerator|`, or
    `none` if the denominator is not a power of two. -/
def dyadicParts (x : Rat) : Option (Nat × Int) :=
  if x.den = 2 ^ x.den.log2 then some (x.num.natAbs, -(x.den.log2 : Int)) else none

/-- `A * 2^s` rounded down and up. -/
def scaledArg (A : Nat) (s : Int) : Int × Int :=
  if s ≥ 0 then (A * 2 ^ s.toNat, A * 2 ^ s.toNat)
  else (A / 2 ^ (-s).toNat, ceilDiv A (2 ^ (-s).toNat))

/-- The terms of the series from term `k` on, `tlo` and `thi` being term `k`
    at `2^-W` rounded down and up. Returns the lower sum and the upper sum,
    the latter with twice the first term left out. At most `fuel` terms. -/
def expSeries (W : Nat) (ylo yhi : Int) : Nat → Nat → Int → Int → Int → Int → Option (Int × Int)
  | 0, _, _, _, _, _ => none
  | fuel + 1, k, tlo, thi, loSum, hiSum =>
    let tlo' := tlo * ylo / (((k + 1 : Nat) : Int) * 2 ^ W)
    let thi' := ceilDiv (thi * yhi) (((k + 1 : Nat) : Int) * 2 ^ W)
    if thi' ≤ 1 then some (loSum + tlo, hiSum + thi + 2 * thi')
    else expSeries W ylo yhi fuel (k + 1) tlo' thi' (loSum + tlo) (hiSum + thi)

/-- Square `n` times at `2^-W`, the lower bound rounded down and the upper
    bound up. -/
def expSquare (W : Nat) : Nat → Int × Int → Int × Int
  | 0, p => p
  | n + 1, (L, H) => expSquare W n (L * L / 2 ^ W, ceilDiv (H * H) (2 ^ W))

/-- From the two sums at `2^-W` to the bounds at `2^-120`: for `x < 0` the
    reciprocals, then `m` squarings, all rounded outwards. -/
def expFinish (neg : Bool) (W m : Nat) (sums : Int × Int) : Int × Int :=
  let start : Int × Int :=
    if neg then (2 ^ (2 * W) / sums.2, ceilDiv (2 ^ (2 * W)) sums.1) else sums
  let r := expSquare W m start
  (r.1 / 2 ^ (W - expPrecision), ceilDiv r.2 (2 ^ (W - expPrecision)))

/-- `exp_bounds(X, e)` of interval.py: `(L, H)` with
    `L ≤ exp (±A * 2^e) * 2^120 ≤ H`, the sign `-` if `neg`. `none` where
    Python raises: an argument of `2^12` or more. Below, `|x| < 2^(bl + e)`
    with `bl` the number of bits of `A`; `y = |x| / 2^m ≤ 2^-8`, and
    `y * 2^W = A * 2^(e - m + W)`. -/
def expBoundsParts (neg : Bool) (A : Nat) (e : Int) : Option (Int × Int) :=
  if A = 0 then some (2 ^ expPrecision, 2 ^ expPrecision) else
  if ((A.log2 + 1 : Nat) : Int) + e > maxExpLog2 then (if neg then some (0, 1) else none) else
  let m : Nat := (max 0 (((A.log2 + 1 : Nat) : Int) + e + 8)).toNat
  let W : Nat := expPrecision + m + 32
  let y := scaledArg A (e - m + W)
  (expSeries W y.1 y.2 (W + 2) 0 (2 ^ W) (2 ^ W) 0 0).map (expFinish neg W m)

/-- `(L, H)` with `L ≤ exp x * 2^120 ≤ H`, as `exp_bounds` in interval.py
    computes it. `none` for an argument of `2^12` or more, and for a number
    that is not dyadic (the checker only meets dyadic numbers). -/
def expBounds (x : Rat) : Option (Int × Int) :=
  match dyadicParts x with
  | none => none
  | some (A, e) => expBoundsParts (x < 0) A e

/-- The bounds as rationals: `(L / 2^120, H / 2^120)`. -/
def expInterval (x : Rat) : Option (Rat × Rat) :=
  (expBounds x).map fun (L, H) => ((L : Rat) / 2 ^ expPrecision, (H : Rat) / 2 ^ expPrecision)

/-! ## Softmax

`softmax` of interval.py, on one row of intervals `[lo k, hi k]`: shift by
the largest upper end `c` (softmax does not change), bound `exp` of the
shifted ends, and enclose the weight of entry `j`,
`e_j / (e_j + Σ_{k ≠ j} e_k)`, which grows with `e_j` and shrinks with
every other `e_k`. -/

/-- The lower bound on the weight of an entry, at `2^-120`:
    `max 0 ⌊el * 2^120 / (el + S_hi - eh)⌋`, or 0 if the denominator is not
    positive. -/
def softmaxLower (el eh Shi : Int) : Int :=
  if el + Shi - eh > 0 then max 0 (el * 2 ^ expPrecision / (el + Shi - eh)) else 0

/-- The upper bound on the weight of an entry, at `2^-120`:
    `min 2^120 ⌈eh * 2^120 / (eh + S_lo - el)⌉`, or `2^120` if the
    denominator is not positive. -/
def softmaxUpper (el eh Slo : Int) : Int :=
  if eh + Slo - el > 0 then min (2 ^ expPrecision) (ceilDiv (eh * 2 ^ expPrecision) (eh + Slo - el))
  else 2 ^ expPrecision

/-- The bounds on the softmax of a row of intervals `[lo k, hi k]`, at
    `2^-120`, after shifting the row by `c`: `el`, `eh` bound `exp` of the
    shifted ends of each entry, and `S_lo`, `S_hi` are their sums over the
    row. `none` if an `exp` bound fails. -/
def softmaxRowBoundsAt (c : Rat) (lo hi : List Rat) : Option (List (Int × Int)) :=
  match lo.mapM (fun v => (expBounds (v - c)).map (·.1)),
      hi.mapM (fun v => (expBounds (v - c)).map (·.2)) with
  | some El, some Eh =>
    some ((El.zip Eh).map fun p => (softmaxLower p.1 p.2 Eh.sum, softmaxUpper p.1 p.2 El.sum))
  | _, _ => none

/-- `softmax` of interval.py on one row: shifted by the largest upper end.
    `none` for an empty row. -/
def softmaxRowBounds (lo hi : List Rat) : Option (List (Int × Int)) :=
  match hi with
  | [] => none
  | h0 :: hs => softmaxRowBoundsAt (hs.foldl max h0) lo (h0 :: hs)

end CompactCheck
