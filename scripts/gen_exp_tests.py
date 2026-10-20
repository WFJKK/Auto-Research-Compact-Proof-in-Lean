#!/usr/bin/env python3
"""Write CompactCheck/ExpTest.lean: Lean's exp and softmax bounds against Python's.

Each test computes `exp_bounds` (core/check/interval.py) on a random dyadic
number, or `softmax` on a random row of intervals, in Python, and checks that
`expBounds` and `softmaxRowBounds` of Exp.lean give the same integers, or
fail where Python raises.

Usage, from the Lean project folder:

    python3 scripts/gen_exp_tests.py <repo> [--seed S] [--n N]

then `lake build CompactCheck.ExpTest`.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

import numpy as np

OUT = Path(__file__).resolve().parent.parent / "CompactCheck" / "ExpTest.lean"

HEADER = '''import CompactCheck.Exp

/-!
# Tests: the exp and softmax bounds are Python's

Written by `scripts/gen_exp_tests.py`: each `#guard` compares `expBounds` or
`softmaxRowBounds` with `exp_bounds` or `softmax` of core/check/interval.py
on random dyadic numbers.

This file uses only core Lean.
-/

namespace CompactCheck.ExpTest

open CompactCheck

/-- `X * 2^e`. -/
def q (X : Int) (e : Int) : Rat :=
  if e ≥ 0 then ((X * 2 ^ e.toNat : Int) : Rat) else (X : Rat) / ((2 ^ (-e).toNat : Nat) : Rat)

'''


def lean_int(v: int) -> str:
    return f"({v})" if v < 0 else str(v)


def rand_dyadic(rng) -> tuple[int, int]:
    kind = rng.random()
    if kind < 0.05:
        return 0, int(rng.integers(-10, 10))
    bits = int(rng.integers(1, 60))
    X = int(rng.integers(1, 2**bits)) if bits < 63 else int(rng.integers(1, 2**62))
    if rng.random() < 0.5:
        X = -X
    if kind < 0.7:  # moderate values
        e = int(rng.integers(-bits - 12, -bits + 6))
    elif kind < 0.85:  # near the limit 2^12
        e = 12 - bits + int(rng.integers(-2, 2))
    else:  # anything
        e = int(rng.integers(-80, 20))
    return X, e


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo", type=Path)
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--n", type=int, default=300)
    args = ap.parse_args()
    sys.path.insert(0, str(args.repo.resolve()))
    from core.check.interval import IT, IntervalError, exp_bounds, softmax

    rng = np.random.default_rng(args.seed)
    out = [HEADER, "/-! ## exp -/\n\n"]
    n_fail = 0
    for _ in range(args.n):
        X, e = rand_dyadic(rng)
        try:
            L, H = exp_bounds(X, e)
            out.append(f"#guard expBounds (q {lean_int(X)} {lean_int(e)}) == some ({lean_int(L)}, {lean_int(H)})\n")
        except IntervalError:
            n_fail += 1
            out.append(f"#guard expBounds (q {lean_int(X)} {lean_int(e)}) == none\n")
    out.append("\n/-! ## softmax, one row -/\n\n")
    for _ in range(args.n // 3):
        n = int(rng.integers(1, 6))
        e = int(rng.integers(-30, 0))
        lo = [int(v) for v in rng.integers(-(2**34), 2**34, size=n)]
        hi = [v + int(rng.integers(0, 2**30)) if rng.random() < 0.7 else v for v in lo]
        s = softmax(IT(np.array(lo, dtype=object), np.array(hi, dtype=object), e), 0)
        assert s.exp == -120
        want = ", ".join(f"({lean_int(int(a))}, {lean_int(int(b))})" for a, b in zip(s.lo, s.hi))
        los = ", ".join(f"q {lean_int(v)} {lean_int(e)}" for v in lo)
        his = ", ".join(f"q {lean_int(v)} {lean_int(e)}" for v in hi)
        out.append(f"#guard softmaxRowBounds [{los}] [{his}] == some [{want}]\n")
    out.append("\nend CompactCheck.ExpTest\n")
    OUT.write_text("".join(out))
    print(f"{args.n} exp tests ({n_fail} refused by Python), {args.n // 3} softmax rows")


if __name__ == "__main__":
    main()
