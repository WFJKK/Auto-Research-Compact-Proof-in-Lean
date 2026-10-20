#!/usr/bin/env python3
"""Write CompactCheck/SemanticsRandomTest.lean: random tests of Semantics.lean.

Each test runs one operation of Semantics.lean on small random integer
tensors and compares the result with PyTorch's (or numpy's, which has the
same semantics), entry by entry, or checks that Lean refuses what PyTorch
refuses. Softmax is tested with a stand-in exponential, x * x + 1 over the
rationals, so that its result is exact; this tests which entries it reads.

Usage, from the Lean project folder:

    python3 scripts/gen_semantics_tests.py [--seed S] [--n N]

then `lake build CompactCheck.SemanticsRandomTest`.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from pathlib import Path

import numpy as np
import torch

OUT = Path(__file__).resolve().parent.parent / "CompactCheck" / "SemanticsRandomTest.lean"

HEADER = '''import CompactCheck.Semantics

/-!
# Random tests of the operations of attention networks

Written by `scripts/gen_semantics_tests.py`: each `#guard` compares an
operation of `Semantics.lean` on random integer tensors with PyTorch's
result, or checks that Lean refuses what PyTorch refuses. Softmax uses a
stand-in exponential, `x * x + 1` over the rationals, so that results are
exact.

This file uses only core Lean.
-/

namespace CompactCheck.SemanticsRandomTest

open CompactCheck

/-- A stand-in for the exponential, to test softmax exactly. -/
local instance : ExpDiv Rat := ⟨fun q => q * q + 1, (· / ·)⟩

'''


def lean_list(xs) -> str:
    return "[" + ", ".join(str(int(x)) for x in xs) + "]"


def lean_int(v: int) -> str:
    return f"({v})" if v < 0 else str(v)


def lean_rat(v: Fraction) -> str:
    if v.denominator == 1:
        return f"({v.numerator} : Rat)"
    return f"({v.numerator} / {v.denominator} : Rat)"


def tensor(a: np.ndarray, ty: str = "Int") -> str:
    a = np.asarray(a)
    if ty == "Int":
        data = ", ".join(lean_int(int(v)) for v in a.reshape(-1))
    else:
        data = ", ".join(lean_rat(Fraction(v)) for v in a.reshape(-1))
    return f"(⟨{lean_list(a.shape)}, #[{data}]⟩ : Tensor {ty})"


def expect(call: str, result, ty: str = "Int") -> str:
    if result is None:
        return f"#guard {call} == none\n"
    return f"#guard {call} == some {tensor(result, ty)}\n"


def rand_shape(rng, rank: int, lo: int = 1, hi: int = 3) -> list[int]:
    return [int(rng.integers(lo, hi + 1)) for _ in range(rank)]


def rand_tensor(rng, shape) -> np.ndarray:
    return rng.integers(-5, 6, size=shape).astype(np.int64)


def gen_broadcast(rng) -> str:
    sa = rand_shape(rng, int(rng.integers(0, 4)))
    sb = list(sa[len(sa) - int(rng.integers(0, len(sa) + 1)):])
    sb = [1 if rng.random() < 0.3 else d for d in sb]
    if rng.random() < 0.3:
        sb = rand_shape(rng, int(rng.integers(0, 2))) + sb
    if rng.random() < 0.5:
        sa, sb = sb, sa
    a, b = rand_tensor(rng, sa), rand_tensor(rng, sb)
    fn = ["add", "sub", "mul"][int(rng.integers(0, 3))]
    try:
        r = {"add": np.add, "sub": np.subtract, "mul": np.multiply}[fn](a, b)
    except ValueError:
        r = None
    return expect(f"broadcastOp (BinOp.apply .{fn}) {tensor(a)} {tensor(b)}", r)


def gen_matmul(rng) -> str:
    ra, rb = int(rng.integers(1, 4)), int(rng.integers(1, 4))
    m, k, n = (int(rng.integers(1, 4)) for _ in range(3))
    k2 = k if rng.random() < 0.85 else k + 1
    batch = rand_shape(rng, int(rng.integers(0, 2)))
    sa = (batch[len(batch) - max(0, ra - 2):] if ra > 2 else []) + ([m, k] if ra >= 2 else [k])
    sb = ([1 if rng.random() < 0.3 else d for d in batch] if rb > 2 else []) + ([k2, n] if rb >= 2 else [k2])
    a, b = rand_tensor(rng, sa), rand_tensor(rng, sb)
    try:
        r = np.matmul(a, b)
    except ValueError:
        r = None
    return expect(f"matmulOp {tensor(a)} {tensor(b)}", r)


def gen_index(rng) -> str:
    shape = rand_shape(rng, int(rng.integers(1, 4)), 1, 4)
    t = rand_tensor(rng, shape)
    items, lean, bad = [], [], False
    for d in shape[: int(rng.integers(0, len(shape) + 1))]:
        c = rng.random()
        if c < 0.3:
            items.append(slice(None))
            lean.append(".all")
        elif c < 0.65:
            i = int(rng.integers(0, d + (1 if rng.random() < 0.1 else 0)))
            bad |= i >= d
            items.append(i)
            lean.append(f"(.one {i})")
        else:
            a = int(rng.integers(0, d + 1))
            b = int(rng.integers(a, d + 1))
            items.append(slice(a, b))
            lean.append(f"(.range {a} {b})")
    r = None if bad else t[tuple(items)]
    return expect(f"indexOp {tensor(t)} [{', '.join(lean)}]", r)


def gen_transpose(rng) -> str:
    rank = int(rng.integers(0, 4))
    t = rand_tensor(rng, rand_shape(rng, rank))
    r = torch.from_numpy(t).T.numpy() if rank <= 2 else None
    return expect(f"transposeOp {tensor(t)}", r)


def gen_unsqueeze(rng) -> str:
    rank = int(rng.integers(0, 4))
    t = rand_tensor(rng, rand_shape(rng, rank))
    dim = int(rng.integers(-rank - 2, rank + 2))
    try:
        r = torch.from_numpy(t).unsqueeze(dim).numpy()
    except IndexError:
        r = None
    return expect(f"unsqueezeOp {tensor(t)} ({dim})", r)


def gen_expand(rng) -> str:
    rank = int(rng.integers(0, 4))
    shape = [1 if rng.random() < 0.5 else d for d in rand_shape(rng, rank)]
    t = rand_tensor(rng, shape)
    target = rand_shape(rng, int(rng.integers(0, 3)))
    for d in shape:
        c = rng.random()
        target.append(-1 if c < 0.3 else int(rng.integers(1, 4)) if d == 1 else d)
    if rng.random() < 0.1 and target:
        target[int(rng.integers(0, len(target)))] = -1
    if rng.random() < 0.1 and target:
        target[int(rng.integers(0, len(target)))] += 1
    try:
        r = torch.from_numpy(t).expand(*target).numpy() if target else torch.from_numpy(t).expand([]).numpy()
    except RuntimeError:
        r = None
    return expect(f"expandOp {tensor(t)} [{', '.join(lean_int(s) for s in target)}]", r)


def gen_cat(rng, stack: bool) -> str:
    rank = int(rng.integers(0 if stack else 1, 4))
    base = rand_shape(rng, rank)
    k = int(rng.integers(1, 4))
    dim = int(rng.integers(-rank - 1, rank + 1)) if stack else int(rng.integers(-rank - 1, rank + 1))
    parts = []
    for _ in range(k):
        s = list(base)
        if not stack and rank and rng.random() < 0.8:
            d = dim % rank if -rank <= dim < rank else 0
            s[d] = int(rng.integers(1, 4))
        if rng.random() < 0.1 and rank:
            s[int(rng.integers(0, rank))] += 1
        parts.append(rand_tensor(rng, s))
    try:
        ts = [torch.from_numpy(p) for p in parts]
        r = (torch.stack(ts, dim) if stack else torch.cat(ts, dim)).numpy()
    except (RuntimeError, IndexError):
        r = None
    name = "stackOp" if stack else "catOp"
    return expect(f"{name} [{', '.join(tensor(p) for p in parts)}] ({dim})", r)


def gen_softmax(rng) -> str:
    rank = int(rng.integers(0, 4))
    t = rand_tensor(rng, rand_shape(rng, rank))
    dim = int(rng.integers(-rank - 1, rank + 1))
    if not -rank <= dim < max(rank, 1) or rank == 0:
        r = None
        if rank == 0 and dim in (0, -1):
            r = None  # normDim of a scalar fails: softmax needs a dimension
    else:
        f = np.vectorize(lambda v: Fraction(int(v)) ** 2 + 1, otypes=[object])(t)
        r = f / f.sum(axis=dim, keepdims=True)
    return expect(f"softmaxOp {tensor(t, 'Rat')} ({dim})", r, "Rat")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=0)
    ap.add_argument("--n", type=int, default=60, help="tests per operation")
    args = ap.parse_args()
    rng = np.random.default_rng(args.seed)
    gens = [("entrywise arithmetic with broadcasting", gen_broadcast), ("torch.matmul", gen_matmul),
            ("indexing", gen_index), ("transpose", gen_transpose), ("unsqueeze", gen_unsqueeze),
            ("expand", gen_expand), ("torch.cat", lambda r: gen_cat(r, False)),
            ("torch.stack", lambda r: gen_cat(r, True)), ("softmax", gen_softmax)]
    out = [HEADER]
    counts = {}
    for title, gen in gens:
        out.append(f"/-! ## {title} -/\n\n")
        lines = [gen(rng) for _ in range(args.n)]
        counts[title] = (len(lines), sum("== none" in ln for ln in lines))
        out.extend(lines)
        out.append("\n")
    out.append("end CompactCheck.SemanticsRandomTest\n")
    OUT.write_text("".join(out))
    for title, (n, refused) in counts.items():
        print(f"{title}: {n} tests, {refused} refused")


if __name__ == "__main__":
    main()
