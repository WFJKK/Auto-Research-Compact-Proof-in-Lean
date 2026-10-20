#!/usr/bin/env python3
"""Compare Lean's token_interval bounds with the Python checker's, bound for bound.

For every development network of a model folder: boxes of inputs with a
constant label (as an interval or token_interval leaf would hold them: one
position varying, several varying, single inputs, and the leaves of trees
grouped by the label), the lowest margin bound of a token_interval leaf in
Lean (`compactcheck tokens`) and in Python
(`GeneralProgram.run_token_interval`). The two must be the same rational
number, or both must reject.

Usage, from the Lean project folder, after `lake build compactcheck`:

    python3 scripts/compare_tokens.py <repo> <model folder> [--boxes N] [--only ID] [--log FILE]

With `--log`, each network's result is appended to FILE as one JSON line,
and networks already in FILE are skipped. Exits with status 1 if anything
disagrees.
"""

from __future__ import annotations

import argparse
import json
import random
import subprocess
import sys
import tempfile
import time
from fractions import Fraction
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import export_network  # noqa: E402
from compare_general import by_label_tree, window  # noqa: E402
from compare_with_python import random_tree  # noqa: E402

LEAN = HERE.parent / ".lake" / "build" / "bin" / "compactcheck"


def tree_boxes(tree: dict, space: list[int]) -> list[list[tuple[int, int]]]:
    """The boxes of a tree's interval leaves."""
    out = []

    def walk(t, box):
        if "leaf" in t:
            if t["leaf"] == "interval":
                out.append(list(box))
            return
        p = t["split"]["position"]
        lo, hi = box[p]
        bounds = [lo] + t["split"]["cuts"] + [hi + 1]
        for (a, b), c in zip(zip(bounds, bounds[1:]), t["children"]):
            nb = list(box)
            nb[p] = (a, b - 1)
            walk(c, nb)

    walk(tree, [(0, v - 1) for v in space])
    return out


def random_boxes(space: list[int], rng: random.Random, n: int, varying: int) -> list[list[tuple[int, int]]]:
    """Boxes with `varying` positions holding ranges of random length."""
    out = []
    for _ in range(n):
        x = [rng.randrange(v) for v in space]
        box = [(t, t) for t in x]
        for p in rng.sample(range(len(space)), min(varying, len(space))):
            length = rng.choice([2, 3, 4, 8, 16, space[p]])
            a = rng.randint(0, max(0, space[p] - length))
            box[p] = (a, min(space[p] - 1, a + length - 1))
        out.append(box)
    return out


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo", type=Path)
    ap.add_argument("model")
    ap.add_argument("--boxes", type=int, default=150, help="random boxes of each kind per network")
    ap.add_argument("--only", default="")
    ap.add_argument("--log", type=Path, default=None)
    args = ap.parse_args()
    repo = args.repo.resolve()
    sys.path.insert(0, str(repo))
    from core.check.cost import Counter
    from core.check.evaluate import CheckError
    from core.check.trace import UnsupportedOp, build_any, make_program
    from core.model_folder import load_model_folder
    from core.zoo import load_weights, networks

    done = {}
    if args.log and args.log.exists():
        for line in args.log.read_text().splitlines():
            if line.strip():
                row = json.loads(line)
                done[row["network"]] = row
    folder = load_model_folder(repo / args.model)
    failures = 0
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        for entry in networks(folder, split="dev"):
            nid = entry["id"]
            if args.only not in nid:
                continue
            if nid in done:
                print(f"{nid}: in the log already, {done[nid]['status']}", flush=True)
                failures += done[nid]["status"] != "ok"
                continue
            setting = entry["setting"]
            space = folder.input_space(setting)
            sizes = folder.sizes(setting)
            net = tmp / f"{nid}.json"
            net.write_text(json.dumps(export_network.export(repo, args.model, nid)))
            rng = random.Random(sum(map(ord, nid)) + 7)
            # the boxes
            boxes = []
            for max_box in (4, 64, 1024):
                win = window(space, rng, 20000)
                label_of = lambda r: folder.task.constant_label(r, sizes)  # noqa: E731
                boxes += tree_boxes(by_label_tree(space, label_of, rng, max_box, win), space)
            for _ in range(2):
                boxes += tree_boxes(random_tree(space, rng, max_depth=rng.choice([2, 3, 4])), space)
            for varying in (0, 1, 2, len(space)):
                boxes += random_boxes(space, rng, args.boxes, varying)
            leaves = []
            for b in boxes:
                lab = folder.task.constant_label(b, sizes)
                if lab is not None:
                    leaves.append({"ranges": [list(r) for r in b], "label": int(lab)})
            if len(leaves) > 3000:
                leaves = rng.sample(leaves, 3000)
            # Python
            weights = load_weights(folder, nid)
            t0 = time.time()
            prog = make_program(build_any(folder.build(setting)), weights, Counter(), space)
            py = []
            for leaf in leaves:
                try:
                    good, worst, j = prog.run_token_interval([tuple(r) for r in leaf["ranges"]], leaf["label"], Counter())
                    py.append(Fraction(worst))
                except (CheckError, UnsupportedOp, ArithmeticError, ValueError, TypeError) as exc:
                    py.append(("error", f"{type(exc).__name__}: {str(exc)[:120]}"))
            t_py = time.time() - t0
            # Lean
            (tmp / "leaves.json").write_text(json.dumps(leaves))
            t0 = time.time()
            out = subprocess.run([str(LEAN), "tokens", str(net), str(tmp / "leaves.json")],
                                 capture_output=True, text=True, check=True).stdout
            ln = json.loads(out.strip().splitlines()[-1])
            t_ln = time.time() - t0
            problems = []
            certified = 0
            for leaf, p, l in zip(leaves, py, ln):
                if isinstance(p, tuple):
                    if l != "error":
                        problems.append(f"{leaf}: Python rejects ({p[1]}), Lean {l}")
                    continue
                if l == "error":
                    problems.append(f"{leaf}: Python {p}, Lean rejects")
                    continue
                lb = Fraction(1) if l is None else Fraction(int(l[0])) * Fraction(2) ** int(l[1])
                if lb != p:
                    problems.append(f"{leaf}: Python {float(p):.6g}, Lean {float(lb):.6g}")
                certified += p > 0
            kinds = {"one varying": 0, "several": 0, "single": 0}
            for leaf in leaves:
                v = sum(lo < hi for lo, hi in leaf["ranges"])
                kinds["single" if v == 0 else "one varying" if v == 1 else "several"] += 1
            errors = sum(isinstance(p, tuple) for p in py)
            status = "ok" if not problems else f"DIFFERS on {len(problems)}: " + "; ".join(problems[:3])
            print(f"{nid}: {len(leaves)} boxes ({kinds}), {certified} certified, {errors} rejected by both, "
                  f"Lean {t_ln:.0f} s, Python {t_py:.0f} s, {status}", flush=True)
            failures += bool(problems)
            if args.log:
                with args.log.open("a") as f:
                    f.write(json.dumps({"network": nid, "status": "ok" if not problems else "differs",
                                        "problems": problems[:20], "boxes": len(leaves), "kinds": kinds,
                                        "certified": int(certified), "errors": errors,
                                        "lean_s": round(t_ln, 1), "python_s": round(t_py, 1)}) + "\n")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
