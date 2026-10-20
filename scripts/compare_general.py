#!/usr/bin/env python3
"""Compare the Lean checker with the Python checker on a general network model.

For the attention models and the xorformer (networks the Python checker
checks with core/check/general.py), on every development network:

1. Single leaves: on a sample of inputs (every input if there are at most
   --singles), Lean's single-input test must accept exactly the inputs the
   Python checker accepts.
2. Interval leaves: random split trees with interval, single and skip
   leaves, and trees of interval leaves grouped by the label (on a random
   sub-box of the space if it holds more than --window inputs); Lean and
   Python must give the same status and count, and the same outcome leaf by
   leaf.
3. token_interval leaves: the same trees by label with token_interval
   leaves, and random trees with some interval leaves made token_interval
   leaves; the same tests.
4. Rules Python refuses on these networks (symmetry, contract, approximate,
   an approximation name on a leaf, the input used other than by a lookup):
   both checkers must reject.

Usage, from the Lean project folder, after `lake build compactcheck`:

    python3 scripts/compare_general.py <repo> <model folder> [--singles N] [--random N] [--only ID]
        [--log FILE]

With `--log`, each network's result is appended to FILE as one JSON line,
and networks already in FILE are skipped, so an interrupted run resumes.

Exits with status 1 if anything disagrees.
"""

from __future__ import annotations

import argparse
import itertools
import json
import random
import subprocess
import sys
import tempfile
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import export_network  # noqa: E402
from compare_with_python import _split, random_tree  # noqa: E402

LEAN = HERE.parent / ".lake" / "build" / "bin" / "compactcheck"


def lean(*args: str):
    out = subprocess.run([str(LEAN), *args], capture_output=True, text=True, check=True).stdout
    return json.loads(out.strip().splitlines()[-1])


def singles_tree(space: list[int], inputs: set[tuple[int, ...]]) -> dict:
    """A tree with a single leaf on each of `inputs` and skip leaves elsewhere."""

    def build(prefix: tuple[int, ...]) -> dict:
        k = len(prefix)
        if k == len(space):
            return {"leaf": "single" if prefix in inputs else "skip"}
        if not any(x[:k] == prefix for x in inputs):
            return {"leaf": "skip"}
        return _split(k, list(range(1, space[k])), [build(prefix + (t,)) for t in range(space[k])])

    return build(())


def window(space: list[int], rng: random.Random, limit: int) -> list[tuple[int, int]]:
    """A random sub-box with at most `limit` inputs, or the whole space if it is that small."""
    if int(np.prod(space)) <= limit:
        return [(0, v - 1) for v in space]
    w = max(1, int(limit ** (1 / len(space))))
    while w > 1 and w ** len(space) > limit:
        w -= 1
    out = []
    for v in space:
        width = min(w, v)
        a = rng.randint(0, v - width)
        out.append((a, a + width - 1))
    return out


def in_window(space: list[int], win: list[tuple[int, int]], inner: dict) -> dict:
    """A tree with `inner` on the box `win` and skip leaves on the rest of the space."""

    def build(k: int) -> dict:
        if k == len(space):
            return inner
        a, b = win[k]
        cuts = [c for c in (a, b + 1) if 0 < c <= space[k] - 1]
        if not cuts:
            return build(k + 1)
        bounds = [0] + cuts + [space[k]]
        return _split(k, cuts, [build(k + 1) if (lo, hi - 1) == (a, b) else {"leaf": "skip"}
                                for lo, hi in zip(bounds, bounds[1:])])

    return build(0)


def by_label_tree(space: list[int], label_of, rng: random.Random, max_box: int,
                  start: list[tuple[int, int]] | None = None, rule: str = "interval") -> dict:
    """Leaves of the rule `rule` on boxes with a constant label where the
    split finds one quickly, single leaves on the inputs left over (random
    splits); on the box `start` if given, which the caller then places in
    the space."""

    def build(ranges: list[tuple[int, int]], depth: int) -> dict:
        size = int(np.prod([hi - lo + 1 for lo, hi in ranges]))
        if all(lo == hi for lo, hi in ranges):
            return {"leaf": "single"}
        if size <= max_box and label_of(ranges) is not None:
            return {"leaf": rule}
        k = max(range(len(ranges)), key=lambda q: ranges[q][1] - ranges[q][0] + rng.random())
        lo, hi = ranges[k]
        cut = rng.randint(lo + 1, hi)
        r1, r2 = list(ranges), list(ranges)
        r1[k] = (lo, cut - 1)
        r2[k] = (cut, hi)
        return _split(k, [cut], [build(r1, depth + 1), build(r2, depth + 1)])

    return build(start or [(0, v - 1) for v in space], 0)


def with_token_leaves(tree: dict, rng: random.Random) -> dict:
    """The tree with about half of its interval leaves made token_interval leaves."""
    if "leaf" in tree:
        if tree["leaf"] == "interval" and rng.random() < 0.5:
            return {**tree, "leaf": "token_interval"}
        return tree
    return {**tree, "children": [with_token_leaves(c, rng) for c in tree["children"]]}


def leaf_outcomes_match(py: dict, ln: list) -> list[str]:
    """Leaves whose outcome differs (Python's outcomes keyed by box and rule)."""
    pyo = {(tuple(map(tuple, o["ranges"])), o["rule"]): o["accepted"] for o in py.get("outcomes") or []}
    bad = []
    for leaf in ln:
        key = (tuple(map(tuple, leaf["ranges"])), leaf["rule"])
        if leaf["rule"] == "skip":
            continue
        if key not in pyo or pyo[key] != leaf["accepted"]:
            bad.append(f"{key}: Python {pyo.get(key)}, Lean {leaf['accepted']}")
    return bad


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo", type=Path)
    ap.add_argument("model")
    ap.add_argument("--singles", type=int, default=600, help="inputs for the single-leaf comparison")
    ap.add_argument("--random", type=int, default=4, help="random split trees per network")
    ap.add_argument("--only", default="")
    ap.add_argument("--window", type=int, default=20000,
                    help="on larger spaces, the trees by label cover a random sub-box of this many inputs")
    ap.add_argument("--log", type=Path, default=None, help="append results here; skip networks already in it")
    args = ap.parse_args()
    done = {}
    if args.log and args.log.exists():
        for line in args.log.read_text().splitlines():
            if line.strip():
                row = json.loads(line)
                done[row["network"]] = row
    repo = args.repo.resolve()
    sys.path.insert(0, str(repo))
    from core.check.checker import check_proof
    from core.model_folder import load_model_folder
    from core.zoo import networks

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
            exported = export_network.export(repo, args.model, nid)
            assert exported["general"], f"{nid} is not a general network"
            net = tmp / f"{nid}.json"
            net.write_text(json.dumps(exported))
            rng = random.Random(sum(map(ord, nid)))
            problems = []
            times = {"Lean": 0.0, "Python": 0.0}

            def both(name: str, proof: dict, expect: str | None = None, per_leaf: bool = True) -> dict:
                body = {"schema": "split-tree-v1", "network": nid, **proof}
                t0 = time.time()
                py = check_proof(body, folder, nid, detail=per_leaf)
                times["Python"] += time.time() - t0
                (tmp / "proof.json").write_text(json.dumps(body))
                t0 = time.time()
                ln = lean(str(net), str(tmp / "proof.json"))
                times["Lean"] += time.time() - t0
                if py["status"] != ln.get("status", "ok") or py["certified"] != ln.get("certified") or (
                        expect and py["status"] != expect):
                    problems.append(f"{name}: Python {py['status']} {py['certified']} {py.get('reason')}, Lean {ln}")
                elif per_leaf and py["status"] == "ok":
                    leaves = lean("leaves", str(net), str(tmp / "proof.json"))
                    bad = leaf_outcomes_match(py, leaves)
                    if bad:
                        problems.append(f"{name}: {len(bad)} leaves differ, e.g. {bad[:3]}")
                return py

            # 1. single leaves
            total = int(np.prod(space))
            if total <= args.singles:
                inputs = set(itertools.product(*[range(v) for v in space]))
            else:
                inputs = {tuple(int(t) for t in row) for row in
                          np.random.default_rng(0).integers(0, space, size=(args.singles, len(space)))}
            py = both("single leaves", {"tree": singles_tree(space, inputs)})
            n_single = py["certified"]

            # 2. interval leaves
            n_trees, certified = 0, []
            label_of = lambda ranges: folder.task.constant_label(ranges, sizes)  # noqa: E731
            for max_box in (4, 64, 1024):
                win = window(space, rng, args.window)
                tree = in_window(space, win, by_label_tree(space, label_of, rng, max_box, win))
                py = both(f"by label, boxes up to {max_box}", {"tree": tree})
                certified.append(py["certified"])
                n_trees += 1
            for i in range(args.random):
                tree = random_tree(space, rng, max_depth=rng.choice([2, 3, 4]))
                both(f"random tree {i}", {"tree": tree})
                n_trees += 1

            # 3. token_interval leaves
            n_token, token_certified = 0, []
            for max_box in (4, 64, 1024):
                win = window(space, rng, args.window)
                tree = in_window(space, win, by_label_tree(space, label_of, rng, max_box, win,
                                                           rule="token_interval"))
                py = both(f"token_interval by label, boxes up to {max_box}", {"tree": tree})
                token_certified.append(py["certified"])
                n_token += 1
            for i in range(args.random):
                tree = with_token_leaves(random_tree(space, rng, max_depth=rng.choice([2, 3, 4])), rng)
                both(f"random tree with token_interval leaves {i}", {"tree": tree})
                n_token += 1

            # 4. what Python refuses on these networks
            skip = {"leaf": "skip"}
            both("symmetry", {"symmetry": True, "tree": skip}, "rejected", per_leaf=False)
            both("contract", {"contract": [{"name": "M", "chain": ["a", "b"]}], "tree": skip}, "rejected",
                 per_leaf=False)
            both("approximate", {"approximate": [{"name": "P", "of": "a", "form": "dense", "values": [[0]]}],
                                 "tree": skip}, "rejected", per_leaf=False)
            both("approximation on a leaf", {"tree": {"leaf": "interval", "approx": "P"}}, "rejected", per_leaf=False)
            both("approximation on a token_interval leaf", {"tree": {"leaf": "token_interval", "approx": "P"}},
                 "rejected", per_leaf=False)

            status = "ok" if not problems else "DIFFERS: " + "; ".join(problems)
            print(f"{nid}: singles {n_single}/{len(inputs)}, {n_trees} interval trees (by label: {certified}), "
                  f"{n_token} token_interval trees (by label: {token_certified}), "
                  f"Lean {times['Lean']:.0f} s, Python {times['Python']:.0f} s, {status}", flush=True)
            failures += bool(problems)
            if args.log:
                with args.log.open("a") as f:
                    f.write(json.dumps({"network": nid, "status": "ok" if not problems else "differs",
                                        "problems": problems, "singles": [n_single, len(inputs)],
                                        "trees": n_trees, "by_label": certified,
                                        "token_trees": n_token, "token_by_label": token_certified,
                                        "lean_s": round(times["Lean"], 1),
                                        "python_s": round(times["Python"], 1)}) + "\n")
    sys.exit(1 if failures else 0)


if __name__ == "__main__":
    main()
