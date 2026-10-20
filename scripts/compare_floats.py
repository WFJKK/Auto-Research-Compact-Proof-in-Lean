#!/usr/bin/env python3
"""Compare the network Lean reads with PyTorch's network, in floats.

For every development network of a model folder: export it, then compute the
logits of many inputs twice, with Lean's definitions (`compactcheck floats`,
which runs `semGraph` of Semantics.lean in float64) and with PyTorch in
float64 on the zoo's weights. Both compute the same real numbers, so they
must agree up to float64 rounding. This checks the exporter and the meaning
Lean gives every operation, on the model's own graph. It works for any
network, with or without exp and softmax.

Usage, from the Lean project folder, after `lake build compactcheck`:

    python3 scripts/compare_floats.py <repo> <model folder> [--inputs N] [--seed S]

Every input is used when there are at most N of them (default 5000);
otherwise N random inputs. Exits with status 1 if any logit differs by more
than 1e-9 times (1 + the largest logit), or a shape differs.
"""

from __future__ import annotations

import argparse
import itertools
import json
import struct
import subprocess
import sys
import tempfile
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import export_network  # noqa: E402

LEAN = HERE.parent / ".lake" / "build" / "bin" / "compactcheck"
TOLERANCE = 1e-9


def lean_floats(net: Path, inputs: list[list[int]], tmp: Path) -> list:
    path = tmp / "inputs.json"
    path.write_text(json.dumps(inputs))
    out = subprocess.run([str(LEAN), "floats", str(net), str(path)], capture_output=True, text=True, check=True)
    rows = json.loads(out.stdout.strip().splitlines()[-1])
    res = []
    for r in rows:
        if r is None:
            res.append(None)
        else:
            vals = [struct.unpack("<d", struct.pack("<Q", b))[0] for b in r["bits"]]
            res.append((r["shape"], np.array(vals)))
    return res


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo", type=Path)
    ap.add_argument("model", help="the model folder, relative to the repository, e.g. models/attn-max2")
    ap.add_argument("--inputs", type=int, default=5000)
    ap.add_argument("--seed", type=int, default=0)
    args = ap.parse_args()
    repo = args.repo.resolve()
    sys.path.insert(0, str(repo))
    import torch

    from core.model_folder import load_model_folder
    from core.zoo import load_module, networks

    folder = load_model_folder(repo / args.model)
    rng = np.random.default_rng(args.seed)
    failed = False
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        for entry in networks(folder, split="dev"):
            nid = entry["id"]
            data = export_network.export(repo, args.model, nid)
            net = tmp / f"{nid}.json"
            net.write_text(json.dumps(data))
            space = folder.input_space(entry["setting"])
            total = int(np.prod(space))
            if total <= args.inputs:
                inputs = [list(x) for x in itertools.product(*[range(v) for v in space])]
            else:
                inputs = rng.integers(0, space, size=(args.inputs, len(space))).tolist()
            lean = lean_floats(net, inputs, tmp)
            module = load_module(folder, nid).double()
            x = torch.nn.functional.one_hot(torch.tensor(inputs), num_classes=space[0]).to(torch.float64)
            with torch.no_grad():
                ref = module(x).numpy()
            worst, bad = 0.0, 0
            for row, want in zip(lean, ref):
                if row is None or row[0] != [1, len(want)]:
                    bad += 1
                    continue
                err = float(np.max(np.abs(row[1] - want)) / (1 + np.max(np.abs(want))))
                worst = max(worst, err)
                bad += err > TOLERANCE
            ok = bad == 0
            failed |= not ok
            print(f"{nid:36s} {len(inputs):6d} inputs, {len(data['graph']['nodes']):3d} operations, "
                  f"largest relative difference {worst:.1e}  {'ok' if ok else f'{bad} DIFFER'}", flush=True)
    sys.exit(1 if failed else 0)


if __name__ == "__main__":
    main()
