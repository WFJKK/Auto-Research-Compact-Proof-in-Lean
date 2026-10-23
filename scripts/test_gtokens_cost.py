"""The token_interval rule for general networks charges what cost-v3 charges, leaf by leaf and over a proof.

    python3 -m pytest scripts/test_gtokens_cost.py -v

`gtokenRun` (TokensCost.lean) runs a list of token_interval leaves on an attention network and bills them;
the Python checker (core/check/tokens.py through `GeneralProgram.run_token_interval`, one program for the
whole list, as for the leaves of one proof) is the reference. For every development network of the
pipeline's attention models, on a sequence of boxes that mixes single inputs, one varying position, several
varying positions, a repeated box and overlapping ranges (so that the rows kept for the proof are reused
fully and in part), `compactcheck gtokens` must give per box Python's verdict, its charge to token_interval
and what the box added to tables, and then the totals.

Needs `lake build compactcheck`, the pipeline repository (next to this one, or COMPACT_PROOF_REPO) with its
trained zoo, and its Python environment. Networks are exported into a temporary folder.
"""

from __future__ import annotations

import json
import os
import random
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
CHECKER = PROJECT / ".lake" / "build" / "bin" / "compactcheck"
REPO = Path(os.environ.get("COMPACT_PROOF_REPO", PROJECT.parent / "auto-research-compact-proof"))
MODELS = ["models/attn-max2", "models/attn-min2", "models/attn-max4", "models/attn-min4",
          "tests/attn_max2_tiny", "tests/attn_min2_tiny", "tests/attn_max4_tiny", "tests/attn_min4_tiny"]
MAX_PARAMS = 20000  # the largest networks are slow in the Python checker and add nothing

pytestmark = pytest.mark.skipif(not (REPO / "core").is_dir() or not CHECKER.exists(),
                                reason="needs the pipeline repository next to this one and `lake build compactcheck`")


def cases() -> list[tuple[str, str]]:
    if not (REPO / "core").is_dir():
        return []
    sys.path.insert(0, str(REPO))
    from core.model_folder import load_model_folder
    from core.zoo import networks
    out = []
    for model in MODELS:
        if not (REPO / model / "zoo" / "manifest.json").exists():
            continue
        folder = load_model_folder(REPO / model)
        out += [(model, e["id"]) for e in networks(folder)]
    return out


def token_boxes(space: list[int], kind: str, rng: random.Random) -> list[list[list[int]]]:
    """A proof's worth of token_interval leaves: the label is constant on most of them by construction
    (for the extreme token m, one position holds m and the others lie on its side of m)."""
    P, V = len(space), space[0]

    def side(m: int) -> tuple[int, int]:
        return (0, m) if kind == "max" else (m, V - 1)

    def box_with(m: int, p: int, varying: set[int]) -> list[list[int]]:
        lo, hi = side(m)
        box = []
        for q in range(P):
            if q == p:
                box.append([m, m])
            elif q in varying:
                a = rng.randint(lo, hi)
                b = rng.randint(a, hi)
                box.append([a, b] if rng.random() < 0.5 else [lo, hi])
            else:
                t = rng.randint(lo, hi)
                box.append([t, t])
        return box

    out = []
    for _ in range(2):  # single inputs
        out.append(box_with(rng.randrange(V), rng.randrange(P), set()))
    for _ in range(3):  # one varying position
        p = rng.randrange(P)
        q = rng.choice([x for x in range(P) if x != p])
        out.append(box_with(rng.randrange(V), p, {q}))
    for _ in range(3):  # every other position varying
        p = rng.randrange(P)
        out.append(box_with(rng.randrange(V), p, set(range(P)) - {p}))
    out.append(list(out[3]))  # a box again: its pure rows are all kept

    def widen(r: list[int]) -> list[int]:  # one more token on the label's side of a varying range
        lo, hi = r
        if lo == hi:
            return r
        return [max(0, lo - 1), hi] if kind == "max" else [lo, min(V - 1, hi + 1)]

    out += [[widen(r) for r in out[i]] for i in (2, 3, 4, 5, 6, 7)]  # overlapping ranges: rows kept in part
    out.append([[0, V - 1]] * P)  # the whole space: no constant label
    return out


@pytest.mark.parametrize("model,network", cases())
def test_gtokens_charges_what_the_python_checker_charges(model, network, tmp_path):
    import numpy as np
    from core.check.cost import Counter
    from core.check.evaluate import CheckError
    from core.check.trace import UnsupportedOp, build_any, make_program
    from core.model_folder import load_model_folder
    from core.zoo import load_weights, network_entry

    folder = load_model_folder(REPO / model)
    setting = network_entry(folder, network)["setting"]
    sizes, space = folder.sizes(setting), folder.input_space(setting)
    weights = load_weights(folder, network)
    if sum(int(np.asarray(w).size) for w in weights.values()) > MAX_PARAMS:
        pytest.skip("large network")
    graph = build_any(folder.build(setting))
    if not getattr(graph, "general", False):
        pytest.skip("a linear network")
    prog = make_program(graph, weights, Counter(), space)  # one program: one proof's memo
    kind = "min" if "min" in folder.name else "max"
    boxes = token_boxes(space, kind, random.Random(network + "/tokens"))
    expected = []
    for box in boxes:
        label = folder.task.constant_label([tuple(r) for r in box], sizes)
        if label is None:
            expected.append((False, 0, 0))
            continue
        c = Counter()
        try:
            ok, _, _ = prog.run_token_interval([tuple(r) for r in box], int(label), c)
        except (CheckError, UnsupportedOp):
            expected.append("rejected")
            break
        leaf, tables = c.by_rule.get("token_interval", 0), c.by_rule.get("tables", 0)
        assert c.total == leaf + tables, f"the Python leaf charged another category: {c.as_dict()}"
        expected.append((bool(ok), leaf, tables))

    net_json, boxes_json = tmp_path / "net.json", tmp_path / "boxes.json"
    r = subprocess.run([sys.executable, "-B", str(HERE / "export_network.py"), str(REPO), model, network, str(net_json)],
                       capture_output=True, text=True, timeout=1800)
    assert r.returncode == 0, r.stderr[-1000:]
    boxes_json.write_text(json.dumps(boxes))
    r = subprocess.run([str(CHECKER), "gtokens", str(net_json), str(boxes_json)], capture_output=True, text=True,
                       timeout=3600)
    assert r.returncode == 0, r.stderr[-1000:]
    rows = [json.loads(line) for line in r.stdout.splitlines() if line.startswith("{")]
    per_box = [row for row in rows if "box" in row]
    assert len(per_box) == len(expected), (per_box, expected)
    for box, row, exp in zip(boxes, per_box, expected):
        assert row["box"] == box
        if exp == "rejected":
            assert row.get("status") == "rejected", (box, row)
            return
        assert (row.get("verdict"), row.get("token_interval"), row.get("tables")) == exp, (box, row, exp)
    total = rows[-1]
    assert total["verdicts"] == [e[0] for e in expected]
    assert total["token_interval"] == sum(e[1] for e in expected)
    assert total["tables"] == sum(e[2] for e in expected)
    # the memo was used: the repeated box added nothing to tables
    assert expected[8][2] == 0 or expected[8] == (False, 0, 0)
