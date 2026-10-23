"""The token_interval rule's price on the token rules the zoo's attention networks never reach.

    python3 -m pytest scripts/test_gtokens_synthetic.py -v

`scripts/test_gtokens_cost.py` compares `gtokenRun` (TokensCost.lean) with the Python checker on the zoo's
attention networks, which use only some of the token rules. A checker may pass the operation a graph of its
own, so the price of every rule matters. Two small networks with random weights are built here to pass
through the others, in leaves where one position varies (values per input) and where several do (interval
tensors):

- `Rows`: rows times a vector that varies along the row, a sum over a row's dimension, a softmax of rows,
  attention weights times rows, the negation of a weighted sum, two weighted sums added, a constant added;
- `PerInput`: rows times a number, the exponential and the negation of what leaves the domain, per-input
  weights times rows, a weighted sum with per-input weights, indexing it, and a matrix product of per-input
  values.

For each, on a sequence of boxes run as one proof (one Python program, so rows are reused), the verdict, the
charge to token_interval and what each box adds to tables must equal Python's, and the test checks that the
Python evaluator went through the rules it is meant to cover.

Needs `lake build compactcheck` and the pipeline repository (next to this one, or COMPACT_PROOF_REPO) with its
Python environment; no zoo, no training.
"""

from __future__ import annotations

import json
import os
import random
import subprocess
import sys
from collections import Counter as Tally
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
CHECKER = PROJECT / ".lake" / "build" / "bin" / "compactcheck"
REPO = Path(os.environ.get("COMPACT_PROOF_REPO", PROJECT.parent / "auto-research-compact-proof"))
N, V, D = 3, 4, 3  # positions, tokens, width

pytestmark = pytest.mark.skipif(not (REPO / "core").is_dir() or not CHECKER.exists(),
                                reason="needs the pipeline repository next to this one and `lake build compactcheck`")


def networks():
    import torch as t

    def param(*shape):
        # multiples of 1/4: small dyadic numbers, so the exact arithmetic stays small
        return t.nn.Parameter(t.round(4 * t.randn(*shape, dtype=t.float64)) / 4)

    class Rows(t.nn.Module):
        def __init__(self):
            super().__init__()
            self.E, self.P, self.c, self.A, self.b, self.U = param(V, D), param(N, D), param(D), param(D, D), param(D), param(D, V)

        def forward(self, x):
            h = x @ self.E + self.P
            s = t.sum(h * self.c, dim=2)
            w = t.softmax(s, dim=1)
            y = t.sum(w.unsqueeze(2) * (h @ self.A), dim=1)
            z = -(h[:, N - 1] @ self.A) + y + self.b
            return z @ self.U

    class PerInput(t.nn.Module):
        def __init__(self):
            super().__init__()
            self.E, self.P, self.c, self.A, self.B = param(V, D), param(N, D), param(D), param(D, D), param(2, V)

        def forward(self, x):
            h = x @ self.E + self.P
            s = t.sum(h * self.c, dim=2)
            e = -t.exp(s * 0.25)
            m = t.sum(e.unsqueeze(2) * h, dim=1)
            q = (m @ self.A)[:, 0:2]
            return q @ self.B

    return {"rows": Rows, "per_input": PerInput}


# the rules each network is meant to take through the Python evaluator, at least once over its boxes
MEANT = {
    "rows": {"mul_sep", "sum_rows", "var_op:softmax", "mul_var_sep", "sum_positions", "scale_mix", "add_mixes",
             "add_mix", "matmul", "collapse"},
    "per_input": {"mul_sep", "sum_rows", "var_op:exp", "var_op:neg", "mul_var_sep", "sum_positions",
                  "var_op:getitem", "var_op:matmul", "to_var", "collapse"},
}


def boxes(rng: random.Random) -> list[list[list[int]]]:
    """Boxes of the max task, with a constant label by construction: one position holds the largest token m,
    the others lie at or below it; single inputs, one varying position, all others varying, a box again and
    widened ranges, and the whole space."""
    def box_with(m, p, varying, full=False):
        out = []
        for q in range(N):
            if q == p:
                out.append([m, m])
            elif q in varying:
                a = rng.randint(0, m)
                out.append([0, m] if full or rng.random() < 0.5 else [a, rng.randint(a, m)])
            else:
                tok = rng.randint(0, m)
                out.append([tok, tok])
        return out

    out = [box_with(rng.randrange(V), rng.randrange(N), set()) for _ in range(2)]
    for _ in range(4):
        p = rng.randrange(N)
        out.append(box_with(rng.randrange(1, V), p, {rng.choice([q for q in range(N) if q != p])}))
    for _ in range(4):  # several positions vary (m >= 1, so [0, m] holds two tokens or more)
        p = rng.randrange(N)
        out.append(box_with(rng.randrange(1, V), p, set(range(N)) - {p}, full=True))
    out.append(list(out[3]))
    out += [[[max(0, lo - 1), hi] if lo < hi else [lo, hi] for lo, hi in out[i]] for i in (2, 6)]
    out.append([[0, V - 1]] * N)
    return out


@pytest.mark.parametrize("name", ["rows", "per_input"])
@pytest.mark.parametrize("seed", [0, 1, 2])
def test_gtokens_charges_what_the_python_checker_charges_on_every_token_rule(name, seed, tmp_path, monkeypatch):
    import torch

    sys.path.insert(0, str(REPO))
    sys.path.insert(0, str(HERE))
    import export_network
    from core.check.arith import Exact
    from core.check.cost import Counter
    from core.check.evaluate import CheckError
    from core.check.general import GeneralProgram, build_general_graph
    from core.check.tokens import TokenEvaluator
    from core.check.trace import UnsupportedOp

    torch.manual_seed(1000 * seed + len(name))
    module = networks()[name]()
    space = [V] * N
    weights = {k: v.detach().numpy() for k, v in module.named_parameters()}
    graph = build_general_graph(module)
    lean_graph, consts = export_network.export_general_graph(graph, export_network.batch1_values(module, space), space, Exact)
    net = {"format": export_network.FORMAT, "model": "synthetic", "network": f"{name}-{seed}", "task": "max",
           "general": True, "graph": lean_graph,
           "weights": export_network.export_general_weights(graph, weights, Exact) + consts}

    # which rules the Python evaluator takes
    seen = Tally()
    for meth in ("mul_sep", "sum_rows", "mul_var_sep", "sum_positions", "scale_mix", "add_mixes", "add_mix",
                 "matmul", "to_var", "collapse", "concretize"):
        orig = getattr(TokenEvaluator, meth)

        def wrapped(self, *a, _orig=orig, _meth=meth, **k):
            out = _orig(self, *a, **k)
            if out is not None:
                seen[_meth] += 1
            return out
        monkeypatch.setattr(TokenEvaluator, meth, wrapped)
    orig_var_op = TokenEvaluator.var_op

    def var_op(self, n, args, kwargs):
        out = orig_var_op(self, n, args, kwargs)
        if out is not None:
            seen[f"var_op:{n.kind}"] += 1
        return out
    monkeypatch.setattr(TokenEvaluator, "var_op", var_op)

    prog = GeneralProgram(graph, weights, Counter(), space)
    bs = boxes(random.Random(f"{name}/{seed}"))
    expected = []
    for box in bs:
        lo, hi = max(r[0] for r in box), max(r[1] for r in box)
        if lo != hi:
            expected.append((False, 0, 0))
            continue
        c = Counter()
        try:
            ok, _, _ = prog.run_token_interval([tuple(r) for r in box], lo, c)
        except (CheckError, UnsupportedOp):
            expected.append("rejected")
            break
        leaf, tables = c.by_rule.get("token_interval", 0), c.by_rule.get("tables", 0)
        assert c.total == leaf + tables, c.as_dict()
        expected.append((bool(ok), leaf, tables))
    missing = MEANT[name] - set(seen)
    assert not missing, f"the boxes never took {sorted(missing)} (took {dict(seen)})"

    net_json, boxes_json = tmp_path / "net.json", tmp_path / "boxes.json"
    net_json.write_text(json.dumps(net))
    boxes_json.write_text(json.dumps(bs))
    r = subprocess.run([str(CHECKER), "gtokens", str(net_json), str(boxes_json)], capture_output=True, text=True,
                       timeout=1800)
    assert r.returncode == 0, r.stderr[-1000:]
    rows = [json.loads(line) for line in r.stdout.splitlines() if line.startswith("{")]
    per_box = [row for row in rows if "box" in row]
    assert len(per_box) == len(expected), (per_box, expected)
    for box, row, exp in zip(bs, per_box, expected):
        assert row["box"] == box
        if exp == "rejected":
            assert row.get("status") == "rejected", (box, row)
            return
        assert (row.get("verdict"), row.get("token_interval"), row.get("tables")) == exp, (box, row, exp)
    assert rows[-1]["token_interval"] == sum(e[1] for e in expected)
    assert rows[-1]["tables"] == sum(e[2] for e in expected)
