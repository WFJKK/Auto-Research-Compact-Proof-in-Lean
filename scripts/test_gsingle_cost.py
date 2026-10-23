"""The open lane's single rule on general networks charges what cost-v3 charges a single leaf.

    python3 -m pytest scripts/test_gsingle_cost.py -v

`CostM.gsingle` (CountedGeneral.lean) runs one input through an attention network and bills it; the
Python checker's single leaf (core/check/general.py, `GeneralProgram.run_singles`) is the reference. For
every development network of the pipeline's attention models, on its first and last input and a few
chosen at random, `compactcheck gsingle` must give the Python checker's verdict and its charge exactly.
`gsingle` charges every operation on every call; cost-v3 charges the operations that do not depend on the
input once, to extract, but on these networks they are all structural (free), so the two agree.

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
MODELS = ["models/attn-max2", "models/attn-min2", "models/attn-max4", "models/attn-min4", "tests/attn_max2_tiny"]
SAMPLE = 6  # inputs per network chosen at random, besides the first and the last
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


@pytest.mark.parametrize("model,network", cases())
def test_gsingle_charges_what_the_python_single_leaf_charges(model, network, tmp_path):
    import numpy as np
    from core.check.cost import Counter
    from core.check.trace import build_any, make_program
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
        pytest.skip("a linear network: the linear single rule is tested elsewhere")
    prog = make_program(graph, weights, Counter(), space)

    # sampled directly: the space of a four-position network at 64 tokens has 16.8 million inputs
    rng = random.Random(network)
    chosen = [[0] * len(space), [v - 1 for v in space]] + [[rng.randrange(v) for v in space] for _ in range(SAMPLE)]
    expected = []
    for x in chosen:
        c = Counter()
        tokens = np.asarray([x], dtype=np.int64)
        labels = np.asarray(folder.task.label(tokens, sizes), dtype=np.int64)
        ok, _ = prog.run_singles(tokens, labels, c)
        expected.append((bool(ok[0]), c.by_rule["single"], sum(c.by_rule.values())))

    net_json, inputs_json = tmp_path / "net.json", tmp_path / "inputs.json"
    r = subprocess.run([sys.executable, "-B", str(HERE / "export_network.py"), str(REPO), model, network, str(net_json)],
                       capture_output=True, text=True, timeout=1800)
    assert r.returncode == 0, r.stderr[-1000:]
    inputs_json.write_text(json.dumps(chosen))
    r = subprocess.run([str(CHECKER), "gsingle", str(net_json), str(inputs_json)], capture_output=True, text=True,
                       timeout=1800)
    assert r.returncode == 0, r.stderr[-1000:]
    rows = [json.loads(line) for line in r.stdout.splitlines() if line.startswith("{")]
    assert len(rows) == len(chosen)
    for x, row, (ok, single, total) in zip(chosen, rows, expected):
        assert row["input"] == x
        assert single == total, "the Python single leaf charged another category"
        assert (row.get("verdict"), row.get("charge")) == (ok, single), (x, row, ok, single)
