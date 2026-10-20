#!/usr/bin/env python3
"""Export one network of the Python pipeline for the Lean checker.

Writes one JSON file with the network's traced graph, its task and its
weights. This script is part of the trusted base: Lean checks proofs about
the network this file describes, so what it writes must be the network the
Python pipeline trains and checks. It therefore only writes down:

* the graph that torch.fx traces from the model folder's model.py, using
  the Python checker's own tracers (core.check.trace for linear networks,
  core.check.general for the others, chosen as core.check.trace.build_any
  chooses), with arguments given by their positions in the list; each
  operation keeps its name, which proof files use to name maps in a
  contraction;
* the zoo's weights, exactly: every float is a dyadic rational, written
  as an integer times a power of two shared by the tensor
  (core.check.arith.Exact, the Python checker's own conversion);
* the task, by name, after checking that the model folder's task.label
  agrees with the Lean task of that name on every input.

In a general graph, sizes, indices and dimensions are numbers, not tensors:
`x.shape[0]` and the like. The exporter computes them on one input (batch
1) and writes the numbers. A number used as a tensor (`scores * 0.125`)
becomes a weight of shape [] named `#const<k>`, converted as the Python
checker converts it (as a float64, exactly).

Usage, from the Lean project folder:

    python3 scripts/export_network.py <repo> <model folder> <network id> <out.json>

for example

    python3 scripts/export_network.py ~/.../Auto-Research-Compact-Proof models/max2 max2-v64-s0 max2-v64-s0.json
"""

from __future__ import annotations

import argparse
import itertools
import json
import sys
from pathlib import Path

import numpy as np

FORMAT = "compactcheck-network-v1"

# The tasks Lean knows (CompactCheck/Task.lean), as numpy functions of a
# (batch, positions) array of tokens.
LEAN_TASKS = {
    "max": lambda tokens: tokens.max(axis=1),
    "min": lambda tokens: tokens.min(axis=1),
    # majorityLabel: 1 if the tokens add up to at least positions // 2 + 1
    "majority": lambda tokens: (tokens.sum(axis=1) >= tokens.shape[1] // 2 + 1).astype(np.int64),
}


class ExportError(ValueError):
    pass


def all_inputs(space: list[int]) -> np.ndarray:
    return np.array(list(itertools.product(*[range(v) for v in space])), dtype=np.int64)


def find_task(task_module, sizes: dict, space: list[int]) -> str:
    """The Lean task that agrees with the model folder's label on every input."""
    tokens = all_inputs(space)
    labels = np.asarray(task_module.label(tokens, sizes), dtype=np.int64)
    for name, fn in LEAN_TASKS.items():
        if np.array_equal(fn(tokens), labels):
            return name
    raise ExportError(f"the task's labels match no task the Lean checker knows ({', '.join(LEAN_TASKS)})")


def export_graph(graph, space: list[int]) -> dict:
    """The traced graph of a linear network, with arguments as positions."""
    if len(set(space)) != 1:
        raise ExportError("the one-hot input needs the same number of values at every position")
    index = {n.name: i for i, n in enumerate(graph.nodes)}
    nodes = []
    for n in graph.nodes:
        if n.op == "input":
            node = {"op": "input"}
        elif n.op == "linear":
            node = {"op": "linear", "arg": index[n.args[0]], "weight": n.weight, "bias": n.bias}
        elif n.op == "sum":
            node = {"op": "sum", "arg": index[n.args[0]], "dim": n.dim}
        elif n.op == "add":
            node = {"op": "add", "left": index[n.args[0]], "right": index[n.args[1]]}
        else:
            raise ExportError(f"operation {n.op!r} is not supported by the Lean checker yet")
        # The name proof files use for this operation (in a contraction chain).
        node["name"] = n.name
        nodes.append(node)
    return {"positions": len(space), "values": space[0], "nodes": nodes, "output": index[graph.output]}


def export_weights(graph, weights: dict, Exact) -> list[dict]:
    names = []
    for n in graph.nodes:
        if n.op == "linear":
            names.append(n.weight)
            if n.bias:
                names.append(n.bias)
    out = []
    for name in names:
        arr = np.asarray(weights[name])
        ex = Exact.from_float(arr)
        ints = [int(v) for v in np.asarray(ex.ints).reshape(-1)]
        out.append({"name": name, "shape": list(arr.shape), "exp": int(ex.exp), "ints": ints})
    return out


# ---------------------------------------------------------------------------
# General graphs (core.check.general)


def _is_ref(a) -> bool:
    return isinstance(a, tuple) and len(a) == 2 and a[0] == "node"


def _plain(v):
    """Sizes and shapes as Python ints and tuples."""
    import torch

    if isinstance(v, torch.Size):
        return tuple(int(d) for d in v)
    if isinstance(v, (tuple, list)):
        return type(v)(_plain(x) for x in v)
    return v


def batch1_values(module, space: list[int]) -> dict:
    """The value of every traced operation on one input (batch 1): tensors,
    and the sizes, indices and dimensions they are made of."""
    import torch
    import torch.fx

    gm = torch.fx.symbolic_trace(module)
    values: dict = {}

    class Recorder(torch.fx.Interpreter):
        def run_node(self, n):
            values[n.name] = super().run_node(n)
            return values[n.name]

    dtype = next(iter(module.parameters()), torch.zeros(())).dtype
    x = torch.zeros(1, len(space), space[0], dtype=dtype)
    x[0, :, 0] = 1
    with torch.no_grad():
        Recorder(gm).run(x)
    return values


def index_items(idx, shape: list[int]) -> list:
    """An index (an int, a slice, or a tuple of them) as Lean's items, one per
    leading dimension: "all", {"one": i} or {"range": [start, stop]}."""
    items = list(idx) if isinstance(idx, tuple) else [idx]
    if len(items) > len(shape):
        raise ExportError(f"index {idx!r} has more items than the tensor has dimensions")
    out = []
    for item, d in zip(items, shape):
        if isinstance(item, int) and not isinstance(item, bool):
            i = item + d if item < 0 else item
            if not 0 <= i < d:
                raise ExportError(f"index {item} out of range for a dimension of size {d}")
            out.append({"one": i})
        elif isinstance(item, slice):
            if item.step not in (None, 1) or any(
                    v is not None and (isinstance(v, bool) or not isinstance(v, int)) for v in (item.start, item.stop)):
                raise ExportError(f"slice {item!r}: only integer bounds and step 1")
            if item.start is None and item.stop is None:
                out.append("all")
            else:
                start, stop, _ = item.indices(d)
                out.append({"range": [start, max(start, stop)]})
        else:
            raise ExportError(f"index item {item!r}: only integers and slices")
    return out


def export_general_graph(graph, values: dict, space: list[int], Exact) -> tuple[dict, list[dict]]:
    """The traced graph of a general network, with arguments as positions, and
    the weights of shape [] for the numbers it uses as tensors."""
    import torch

    from core.check.general import _dim

    if len(set(space)) != 1:
        raise ExportError("the one-hot input needs the same number of values at every position")
    index: dict[str, int] = {}
    nodes: list[dict] = []
    consts: list[dict] = []

    def resolve(a):
        """A size, index or dimension argument, as plain Python numbers."""
        if _is_ref(a):
            v = values[a[1]]
            if isinstance(v, torch.Tensor):
                raise ExportError(f"{a[1]} is a tensor where a number is needed")
            return _plain(v)
        if isinstance(a, (list, tuple)):
            return type(a)(resolve(x) for x in a)
        if isinstance(a, slice):
            return slice(resolve(a.start), resolve(a.stop), resolve(a.step))
        return a

    def tensor_shape(a) -> list[int]:
        if not (_is_ref(a) and isinstance(values[a[1]], torch.Tensor)):
            raise ExportError(f"{a!r} is not a tensor")
        return list(values[a[1]].shape)

    def operand(a) -> int:
        """The position of a tensor argument. A number becomes a weight of shape
        [], as the Python checker's GeneralProgram._tensor converts it."""
        if _is_ref(a) and isinstance(values[a[1]], torch.Tensor):
            return index[a[1]]
        v = resolve(a)
        if isinstance(v, bool) or not isinstance(v, (int, float)):
            raise ExportError(f"{a!r} where a tensor is needed")
        ex = Exact.from_float(np.asarray(v, dtype=np.float64))
        name = f"#const{len(consts)}"
        consts.append({"name": name, "shape": [], "exp": int(ex.exp),
                       "ints": [int(i) for i in np.asarray(ex.ints).reshape(-1)]})
        nodes.append({"op": "param", "weight": name, "name": name})
        return len(nodes) - 1

    for n in graph.nodes:
        k, args, kwargs = n.kind, n.args, n.kwargs
        if not isinstance(values[n.name], torch.Tensor):
            # A size, a shape or an entry of one: written where it is used.
            if k not in ("getattr", "size", "getitem"):
                raise ExportError(f"{n.name}: {k} of numbers; only tensors can be computed with")
            continue
        if k == "input":
            node = {"op": "input"}
        elif k == "param":
            node = {"op": "param", "weight": n.target}
        elif k == "linear":
            bias = f"{n.target}.bias"
            node = {"op": "linear", "arg": operand(args[0]), "weight": f"{n.target}.weight",
                    "bias": bias if bias in graph.params else None}
        elif k == "getattr":  # .T; .shape is not a tensor
            if args[1] != "T" or len(tensor_shape(args[0])) > 2:
                raise ExportError(f"{n.name}: only the .T of a matrix")
            node = {"op": "transpose", "arg": operand(args[0])}
        elif k == "getitem":
            items = index_items(resolve(args[1]), tensor_shape(args[0]))
            node = {"op": "index", "arg": operand(args[0]), "items": items}
        elif k in ("add", "sub", "mul"):
            if kwargs:
                raise ExportError(f"{n.name}: {k} with keyword arguments")
            node = {"op": "binary", "fn": k, "left": operand(args[0]), "right": operand(args[1])}
        elif k == "neg":
            node = {"op": "neg", "arg": operand(args[0])}
        elif k == "matmul":
            node = {"op": "matmul", "left": operand(args[0]), "right": operand(args[1])}
        elif k == "unsqueeze":
            node = {"op": "unsqueeze", "arg": operand(args[0]), "dim": int(resolve(_dim(args, kwargs, 1)))}
        elif k == "expand":
            sizes = [resolve(s) for s in args[1:]]
            if len(sizes) == 1 and isinstance(sizes[0], (tuple, list)):
                sizes = list(sizes[0])
            if any(isinstance(s, bool) or not isinstance(s, int) for s in sizes):
                raise ExportError(f"{n.name}: expand to sizes that are not integers")
            node = {"op": "expand", "arg": operand(args[0]), "shape": sizes}
        elif k == "transpose":  # as GeneralProgram: a matrix, its two dimensions
            d0 = kwargs.get("dim0", args[1] if len(args) > 1 else None)
            d1 = kwargs.get("dim1", args[2] if len(args) > 2 else None)
            d0, d1 = resolve(d0), resolve(d1)
            if (len(tensor_shape(args[0])) != 2 or not isinstance(d0, int) or not isinstance(d1, int)
                    or not (-2 <= d0 < 2 and -2 <= d1 < 2) or d0 % 2 == d1 % 2):
                raise ExportError(f"{n.name}: transpose of something other than a matrix")
            node = {"op": "transpose", "arg": operand(args[0])}
        elif k in ("cat", "stack"):
            if not isinstance(args[0], (list, tuple)):
                raise ExportError(f"{n.name}: {k} of something other than a list of tensors")
            parts = [operand(a) for a in args[0]]
            dim = int(resolve(_dim(args, kwargs, 1))) if (len(args) > 1 or "dim" in kwargs) else 0
            node = {"op": k, "args": parts, "dim": dim}
        elif k == "sum":
            if kwargs.get("keepdim") or (set(kwargs) - {"dim"}) or len(args) > 2:
                raise ExportError(f"{n.name}: sum with keepdim or extra arguments")
            dim = resolve(_dim(args, kwargs, 1))
            if isinstance(dim, bool) or not isinstance(dim, int):
                raise ExportError(f"{n.name}: sum over exactly one dimension")
            node = {"op": "sum", "arg": operand(args[0]), "dim": dim}
        elif k == "exp":
            node = {"op": "exp", "arg": operand(args[0])}
        elif k == "softmax":
            node = {"op": "softmax", "arg": operand(args[0]), "dim": int(resolve(_dim(args, kwargs, 1)))}
        elif k == "zeros_like":
            node = {"op": "zeros_like", "arg": operand(args[0])}
        else:
            raise ExportError(f"{n.name}: operation {k!r} is not supported by the Lean checker yet")
        node["name"] = n.name
        nodes.append(node)
        index[n.name] = len(nodes) - 1
    if graph.output not in index:
        raise ExportError("the output is not a tensor")
    return ({"positions": len(space), "values": space[0], "nodes": nodes, "output": index[graph.output]}, consts)


def export_general_weights(graph, weights: dict, Exact) -> list[dict]:
    missing = [p for p in graph.params if p not in weights]
    if missing:
        raise ExportError(f"weights {missing} are missing")
    out = []
    for name in graph.params:
        arr = np.asarray(weights[name])
        ex = Exact.from_float(arr)
        ints = [int(v) for v in np.asarray(ex.ints).reshape(-1)]
        out.append({"name": name, "shape": list(arr.shape), "exp": int(ex.exp), "ints": ints})
    return out


def export(repo: Path, model: str, network_id: str) -> dict:
    sys.path.insert(0, str(repo))
    from core.check.arith import Exact
    from core.check.trace import UnsupportedOp, build_graph
    from core.model_folder import load_model_folder
    from core.zoo import load_weights, network_entry

    folder = load_model_folder(repo / model)
    entry = network_entry(folder, network_id)
    setting = entry["setting"]
    space = folder.input_space(setting)
    weights = load_weights(folder, network_id)  # checks the manifest hash; refuses held-out networks
    module = folder.build(setting)
    try:  # as core.check.trace.build_any
        graph = build_graph(module)
    except UnsupportedOp:
        from core.check.general import build_general_graph

        try:
            general = build_general_graph(module)
        except UnsupportedOp as exc:
            raise ExportError(f"the Python checker cannot trace this network ({exc})") from exc
        lean_graph, consts = export_general_graph(general, batch1_values(module, space), space, Exact)
        lean_weights = export_general_weights(general, weights, Exact) + consts
    else:
        lean_graph, lean_weights = export_graph(graph, space), export_weights(graph, weights, Exact)
        general = None
    return {
        "format": FORMAT,
        "model": folder.name,
        "network": network_id,
        "task": find_task(folder.task, folder.sizes(setting), space),
        # Checked as core.check.general checks it (not as a linear network).
        "general": general is not None,
        "graph": lean_graph,
        "weights": lean_weights,
    }


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("repo", type=Path, help="the Auto-Research-Compact-Proof repository")
    ap.add_argument("model", help="the model folder, relative to the repository, e.g. models/max2")
    ap.add_argument("network", help="the network id, e.g. max2-v64-s0")
    ap.add_argument("out", type=Path, help="the JSON file to write")
    args = ap.parse_args()
    try:
        data = export(args.repo.resolve(), args.model, args.network)
    except ExportError as exc:
        sys.exit(f"export_network: {exc}")
    args.out.write_text(json.dumps(data))
    print(f"wrote {args.out} ({data['task']}, {len(data['graph']['nodes'])} operations)")


if __name__ == "__main__":
    main()
