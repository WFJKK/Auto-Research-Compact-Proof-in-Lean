#!/usr/bin/env python3
"""Check the proofs of a pipeline run with the Lean checker.

For every record in the run's archive.jsonl that has a proof file, on a
development network: the Lean checker must certify the number the Python
checker recorded, and reject what the Python checker rejected. Held-out
networks are skipped (their weights are for the final evaluation only).

Usage, from the Lean project folder, after `lake build compactcheck`:

    python3 scripts/check_run.py <repo> <run dir> [--only TEXT] [--limit N] [--log FILE]

Each result is appended to the log (default lean-<run id>.jsonl in the
current folder), and records already in the log are skipped, so an
interrupted check resumes where it stopped. Exits with status 1 if Lean and
Python disagree on any record.

Proofs the Python checker accepted with a leaf rule the Lean checker does
not have yet (rules adopted through the rule route, such as token_convex)
are skipped and counted, not logged, so a later check picks them up.

A proof file identical to one already checked on the same network (the
brute-force baseline at every knob value, say) is not run again: Lean's
answer is the same, so it is reused and logged with lean_s 0.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import subprocess
import sys
import tempfile
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import export_network  # noqa: E402

LEAN = HERE.parent / ".lake" / "build" / "bin" / "compactcheck"


LEAN_LEAF_RULES = {"single", "skip", "interval", "token_interval"}


def leaf_rules(tree) -> set:
    """The rule names of a proof tree's leaves."""
    if not isinstance(tree, dict):
        return set()
    if "leaf" in tree:
        return {str(tree["leaf"])}
    out = set()
    for child in tree.get("children") or []:
        out |= leaf_rules(child)
    return out


def knob_label(rec: dict) -> str:
    """As core.archive.knob_label."""
    return f"b{int(rec['budget'])}" if rec.get("budget") is not None else f"k{float(rec['knob']):g}"


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("repo", type=Path)
    ap.add_argument("run", type=Path, help="the run folder, <runs_dir>/<run id>")
    ap.add_argument("--only", default="", help="only records whose id contains this")
    ap.add_argument("--limit", type=int, default=0, help="stop after this many new checks")
    ap.add_argument("--log", type=Path, default=None)
    ap.add_argument("--timeout", type=int, default=3600, help="seconds per proof")
    args = ap.parse_args()
    repo, run = args.repo.resolve(), args.run.expanduser().resolve()
    sys.path.insert(0, str(repo))
    from core.model_folder import load_model_folder
    from core.zoo import network_entry

    records = []
    with open(run / "archive.jsonl") as f:
        seen = set()
        for line in f:
            if line.strip():
                rec = json.loads(line)
                if rec.get("record_id") not in seen:
                    seen.add(rec.get("record_id"))
                    records.append(rec)
    log = args.log or Path(f"lean-{run.name}.jsonl")
    done = {}
    if log.exists():
        for line in log.read_text().splitlines():
            if line.strip():
                r = json.loads(line)
                done[r["record_id"]] = r
    counts = {"agree": 0, "DIFFERS": 0, "held out": 0, "not supported": 0, "rule not in Lean": 0}
    for r in done.values():
        counts["agree" if r["agree"] else "DIFFERS"] += 1
    # Lean's answers by (network, proof file digest), to reuse for identical proof files
    answers = {(r["network"], r["proof_sha256"]): r for r in done.values() if "proof_sha256" in r}
    new = 0
    with tempfile.TemporaryDirectory() as tmp:
        tmp = Path(tmp)
        nets: dict[str, Path | str] = {}
        for rec in records:
            rid = rec.get("record_id", "")
            if rec.get("network") is None or args.only not in rid or rid in done:
                continue
            gz = run / f"round_{rec['round']:03d}" / f"attempt_{rec['attempt']}" / "proofs" / \
                f"{rec['network']}__{knob_label(rec)}.json.gz"
            if not gz.exists():
                continue
            model = f"models/{rec['model']}"
            nid = rec["network"]
            if nid not in nets:
                folder = load_model_folder(repo / model)
                if network_entry(folder, nid)["split"] != "dev":
                    nets[nid] = "held out"
                else:
                    try:
                        exported = export_network.export(repo, model, nid)
                    except Exception as exc:  # a network the Lean checker cannot read yet
                        print(f"{nid}: not checked, the network cannot be exported: {str(exc)[:200]}")
                        nets[nid] = "not supported"
                    else:
                        nets[nid] = tmp / f"{nid}.json"
                        nets[nid].write_text(json.dumps(exported))
            if isinstance(nets[nid], str):
                counts[nets[nid]] += 1
                continue
            proof = tmp / "proof.json"
            proof.write_bytes(gzip.decompress(gz.read_bytes()))
            py_status = "ok" if rec["status"] == "ok" else "rejected"
            if py_status == "ok":
                try:
                    missing = leaf_rules(json.loads(proof.read_text()).get("tree")) - LEAN_LEAF_RULES
                except (ValueError, AttributeError):
                    missing = set()
                if missing:
                    counts["rule not in Lean"] += 1
                    continue
            py_count = rec["certified"] if rec["status"] == "ok" else 0
            digest = hashlib.sha256(proof.read_bytes()).hexdigest()
            t0 = time.time()
            if (nid, digest) in answers:
                a = answers[(nid, digest)]
                ln = {"certified": a["lean"], "status": a["lean_status"], "reason": a["lean_reason"]}
            else:
                try:
                    out = subprocess.run([str(LEAN), str(nets[nid]), str(proof)], capture_output=True,
                                         text=True, check=True, timeout=args.timeout).stdout
                    ln = json.loads(out.strip().splitlines()[-1])
                except subprocess.TimeoutExpired:
                    ln = {"certified": None, "status": "timeout"}
            seconds = time.time() - t0
            agree = ln.get("certified") == py_count and ln.get("status", "ok") == py_status
            result = {"record_id": rid, "python": py_count, "python_status": py_status,
                      "lean": ln.get("certified"), "lean_status": ln.get("status", "ok"),
                      "lean_reason": ln.get("reason"), "lean_s": round(seconds, 2), "agree": agree,
                      "network": nid, "proof_sha256": digest}
            if ln.get("status") != "timeout":
                answers.setdefault((nid, digest), result)
            with open(log, "a") as f:
                f.write(json.dumps(result) + "\n")
            counts["agree" if agree else "DIFFERS"] += 1
            print(f"{rid:60s} Python {py_status:8s} {py_count!s:>6s}  Lean {result['lean_status']:8s} "
                  f"{result['lean']!s:>6s}  {seconds:7.1f}s  {'ok' if agree else 'DIFFERS'}", flush=True)
            new += 1
            if args.limit and new >= args.limit:
                break
    print(f"{counts['agree']} agree, {counts['DIFFERS']} differ; skipped: {counts['held out']} on held-out networks, "
          f"{counts['not supported']} on networks the Lean checker cannot read yet, "
          f"{counts['rule not in Lean']} with a leaf rule the Lean checker does not have yet; log {log}")
    sys.exit(1 if counts["DIFFERS"] else 0)


if __name__ == "__main__":
    main()
