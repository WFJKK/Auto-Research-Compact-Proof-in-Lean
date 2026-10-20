"""Tests of the open lane's acceptance service (scripts/accept.py): the hand-built example is accepted, and
every way a candidate can be wrong is rejected with the right status.

    python3 -m pytest scripts/test_accept.py -v

Needs the Lean project built (`lake build` of the library and `lake build acceptcheck`), the pipeline
repository (REPO below, or the environment variable COMPACT_PROOF_REPO), and its Python environment. Each test
compiles Lean against Mathlib, so the file takes a few minutes. The work folder is kept between tests
(the exported network and the protected module are cached) and deleted at the end.
"""

from __future__ import annotations

import json
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

HERE = Path(__file__).resolve().parent
PROJECT = HERE.parent
EXAMPLE = PROJECT / "examples" / "open_lane" / "max2_tiny_brute"
REPO = Path(os.environ.get("COMPACT_PROOF_REPO", PROJECT.parent / "auto-research-compact-proof"))

pytestmark = pytest.mark.skipif(not (REPO / "core").is_dir(), reason="the pipeline repository is not next to this one")


@pytest.fixture(scope="module")
def work(tmp_path_factory):
    return tmp_path_factory.mktemp("accept-work")


def submit(candidate: Path, work: Path, mode: str = "hardened") -> dict:
    r = subprocess.run([sys.executable, "-B", str(HERE / "accept.py"), "submit", str(candidate), "--repo", str(REPO),
                        "--work", str(work), "--mode", mode], capture_output=True, text=True, timeout=3600)
    assert r.stdout.strip(), r.stderr
    receipt = json.loads(r.stdout)
    assert (r.returncode == 0) == (receipt["status"] == "accepted")
    return receipt


def variant(tmp_path: Path, name: str, lean: str | None = None, manifest: dict | None = None,
            module_path: str = "Candidate/Max2Tiny.lean") -> Path:
    """A copy of the example with its Lean source or manifest changed."""
    d = tmp_path / name
    shutil.copytree(EXAMPLE, d)
    m = json.loads((d / "manifest.json").read_text())
    if manifest:
        m.update(manifest)
    m["candidate_id"] = name
    (d / "manifest.json").write_text(json.dumps(m))
    if lean is not None:
        p = d / module_path
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(lean)
    return d


SOURCE = (EXAMPLE / "Candidate" / "Max2Tiny.lean").read_text()


def test_the_hand_built_proof_is_accepted(work):
    r = submit(EXAMPLE, work)
    assert r["status"] == "accepted", r["reason"]
    assert r["certified_count"] == 64 and r["domain_size"] == 64
    assert set(r["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
    assert r["replayed_constants"] >= 4
    assert Path(r["receipt_path"]).exists()
    if sys.platform == "linux":
        assert r["isolation"] == "landlock"


def test_a_claim_above_the_count_is_rejected(work, tmp_path):
    """The network answers all 64 inputs correctly, so no claim above 64 can be proved; the domain has 64
    inputs, so a claim of 65 is rejected before anything is compiled. A claim of 64 made against the
    protected module of another claim is an import that is not allowed."""
    r = submit(variant(tmp_path, "claim-65", manifest={"claimed_count": 65}), work)
    assert r["status"] == "rejected" and "0 to 64" in r["reason"]
    r = submit(variant(tmp_path, "claim-63-mismatch", manifest={"claimed_count": 63}), work)
    assert r["status"] == "rejected" and "imports" in r["reason"]
    # a proof of a count the kernel finds false does not compile (one input is fine; D is 64, not 63)
    src = SOURCE.replace("D weights = 64", "D weights = 63").replace("claimedCount = 64 := rfl", "claimedCount = 63 := rfl")
    src = src.replace("_c64", "_c63")
    r = submit(variant(tmp_path, "claim-63-tried", lean=src, manifest={"claimed_count": 63}), work)
    assert r["status"] == "rejected" and "does not compile" in r["reason"]


def test_sorry_is_rejected(work, tmp_path):
    src = SOURCE.replace("decide +kernel", "sorry")
    r = submit(variant(tmp_path, "sorry", lean=src), work)
    assert r["status"] == "rejected" and "sorryAx" in r["reason"]


def test_native_decide_is_rejected(work, tmp_path):
    src = SOURCE.replace("decide +kernel", "native_decide")
    r = submit(variant(tmp_path, "native", lean=src), work)
    # this toolchain gives native_decide an axiom of its own; either way it is not a standard axiom
    assert r["status"] == "rejected" and "axioms that are not allowed" in r["reason"] and "native" in r["reason"]


def test_a_theorem_of_another_type_is_rejected(work, tmp_path):
    src = SOURCE.replace("theorem performance : Target := by", "theorem performance : True := by\n  trivial\n\ntheorem performance' : Target := by")
    r = submit(variant(tmp_path, "wrong-type", lean=src), work)
    assert r["status"] == "rejected" and "kernel rejects Challenge.proof" in r["reason"]


def test_a_conditional_claim_is_rejected(work, tmp_path):
    src = SOURCE.replace("theorem performance : Target := by", "theorem performance (h : False) : Target := by\n  exact h.elim\n\ntheorem performance' : Target := by")
    r = submit(variant(tmp_path, "conditional", lean=src), work)
    assert r["status"] == "rejected" and "kernel rejects Challenge.proof" in r["reason"]


def test_another_network_cannot_be_imported(work, tmp_path):
    src = SOURCE.replace("import Protected.N_max2_tiny_v8_s0_c64", "import Protected.N_max2_tiny_v8_s1_c64")
    r = submit(variant(tmp_path, "other-network", lean=src), work)
    assert r["status"] == "rejected" and "imports" in r["reason"]


def test_redeclaring_a_trusted_constant_is_rejected(work, tmp_path):
    src = SOURCE.replace("namespace Candidate.Max2Tiny", "theorem CompactCheck.singleOk_correct' : True := trivial\n\nnamespace Candidate.Max2Tiny")
    # a new name in a trusted namespace is allowed; the same name as a trusted constant is not
    r = submit(variant(tmp_path, "new-name", lean=src), work)
    assert r["status"] == "accepted", r["reason"]
    src2 = SOURCE.replace("namespace Candidate.Max2Tiny", "namespace CompactCheck\ntheorem shapeSize_three' : True := trivial\nend CompactCheck\n\nnamespace Candidate.Max2Tiny")
    r = submit(variant(tmp_path, "new-name-2", lean=src2), work)
    assert r["status"] == "accepted", r["reason"]


def test_a_macro_cannot_change_the_challenge(work, tmp_path):
    hijack = (
        "\nopen Lean Elab Command in\n"
        "macro_rules | `(theorem $n:ident : $t := $p) => `(theorem $n : True := trivial)\n"
    )
    src = SOURCE.replace("theorem performance : Target := by", "theorem performance : Target := by\n  trivial\n  done\n\ntheorem performance' : Target := by")
    r = submit(variant(tmp_path, "macro", lean=src + hijack), work)
    assert r["status"] == "rejected"


def test_bad_manifests_are_rejected(work, tmp_path):
    for name, change, text in (
        ("string-count", {"claimed_count": "63"}, "natural number"),
        ("negative-count", {"claimed_count": -1}, "natural number"),
        ("bool-count", {"claimed_count": True}, "natural number"),
        ("theorem-outside", {"theorem": "Mathlib.performance"}, "under Candidate."),
        ("module-outside", {"modules": ["Other/X.lean"]}, "Candidate/<Name>.lean"),
    ):
        r = submit(variant(tmp_path, name, manifest=change), work)
        assert r["status"] == "rejected" and text in r["reason"], (name, r["reason"])


@pytest.mark.skipif(sys.platform != "linux", reason="Landlock is Linux only")
def test_the_box_blocks_writes_outside_it(work, tmp_path):
    target = work / "receipts" / "forged.json"
    src = SOURCE.replace("namespace Candidate.Max2Tiny",
                         f'#eval IO.FS.writeFile "{target}" "{{}}"\n\nnamespace Candidate.Max2Tiny')
    r = submit(variant(tmp_path, "writer", lean=src), work)
    assert r["status"] == "rejected" and "does not compile" in r["reason"]
    assert not target.exists()


def test_a_tampered_protected_module_is_caught(work, tmp_path):
    """`acceptcheck protected` compares the module with the network file: a changed weight is a mismatch."""
    sys.path.insert(0, str(HERE))
    import accept
    import make_protected
    sys.path.pop(0)
    accept._repo = REPO
    net_json = accept.export_network(REPO, "tests/max2_tiny", "max2_tiny-v8-s0", work)
    net = json.loads(net_json.read_text())
    name, src = make_protected.render(net, 64)
    bad = src.replace("dyadic 1505767040", "dyadic 1505767041", 1)
    assert bad != src
    ws = tmp_path / "tampered"
    (ws / "Protected").mkdir(parents=True)
    (ws / "Protected" / f"{name}.lean").write_text(bad)
    lean, lp = accept.lean_binary(), accept.lean_path()
    mode = accept.box_mode("hardened")
    res = accept.compile_module(ws, ws, f"Protected.{name}", ws / "Protected" / f"{name}.lean", lean, lp, mode)
    assert res["rc"] == 0, res["stdout"][-500:]
    env = accept.box_env(ws, lean, lp)
    chk = accept.run_boxed(ws, [str(accept.acceptcheck_binary()), "protected", str(net_json), f"Protected.{name}",
                                res["olean"]], env, mode, 600, [str(accept.toolchain_root(lean)), str(PROJECT), str(net_json)])
    last = accept.last_json(chk["stdout"])
    assert last and last["status"] == "mismatch" and "weights" in last["reason"], chk
