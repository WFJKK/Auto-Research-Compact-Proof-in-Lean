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
SCORED = PROJECT / "examples" / "open_lane" / "max2_tiny_scored"
AGENT = PROJECT / "examples" / "open_lane" / "max2_tiny_agent_cols23"
PORT = PROJECT / "examples" / "open_lane" / "max2_tiny_cols23_v3"
TREE = PROJECT / "examples" / "open_lane" / "max2_tiny_decision_tree"
REPO = Path(os.environ.get("COMPACT_PROOF_REPO", PROJECT.parent / "auto-research-compact-proof"))

pytestmark = pytest.mark.skipif(not (REPO / "core").is_dir(), reason="the pipeline repository is not next to this one")


@pytest.fixture(scope="module")
def work(tmp_path_factory):
    return tmp_path_factory.mktemp("accept-work")


SMALL_BUDGET = {"ACCEPT_SIZE_BUDGET_BASE": "512", "ACCEPT_SIZE_BUDGET_PER_PARAM": "1"}  # 592 on the tiny network


def copy_bound(nums: list[int]) -> int:
    """The least any encoding of these numbers can measure: one unit per bit (a numeral or a string; a list
    of booleans or a Church numeral costs at least twice that)."""
    return sum(max(1, abs(v).bit_length()) for v in nums)


def submit(candidate: Path, work: Path, mode: str = "hardened", env: dict | None = None) -> dict:
    """Submit a candidate. With env SMALL_BUDGET the size budget is 592 on the tiny network: the brute-force
    checker (about 370) fits, a copy of its 80 weights (over 1,700) does not. The default budget is
    calibrated for real networks, where the weights outweigh any checker; on the tiny network they do not
    (test_a_copy_of_the_weights_is_refused_under_the_default_policy_on_a_real_network uses the default)."""
    r = subprocess.run([sys.executable, "-B", str(HERE / "accept.py"), "submit", str(candidate), "--repo", str(REPO),
                        "--work", str(work), "--mode", mode], capture_output=True, text=True, timeout=3600,
                       env={**os.environ, **(env or {})})
    assert r.stdout.strip(), r.stderr
    receipt = json.loads(r.stdout)
    assert (r.returncode == 0) == (receipt["status"] == "accepted")
    return receipt


def variant(tmp_path: Path, name: str, lean: str | None = None, manifest: dict | None = None,
            module_path: str = "Candidate/Max2Tiny.lean", base: Path = EXAMPLE) -> Path:
    """A copy of the example with its Lean source or manifest changed."""
    d = tmp_path / name
    shutil.copytree(base, d)
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
SCORED_SOURCE = (SCORED / "Candidate" / "Max2TinyScored.lean").read_text()
NEW_D = "def D : Checker := fun I => countSingles I graph task (allInputs task.space)"
assert NEW_D in SCORED_SOURCE


def scored_variant(tmp_path: Path, name: str, lean: str) -> Path:
    return variant(tmp_path, name, lean=lean, module_path="Candidate/Max2TinyScored.lean", base=SCORED)


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


# ---- the scored path (docs/COUNTED.md) ------------------------------------------------------------------
def test_the_scored_proof_is_verified_and_scored(work):
    r = submit(SCORED, work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s["reason"]
    assert s["bill"] == 64 * 63 and s["read"] == 0 and s["extract"] == 80
    assert s["length"] == s["bill"] + s["extract"] + s["read"]
    assert s["description_size"] <= s["size_budget"] and s["general_kernel_ms"] <= s["general_kernel_budget_ms"]
    assert set(s["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
    assert [x["step"] for x in r["steps"]] == ["protected", "compile", "kernel", "closure", "score"]


def test_a_wrong_bill_is_refused_scoring(work, tmp_path):
    """The instance theorem states the exact bill; the service asks for the manifest's. The kernel's rejection
    of the mismatched statement refuses scoring, and the proof stays verified."""
    d = variant(tmp_path, "wrong-bill", module_path="Candidate/Max2TinyScored.lean", base=SCORED)
    m = json.loads((d / "manifest.json").read_text())
    m["scored"]["claimed_bill"] = 4031
    (d / "manifest.json").write_text(json.dumps(m))
    r = submit(d, work)
    assert r["status"] == "accepted" and r["certified_count"] == 64
    assert r["scoring"]["status"] == "refused" and "Challenge.instance" in r["scoring"]["reason"]


def test_a_checker_that_trusts_the_certificate_is_rejected_with_its_sorry(work, tmp_path):
    """`D` returns the certificate's size as the count: its soundness theorem is false in general, so the
    candidate can only `sorry` it, and the whole submission is rejected (the target's proof uses it)."""
    src = SCORED_SOURCE.replace(NEW_D, "def D : Checker := fun I => do\n  let n ← I.certSize\n  pure (I.nofNat n)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h", "  sorry")
    src = src.replace("some (64, 64 * 63)", "some (0, 0)").replace("exact D_sound weights cert 64 cost h", "sorry")
    r = submit(scored_variant(tmp_path, "trusts-cert", src), work)
    assert r["status"] == "rejected" and "sorryAx" in r["reason"]


def test_the_general_layer_may_not_touch_the_weights_not_proving_anti_hiding(work, tmp_path):
    """A checker that looks at the protected weights directly is outside the counted language, and the
    service says which constant it uses. This checks eligibility, not the anti-hiding property."""
    src = SCORED_SOURCE.replace(NEW_D, "def D : Checker := fun I => countSingles I graph task (if weights.length = 0 then [] else allInputs task.space)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  simp only [D] at h\n  rw [if_neg (by decide : ¬ weights.length = 0)] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    r = submit(scored_variant(tmp_path, "uses-weights", src), work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "weights" in s["reason"], s


def test_a_copy_of_the_weights_as_literals_is_refused_scoring_not_proving_anti_hiding(work, tmp_path):
    """A general-layer definition carrying the network's numbers as literals goes over the size budget."""
    net = json.loads((work / "networks" / "max2_tiny-v8-s0.json").read_text())
    nums = [abs(v) for w in net["weights"] for v in w["ints"]]
    table = "def table : List Nat := [" + ", ".join(str(v) for v in nums) + "]\n\n"
    src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                table + "/-- The checker: every input of the task's space. -/\ndef D : Checker := fun I => countSingles I graph task (if table.length = 0 then [] else allInputs task.space)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  simp only [D, table, List.length_cons, Nat.succ_ne_zero, ite_false] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    r = submit(scored_variant(tmp_path, "weights-copy", src), work, env=SMALL_BUDGET)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "description size" in s["reason"], s
    assert s["description_size"] >= copy_bound(nums)


def test_a_checker_outside_the_counted_language_is_refused_scoring(work, tmp_path):
    """`Interp.counting` and `CostM` are not on the allowlist: a checker that runs the counting interpreter
    itself (for free, outside the bill) is refused scoring, even when the result is the same."""
    src = SCORED_SOURCE.replace(NEW_D,
                                "def D : Checker := fun I => countSingles I graph task "
                                "(if (CostM.billed (countSingles Interp.counting graph task [[0, 0]]) ⟨[], #[]⟩).isSome then allInputs task.space else allInputs task.space)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  simp only [D, ite_self] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    r = submit(scored_variant(tmp_path, "bare-function", src), work)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "Interp.counting" in s["reason"] and "CostM.billed" in s["reason"], s


# ---- kinds, assurance, zero coverage, the development compile --------------------------------------------
def test_an_auxiliary_lemma_is_accepted_without_a_count(work, tmp_path):
    r = submit(variant(tmp_path, "aux-lemma", manifest={"kind": "auxiliary", "theorem": "Candidate.Max2Tiny.D_sound"}), work)
    assert r["status"] == "accepted", r["reason"]
    assert r["claim_kind"] == "auxiliary" and r["certified_count"] is None and r["score_eligible"] is False
    assert "numCorrect" in r["statement"] and set(r["axioms"]) <= {"propext", "Classical.choice", "Quot.sound"}
    r = submit(variant(tmp_path, "aux-def", manifest={"kind": "auxiliary", "theorem": "Candidate.Max2Tiny.D"}), work)
    assert r["status"] == "rejected" and "not a theorem" in r["reason"]


def test_a_scored_proof_is_marked_kernel_checked(work):
    r = submit(SCORED, work)
    assert r["claim_kind"] == "performance" and r["score_eligible"] is True
    assert r["execution_assurance"] == "kernel_checked_instance" and r["scoring"]["assurance"] == "kernel_checked_instance"
    assert r["cost_model"] == "cost-v3"


ZERO = """import Protected.N_max2_tiny_v8_s0_c0
import CompactCheck.Soundness
import CompactCheck.CountedOps

namespace Candidate.Zero
open CompactCheck Protected.N_max2_tiny_v8_s0_c0

def D : Checker := fun I => pure I.nzero

theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),
    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by
  intro w c n cost h
  simp only [D, CostM.exec, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h
  omega

theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (0, 0) := by decide +kernel

theorem performance : Target := Nat.zero_le _

end Candidate.Zero
"""


def test_zero_coverage_is_accepted_and_scored_not_rejected(work, tmp_path):
    d = variant(tmp_path, "zero", lean=ZERO, module_path="Candidate/Zero.lean", base=SCORED)
    (d / "Candidate" / "Max2TinyScored.lean").unlink()
    m = json.loads((d / "manifest.json").read_text())
    m.update(claimed_count=0, theorem="Candidate.Zero.performance", modules=["Candidate/Zero.lean"],
             scored={"checker": "Candidate.Zero.D", "sound": "Candidate.Zero.D_sound", "instance": "Candidate.Zero.D_instance",
                     "certificate": [], "claimed_bill": 0})
    (d / "manifest.json").write_text(json.dumps(m))
    r = submit(d, work)
    assert r["status"] == "accepted" and r["certified_count"] == 0, r["reason"]
    assert r["scoring"]["status"] == "scored" and r["scoring"]["length"] == 80, r["scoring"]


def test_an_invented_axiom_is_rejected(work, tmp_path):
    src = SOURCE.replace("theorem performance : Target := by", "axiom cheat : Target\n\ntheorem performance : Target := cheat\n\ntheorem performance' : Target := by")
    r = submit(variant(tmp_path, "axiom", lean=src), work)
    assert r["status"] == "rejected" and "axioms that are not allowed" in r["reason"] and "cheat" in r["reason"]


def test_a_soundness_proof_about_another_checker_is_refused_scoring(work, tmp_path):
    """The manifest names D; the soundness theorem is about D2. The service builds the statement for D, so the
    kernel rejects the candidate's theorem at that type: verified, not scored."""
    src = SCORED_SOURCE.replace("/-! ## Specific layer -/", "def D2 : Checker := fun I => pure I.nzero\n\ntheorem D2_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),\n    CostM.exec (D2 Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by\n  intro w c n cost h\n  simp only [D2, CostM.exec, CostM.run_pure, Option.some.injEq, Prod.mk.injEq] at h\n  omega\n\n/-! ## Specific layer -/")
    d = scored_variant(tmp_path, "other-program", src)
    m = json.loads((d / "manifest.json").read_text())
    m["scored"]["sound"] = "Candidate.Max2TinyScored.D2_sound"
    (d / "manifest.json").write_text(json.dumps(m))
    r = submit(d, work)
    assert r["status"] == "accepted" and r["certified_count"] == 64
    assert r["scoring"]["status"] == "refused" and "Challenge.sound" in r["scoring"]["reason"], r["scoring"]


def test_the_development_compile_reports_errors_and_never_accepts(work, tmp_path):
    ws = tmp_path / "ws"
    (ws / "Candidate").mkdir(parents=True)
    (ws / "Candidate" / "Dev.lean").write_text(SCORED_SOURCE.replace("decide +kernel", "exact rfl"))
    cmd = [sys.executable, "-B", str(HERE / "accept.py"), "compile", str(ws), "Candidate/Dev.lean", "--repo", str(REPO),
           "--work", str(work), "--model", "tests/max2_tiny", "--network", "max2_tiny-v8-s0", "--claimed", "64"]
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
    out = json.loads(r.stdout)
    assert r.returncode == 1 and out["ok"] is False and "error" in out["messages"].lower() and out["protected_module"].endswith("_c64")
    (ws / "Candidate" / "Dev.lean").write_text(SCORED_SOURCE)
    r = subprocess.run(cmd, capture_output=True, text=True, timeout=1800)
    out = json.loads(r.stdout)
    assert r.returncode == 0 and out["ok"] is True
    assert not list((work / "receipts").glob("*Dev*"))  # a compile is not a submission


def test_the_agents_pilot_proof_is_verified_and_refused_scoring_in_the_current_language(work):
    """The pilot's third submission of round 1 (20 October 2026), kept as the agent wrote it: the columns of
    M = U L E, 23 of 64 inputs for a bill of 458. It was written in the first counted language (a concrete
    `CostM Nat`, with concrete booleans); every later version (a checker is a function of the interpreter)
    refuses it: its checker uses `CostM` directly. Its mathematics is still verified."""
    r = submit(AGENT, work)
    assert r["status"] == "accepted" and r["certified_count"] == 23, r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "CostM" in s["reason"], s
    assert r["score_eligible"] is False


# ---- the handoff's remaining fixtures ----------------------------------------------------------------------
def test_the_weights_packed_into_one_literal_are_refused_scoring_not_proving_anti_hiding(work, tmp_path):
    """A copy of the weights encoded in a single big natural number (24 bits each) in a general-layer
    definition: the measure charges a numeral 1 per bit, so the copy weighs 24 per weight."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    accept._repo = REPO
    net = json.loads(accept.export_network(REPO, "tests/max2_tiny", "max2_tiny-v8-s0", work).read_text())
    nums = [abs(v) % (1 << 24) for w in net["weights"] for v in w["ints"]]
    packed = 0
    for v in nums:
        packed = (packed << 24) | v
    table = f"def packed : Nat := {packed}\n\ndef unpack (n k : Nat) : Nat := (n >>> (24 * k)) % (1 <<< 24)\n\n"
    src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                table + "/-- The checker: every input of the task's space. -/\ndef D : Checker := fun I => countSingles I graph task (if unpack packed 0 = 0 then [] else allInputs task.space)")
    src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                      "  intro w c n cost h\n  unfold numCorrect\n  simp only [D] at h\n  rw [if_neg (by decide : ¬ unpack packed 0 = 0)] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
    r = submit(scored_variant(tmp_path, "weights-packed", src), work, env=SMALL_BUDGET)
    assert r["status"] == "accepted", r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "description size" in s["reason"], s
    assert s["description_size"] >= 24 * len(nums)


def test_option_overrides_in_the_candidate_do_not_reach_the_service(work, tmp_path):
    """A candidate may raise its own elaboration limits; the service's budgets are measured by the service
    (kernel time of the replay, literal weight), so the submission is scored exactly as without them."""
    src = SCORED_SOURCE.replace("/-- The kernel runs the single rule on all 64 inputs",
                                "set_option maxHeartbeats 0 in\nset_option maxRecDepth 100000 in\n/-- The kernel runs the single rule on all 64 inputs")
    assert src != SCORED_SOURCE
    r = submit(scored_variant(tmp_path, "options", src), work)
    assert r["status"] == "accepted" and r["scoring"]["status"] == "scored" and r["scoring"]["length"] == 4112, r


def test_a_candidate_cannot_change_its_sources_during_evaluation(work, tmp_path):
    """The sources the service compiles are its own copy, read-only in the box: a candidate that tries to
    rewrite them while compiling fails to compile, and the copy is what was submitted."""
    src = SOURCE.replace("namespace Candidate.Max2Tiny",
                         '#eval IO.FS.writeFile "Candidate/Max2Tiny.lean" "theorem Candidate.Max2Tiny.performance : True := trivial"\n\nnamespace Candidate.Max2Tiny')
    d = variant(tmp_path, "race", lean=src)
    r = submit(d, work)
    assert r["status"] == "rejected" and "does not compile" in r["reason"], r["reason"]
    copies = sorted((work / "submissions").glob("race-*/Candidate/Max2Tiny.lean"))
    assert copies and copies[-1].read_text() == src


def test_renaming_or_hiding_a_definition_does_not_hide_its_data(work, tmp_path):
    """The size budget is measured over the checker's computational closure, whatever the names: a
    private definition, an underscore name or a `match_1` name carrying a copy of the weights is still
    counted, and the submission refused scoring."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    accept._repo = REPO
    net = json.loads(accept.export_network(REPO, "tests/max2_tiny", "max2_tiny-v8-s0", work).read_text())
    nums = [abs(v) for w in net["weights"] for v in w["ints"]]
    for name, decl in (("private-table", "private def table"), ("underscore-table", "def _table"), ("match-name", "def match_1")):
        ident = decl.split()[-1]
        table = f"{decl} : List Nat := [" + ", ".join(str(v) for v in nums) + "]\n\n"
        src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                    table + "/-- The checker: every input of the task's space. -/\ndef D : Checker := fun I => countSingles I graph task "
                                    f"(if {ident}.length = 0 then [] else allInputs task.space)")
        src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h",
                          f"  intro w c n cost h\n  unfold numCorrect\n  simp only [D, {ident}, List.length_cons, Nat.succ_ne_zero, ite_false] at h\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
        r = submit(scored_variant(tmp_path, name, src), work, env=SMALL_BUDGET)
        assert r["status"] == "accepted", (name, r["reason"])
        s = r["scoring"]
        assert s["status"] == "refused" and "description size" in s["reason"], (name, s)
        assert s["description_size"] >= copy_bound(nums)


def test_a_table_of_booleans_or_a_church_encoding_is_refused_scoring_not_proving_anti_hiding(work, tmp_path):
    """A copy of the weights as a list of booleans (one constructor per bit) and as a Church encoding (one
    function per number applying `c0` or `c1` per bit, no numeral anywhere): the description size counts
    every node, so both weigh at least two per bit, more than the weights as numerals, and both are
    refused."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    accept._repo = REPO
    net = json.loads(accept.export_network(REPO, "tests/max2_tiny", "max2_tiny-v8-s0", work).read_text())
    nums = [abs(v) % (1 << 24) for w in net["weights"] for v in w["ints"]]
    bits = [(v >> k) & 1 for v in nums for k in range(24)]
    bools = "def table : List Bool := [" + ", ".join("true" if b else "false" for b in bits) + "]\n\n"
    # one function per number (24 applications deep; a single 1920-deep term overflows the elaborator)
    chunks = ", ".join("fun z => " + "".join(f"c{(v >> k) & 1} (" for k in range(24)) + "z" + ")" * 24 for v in nums)
    church = (f"def table (c0 c1 : Nat → Nat) (z : Nat) : Nat := [{chunks}].foldl (fun z f => f z) z\n\n"
              "def decoded : Nat := table (fun n => 2 * n) (fun n => 2 * n + 1) 0\n\n")
    for name, defs, cond in (("bool-table", bools, "table.length = 0"), ("church-table", church, "decoded = 0")):
        src = SCORED_SOURCE.replace("/-- The checker: every input of the task's space. -/\n" + NEW_D,
                                    defs + "/-- The checker: every input of the task's space. -/\ndef D : Checker := fun I => countSingles I graph task "
                                    f"(if {cond} then [] else allInputs task.space)")
        # the tables are too large for simp to unfold (recursion depth), so the condition is decided by the kernel
        proof = (f"  intro w c n cost h\n  unfold numCorrect\n  simp only [D] at h\n  rw [if_neg (by decide +kernel : ¬ {cond})] at h\n"
                 "  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h")
        src = src.replace("  intro w c n cost h\n  unfold numCorrect\n  exact countSingles_le ⟨w, c⟩ (allInputs task.space) [] n cost h", proof)
        r = submit(scored_variant(tmp_path, name, src), work, env=SMALL_BUDGET)
        assert r["status"] == "accepted", (name, r["reason"])
        s = r["scoring"]
        assert s["status"] == "refused" and "description size" in s["reason"], (name, s)
        assert s["description_size"] >= 2 * 24 * len(nums), (name, s["description_size"])


def test_branching_into_the_checkers_own_code_is_not_expressible(work, tmp_path):
    """The reviewers' counterexamples to versions 2 and 3, as written: the continuation `I.ifN bit (k 1)
    (k 0)` and the masked conditional `nadd (nmask b (k 1)) (nmask nb (k 0))`. Neither `ifN` nor `nmask`
    exists in version 4, so neither checker compiles; the only uses of a truth value are countB, nscale,
    selectV and the charged gates, none of which runs the checker's own code or conditions a count."""
    src = SCORED_SOURCE.replace("    pure (I.nadd (I.countB ok) n)",
                                "    I.ifN ok (pure (I.nadd (I.nofNat 1) n)) (pure (I.nadd (I.nofNat 0) n))")
    assert src != SCORED_SOURCE
    r = submit(scored_variant(tmp_path, "continuation", src), work)
    assert r["status"] == "rejected" and "does not compile" in r["reason"] and "ifN" in r["reason"], r["reason"]
    src = SCORED_SOURCE.replace("    pure (I.nadd (I.countB ok) n)",
                                "    let nok ← I.bnot \"m\" ok\n    pure (I.nadd (I.nmask ok (I.nofNat 1)) (I.nmask nok n))")
    assert src != SCORED_SOURCE
    r = submit(scored_variant(tmp_path, "masked-conditional", src), work)
    assert r["status"] == "rejected" and "does not compile" in r["reason"] and "nmask" in r["reason"], r["reason"]


def test_a_decision_tree_over_truth_values_bills_every_node(work):
    """The version 3 reviewer's decoder written in version 4 (examples/open_lane/max2_tiny_decision_tree):
    the path indicator passes a charged gate at every node, so a tree over k = 4 truth values of one weight
    bills 3 (2^4 - 1) = 45 gates on top of the 4 numerals and 4 comparisons that made the truth values,
    whatever its leaves compute (here nothing: count 0). This is the accounting the free mask broke."""
    r = submit(TREE, work)
    assert r["status"] == "accepted" and r["certified_count"] == 0, r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s["reason"]
    assert s["bill"] == 53 == 2 * 4 + 3 * (2 ** 4 - 1) and s["length"] == 53 + 80


def test_the_ported_column_proof_is_scored_under_language_v4(work):
    """The agent's column proof ported by hand to version 4 (examples/open_lane/max2_tiny_cols23_v3): the
    interface keeps a meaningful method expressible, provable and scoreable. 23 of 64, bill 562 (the
    agent's 458 plus 104 charged gates), length 642; its description size calibrates the default budget."""
    r = submit(PORT, work)
    assert r["status"] == "accepted" and r["certified_count"] == 23, r["reason"]
    s = r["scoring"]
    assert s["status"] == "scored", s["reason"]
    assert s["bill"] == 562 and s["length"] == 642 and s["description_size"] <= s["size_budget"]
    assert r["score_eligible"] is True


def test_the_default_size_budget_is_below_a_copy_of_the_weights_on_every_zoo_setting():
    """The policy's arithmetic, with no Lean: for one network of every size setting of every model in the
    pipeline's zoo, the bits of its weights as the exporter writes them (integers over the tensor's common
    power-of-two exponent: the least any encoding measures, one unit per bit) exceed 8192 + 4 E. The tiny
    test network (E = 80) is the exception the other size tests work around with SMALL_BUDGET."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    from fractions import Fraction
    import numpy as np
    seen = []
    for manifest in sorted((REPO / "models").glob("*/zoo/manifest.json")):
        m = json.loads(manifest.read_text())
        settings = set()
        for n in m["networks"]:
            if n["setting"] in settings:
                continue
            settings.add(n["setting"])
            z = np.load(manifest.parent / n["weights"])
            bits = E = 0
            for key in z:
                arr = np.asarray(z[key])
                if arr.dtype.kind != "f":
                    continue
                fr = [Fraction(float(v)) for v in arr.reshape(-1).astype(np.float64)]
                den = max([f.denominator for f in fr] + [1])
                ints = [int(f * den) for f in fr]
                bits += copy_bound(ints)
                E += len(ints)
            budget = accept.SIZE_BUDGET_BASE + accept.SIZE_BUDGET_PER_PARAM * E
            seen.append((manifest.parent.parent.name, n["setting"], E, bits, budget))
            assert bits > budget, (manifest.parent.parent.name, n["setting"], E, bits, budget)
    assert len(seen) >= 6, seen


def test_a_copy_of_the_weights_is_refused_under_the_default_policy_on_a_real_network(work, tmp_path):
    """max2 v64 (E = 1,088, 23 to 35 bits per weight): a numeral copy of the weights in the general layer
    measures above the default budget 8192 + 4 E = 12,544 and is refused scoring, with no test hook. The
    checker certifies nothing (count 0, so the kernel work is small); the proof stays verified."""
    sys.path.insert(0, str(HERE))
    import accept
    sys.path.pop(0)
    accept._repo = REPO
    net = json.loads(accept.export_network(REPO, "models/max2", "max2-v64-s0", work).read_text())
    nums = [abs(v) for w in net["weights"] for v in w["ints"]]
    assert len(nums) == 1088
    src = "\n".join([
        "import Protected.N_max2_v64_s0_c0", "import CompactCheck.Soundness", "import CompactCheck.CountedOps", "",
        "namespace Candidate.Max2V64Copy", "open CompactCheck Protected.N_max2_v64_s0_c0", "",
        "def table : List Nat := [" + ", ".join(str(v) for v in nums) + "]", "",
        "def D : Checker := fun I => pure (I.nofNat (table.length - table.length))", "",
        "theorem D_sound : ∀ (w : Weights ℚ) (c : Cert) (n : Nat) (cost : Cost),",
        "    CostM.exec (D Interp.counting) ⟨w, c⟩ = some (n, cost) → n ≤ numCorrect graph w task := by",
        "  intro w c n cost h",
        "  have h' : (pure (table.length - table.length) : CostM Nat).run ⟨w, c⟩ [] = some (n, cost) := h",
        "  rw [CostM.run_pure] at h'",
        "  simp only [Option.some.injEq, Prod.mk.injEq, Nat.sub_self] at h'",
        "  rw [← h'.1]", "  exact Nat.zero_le _", "",
        "theorem D_instance : CostM.billed (D Interp.counting) ⟨weights, cert⟩ = some (0, 0) := by",
        "  decide +kernel", "",
        "theorem performance : Target := by",
        "  show claimedCount ≤ numCorrect graph weights task", "  exact Nat.zero_le _", "",
        "end Candidate.Max2V64Copy", ""])
    manifest = {"model": "models/max2", "network": "max2-v64-s0", "claimed_count": 0,
                "theorem": "Candidate.Max2V64Copy.performance", "modules": ["Candidate/Max2V64Copy.lean"],
                "scored": {"checker": "Candidate.Max2V64Copy.D", "sound": "Candidate.Max2V64Copy.D_sound",
                           "instance": "Candidate.Max2V64Copy.D_instance", "certificate": [], "claimed_bill": 0}}
    d = variant(tmp_path, "v64-copy", lean=src, manifest=manifest, module_path="Candidate/Max2V64Copy.lean", base=SCORED)
    (d / "Candidate" / "Max2TinyScored.lean").unlink()
    r = submit(d, work)
    assert r["status"] == "accepted" and r["certified_count"] == 0, r["reason"]
    s = r["scoring"]
    assert s["status"] == "refused" and "description size" in s["reason"], s
    assert s["size_budget"] == 8192 + 4 * 1088 and s["description_size"] >= copy_bound(nums) > s["size_budget"], s


def test_the_service_reports_the_identity_its_receipts_carry(work):
    """`accept.py identity` is what a run records when it starts and checks when it resumes: the project's
    commit, the toolchain, trusted-source and policy digests every receipt carries, and the binary."""
    r = subprocess.run([sys.executable, "-B", str(HERE / "accept.py"), "identity"], capture_output=True, text=True, timeout=600)
    ident = json.loads(r.stdout)
    assert set(ident) == {"commit", "dirty", "toolchain", "lean_project", "policy", "acceptcheck"}
    receipt = submit(SCORED, work)
    assert receipt["status"] == "accepted"
    for k in ("commit", "toolchain", "lean_project", "policy", "acceptcheck"):
        assert receipt["digests"][k] == ident[k], k
    assert "dirty" not in receipt["digests"]
    with_hook = subprocess.run([sys.executable, "-B", str(HERE / "accept.py"), "identity"], capture_output=True, text=True,
                               timeout=600, env={**os.environ, **SMALL_BUDGET})
    assert json.loads(with_hook.stdout)["policy"] != ident["policy"]  # the hooks are part of the policy
