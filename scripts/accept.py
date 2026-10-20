#!/usr/bin/env python3
"""The open lane's acceptance service: takes a candidate's Lean modules, builds them in a box, and asks the
kernel whether they prove the protected target. Writes a receipt.

    python3 scripts/accept.py submit <candidate dir> --repo <pipeline repo> --work <work dir> [--mode M]

The candidate dir holds manifest.json and the modules it names:

    {"schema": "open-lane-candidate-v1", "candidate_id": "...",
     "model": "models/max2", "network": "max2-v64-s0", "claimed_count": 4095,
     "theorem": "Candidate.Cubic.performance", "modules": ["Candidate/Cubic.lean"]}

What happens, in order (every step's outcome is in the receipt):

1. The manifest is checked: types, a claimed count that is a natural number, module paths under Candidate/
   with identifier names, no symbolic links. Module files may import only Candidate.* (among the submitted
   modules), the protected module, CompactCheck.* and Mathlib.*.
2. The network is exported from the pipeline's zoo with scripts/export_network.py (cached by network), and
   the protected module Protected.N_<network>_c<claimed> is written by scripts/make_protected.py and compiled;
   `acceptcheck protected` checks its constants against the network file with the checker's own reader.
3. Each candidate module is compiled with `lean` in a box (Landlock on Linux: no network, reads only the
   toolchain, the Lean project, the workspace and system files, writes only the workspace's out/ and tmp/;
   `process` mode elsewhere, which is weak and is recorded as such), under time and memory limits.
4. `acceptcheck check` imports the trusted modules only, replays every constant of the candidate's .olean
   files through the kernel, and asks the kernel to accept `Challenge.proof : Target := <theorem>`.
5. The axioms of the challenge must be among propext, Classical.choice and Quot.sound.

Receipt statuses: accepted, rejected (the candidate is at fault: manifest, compile error, kernel rejection,
axioms), unsupported (the network has an operation the Lean checker does not know), timeout, error
(infrastructure). A certified count is given only with status accepted. Receipts go to <work>/receipts/,
which the box cannot write. The service never trusts a candidate's own build output.

A scored submission (docs/COUNTED.md) adds to its manifest

    "scored": {"checker": "Candidate.X.D", "sound": "Candidate.X.D_sound", "instance": "Candidate.X.D_instance",
               "certificate": [...numbers...], "claimed_bill": 12345}

and, once verified as above, goes through the scored path: the certificate becomes the protected module's
`cert`; `acceptcheck closure` checks that the checker touches numbers only through the counted primitives
(accept/allowlist.txt); `acceptcheck score` has the kernel accept the soundness theorem at the fixed shape and
the instance `CostM.billed D ⟨weights, cert⟩ = some (claimed_count, claimed_bill)`, and measures the general
layer (literal weight, kernel time), which the policy budgets below bound. The receipt's `scoring` block says
whether the submission is scored and gives the length in cost-v3 units: the bill, plus `extract` (one per
weight entry) and `read` (one per certificate number). A submission refused scoring stays verified.

    python3 scripts/accept.py protected <network.json> <claimed> --work <work dir> [--certificate c.json]

builds and checks a protected module alone (for tests, and for a candidate's own development).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import sys
import time
from pathlib import Path

HERE = Path(__file__).resolve().parent
LEAN_PROJECT = HERE.parent
SCHEMA = "open-lane-candidate-v1"
RECEIPT_SCHEMA = "open-lane-receipt-v1"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
TRUSTED_PREFIXES = ("CompactCheck.", "Mathlib.")
IDENT = re.compile(r"^[A-Za-z_][A-Za-z0-9_]*$")
IMPORT_LINE = re.compile(r"^\s*import\s+([A-Za-z_][A-Za-z0-9_.]*)\s*$")
COMPILE_TIMEOUT_S = 3600
CHECK_TIMEOUT_S = 3600
MEMORY_MB = 12288  # virtual: Mathlib's .olean files are mapped into memory
ALLOWLIST = LEAN_PROJECT / "accept" / "allowlist.txt"
# the scoring policy (docs/COUNTED.md): the general layer's free data and kernel work are bounded
LITERAL_BUDGET_BASE = 32      # literal weight allowed to the general layer (acceptcheck's litWeight) ...
LITERAL_BUDGET_PER_PARAM = 8  # ... plus one per this many weight entries: a copy of the weights costs more
GENERAL_KERNEL_BUDGET_MS = 120_000  # kernel time to replay the general layer


def literal_budget(extract: int) -> int:
    return LITERAL_BUDGET_BASE + extract // LITERAL_BUDGET_PER_PARAM


class Reject(Exception):
    """The candidate is at fault."""


class Unsupported(Exception):
    pass


class Infra(Exception):
    pass


def sha256_file(p: Path) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def sha256_text(s: str) -> str:
    return hashlib.sha256(s.encode()).hexdigest()


# ---- the toolchain and the project ---------------------------------------------------------------
def lean_binary() -> Path:
    for candidate in (shutil.which("lean"), str(Path.home() / ".elan" / "bin" / "lean")):
        if candidate and Path(candidate).exists():
            p = Path(candidate).resolve()
            # elan's bin/lean is a proxy; ask it where the real toolchain is
            try:
                out = subprocess.run([str(p), "--print-prefix"], capture_output=True, text=True, timeout=60,
                                     cwd=str(LEAN_PROJECT))
                if out.returncode == 0 and out.stdout.strip():
                    return Path(out.stdout.strip()) / "bin" / "lean"
            except (OSError, subprocess.TimeoutExpired):
                pass
            return p
    raise Infra("no lean binary found (install elan)")


def toolchain_root(lean: Path) -> Path:
    return lean.parent.parent


def lean_path() -> list[str]:
    """The LEAN_PATH of the Lean project: its build and its packages' builds."""
    r = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"], capture_output=True, text=True,
                       cwd=str(LEAN_PROJECT), timeout=300, env={**os.environ, "PATH": _path_with_elan()})
    if r.returncode != 0 or not r.stdout.strip():
        raise Infra(f"lake env failed in {LEAN_PROJECT}: {r.stderr[-500:]}")
    return [p for p in r.stdout.strip().split(":") if p]


def _path_with_elan() -> str:
    return str(Path.home() / ".elan" / "bin") + ":" + os.environ.get("PATH", "/usr/bin:/bin")


def acceptcheck_binary() -> Path:
    p = LEAN_PROJECT / ".lake" / "build" / "bin" / "acceptcheck"
    if not p.exists():
        raise Infra(f"{p} is missing: run `lake build acceptcheck` in {LEAN_PROJECT}")
    return p


# ---- the box -----------------------------------------------------------------------------------------
def box_mode(want: str) -> str:
    if want == "process":
        return "process"
    try:
        sys.path.insert(0, str(_repo))
        from core.sandbox import landlock_available
    finally:
        sys.path.pop(0)
    if landlock_available():
        return "landlock"
    if want == "landlock":
        raise Infra("Landlock is not available on this machine")
    return "process"


_repo: Path = Path(".")


def run_boxed(ws: Path, cmd: list[str], env: dict, mode: str, timeout_s: float, read_extra: list[str]) -> dict:
    """Run cmd in the box rooted at ws (out/ and tmp/ writable). Returns rc, stdout, stderr, timed_out."""
    sys.path.insert(0, str(_repo))
    try:
        from core.sandbox import SYSTEM_READ, DEVICE_READ, DEVICE_READ_WRITE, PROC_READ
        import core.harness as harness
    finally:
        sys.path.pop(0)
    (ws / "out").mkdir(exist_ok=True)
    (ws / "tmp").mkdir(exist_ok=True)
    shutil.copy(harness.__file__, ws / "_harness.py")
    shutil.copy(HERE / "_boxrun.py", ws / "_boxrun.py")
    policy = None
    if mode == "landlock":
        read = [p for p in SYSTEM_READ + DEVICE_READ + PROC_READ if os.path.exists(p)] + [str(ws)] + read_extra
        policy = {"read": read, "read_write": [str(ws / "out"), str(ws / "tmp")] + list(DEVICE_READ_WRITE),
                  "own_proc": True}
    job = {"policy": policy, "limits": {"RLIMIT_AS": MEMORY_MB << 20, "RLIMIT_CPU": int(timeout_s) + 60},
           "cwd": str(ws), "env": env, "cmd": cmd}
    (ws / "job.json").write_text(json.dumps(job))
    t0 = time.time()
    try:
        p = subprocess.run([sys.executable, "-I", "-B", str(ws / "_boxrun.py"), str(ws / "job.json")],
                           capture_output=True, text=True, timeout=timeout_s, cwd=str(ws))
    except subprocess.TimeoutExpired as exc:
        return {"rc": -9, "stdout": exc.stdout or "", "stderr": "timed out", "timed_out": True,
                "seconds": round(time.time() - t0, 1)}
    return {"rc": p.returncode, "stdout": p.stdout, "stderr": p.stderr, "timed_out": False,
            "seconds": round(time.time() - t0, 1)}


# ---- the pieces ---------------------------------------------------------------------------------------
def export_network(repo: Path, model: str, network: str, work: Path) -> Path:
    out = work / "networks" / f"{network}.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    if out.exists():
        return out
    r = subprocess.run([sys.executable, "-B", str(HERE / "export_network.py"), str(repo), model, network, str(out)],
                       capture_output=True, text=True, timeout=1800)
    if r.returncode != 0:
        msg = (r.stderr or r.stdout)[-800:]
        if "not supported" in msg or "ExportError" in msg:
            raise Unsupported(f"the network cannot be exported for the Lean checker: {msg}")
        raise Infra(f"export failed: {msg}")
    return out


def box_env(ws: Path, lean: Path, lp: list[str]) -> dict:
    """The environment of a boxed lean or acceptcheck: the search path, the toolchain, a home in tmp/."""
    root = toolchain_root(lean)
    return {"LEAN_PATH": ":".join(lp + [str(ws / "out")]), "LEAN_SYSROOT": str(root),
            "PATH": f"{root / 'bin'}:/usr/bin:/bin", "HOME": str(ws / "tmp"), "TMPDIR": str(ws / "tmp"),
            "LANG": "C.UTF-8"}


def compile_module(ws: Path, root: Path, module: str, src: Path, lean: Path, lp: list[str], mode: str,
                   timeout_s: float = COMPILE_TIMEOUT_S) -> dict:
    """Compile one module whose source is src (module name relative to root) into ws/out."""
    out = ws / "out" / (module.replace(".", "/") + ".olean")
    out.parent.mkdir(parents=True, exist_ok=True)
    env = box_env(ws, lean, lp)
    cmd = [str(lean), "-R", str(root), "-o", str(out), str(src)]
    res = run_boxed(ws, cmd, env, mode, timeout_s, [str(toolchain_root(lean)), str(LEAN_PROJECT)] + lp)
    res["module"] = module
    res["olean"] = str(out)
    return res


def check_imports(text: str, module: str, modules: set[str], protected: str) -> list[str]:
    """The module's imports, each checked against the allowlist. Imports must come first, as in Lean."""
    imports = []
    for line in text.splitlines():
        s = line.strip()
        if not s or s.startswith("--"):
            continue
        m = IMPORT_LINE.match(line)
        if not m:
            break
        name = m.group(1)
        if name.startswith("Candidate."):
            if name not in modules:
                raise Reject(f"{module} imports {name}, which is not a submitted module")
            if name == module:
                raise Reject(f"{module} imports itself")
        elif name == protected or name.startswith(TRUSTED_PREFIXES):
            pass
        else:
            raise Reject(f"{module} imports {name}; allowed: the submitted Candidate modules, {protected}, "
                         "CompactCheck.* and Mathlib.*")
        imports.append(name)
    return imports


def order_modules(deps: dict[str, list[str]]) -> list[str]:
    """Candidate modules in an order where every import comes first."""
    out, state = [], {}

    def visit(m, trail):
        if state.get(m) == 2:
            return
        if state.get(m) == 1:
            raise Reject("the candidate modules import each other in a cycle: " + " -> ".join(trail + [m]))
        state[m] = 1
        for d in deps[m]:
            if d.startswith("Candidate."):
                visit(d, trail + [m])
        state[m] = 2
        out.append(m)

    for m in sorted(deps):
        visit(m, [])
    return out


def read_manifest(cdir: Path) -> dict:
    p = cdir / "manifest.json"
    if not p.is_file():
        raise Reject("manifest.json is missing")
    try:
        m = json.loads(p.read_text())
    except ValueError as exc:
        raise Reject(f"manifest.json is not JSON: {exc}")
    if not isinstance(m, dict) or m.get("schema") != SCHEMA:
        raise Reject(f"manifest schema must be {SCHEMA}")
    for key, typ in (("candidate_id", str), ("model", str), ("network", str), ("theorem", str), ("modules", list)):
        if not isinstance(m.get(key), typ):
            raise Reject(f"manifest field {key} must be a {typ.__name__}")
    c = m.get("claimed_count")
    if not isinstance(c, int) or isinstance(c, bool) or c < 0:
        raise Reject("claimed_count must be a natural number")
    if not re.match(r"^[A-Za-z0-9_.-]{1,80}$", m["candidate_id"]):
        raise Reject("candidate_id must be 1 to 80 letters, digits, dots, dashes or underscores")
    if not m["modules"]:
        raise Reject("modules is empty")
    for rel in m["modules"]:
        if not isinstance(rel, str) or not rel.startswith("Candidate/") or not rel.endswith(".lean"):
            raise Reject(f"module path {rel!r} must be Candidate/<Name>.lean")
        parts = rel[len("Candidate/"):-len(".lean")].split("/")
        if not all(IDENT.match(x) for x in parts):
            raise Reject(f"module path {rel!r} is not made of identifiers")
        f = cdir / rel
        if f.is_symlink() or not f.is_file():
            raise Reject(f"module {rel} is missing or is a symbolic link")
    parts = m["theorem"].split(".")
    if len(parts) < 2 or parts[0] != "Candidate" or not all(IDENT.match(x) for x in parts):
        raise Reject("theorem must be a name under Candidate., made of identifiers")
    if not re.match(r"^[A-Za-z0-9_./-]+$", m["model"]) or ".." in m["model"]:
        raise Reject("model must be a relative path in the pipeline repository")
    if not re.match(r"^[A-Za-z0-9_-]+$", m["network"]):
        raise Reject("network must be a network id")
    if "scored" in m:
        s = m["scored"]
        if not isinstance(s, dict):
            raise Reject("scored must be an object")
        for key in ("checker", "sound", "instance"):
            v = s.get(key)
            if not isinstance(v, str):
                raise Reject(f"scored.{key} must be a constant name")
            ps = v.split(".")
            if len(ps) < 2 or ps[0] != "Candidate" or not all(IDENT.match(x) for x in ps):
                raise Reject(f"scored.{key} must be a name under Candidate., made of identifiers")
        b = s.get("claimed_bill")
        if not isinstance(b, int) or isinstance(b, bool) or b < 0:
            raise Reject("scored.claimed_bill must be a natural number")
        sys.path.insert(0, str(HERE))
        try:
            import make_protected
        finally:
            sys.path.pop(0)
        try:
            s["certificate"] = make_protected.canonical_cert(s.get("certificate", []))
        except make_protected.ProtectedError as exc:
            raise Reject(f"scored.certificate: {exc}")
    return m


# ---- the protected module ---------------------------------------------------------------------------
def build_protected(net_json: Path, claimed: int, work: Path, lean: Path, lp: list[str], mode: str,
                    cert: list | None = None) -> dict:
    """Write, compile and verify the protected module; returns {module, olean, ...}. Cached by content."""
    sys.path.insert(0, str(HERE))
    try:
        import make_protected
    finally:
        sys.path.pop(0)
    net = json.loads(net_json.read_text())
    try:
        name, src = make_protected.render(net, claimed, cert)
    except make_protected.ProtectedError as exc:
        if "not supported" in str(exc):
            raise Unsupported(str(exc))
        raise Reject(str(exc))
    module = f"Protected.{name}"
    pdir = work / "protected"
    ws = pdir / name
    olean = ws / "out" / "Protected" / f"{name}.olean"
    stamp = ws / "verified.json"
    if olean.exists() and stamp.exists() and json.loads(stamp.read_text()).get("source_sha256") == sha256_text(src):
        return {"module": module, "olean": str(olean), "lean_path_dir": str(ws / "out"), "cached": True,
                "domain": json.loads(stamp.read_text())["domain"]}
    shutil.rmtree(ws, ignore_errors=True)
    (ws / "Protected").mkdir(parents=True)
    srcp = ws / "Protected" / f"{name}.lean"
    srcp.write_text(src)
    (ws / "cert.json").write_text(json.dumps(cert or []))
    res = compile_module(ws, ws, module, srcp, lean, lp, mode)
    if res["timed_out"]:
        raise Infra("compiling the protected module timed out")
    if res["rc"] != 0:
        raise Infra(f"the protected module does not compile: {res['stdout'][-1500:]}{res['stderr'][-500:]}")
    env = box_env(ws, lean, lp)
    chk = run_boxed(ws, [str(acceptcheck_binary()), "protected", str(net_json), module, str(olean)], env, mode,
                    CHECK_TIMEOUT_S, [str(toolchain_root(lean)), str(LEAN_PROJECT), str(net_json)])
    last = last_json(chk["stdout"])
    if chk["rc"] != 0 or not last or last.get("status") != "ok":
        raise Infra(f"the protected module does not match the network file: {last or chk['stderr'][-800:]}")
    stamp.write_text(json.dumps({"source_sha256": sha256_text(src), "domain": last["domain"],
                                 "network": last["network"]}))
    return {"module": module, "olean": str(olean), "lean_path_dir": str(ws / "out"), "cached": False,
            "domain": last["domain"]}


def last_json(text: str) -> dict | None:
    for line in reversed(text.strip().splitlines()):
        line = line.strip()
        if line.startswith("{"):
            try:
                return json.loads(line)
            except ValueError:
                return None
    return None


# ---- a submission -------------------------------------------------------------------------------------
def submit(cdir: Path, repo: Path, work: Path, want_mode: str) -> dict:
    global _repo
    _repo = repo
    t0 = time.time()
    receipt = {"schema": RECEIPT_SCHEMA, "candidate_id": None, "status": None, "reason": None,
               "certified_count": None, "domain_size": None, "claimed_count": None, "network": None,
               "theorem": None, "axioms": None, "isolation": None, "steps": [], "digests": {},
               "scoring": {"status": "not_requested"},
               "seconds": None, "time": time.strftime("%Y-%m-%dT%H:%M:%S%z")}
    ws = None
    try:
        manifest = read_manifest(cdir)
        receipt.update(candidate_id=manifest["candidate_id"], claimed_count=manifest["claimed_count"],
                       network=manifest["network"], theorem=manifest["theorem"])
        mode = box_mode(want_mode)
        receipt["isolation"] = mode if mode == "landlock" else "process (weak: no Landlock here)"
        lean = lean_binary()
        lp = lean_path()
        receipt["digests"]["toolchain"] = (toolchain_root(lean) / "bin" / "lean").name + ":" + sha256_file(lean)[:16]
        receipt["digests"]["lean_project"] = project_digest()
        # the modules and their imports
        modules = {}
        for rel in manifest["modules"]:
            name = "Candidate." + rel[len("Candidate/"):-len(".lean")].replace("/", ".")
            if name in modules:
                raise Reject(f"module {name} is listed twice")
            modules[name] = cdir / rel
        receipt["digests"]["modules"] = {m: sha256_file(p) for m, p in modules.items()}
        # the network and the protected target
        net_json = export_network(repo, manifest["model"], manifest["network"], work)
        receipt["digests"]["network_file"] = sha256_file(net_json)
        scored = manifest.get("scored")
        receipt["digests"]["policy"] = policy_digest()
        prot = build_protected(net_json, manifest["claimed_count"], work, lean, lp, mode,
                               scored["certificate"] if scored else None)
        receipt["domain_size"] = prot["domain"]
        receipt["steps"].append({"step": "protected", "module": prot["module"], "cached": prot["cached"]})
        deps = {m: check_imports(p.read_text(), m, set(modules), prot["module"]) for m, p in modules.items()}
        order = order_modules(deps)
        # the workspace
        ws = work / "submissions" / f"{manifest['candidate_id']}-{int(t0)}"
        if ws.exists():
            raise Infra(f"{ws} exists")
        (ws / "Candidate").mkdir(parents=True)
        for m, p in modules.items():
            dst = ws / (m.replace(".", "/") + ".lean")
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(p, dst)
        lp_all = lp + [prot["lean_path_dir"]]
        oleans = []
        for m in order:
            res = compile_module(ws, ws, m, ws / (m.replace(".", "/") + ".lean"), lean, lp_all, mode)
            receipt["steps"].append({"step": "compile", "module": m, "rc": res["rc"], "seconds": res["seconds"],
                                     "timed_out": res["timed_out"]})
            if res["timed_out"]:
                receipt.update(status="timeout", reason=f"compiling {m} exceeded {COMPILE_TIMEOUT_S} s")
                return finish(receipt, work, t0)
            if res["rc"] != 0:
                raise Reject(f"{m} does not compile: {(res['stdout'] + res['stderr'])[-2000:]}")
            oleans.append(res["olean"])
        # the kernel
        trusted = [prot["module"]] + sorted({d for ds in deps.values() for d in ds if not d.startswith("Candidate.")})
        env = box_env(ws, lean, lp_all)
        cmd = [str(acceptcheck_binary()), "check", prot["module"] + ".Target", manifest["theorem"]] + trusted + ["--"] + oleans
        chk = run_boxed(ws, cmd, env, mode, CHECK_TIMEOUT_S, [str(toolchain_root(lean)), str(LEAN_PROJECT)] + lp_all)
        receipt["steps"].append({"step": "kernel", "rc": chk["rc"], "seconds": chk["seconds"], "timed_out": chk["timed_out"]})
        if chk["timed_out"]:
            receipt.update(status="timeout", reason=f"the kernel check exceeded {CHECK_TIMEOUT_S} s")
            return finish(receipt, work, t0)
        last = last_json(chk["stdout"])
        if chk["rc"] != 0 or last is None:
            raise Infra(f"acceptcheck failed: {(chk['stdout'] + chk['stderr'])[-1500:]}")
        if last.get("status") != "accepted":
            raise Reject(last.get("reason") or "the kernel rejected the candidate")
        axioms = list(last.get("axioms") or [])
        receipt["axioms"] = axioms
        bad = sorted(set(axioms) - ALLOWED_AXIOMS)
        if bad:
            raise Reject(f"the proof depends on axioms that are not allowed: {', '.join(bad)}")
        receipt.update(status="accepted", certified_count=manifest["claimed_count"],
                       replayed_constants=last.get("replayed"))
        if scored:
            receipt["scoring"] = score(scored, manifest, prot, net_json, trusted, oleans, ws, env, mode, lean, lp_all, receipt)
    except Reject as exc:
        receipt.update(status="rejected", reason=str(exc))
    except Unsupported as exc:
        receipt.update(status="unsupported", reason=str(exc))
    except Infra as exc:
        receipt.update(status="error", reason=str(exc))
    return finish(receipt, work, t0)


def score(scored: dict, manifest: dict, prot: dict, net_json: Path, trusted: list[str], oleans: list[str], ws: Path,
          env: dict, mode: str, lean: Path, lp_all: list[str], receipt: dict) -> dict:
    """The scored path, after verification: the closure check, the kernel's two challenges, the budgets, the
    length. Returns the receipt's `scoring` block; never raises for the candidate's faults."""
    net = json.loads(net_json.read_text())
    extract = sum(len(w["ints"]) for w in net["weights"])
    read = len(scored["certificate"])
    out = {"status": None, "reason": None, "bill": None, "extract": extract, "read": read, "length": None,
           "literals": None, "literal_budget": literal_budget(extract), "general_kernel_ms": None,
           "general_kernel_budget_ms": GENERAL_KERNEL_BUDGET_MS, "rest_kernel_ms": None, "axioms": None}
    read_extra = [str(toolchain_root(lean)), str(LEAN_PROJECT)] + lp_all
    # the checker touches numbers only through the counted primitives
    cmd = [str(acceptcheck_binary()), "closure", scored["checker"], str(ALLOWLIST), prot["module"]] + trusted + ["--"] + oleans
    chk = run_boxed(ws, cmd, env, mode, CHECK_TIMEOUT_S, read_extra)
    receipt["steps"].append({"step": "closure", "rc": chk["rc"], "seconds": chk["seconds"], "timed_out": chk["timed_out"]})
    last = last_json(chk["stdout"])
    if chk["timed_out"] or chk["rc"] != 0 or last is None:
        raise Infra(f"acceptcheck closure failed: {(chk['stdout'] + chk['stderr'])[-1500:]}")
    if last.get("status") != "ok":
        out.update(status="refused", reason="the checker uses constants outside the counted language: "
                   + ", ".join(last.get("offending") or []) + (f" ({last['reason']})" if last.get("reason") else ""))
        return out
    out["closure_visited"] = last.get("visited")
    # the kernel: the soundness shape and the instance
    cmd = [str(acceptcheck_binary()), "score", prot["module"], scored["checker"], scored["sound"], scored["instance"],
           str(manifest["claimed_count"]), str(scored["claimed_bill"])] + trusted + ["--"] + oleans
    chk = run_boxed(ws, cmd, env, mode, CHECK_TIMEOUT_S, read_extra)
    receipt["steps"].append({"step": "score", "rc": chk["rc"], "seconds": chk["seconds"], "timed_out": chk["timed_out"]})
    if chk["timed_out"]:
        out.update(status="timeout", reason=f"the scored kernel check exceeded {CHECK_TIMEOUT_S} s")
        return out
    last = last_json(chk["stdout"])
    if chk["rc"] != 0 or last is None:
        raise Infra(f"acceptcheck score failed: {(chk['stdout'] + chk['stderr'])[-1500:]}")
    if last.get("status") != "accepted":
        out.update(status="refused", reason=last.get("reason") or "the kernel rejected the scored submission")
        return out
    axioms = list(last.get("axioms") or [])
    out["axioms"] = axioms
    bad = sorted(set(axioms) - ALLOWED_AXIOMS)
    if bad:
        out.update(status="refused", reason=f"the scored proofs depend on axioms that are not allowed: {', '.join(bad)}")
        return out
    general, rest = last.get("general") or {}, last.get("rest") or {}
    out.update(literals=general.get("literals"), general_kernel_ms=general.get("kernel_ms"), rest_kernel_ms=rest.get("kernel_ms"),
               general_constants=general.get("constants"))
    if out["literals"] is None or out["literals"] > out["literal_budget"]:
        out.update(status="refused", reason=f"the general layer's literal weight {out['literals']} exceeds the budget {out['literal_budget']}")
        return out
    if out["general_kernel_ms"] is None or out["general_kernel_ms"] > GENERAL_KERNEL_BUDGET_MS:
        out.update(status="refused", reason=f"replaying the general layer took {out['general_kernel_ms']} ms, over the budget {GENERAL_KERNEL_BUDGET_MS} ms")
        return out
    # the length, in cost-v3 units
    out.update(status="scored", bill=scored["claimed_bill"], length=scored["claimed_bill"] + extract + read)
    return out


def policy_digest() -> str:
    """A digest of the scoring policy: the allowlist and the budgets."""
    h = hashlib.sha256()
    h.update(ALLOWLIST.read_bytes() if ALLOWLIST.exists() else b"")
    h.update(json.dumps({"literal_budget": [LITERAL_BUDGET_BASE, LITERAL_BUDGET_PER_PARAM],
                         "general_kernel_budget_ms": GENERAL_KERNEL_BUDGET_MS,
                         "allowed_axioms": sorted(ALLOWED_AXIOMS), "trusted_prefixes": TRUSTED_PREFIXES}).encode())
    return h.hexdigest()[:16]


def finish(receipt: dict, work: Path, t0: float) -> dict:
    receipt["seconds"] = round(time.time() - t0, 1)
    if receipt["status"] != "accepted":
        receipt["certified_count"] = None
    rdir = work / "receipts"
    rdir.mkdir(parents=True, exist_ok=True)
    name = f"{receipt['candidate_id'] or 'invalid'}-{int(t0)}.json"
    (rdir / name).write_text(json.dumps(receipt, indent=1))
    receipt["receipt_path"] = str(rdir / name)
    return receipt


def project_digest() -> str:
    """A digest of the Lean project's source: the trusted base of every receipt."""
    h = hashlib.sha256()
    files = sorted(list(LEAN_PROJECT.glob("CompactCheck/*.lean")) + [LEAN_PROJECT / "AcceptMain.lean",
                   LEAN_PROJECT / "lakefile.toml", LEAN_PROJECT / "lake-manifest.json", LEAN_PROJECT / "lean-toolchain",
                   HERE / "make_protected.py", HERE / "export_network.py", HERE / "accept.py", HERE / "_boxrun.py"])
    for f in files:
        if f.exists():
            h.update(f.name.encode() + b"\0" + f.read_bytes() + b"\0")
    return h.hexdigest()[:16]


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    s = sub.add_parser("submit")
    s.add_argument("candidate", type=Path)
    s.add_argument("--repo", type=Path, required=True, help="the pipeline repository")
    s.add_argument("--work", type=Path, required=True, help="networks, protected modules, workspaces and receipts")
    s.add_argument("--mode", default="hardened", choices=("hardened", "landlock", "process"))
    p = sub.add_parser("protected")
    p.add_argument("network", type=Path)
    p.add_argument("claimed", type=int)
    p.add_argument("--repo", type=Path, required=True)
    p.add_argument("--work", type=Path, required=True)
    p.add_argument("--mode", default="hardened", choices=("hardened", "landlock", "process"))
    p.add_argument("--certificate", type=Path, help="a JSON list of numbers, for a scored submission's module")
    args = ap.parse_args(argv)
    global _repo
    _repo = args.repo.resolve()
    if args.cmd == "submit":
        r = submit(args.candidate.resolve(), _repo, args.work.resolve(), args.mode)
        print(json.dumps(r, indent=1))
        return 0 if r["status"] == "accepted" else 1
    mode = box_mode(args.mode)
    cert = json.loads(args.certificate.read_text()) if args.certificate else None
    r = build_protected(args.network.resolve(), args.claimed, args.work.resolve(), lean_binary(), lean_path(), mode, cert)
    print(json.dumps(r, indent=1))
    return 0


if __name__ == "__main__":
    sys.exit(main())
