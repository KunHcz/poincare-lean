#!/usr/bin/env python3
"""Verify the finite-chain consequence, not geometric surgery existence."""
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import time

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[1]
HELPER = REPOSITORY / "submissions/jsp-000007-dini-extinction/constant-curvature/scripts/verify.py"
SPEC = importlib.util.spec_from_file_location("flow_chain_helpers", HELPER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("The preserved verifier helper is missing")
shared = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(shared)
GEOMETRY_PIN = "ad76f2f1dfb959f4d8fc46fac9ed9feffdf497d9"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_inputs():
    source = json.loads((ROOT / "source-manifest.json").read_text())["files"]
    for rel, expected in source.items():
        if digest(ROOT / rel) != expected:
            raise RuntimeError("Changed submitted source: " + rel)
    lean_files = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*.lean") if ".lake" not in p.parts}
    if lean_files != {rel for rel in source if rel.endswith(".lean")}:
        raise RuntimeError("Unexpected proof source inventory")
    original = REPOSITORY / "submissions/jsp-000007-dini-extinction/scalar-flow-bounds/ScalarFlowBounds.lean"
    if digest(original) != digest(ROOT / "ScalarFlowBounds.lean"):
        raise RuntimeError("The reused scalar proof has changed")
    pins = {}
    for dep in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]:
        if dep["type"] != "git":
            raise RuntimeError("Unpinned dependency")
        path = ROOT / ".lake/packages" / dep["name"]
        pin = shared.checked(["git", "rev-parse", "HEAD"], path)
        if pin != dep["rev"] or shared.checked(["git", "status", "--porcelain", "--untracked-files=no"], path):
            raise RuntimeError("Changed dependency: " + dep["name"])
        pins[dep["name"]] = pin
    if pins.get("DifferentialGeometry") != GEOMETRY_PIN or pins.get("mathlib") != shared.MATHLIB_COMMIT:
        raise RuntimeError("Unexpected mathematical dependency")
    return source, pins


def main():
    output = ROOT / "verification-output"
    output.mkdir(exist_ok=True)
    record = output / "verification.json"
    record.write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    started = datetime.now(timezone.utc).isoformat()
    source, pins = check_inputs()
    version = shared.checked(["lake", "env", "lean", "--version"], ROOT)
    if "version 4.33.1," not in version or shared.LEAN_COMMIT not in version:
        raise RuntimeError("Unexpected Lean version")

    def run(label, args, expected_error=None, timeout=1200):
        proc = shared.run(args, ROOT, timeout=timeout)
        text = proc.stdout.replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")
        (output / (label + ".log")).write_text(text)
        if expected_error is None:
            if proc.returncode:
                raise RuntimeError(label + " failed")
        elif not proc.returncode or expected_error not in text or not re.search(r"error(?:\([^)]*\))?:", text):
            raise RuntimeError(label + " was not rejected as required")
        return text

    run("build", ["lake", "--wfail", "build"])
    names = ["PoincareFlowChains." + name for name in
             re.findall(r"^theorem (\w+)", (ROOT / "FlowChainBounds.lean").read_text(), re.M)]
    tests = ["PoincareFlowChainsTests." + name for name in
             re.findall(r"^theorem (\w+)", (ROOT / "FlowChainTests.lean").read_text(), re.M)]
    if len(names) != 5 or len(tests) != 5:
        raise RuntimeError("Fixed theorem inventory changed")
    local = ROOT / ".lake/verification"
    local.mkdir(parents=True, exist_ok=True)
    audit = local / "Axioms.lean"
    audit.write_text("import FlowChainAudit\n" + "".join("#print axioms " + n + "\n" for n in names + tests))
    axioms = shared.parse_axioms(run("axioms", ["lake", "env", "lean", str(audit)]), names + tests)
    replay_start = time.monotonic()
    text = run("kernel-replay", ["lake", "env", "leanchecker", "--verbose", "--fresh", "FlowChainAudit"],
               timeout=1800)
    replay_seconds = round(time.monotonic() - replay_start, 2)
    if "replaying FlowChainAudit with --fresh" not in text:
        raise RuntimeError("No final root replay confirmation")
    gate = (ROOT / "FlowChainAudit.lean").read_text()
    proof = (ROOT / "FlowChainBounds.lean").read_text()
    if gate.count("run_cmd do\n") != 1:
        raise RuntimeError("Unexpected audit placement")
    fixtures = {
        "extra_axiom": (gate.replace("run_cmd do\n", "axiom PoincareFlowChains.sentinel : False\nrun_cmd do\n"),
                        "non-whitelisted axiom PoincareFlowChains.sentinel"),
        "placeholder": (gate.replace("run_cmd do\n", "theorem PoincareFlowChains.sentinel : False := by sorry\nrun_cmd do\n"),
                        "non-whitelisted axiom sorryAx"),
        "missing_cap_bound": (proof.replace("hcap : ∀ y, ¬ survives y → 0 ≤ rB y", "hcap : True"), "hcap"),
        "not_a_flow": (proof.replace("hS : ∀ j ≤ n, IsSolutionOn (I := 𝓡 3) (S j)", "hS : ∀ j ≤ n, True"), "hS"),
        "reset_clock": ("import FlowChainBounds\nexample : PoincareFlowChains.elapsed (fun _ => (1 : ℝ)) 3 = 1 := by\n"
                        "  norm_num [PoincareFlowChains.elapsed]\n", "unsolved goals"),
    }
    for name, (text, expected_error) in fixtures.items():
        path = local / (name + ".lean")
        path.write_text(text)
        run(name, ["lake", "env", "lean", str(path)], expected_error, timeout=300)
    if check_inputs() != (source, pins):
        raise RuntimeError("Inputs changed during verification")
    result = {
        "status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED",
        "scope": "Normalized scalar control on finite chains of genuine Ricci flows, allowing different manifolds, under explicit surviving-region and nonnegative-cap bounds",
        "full_poincare_formalization": False,
        "started_at_utc": started, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version, "source_files": source, "dependency_pins": pins,
        "new_production_theorems": names, "new_regression_theorems": tests,
        "axioms": axioms, "namespace_wide_audit": True,
        "full_fresh_kernel_replay": True, "replay_seconds": replay_seconds,
        "default_warning_as_error_build": True,
        "negative_controls": {name: "REJECTED" for name in fixtures},
        "source_and_dependencies_checked_before_and_after": True,
        "reused_scalar_proof_unchanged": True,
        "surgery_or_cap_construction_proved": False,
        "geometric_extinction_proved": False,
        "independent_checker_implementation": False,
        "independent_human_review": False,
        "clean_full_dependency_rebuild": False,
        "eligible_complete_original_problem_submission": False,
        "verifier_hashes": {"verify.py": digest(Path(__file__)),
            "../../submissions/jsp-000007-dini-extinction/constant-curvature/scripts/verify.py": digest(HELPER)},
    }
    record.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ["status", "scope", "full_fresh_kernel_replay", "full_poincare_formalization"]}, indent=2))


if __name__ == "__main__":
    main()
