#!/usr/bin/env python3
"""Verify the explicitly positive-Ricci case, never unrestricted Poincare."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
HELPER = ROOT.parent / "constant-curvature/scripts/verify.py"
SPEC = importlib.util.spec_from_file_location("poincare_curvature_verifier", HELPER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("The previously submitted verifier helper is missing")
shared = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(shared)
SOURCE_COMMIT = "ad76f2f1dfb959f4d8fc46fac9ed9feffdf497d9"
ORIGINAL_COMMIT = "1b535dd102b94cc42b107cca27059687888f08b3"
PATCH_FILE = "DifferentialGeometry/Geometry/Curvature/CovGradRoughLap/HomFieldCurvatureJetDecomposition.lean"
DECLARATIONS = [
    "DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_positive_ricci",
    "PoincareHamilton.positiveRicci_poincare",
    "PoincareHamiltonTests.literal_positive_ricci_endpoint",
    "PoincareHamiltonTests.literal_positive_ricci_homeomorph",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked(args: list[str], cwd: Path) -> str:
    proc = shared.run(args, cwd, timeout=300)
    if proc.returncode:
        raise RuntimeError("Command failed: " + proc.stdout)
    return proc.stdout.strip()


def check_pins() -> dict[str, str]:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    pins = {}
    for dep in manifest["packages"]:
        if dep["type"] != "git":
            raise RuntimeError("A local/unpinned dependency is not allowed")
        path = ROOT / ".lake/packages" / dep["name"]
        revision = checked(["git", "rev-parse", "HEAD"], path)
        if revision != dep["rev"] or checked(
                ["git", "status", "--porcelain", "--untracked-files=no"], path):
            raise RuntimeError("Dependency changed: " + dep["name"])
        pins[dep["name"]] = revision
    if pins.get("DifferentialGeometry") != SOURCE_COMMIT or pins.get("mathlib") != shared.MATHLIB_COMMIT:
        raise RuntimeError("Unexpected mathematical dependency")
    geometry = ROOT / ".lake/packages/DifferentialGeometry"
    changed = checked(["git", "diff", "--name-only", ORIGINAL_COMMIT, SOURCE_COMMIT], geometry).splitlines()
    if changed != [PATCH_FILE]:
        raise RuntimeError("The disclosed upstream proof-cost patch changed scope")
    return pins


def check_source() -> dict[str, str]:
    expected = json.loads((ROOT / "source-manifest.json").read_text())["files"]
    result = {rel: sha256(ROOT / rel) for rel in expected}
    if result != expected:
        raise RuntimeError("Source differs from the submitted manifest")
    actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*.lean")
              if ".lake" not in p.relative_to(ROOT).parts}
    if actual != {rel for rel in expected if rel.endswith(".lean")}:
        raise RuntimeError("The Lean source inventory changed")
    return result


def terminate_group(proc: subprocess.Popen) -> None:
    if proc.poll() is None:
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()


def bounded_run(args: list[str], out: Path, label: str, timeout: int,
                memory_limit_mb: int) -> tuple[int, str, dict]:
    start = time.monotonic()
    peak = 0
    reason = None
    log_path = out / (label + ".log")
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "2"
    with log_path.open("w") as log:
        proc = subprocess.Popen(args, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                                start_new_session=True)
        try:
            while proc.poll() is None:
                listing = subprocess.check_output(["ps", "-axo", "pgid=,rss="], text=True)
                rss = sum(int(parts[1]) for line in listing.splitlines()
                          if len(parts := line.split()) == 2 and int(parts[0]) == proc.pid)
                peak = max(peak, rss)
                elapsed = time.monotonic() - start
                progress = {"status": "RUNNING_NOT_VERIFIED", "stage": label,
                            "elapsed_seconds": round(elapsed), "rss_kib": rss,
                            "peak_rss_kib": peak}
                (out / "progress.json").write_text(json.dumps(progress, indent=2) + "\n")
                if elapsed > timeout or rss > memory_limit_mb * 1024:
                    reason = "TIME_GUARD" if elapsed > timeout else "MEMORY_GUARD"
                    terminate_group(proc)
                    break
                time.sleep(3)
            code = proc.wait()
        except BaseException:
            terminate_group(proc)
            raise
    text = log_path.read_text().replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")
    log_path.write_text(text)
    stats = {"exit_code": code, "elapsed_seconds": round(time.monotonic() - start, 2),
             "peak_rss_kib": peak, "memory_limit_mb": memory_limit_mb, "guard": reason}
    (out / (label + "-process.json")).write_text(json.dumps(stats, indent=2) + "\n")
    if reason:
        raise RuntimeError(label + " did not finish: " + reason)
    return code, text, stats


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "verification-output")
    parser.add_argument("--build-timeout", type=int, default=7200)
    parser.add_argument("--replay-timeout", type=int, default=3600)
    parser.add_argument("--memory-limit-mb", type=int, default=24576)
    options = parser.parse_args()
    if min(options.build_timeout, options.replay_timeout, options.memory_limit_mb) <= 0:
        parser.error("Resource limits must be positive")
    out = options.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report_path = out / "verification.json"
    report_path.write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    started = datetime.now(timezone.utc).isoformat()
    source = check_source()
    pins = check_pins()
    version = checked(["lake", "env", "lean", "--version"], ROOT)
    if "version 4.33.1," not in version or shared.LEAN_COMMIT not in version:
        raise RuntimeError("Unexpected Lean compiler")
    code, _, build = bounded_run(["lake", "--wfail", "build"], out, "build",
                                options.build_timeout, options.memory_limit_mb)
    if code:
        raise RuntimeError("Default build failed")
    local = ROOT / ".lake/verification-positive-ricci"
    local.mkdir(parents=True, exist_ok=True)
    audit = local / "AxiomInventory.lean"
    audit.write_text("import PoincareHamiltonAudit\n" +
                     "".join("#print axioms " + name + "\n" for name in DECLARATIONS))
    proc = shared.run(["lake", "env", "lean", str(audit)], ROOT, timeout=600)
    text = proc.stdout.replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")
    (out / "axioms.log").write_text(text)
    if proc.returncode:
        raise RuntimeError("Axiom inventory failed")
    axioms = shared.parse_axioms(text, DECLARATIONS)
    code, text, replay = bounded_run(
        ["lake", "env", "leanchecker", "--verbose", "--fresh", "PoincareHamiltonAudit"],
        out, "kernel-replay", options.replay_timeout, options.memory_limit_mb)
    if code or "replaying PoincareHamiltonAudit with --fresh" not in text:
        raise RuntimeError("Fresh root kernel replay failed")

    gate = (ROOT / "PoincareHamiltonAudit.lean").read_text()
    endpoint = (ROOT / "PoincareHamilton/PositiveRicci.lean").read_text()
    pos = "    (hpos : admitsPositiveRicci (I := 𝓡 3) (M := M)) :"
    if gate.count("run_cmd do\n") != 1 or endpoint.count(pos) != 1:
        raise RuntimeError("Unexpected audit/endpoint boundary")
    fixtures = {
        "extra_axiom": (gate.replace("run_cmd do\n",
            "axiom PoincareHamilton.sentinel : False\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareHamilton.sentinel"),
        "placeholder": (gate.replace("run_cmd do\n",
            "theorem PoincareHamilton.sentinel : False := by sorry\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "missing_positive_ricci": (endpoint.replace(pos, "    :"), "hpos"),
        "missing_simple_connectivity": (endpoint.replace("[SimplyConnectedSpace M]", ""),
                                        "SimplyConnectedSpace"),
    }
    negatives = {}
    for label, (content, diagnostic) in fixtures.items():
        path = local / (label + ".lean")
        path.write_text(content)
        proc = shared.run(["lake", "env", "lean", str(path)], ROOT, timeout=600)
        text = proc.stdout.replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")
        (out / (label + ".log")).write_text(text)
        if not proc.returncode or diagnostic not in text or not re.search(r"error(?:\([^)]*\))?:", text):
            raise RuntimeError("Negative control was not rejected: " + label)
        negatives[label] = {"status": "REJECTED", "exit_code": proc.returncode}
    if check_source() != source or check_pins() != pins:
        raise RuntimeError("Source or dependency changed during verification")
    report = {
        "status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED", "problem_id": "JSP-000007",
        "scope": "Closed simply connected smooth three-manifolds admitting a genuine positive-Ricci metric",
        "full_poincare_formalization": False, "positive_ricci_case_verified": True,
        "started_at_utc": started, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version, "source_files": source, "dependency_pins": pins,
        "upstream_geometry_original_commit": ORIGINAL_COMMIT,
        "upstream_geometry_proof_cost_fix": {"commit": SOURCE_COMMIT,
            "file": PATCH_FILE, "pull_request": "https://github.com/qinz1yang/differential-geometry/pull/78"},
        "default_build_pass": True, "warnings_as_errors": True,
        "full_fresh_kernel_replay": True, "build_process": build, "replay_process": replay,
        "independent_checker_implementation": False, "independent_human_review": False,
        "clean_from_scratch_build": False, "full_dependency_source_rebuild": False,
        "source_and_dependencies_clean_before_and_after": True,
        "axioms": axioms, "namespace_wide_audit": True, "regression_theorems": 3,
        "negative_controls": negatives, "concrete_positive_ricci_model_test": False,
        "verifier_hashes": {"scripts/verify.py": sha256(Path(__file__)),
            "../constant-curvature/scripts/verify.py": sha256(HELPER)},
        "award_eligibility": "UNDETERMINED", "novel_mathematical_discovery": False,
        "formalization_priority": "NOT_ESTABLISHED",
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    (out / "progress.json").write_text('{"status":"COMPLETED_SEE_VERIFICATION_RECORD"}\n')
    print(json.dumps({k: report[k] for k in ("status", "scope", "positive_ricci_case_verified",
                                            "full_fresh_kernel_replay", "full_poincare_formalization")}, indent=2))


if __name__ == "__main__":
    main()
