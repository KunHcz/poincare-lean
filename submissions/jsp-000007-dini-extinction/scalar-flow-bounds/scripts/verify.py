#!/usr/bin/env python3
"""Verify geometric scalar estimates; do not claim existence of surgery or Poincare closure."""
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
SPEC = importlib.util.spec_from_file_location("scalar_flow_verification_helpers", HELPER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("The immutable shared verifier helper is missing")
shared = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(shared)
GEOMETRY_COMMIT = "ad76f2f1dfb959f4d8fc46fac9ed9feffdf497d9"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked(args: list[str], cwd: Path) -> str:
    proc = shared.run(args, cwd, timeout=300)
    if proc.returncode:
        raise RuntimeError("Command failed: " + proc.stdout)
    return proc.stdout.strip()


def sources() -> dict[str, str]:
    expected = json.loads((ROOT / "source-manifest.json").read_text())["files"]
    actual = {rel: digest(ROOT / rel) for rel in expected}
    if actual != expected:
        raise RuntimeError("Source differs from the submitted manifest")
    lean = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*.lean")
            if ".lake" not in p.relative_to(ROOT).parts}
    if lean != {rel for rel in expected if rel.endswith(".lean")}:
        raise RuntimeError("Unexpected Lean source inventory")
    return actual


def dependencies() -> dict[str, str]:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    pins = {}
    for dep in manifest["packages"]:
        if dep["type"] != "git":
            raise RuntimeError("Unpinned local dependency")
        path = ROOT / ".lake/packages" / dep["name"]
        pin = checked(["git", "rev-parse", "HEAD"], path)
        if pin != dep["rev"] or checked(
                ["git", "status", "--porcelain", "--untracked-files=no"], path):
            raise RuntimeError("Changed dependency: " + dep["name"])
        pins[dep["name"]] = pin
    if pins.get("DifferentialGeometry") != GEOMETRY_COMMIT or pins.get("mathlib") != shared.MATHLIB_COMMIT:
        raise RuntimeError("Unexpected mathematical dependency pins")
    return pins


def sanitize(text: str) -> str:
    return text.replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")


def stop(proc: subprocess.Popen) -> None:
    if proc.poll() is None:
        os.killpg(proc.pid, signal.SIGTERM)
        try:
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()


def replay(out: Path, timeout: int, memory_mb: int) -> dict:
    started = time.monotonic()
    peak = 0
    guard = None
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "2"
    logfile = out / "kernel-replay.log"
    with logfile.open("w") as log:
        proc = subprocess.Popen(["lake", "env", "leanchecker", "--verbose", "--fresh",
                                 "ScalarFlowBoundsAudit"], cwd=ROOT, env=env,
                                stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while proc.poll() is None:
                listing = subprocess.check_output(["ps", "-axo", "pgid=,rss="], text=True)
                rss = sum(int(parts[1]) for line in listing.splitlines()
                          if len(parts := line.split()) == 2 and int(parts[0]) == proc.pid)
                peak = max(peak, rss)
                elapsed = time.monotonic() - started
                (out / "progress.json").write_text(json.dumps({"status": "RUNNING_NOT_VERIFIED",
                    "elapsed_seconds": round(elapsed), "rss_kib": rss, "peak_rss_kib": peak}, indent=2) + "\n")
                if elapsed > timeout or rss > memory_mb * 1024:
                    guard = "TIME_GUARD" if elapsed > timeout else "MEMORY_GUARD"
                    stop(proc)
                    break
                time.sleep(3)
            code = proc.wait()
        except BaseException:
            stop(proc)
            raise
    text = sanitize(logfile.read_text())
    logfile.write_text(text)
    result = {"exit_code": code, "elapsed_seconds": round(time.monotonic() - started, 2),
              "peak_rss_kib": peak, "memory_limit_mb": memory_mb, "guard": guard}
    (out / "kernel-replay-process.json").write_text(json.dumps(result, indent=2) + "\n")
    if guard or code or "replaying ScalarFlowBoundsAudit with --fresh" not in text:
        raise RuntimeError("Full root kernel replay did not complete successfully")
    return result


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "verification-output")
    parser.add_argument("--replay-timeout", type=int, default=1800)
    parser.add_argument("--memory-limit-mb", type=int, default=24576)
    options = parser.parse_args()
    if options.replay_timeout <= 0 or options.memory_limit_mb <= 0:
        parser.error("Resource limits must be positive")
    out = options.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report = out / "verification.json"
    report.write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    started = datetime.now(timezone.utc).isoformat()
    before = sources()
    pins = dependencies()
    version = checked(["lake", "env", "lean", "--version"], ROOT)
    if "version 4.33.1," not in version or shared.LEAN_COMMIT not in version:
        raise RuntimeError("Unexpected Lean compiler")
    proc = shared.run(["lake", "--wfail", "build"], ROOT, timeout=1200)
    (out / "build.log").write_text(sanitize(proc.stdout))
    if proc.returncode:
        raise RuntimeError("Default warning-as-error build failed")
    names = ["PoincareScalarFlow." + n for n in re.findall(
        r"^theorem (\w+)", (ROOT / "ScalarFlowBounds.lean").read_text(), re.M)]
    tests = ["PoincareScalarFlowTests." + n for n in re.findall(
        r"^theorem (\w+)", (ROOT / "ScalarFlowBoundsTests.lean").read_text(), re.M)]
    if len(names) != 13 or len(tests) != 8:
        raise RuntimeError("The submitted theorem inventory changed")
    local = ROOT / ".lake/verification"
    local.mkdir(parents=True, exist_ok=True)
    audit = local / "Audit.lean"
    audit.write_text("import ScalarFlowBoundsAudit\n" +
                     "".join("#print axioms " + n + "\n" for n in names + tests))
    proc = shared.run(["lake", "env", "lean", str(audit)], ROOT, timeout=300)
    text = sanitize(proc.stdout)
    (out / "axioms.log").write_text(text)
    if proc.returncode:
        raise RuntimeError("Explicit axiom audit failed")
    axioms = shared.parse_axioms(text, names + tests)
    process = replay(out, options.replay_timeout, options.memory_limit_mb)
    gate = (ROOT / "ScalarFlowBoundsAudit.lean").read_text()
    source = (ROOT / "ScalarFlowBounds.lean").read_text()
    if gate.count("run_cmd do\n") != 1 or "hS : IsSolutionOn" not in source:
        raise RuntimeError("Unexpected proof/audit structure")
    fixtures = {
        "extra_axiom": (gate.replace("run_cmd do\n",
            "axiom PoincareScalarFlow.sentinel : False\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareScalarFlow.sentinel"),
        "placeholder": (gate.replace("run_cmd do\n",
            "theorem PoincareScalarFlow.sentinel : False := by sorry\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "not_a_ricci_solution": (source.replace("hS : IsSolutionOn (I := 𝓡 3) S", "hS : True"),
                                "hS"),
        "missing_initial_bound": (source.replace("    (hinit : ∀ x : M, -6 ≤ S.scalar 0 x)\n", ""),
                                  "hinit"),
        "wrong_barrier_value": ("import ScalarFlowBounds\n"
            "example : DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier 3 (-6) 1 = -6 := by\n"
            "  norm_num [DifferentialGeometry.PDE.RicciFlow.scalarLowerBarrier]\n", "unsolved goals"),
    }
    negatives = {}
    for label, (content, diagnostic) in fixtures.items():
        path = local / (label + ".lean")
        path.write_text(content)
        proc = shared.run(["lake", "env", "lean", str(path)], ROOT, timeout=300)
        text = sanitize(proc.stdout)
        (out / (label + ".log")).write_text(text)
        if not proc.returncode or diagnostic not in text or not re.search(r"error(?:\([^)]*\))?:", text):
            raise RuntimeError("Negative control was not rejected: " + label)
        negatives[label] = {"status": "REJECTED", "exit_code": proc.returncode}
    if sources() != before or dependencies() != pins:
        raise RuntimeError("Source or dependency changed during verification")
    result = {"status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED", "problem_id": "JSP-000007",
        "scope": "Geometric scalar lower bounds and global-clock restart for compact smooth three-dimensional Ricci flows",
        "started_at_utc": started, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version, "source_files": before, "dependency_pins": pins,
        "production_theorems": names, "regression_theorems": tests, "axioms": axioms,
        "namespace_wide_audit": True, "default_build_pass": True, "warnings_as_errors": True,
        "full_fresh_kernel_replay": True, "replay_process": process, "negative_controls": negatives,
        "source_and_dependency_pins_clean_before_and_after": True,
        "independent_checker_implementation": False, "independent_human_review": False,
        "clean_from_scratch_build": False, "full_dependency_source_rebuild": False,
        "concrete_ricci_flow_model_constructed": False, "positive_curvature_assumed": False,
        "flow_existence_proved": False, "surgery_scalar_preservation_proved": False,
        "full_poincare_formalization": False, "novel_mathematical_discovery": False,
        "award_eligibility": "UNDETERMINED", "formalization_priority": "NOT_ESTABLISHED",
        "verifier_hashes": {"scripts/verify.py": digest(Path(__file__)),
            "../constant-curvature/scripts/verify.py": digest(HELPER)}}
    report.write_text(json.dumps(result, indent=2) + "\n")
    (out / "progress.json").write_text('{"status":"COMPLETED_SEE_VERIFICATION_RECORD"}\n')
    print(json.dumps({k: result[k] for k in ("status", "scope", "full_fresh_kernel_replay",
                                            "full_poincare_formalization")}, indent=2))


if __name__ == "__main__":
    main()
