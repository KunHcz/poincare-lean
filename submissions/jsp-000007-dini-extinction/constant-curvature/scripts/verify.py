#!/usr/bin/env python3
"""Verify the constant-positive-curvature case, not unrestricted Poincare."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LEAN_COMMIT = "819816b2e0a3bf405af45ae5c7af2491d8f5bee6"
GEOMETRY_COMMIT = "1b535dd102b94cc42b107cca27059687888f08b3"
MATHLIB_COMMIT = "0df444a360eaa60ab8c11dca51a86af692955474"
DECLARATIONS = [
    "PoincareHamilton.roundQuotient_proj_surjective",
    "PoincareHamilton.roundQuotient_mfderiv_surjective",
    "PoincareHamilton.roundQuotient_proj_localDiffeomorph",
    "PoincareHamilton.roundQuotientDiffeomorph",
    "PoincareHamilton.diffeomorph_sphere_of_sphericalSpaceForm",
    "PoincareHamilton.constantPositiveCurvature_poincare",
    "PoincareHamilton.constantPositiveCurvature_homeomorph_sphere",
    "DifferentialGeometry.Geometry.constant_positive_sectional_curvature_implies_spherical_space_form",
    "PoincareHamiltonTests.literal_metric_endpoint",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_axioms(text: str, names: list[str]) -> dict[str, list[str]]:
    result = {}
    for name in names:
        prefix = "'" + re.escape(name) + r"'\s+"
        empty = re.findall(prefix + "does not depend on any axioms", text)
        filled = re.findall(prefix + r"depends on axioms:\s*\[([^\]]*)\]", text)
        if len(empty) + len(filled) != 1:
            raise ValueError("Missing or duplicated audit for " + name)
        axioms = [] if empty else [a.strip() for a in filled[0].split(",") if a.strip()]
        if set(axioms) - ALLOWED:
            raise ValueError("Nonstandard axiom for " + name)
        result[name] = axioms
    return result


def run(args: list[str], cwd: Path = ROOT, timeout: int = 1200) -> subprocess.CompletedProcess:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "2"
    with subprocess.Popen(args, cwd=cwd, env=env, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, start_new_session=True) as proc:
        try:
            output, _ = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.communicate()
            raise RuntimeError("Timed out: " + args[0])
    return subprocess.CompletedProcess(args, proc.returncode, output, "")


def checked(args: list[str], cwd: Path = ROOT) -> str:
    proc = run(args, cwd)
    if proc.returncode:
        raise RuntimeError("Command failed: " + proc.stdout)
    return proc.stdout.strip()


def source_inventory() -> dict[str, str]:
    files = [p for p in ROOT.rglob("*.lean") if ".lake" not in p.relative_to(ROOT).parts]
    files += [ROOT / n for n in ("lean-toolchain", "lakefile.toml", "lake-manifest.json")]
    return {str(p.relative_to(ROOT)): sha256(p) for p in sorted(files)}


def dependency_inventory() -> dict[str, str]:
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    pins = {}
    for dep in manifest["packages"]:
        if dep["type"] != "git":
            raise RuntimeError("An unpinned local dependency is not permitted")
        path = ROOT / ".lake/packages" / dep["name"]
        revision = checked(["git", "rev-parse", "HEAD"], path)
        if revision != dep["rev"] or checked(
                ["git", "status", "--porcelain", "--untracked-files=no"], path):
            raise RuntimeError("Dependency changed: " + dep["name"])
        pins[dep["name"]] = revision
    if pins.get("DifferentialGeometry") != GEOMETRY_COMMIT or pins.get("mathlib") != MATHLIB_COMMIT:
        raise RuntimeError("Unexpected mathematical dependency pins")
    return pins


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "verification-output")
    out = parser.parse_args().output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report_path = out / "verification.json"
    report_path.write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    started = datetime.now(timezone.utc).isoformat()
    source_before = source_inventory()
    expected = json.loads((ROOT / "source-manifest.json").read_text())
    if source_before != expected["files"]:
        raise RuntimeError("Source differs from the submitted manifest")
    version = checked(["lake", "env", "lean", "--version"])
    if "version 4.33.1," not in version or LEAN_COMMIT not in version:
        raise RuntimeError("Unexpected Lean compiler")
    pins = dependency_inventory()

    def log(label: str, proc: subprocess.CompletedProcess, success: bool = True) -> str:
        text = proc.stdout.replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")
        (out / (label + ".log")).write_text(text)
        if success and proc.returncode:
            raise RuntimeError(label + " failed; see its log")
        return text

    log("build", run(["lake", "--wfail", "build"]))
    local = ROOT / ".lake/verification"
    local.mkdir(parents=True, exist_ok=True)
    audit = local / "Declarations.lean"
    audit.write_text("import PoincareHamiltonAudit\n" +
                     "".join("#print axioms " + name + "\n" for name in DECLARATIONS))
    axioms = parse_axioms(log("axioms", run(["lake", "env", "lean", str(audit)])), DECLARATIONS)

    replay = run(["lake", "env", "leanchecker", "--verbose", "--fresh", "PoincareHamiltonAudit"])
    text = log("kernel-replay", replay)
    if "replaying PoincareHamiltonAudit with --fresh" not in text:
        raise RuntimeError("No fresh-environment replay confirmation")

    gate = (ROOT / "PoincareHamiltonAudit.lean").read_text()
    if gate.count("run_cmd do\n") != 1:
        raise RuntimeError("Unexpected final audit boundary")
    source = (ROOT / "PoincareHamilton/SphericalSpaceForm.lean").read_text()
    original = "    (hconst : admitsConstantPositiveSectionalCurvature (I := 𝓡 3) (M := M)) :"
    if source.count(original) != 2:
        raise RuntimeError("Unexpected endpoint hypotheses")
    fixtures = {
        "extra_axiom": (gate.replace("run_cmd do\n",
            "axiom PoincareHamilton.sentinel : False\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareHamilton.sentinel"),
        "placeholder": (gate.replace("run_cmd do\n",
            "theorem PoincareHamilton.sentinel : False := by sorry\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "missing_curvature": (source.replace(original, "    :", 1), "hconst"),
        "missing_simple_connectivity": (source.replace("[SimplyConnectedSpace M]", ""),
                                        "SimplyConnectedSpace"),
    }
    negatives = {}
    for label, (source, diagnostic) in fixtures.items():
        fixture = local / (label + ".lean")
        fixture.write_text(source)
        proc = run(["lake", "env", "lean", str(fixture)])
        text = log(label, proc, success=False)
        if not proc.returncode or diagnostic not in text or not re.search(r"error(?:\([^)]*\))?:", text):
            raise RuntimeError("Negative control was not correctly rejected: " + label)
        negatives[label] = {"status": "REJECTED", "exit_code": proc.returncode}

    if source_inventory() != source_before or dependency_inventory() != pins:
        raise RuntimeError("Source or dependencies changed during verification")
    report = {
        "status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED", "problem_id": "JSP-000007",
        "scope": "Closed simply connected smooth three-manifolds admitting a genuine constant-positive-sectional-curvature metric",
        "full_poincare_formalization": False, "positive_ricci_case_verified": False,
        "started_at_utc": started, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version, "dependency_pins": pins, "source_files": source_before,
        "default_build_pass": True, "warnings_as_errors": True, "from_scratch_build": False,
        "full_fresh_kernel_replay": True, "independent_checker_implementation": False,
        "independent_human_review": False, "full_dependency_source_rebuild": False,
        "key_declarations": DECLARATIONS, "axioms": axioms,
        "namespace_wide_audit": True, "regression_theorems": 5,
        "negative_controls": negatives, "award_eligibility": "UNDETERMINED",
        "novel_mathematical_discovery": False, "formalization_priority": "NOT_ESTABLISHED",
        "verifier_sha256": sha256(Path(__file__)),
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in (
        "status", "scope", "default_build_pass", "full_fresh_kernel_replay", "full_poincare_formalization")}, indent=2))


if __name__ == "__main__":
    main()
