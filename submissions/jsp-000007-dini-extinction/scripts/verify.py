#!/usr/bin/env python3
"""Rebuild and kernel-replay the exact submitted component, not the Poincare theorem."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}


def digest(path: Path) -> dict:
    data = path.read_bytes()
    return {"sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}


def parse_axioms(text: str, names: list[str]) -> dict[str, list[str]]:
    result = {}
    for name in names:
        prefix = "'" + re.escape(name) + "' "
        empty = re.findall(prefix + r"does not depend on any axioms", text)
        filled = re.findall(prefix + r"depends on axioms: \[([^\]]*)\]", text)
        if len(empty) + len(filled) != 1:
            raise ValueError("Missing or duplicate axiom audit: " + name)
        axioms = [] if empty else [s.strip() for s in filled[0].split(",") if s.strip()]
        if set(axioms) - ALLOWED:
            raise ValueError("Non-whitelisted axiom: " + name)
        result[name] = axioms
    return result


def execute(args: list[str], cwd: Path = ROOT, timeout: int = 600) -> subprocess.CompletedProcess:
    with subprocess.Popen(args, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                          text=True, start_new_session=True) as proc:
        try:
            stdout, stderr = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.communicate(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.communicate()
            raise RuntimeError("Verification timed out: " + args[0])
        return subprocess.CompletedProcess(args, proc.returncode, stdout, stderr)


def require_ok(proc: subprocess.CompletedProcess, label: str) -> str:
    if proc.returncode != 0:
        raise RuntimeError(f"{label} failed with exit {proc.returncode}:\n{proc.stdout}\n{proc.stderr}")
    return proc.stdout.strip()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", default="verification-output")
    args = parser.parse_args()
    out = ROOT / args.output
    out.mkdir(parents=True, exist_ok=True)
    cfg = json.loads((ROOT / "verification-config.json").read_text())
    # Invalidate a previous success record before starting another run.
    report_path = out / "verification.json"
    report_path.write_text(json.dumps({"status": "IN_PROGRESS_NOT_VERIFIED"}) + "\n")
    started = datetime.now(timezone.utc).isoformat()
    for relative, expected in cfg["unchanged_files"].items():
        if digest(ROOT / relative)["sha256"] != expected:
            raise RuntimeError("The source differs from the disclosed upstream commit: " + relative)
    version = require_ok(execute(["lake", "env", "lean", "--version"]), "Lean version")
    if f"version {cfg['lean_version']}," not in version or cfg["lean_commit"] not in version:
        raise RuntimeError("Unexpected Lean version: " + version)
    pins = {}
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for dep in manifest["packages"]:
        path = ROOT / ".lake/packages" / dep["name"]
        sha = require_ok(execute(["git", "rev-parse", "HEAD"], path), "dependency pin")
        if sha != dep["rev"]:
            raise RuntimeError("Dependency revision mismatch: " + dep["name"])
        if require_ok(execute(["git", "status", "--porcelain", "--untracked-files=no"], path),
                      "dependency cleanliness"):
            raise RuntimeError("Modified tracked dependency: " + dep["name"])
        pins[dep["name"]] = sha
    if pins.get("mathlib") != cfg["mathlib_commit"]:
        raise RuntimeError("Unexpected Mathlib pin")

    def log(name: str, proc: subprocess.CompletedProcess) -> str:
        text = (proc.stdout + proc.stderr).replace(str(ROOT), "$PROJECT")
        text = text.replace(str(Path.home()), "$HOME")
        (out / name).write_text(text)
        return text

    build = ROOT / ".lake/build"
    if build.is_symlink():
        raise RuntimeError("Refusing to clean a symlinked project build")
    if build.exists():
        shutil.rmtree(build)
    proc = execute(["lake", "--wfail", "build"])
    log("build.log", proc)
    require_ok(proc, "clean project rebuild with warnings as errors")

    local = ROOT / ".lake/validation"
    local.mkdir(parents=True, exist_ok=True)
    names = ["PoincareConjecture." + n for n in cfg["theorems"]]
    audit_file = local / "AxiomAudit.lean"
    audit_file.write_text("import PoincareConjectureTests\n" + "".join(
        "#print axioms " + n + "\n" for n in names))
    proc = execute(["lake", "env", "lean", str(audit_file)])
    text = log("axioms.log", proc)
    require_ok(proc, "explicit axiom inventory")
    axioms = parse_axioms(text, names)

    proc = execute(["lake", "env", "leanchecker", "--verbose", "--fresh", "PoincareConjectureTests"],
                   timeout=900)
    text = log("kernel-replay.log", proc)
    require_ok(proc, "fresh-environment kernel replay")
    if "replaying PoincareConjectureTests with --fresh" not in text:
        raise RuntimeError("No fresh kernel replay confirmation")

    test_source = (ROOT / "PoincareConjectureTests.lean").read_text()
    if test_source.count("run_cmd do\n") != 1:
        raise RuntimeError("Changed audit boundary in regression module")
    fixtures = {
        "extra_axiom": (test_source.replace("run_cmd do\n",
            "axiom PoincareConjecture.auditSentinel : False\n\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareConjecture.auditSentinel"),
        "placeholder": (test_source.replace("run_cmd do\n",
            "theorem PoincareConjecture.auditSentinel : False := by sorry\n\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "false_initial_value": ("import PoincareConjecture.Extinction.ScalarBarrier\n"
            "example : PoincareConjecture.extinctionBarrier 0 0 0 = 1 := by\n"
            "  simpa using PoincareConjecture.extinctionBarrier_initial (s := 0) (by norm_num) 0\n",
            "error:"),
    }
    negatives = {}
    for label, (source, expected_error) in fixtures.items():
        fixture = local / (label + ".lean")
        fixture.write_text(source)
        proc = execute(["lake", "env", "lean", str(fixture)])
        text = log(label + ".log", proc)
        if proc.returncode == 0 or expected_error not in text:
            raise RuntimeError("Negative control was not rejected as expected: " + label)
        negatives[label] = {"status": "REJECTED", "exit_code": proc.returncode}

    files = {f: digest(ROOT / f) for f in cfg["unchanged_files"]}
    for f in ["verification-config.json", "scripts/verify.py"]:
        files[f] = digest(ROOT / f)
    report = {
        "status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED", "problem_id": cfg["problem_id"],
        "scope": cfg["scope"], "started_at_utc": started,
        "completed_at_utc": datetime.now(timezone.utc).isoformat(), "lean_version": version,
        "source_upstream_commit": cfg["upstream_commit"], "source_files_unchanged": True,
        "dependency_pins": pins, "clean_project_rebuild": True, "warnings_as_errors": True,
        "full_fresh_kernel_replay": True, "independent_checker_implementation": False,
        "independent_human_review": False, "full_dependency_source_rebuild": False,
        "axioms": axioms, "audited_production_theorems": len(axioms),
        "namespace_wide_audit_in_default_build": True, "negative_controls": negatives,
        "files": files, "full_poincare_formalization": False,
        "award_eligibility": "UNDETERMINED", "novel_mathematical_discovery": False,
        "formalization_priority": "NOT_ESTABLISHED",
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
