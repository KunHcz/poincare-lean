#!/usr/bin/env python3
"""Check the immutable upstream topology extension without replacing this package's sources.

The original analytic submission remains an independently reproducible snapshot.
This additive verifier checks its extended upstream snapshot and emits separate evidence.
Neither snapshot proves the general topological Poincare theorem.
"""
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

PACKAGE = Path(__file__).resolve().parents[1]
SOURCE_REPOSITORY = "https://github.com/KunHcz/Poincare-Conjecture.git"
SOURCE_COMMIT = "f07c59b825f344fa7577907f2427e0aad47704a1"
MATHLIB_COMMIT = "520045ab14e26149ee970e2e617ca04b09bde5d6"
HATCHER_COMMIT = "bb91a091f0b968f8bbe8d861e025a88d82b161be"
LEAN_COMMIT = "f054605aea4b840552cca2e725580bffd1e1b704"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
KNOWN_WARNING = (
    "warning: HatcherLib/Ch1/Circle.lean:38:0: Definition `unitCircleCov` is a proposition; "
    "use `theorem` instead of `def`"
)


def run(args: list[str], cwd: Path, timeout: int = 900) -> subprocess.CompletedProcess:
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "2"
    with subprocess.Popen(args, cwd=cwd, env=env, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, text=True, start_new_session=True) as proc:
        try:
            output, _ = proc.communicate(timeout=timeout)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGTERM)
            try:
                proc.communicate(timeout=10)
            except subprocess.TimeoutExpired:
                os.killpg(proc.pid, signal.SIGKILL)
                proc.communicate()
            raise RuntimeError("Verification timed out: " + args[0])
    return subprocess.CompletedProcess(args, proc.returncode, output, "")


def checked(args: list[str], cwd: Path) -> str:
    proc = run(args, cwd)
    if proc.returncode:
        raise RuntimeError(f"Command failed ({proc.returncode}): {proc.stdout}")
    return proc.stdout.strip()


def parse_axioms(text: str, names: list[str]) -> dict[str, list[str]]:
    result = {}
    for name in names:
        prefix = "'" + re.escape(name) + r"'\s+"
        empty = re.findall(prefix + r"does not depend on any axioms", text)
        filled = re.findall(prefix + r"depends on axioms:\s*\[([^\]]*)\]", text)
        if len(empty) + len(filled) != 1:
            raise ValueError("Missing or duplicate axiom result: " + name)
        axioms = [] if empty else [a.strip() for a in filled[0].split(",") if a.strip()]
        if set(axioms) - ALLOWED:
            raise ValueError("Nonstandard axiom in " + name)
        result[name] = axioms
    return result


def check_diagnostics(text: str) -> list[str]:
    # Handle both Lake's prefix format and Lean's filename-prefixed diagnostics.
    if re.search(r"(?:^|:\s)error(?:\([^)]*\))?:", text, re.M):
        raise ValueError("Lean error in successful-command output")
    warnings = []
    for line in text.splitlines():
        if re.search(r"(?:^|:\s)warning(?:\([^)]*\))?:", line):
            if line != KNOWN_WARNING:
                raise ValueError("Unexpected warning: " + line)
            warnings.append(line)
    return warnings


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkout", type=Path,
                        help="Existing clean repository at the exact source commit")
    parser.add_argument("--output", type=Path,
                        default=PACKAGE / "verification-output/topology-extension")
    options = parser.parse_args()
    out = options.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report_path = out / "verification.json"
    report_path.write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    started = datetime.now(timezone.utc).isoformat()
    checkout = (options.checkout or PACKAGE / ".lake/topology-extension-source").resolve()
    if not checkout.exists():
        checkout.parent.mkdir(parents=True, exist_ok=True)
        checked(["git", "clone", "--no-checkout", SOURCE_REPOSITORY, str(checkout)], checkout.parent)
        checked(["git", "checkout", "--detach", SOURCE_COMMIT], checkout)
    if checked(["git", "rev-parse", "HEAD"], checkout) != SOURCE_COMMIT:
        raise RuntimeError("Wrong source revision; existing checkouts are not modified")
    if checked(["git", "status", "--porcelain", "--untracked-files=no"], checkout):
        raise RuntimeError("Tracked source changes are not allowed")
    project = checkout / "PoincareConjecture"

    def log(label: str, proc: subprocess.CompletedProcess) -> str:
        output = proc.stdout.replace(str(checkout), "$CHECKOUT").replace(str(Path.home()), "$HOME")
        (out / (label + ".log")).write_text(output)
        return output

    version = checked(["lake", "env", "lean", "--version"], project)
    if "version 4.32.1," not in version or LEAN_COMMIT not in version:
        raise RuntimeError("Unexpected Lean compiler: " + version)
    setup = run(["lake", "exe", "cache", "get"], project)
    log("dependency-setup", setup)
    if setup.returncode:
        raise RuntimeError("Dependency setup failed")
    pins = {}
    manifest = json.loads((project / "lake-manifest.json").read_text())
    for dependency in manifest["packages"]:
        path = project / ".lake/packages" / dependency["name"]
        actual = checked(["git", "rev-parse", "HEAD"], path)
        if actual != dependency["rev"]:
            raise RuntimeError("Dependency pin mismatch: " + dependency["name"])
        if checked(["git", "status", "--porcelain", "--untracked-files=no"], path):
            raise RuntimeError("Modified dependency: " + dependency["name"])
        pins[dependency["name"]] = actual
    if pins.get("mathlib") != MATHLIB_COMMIT or pins.get("HatcherLib") != HATCHER_COMMIT:
        raise RuntimeError("Unexpected mathematical dependency")
    proc = run(["lake", "build"], project)
    text = log("build", proc)
    if proc.returncode:
        raise RuntimeError("Default build failed")
    warnings = check_diagnostics(text)

    names = []
    for path in sorted((project / "PoincareConjecture").rglob("*.lean")):
        names += ["PoincareConjecture." + n for n in re.findall(
            r"^(?:@\[simp\]\s+)?theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)", path.read_text(), re.M)]
    if len(names) != 45 or len(set(names)) != 45:
        raise RuntimeError("The pinned declaration inventory changed")
    local = project / ".lake/topology-extension-validation"
    local.mkdir(parents=True, exist_ok=True)
    audit = local / "Audit.lean"
    audit.write_text("import PoincareConjectureTests\n" +
                     "".join("#print axioms " + n + "\n" for n in names))
    proc = run(["lake", "env", "lean", str(audit)], project)
    text = log("axioms", proc)
    if proc.returncode:
        raise RuntimeError("Axiom audit failed")
    axioms = parse_axioms(text, names)
    proc = run(["lake", "env", "leanchecker", "--verbose", "--fresh",
                "PoincareConjectureTests"], project, timeout=1200)
    text = log("kernel-replay", proc)
    if proc.returncode or "replaying PoincareConjectureTests with --fresh" not in text:
        raise RuntimeError("Fresh-environment kernel replay failed")

    tests = (project / "PoincareConjectureTests.lean").read_text()
    if tests.count("run_cmd do\n") != 1:
        raise RuntimeError("Unexpected audit placement")
    finite = (project / "PoincareConjecture/Topology/FiniteQuotient.lean").read_text()
    if "[IsCancelSMul G E]" not in finite:
        raise RuntimeError("Unexpected finite quotient source")
    negatives = {}
    fixtures = {
        "extra_axiom": (tests.replace("run_cmd do\n",
            "axiom PoincareConjecture.sentinel : False\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareConjecture.sentinel"),
        "placeholder": (tests.replace("run_cmd do\n",
            "theorem PoincareConjecture.sentinel : False := by sorry\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "removed_freeness": (finite.replace("[IsCancelSMul G E]", ""), "IsCancelSMul G E"),
    }
    for label, (source, expected) in fixtures.items():
        fixture = local / (label + ".lean")
        fixture.write_text(source)
        proc = run(["lake", "env", "lean", str(fixture)], project)
        text = log(label, proc)
        if not proc.returncode or expected not in text or not re.search(r"error(?:\([^)]*\))?:", text):
            raise RuntimeError("Negative control not rejected: " + label)
        negatives[label] = {"status": "REJECTED", "exit_code": proc.returncode}

    if checked(["git", "rev-parse", "HEAD"], checkout) != SOURCE_COMMIT or checked(
            ["git", "status", "--porcelain", "--untracked-files=no"], checkout):
        raise RuntimeError("Source changed during verification")
    tracked = checked(["git", "ls-tree", "-r", "--name-only", SOURCE_COMMIT,
                       "PoincareConjecture"], checkout).splitlines()
    files = {}
    for relative in tracked:
        if relative.endswith(".lean") or Path(relative).name in {
                "lean-toolchain", "lake-manifest.json", "TOPOLOGY_VALIDATION.md"}:
            raw = (checkout / relative).read_bytes()
            files[relative] = {"sha256": hashlib.sha256(raw).hexdigest(), "bytes": len(raw)}
    report = {
        "status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED", "problem_id": "JSP-000007",
        "source_repository": SOURCE_REPOSITORY, "source_commit": SOURCE_COMMIT,
        "source_checkout_clean_before_and_after": True,
        "started_at_utc": started, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version, "dependency_pins": pins, "default_build_pass": True,
        "clean_from_scratch_build": False, "pinned_dependency_style_warnings": warnings,
        "full_fresh_kernel_replay": True, "independent_checker_implementation": False,
        "independent_human_review": False, "full_dependency_source_rebuild": False,
        "audited_production_theorems": len(axioms), "axioms": axioms,
        "namespace_wide_audit_in_default_build": True, "negative_controls": negatives,
        "files": files, "full_poincare_formalization": False,
        "award_eligibility": "UNDETERMINED", "formalization_priority": "NOT_ESTABLISHED",
        "scope": "Three analytic and three topological endgame blueprint components; not full closure.",
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ["status", "source_commit", "audited_production_theorems",
                                           "full_fresh_kernel_replay", "full_poincare_formalization"]}, indent=2))


if __name__ == "__main__":
    main()
