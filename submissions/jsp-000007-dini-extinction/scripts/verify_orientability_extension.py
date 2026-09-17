#!/usr/bin/env python3
"""Verify the pinned orientability extension without replacing earlier snapshots."""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re

import verify_topology_extension as shared

SOURCE_COMMIT = "d5cf293fcee9164a449fcc833d049d51aab52bc3"
PREVIOUS_COMMIT = "f07c59b825f344fa7577907f2427e0aad47704a1"
SOURCE_FILES = [
    "PoincareConjecture/Topology/OrientationCover.lean",
    "PoincareConjecture/Geometry/Orientability.lean",
]


def hash_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_pins(project: Path) -> dict[str, str]:
    manifest = json.loads((project / "lake-manifest.json").read_text())
    pins = {}
    for dep in manifest["packages"]:
        if dep["type"] != "git":
            raise RuntimeError("Unpinned dependency")
        path = project / ".lake/packages" / dep["name"]
        pin = shared.checked(["git", "rev-parse", "HEAD"], path)
        if pin != dep["rev"] or shared.checked(
                ["git", "status", "--porcelain", "--untracked-files=no"], path):
            raise RuntimeError("Dependency changed: " + dep["name"])
        pins[dep["name"]] = pin
    if pins.get("mathlib") != shared.MATHLIB_COMMIT or pins.get("HatcherLib") != shared.HATCHER_COMMIT:
        raise RuntimeError("Unexpected mathematical dependencies")
    return pins


def check_checkout(checkout: Path) -> None:
    if shared.checked(["git", "rev-parse", "HEAD"], checkout) != SOURCE_COMMIT:
        raise RuntimeError("Wrong source commit; existing checkouts are not modified")
    if shared.checked(["git", "status", "--porcelain", "--untracked-files=no"], checkout):
        raise RuntimeError("Tracked source changes are not allowed")


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkout", type=Path)
    parser.add_argument("--output", type=Path,
                        default=shared.PACKAGE / "verification-output/orientability-extension")
    options = parser.parse_args()
    out = options.output.resolve()
    out.mkdir(parents=True, exist_ok=True)
    report_path = out / "verification.json"
    report_path.write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    started = datetime.now(timezone.utc).isoformat()
    checkout = (options.checkout or shared.PACKAGE / ".lake/orientability-extension-source").resolve()
    if not checkout.exists():
        checkout.parent.mkdir(parents=True, exist_ok=True)
        shared.checked(["git", "clone", "--no-checkout", shared.SOURCE_REPOSITORY, str(checkout)],
                       checkout.parent)
        shared.checked(["git", "checkout", "--detach", SOURCE_COMMIT], checkout)
    check_checkout(checkout)
    project = checkout / "PoincareConjecture"

    def log(label: str, proc) -> str:
        text = proc.stdout.replace(str(checkout), "$CHECKOUT").replace(str(Path.home()), "$HOME")
        (out / (label + ".log")).write_text(text)
        return text

    version = shared.checked(["lake", "env", "lean", "--version"], project)
    if "version 4.32.1," not in version or shared.LEAN_COMMIT not in version:
        raise RuntimeError("Unexpected Lean compiler")
    proc = shared.run(["lake", "exe", "cache", "get"], project)
    log("dependency-setup", proc)
    if proc.returncode:
        raise RuntimeError("Dependency setup failed")
    pins = check_pins(project)
    target = "PoincareConjecture/PoincareConjecture/Topology/Statement.lean"
    if shared.checked(["git", "diff", PREVIOUS_COMMIT, SOURCE_COMMIT, "--", target], checkout):
        raise RuntimeError("The unrestricted Poincare target was changed")

    proc = shared.run(["lake", "build"], project)
    text = log("build", proc)
    if proc.returncode:
        raise RuntimeError("Default build failed")
    warnings = shared.check_diagnostics(text)
    names = []
    for p in sorted((project / "PoincareConjecture").rglob("*.lean")):
        names += ["PoincareConjecture." + n for n in re.findall(
            r"^(?:@\[simp\]\s+)?theorem\s+([A-Za-z_][A-Za-z0-9_'.]*)", p.read_text(), re.M)]
    new_names = ["PoincareConjecture." + n for rel in SOURCE_FILES for n in
                 re.findall(r"^theorem (\w+)", (project / rel).read_text(), re.M)]
    if len(names) != 60 or len(set(names)) != 60 or len(new_names) != 15:
        raise RuntimeError("The fixed theorem inventory changed")
    local = project / ".lake/orientability-extension-validation"
    local.mkdir(parents=True, exist_ok=True)
    audit = local / "Audit.lean"
    audit.write_text("import PoincareConjectureTests\n" +
                     "".join("#print axioms " + n + "\n" for n in names))
    proc = shared.run(["lake", "env", "lean", str(audit)], project)
    text = log("axioms", proc)
    if proc.returncode:
        raise RuntimeError("Axiom audit failed")
    axioms = shared.parse_axioms(text, names)
    proc = shared.run(["lake", "env", "leanchecker", "--verbose", "--fresh",
                       "PoincareConjectureTests"], project, timeout=1500)
    text = log("kernel-replay", proc)
    if proc.returncode or "replaying PoincareConjectureTests with --fresh" not in text:
        raise RuntimeError("Fresh root kernel replay failed")

    gate = (project / "PoincareConjectureTests.lean").read_text()
    cover = (project / SOURCE_FILES[0]).read_text()
    sign_definition = "def orientationChange (d : ℝ) (s : Bool) : Bool := if 0 < d then s else !s"
    if gate.count("run_cmd do\n") != 1 or cover.count(sign_definition) != 1:
        raise RuntimeError("Unexpected source or audit boundary")
    fixtures = {
        "extra_axiom": (gate.replace("run_cmd do\n",
            "axiom PoincareConjecture.orientationSentinel : False\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareConjecture.orientationSentinel"),
        "placeholder": (gate.replace("run_cmd do\n",
            "theorem PoincareConjecture.orientationSentinel : False := by sorry\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "removed_simple_connectivity": (cover.replace("[SimplyConnectedSpace B]", ""),
                                        "SimplyConnectedSpace"),
        "no_sign_reversal": (cover.replace(sign_definition,
            "def orientationChange (_d : ℝ) (s : Bool) : Bool := s"), "unsolved goals"),
    }
    negatives = {}
    for label, (source, diagnostic) in fixtures.items():
        path = local / (label + ".lean")
        path.write_text(source)
        proc = shared.run(["lake", "env", "lean", str(path)], project)
        text = log(label, proc)
        if not proc.returncode or diagnostic not in text or not re.search(r"error(?:\([^)]*\))?:", text):
            raise RuntimeError("Negative control was not rejected: " + label)
        if label == "no_sign_reversal" and "d < 0" not in text:
            raise RuntimeError("Sign mutation did not expose the negative-determinant case")
        negatives[label] = {"status": "REJECTED", "exit_code": proc.returncode}

    check_checkout(checkout)
    if check_pins(project) != pins:
        raise RuntimeError("Dependencies changed during verification")
    tracked = shared.checked(["git", "ls-tree", "-r", "--name-only", SOURCE_COMMIT,
                              "PoincareConjecture"], checkout).splitlines()
    files = {rel: {"sha256": hash_file(checkout / rel), "bytes": (checkout / rel).stat().st_size}
             for rel in tracked if rel.endswith(".lean") or Path(rel).name in {
                 "lean-toolchain", "lake-manifest.json", "ORIENTABILITY_VALIDATION.md"}}
    report = {
        "status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED", "problem_id": "JSP-000007",
        "source_repository": shared.SOURCE_REPOSITORY, "source_commit": SOURCE_COMMIT,
        "source_and_dependencies_clean_before_and_after": True, "unrestricted_target_unchanged": True,
        "started_at_utc": started, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version, "dependency_pins": pins, "default_build_pass": True,
        "full_fresh_kernel_replay": True, "independent_checker_implementation": False,
        "clean_from_scratch_build": False, "full_dependency_source_rebuild": False,
        "independent_human_review": False, "pinned_dependency_style_warnings": warnings,
        "audited_production_theorems": len(axioms), "new_orientation_theorems": new_names,
        "new_regression_theorems": 7, "namespace_wide_audit": True, "axioms": axioms,
        "negative_controls": negatives, "files": files,
        "blueprint_structure_check": "NOT_PERFORMED_PERMISSION_BLOCKED",
        "verifier_hashes": {"verify_orientability_extension.py": hash_file(Path(__file__)),
                            "verify_topology_extension.py": hash_file(Path(shared.__file__))},
        "scope": "Orientation double cover and positive tangent-frame transitions for simply connected C1 three-manifolds; previous analytic and topology components retained",
        "full_poincare_formalization": False, "award_eligibility": "UNDETERMINED",
        "formalization_priority": "NOT_ESTABLISHED", "novel_mathematical_discovery": False,
    }
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({k: report[k] for k in ("status", "source_commit", "audited_production_theorems",
                                            "full_fresh_kernel_replay", "full_poincare_formalization")}, indent=2))


if __name__ == "__main__":
    main()
