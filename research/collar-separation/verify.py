#!/usr/bin/env python3
"""Verify collar-derived separation and capping, not unrestricted Poincare."""
from __future__ import annotations

from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import time

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[1]
HELPER = REPOSITORY / "submissions/jsp-000007-dini-extinction/scripts/verify_topology_extension.py"
SPEC = importlib.util.spec_from_file_location("collar_separation_verifier_helpers", HELPER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("The preserved verification helper is missing")
shared = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(shared)
REUSED = ["CapFilling.lean", "PuncturedCap.lean", "AttachmentOpen.lean", "ConnectedCap.lean",
          "HomotopicFactorization.lean", "CappingTheorem.lean", "ClosedCover.lean", "CutSides.lean"]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def input_file(relative: str) -> Path:
    path = (ROOT / relative).resolve()
    if not path.is_relative_to(ROOT.resolve()) or not path.is_file():
        raise ValueError("Missing or escaping source: " + relative)
    return path


def sources() -> dict:
    config = json.loads((ROOT / "source-manifest.json").read_text())
    for relative, expected in config["files"].items():
        if digest(input_file(relative)) != expected:
            raise ValueError("Changed source: " + relative)
    actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*.lean")
              if ".lake" not in p.relative_to(ROOT).parts}
    if actual != {p for p in config["files"] if p.endswith(".lean")}:
        raise ValueError("Unexpected Lean source inventory")
    for relative in REUSED:
        if digest(ROOT / relative) != digest(ROOT.parent / "closed-cover" / relative):
            raise ValueError("A reused immutable proof was modified: " + relative)
    all_names = config["production_theorems"] + config["regression_theorems"]
    if not config["production_theorems"] or not config["regression_theorems"] or len(all_names) != len(set(all_names)):
        raise ValueError("Empty or duplicate theorem inventory")
    return config


def dependencies() -> dict[str, str]:
    pins = {}
    for dep in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]:
        if dep["type"] != "git":
            raise ValueError("Unpinned local dependency")
        path = ROOT / ".lake/packages" / dep["name"]
        pin = shared.checked(["git", "rev-parse", "HEAD"], path)
        if pin != dep["rev"] or shared.checked(
                ["git", "status", "--porcelain", "--untracked-files=no"], path):
            raise ValueError("Changed dependency: " + dep["name"])
        pins[dep["name"]] = pin
    if pins.get("mathlib") != shared.MATHLIB_COMMIT or pins.get("HatcherLib") != shared.HATCHER_COMMIT:
        raise ValueError("Unexpected mathematical dependency pin")
    return pins


def main() -> None:
    out = ROOT / "verification-output"
    out.mkdir(exist_ok=True)
    record = out / "verification.json"
    record.write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    started = datetime.now(timezone.utc).isoformat()
    config, pins = sources(), dependencies()
    script_hash, helper_hash = digest(Path(__file__)), digest(HELPER)
    version = shared.checked(["lake", "env", "lean", "--version"], ROOT)
    if "version 4.32.1," not in version or shared.LEAN_COMMIT not in version:
        raise ValueError("Unexpected Lean compiler")

    def run(label: str, command: list[str], error: str | None = None, timeout: int = 900) -> str:
        proc = shared.run(command, ROOT, timeout=timeout)
        text = proc.stdout.replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")
        (out / (label + ".log")).write_text(text)
        if error is None:
            if proc.returncode:
                raise RuntimeError(label + " failed; see its log")
        elif not proc.returncode or error not in text or not re.search(r"error(?:\([^)]*\))?:", text):
            raise RuntimeError("Negative control was not rejected: " + label)
        return text

    warnings = shared.check_diagnostics(run("build", ["lake", "build"]))
    local = ROOT / ".lake/verification"
    local.mkdir(parents=True, exist_ok=True)
    names = config["production_theorems"] + config["regression_theorems"]
    audit = local / "Inventory.lean"
    audit.write_text("import SeparationAudit\n" + "".join("#print axioms " + n + "\n" for n in names))
    axioms = shared.parse_axioms(run("axioms", ["lake", "env", "lean", str(audit)]), names)
    statements = local / "Statements.lean"
    statements.write_text("""import SeparationAudit
#check @PoincareSeparation.exists_global_crossing_lift
#check @PoincareSeparation.exists_pathConnected_separation_of_collar
#check @PoincareSeparation.sphere_collar_separates_and_caps
#check @PoincareSeparationTests.actual_cylinder_both_caps_simplyConnected
#print PoincareSeparation.centralSphere
#print PoincareSeparation.crossingHeight
#print PoincareSeparationTests.CompactCylinder
#print PoincareSeparationTests.cylinderCollar
""")
    run("statements", ["lake", "env", "lean", str(statements)])
    (out / "statement-review-source.txt").write_text(statements.read_text())
    gate = (ROOT / "SeparationAudit.lean").read_text()
    phase = (ROOT / "CollarPhase.lean").read_text()
    separator = (ROOT / "CollarSeparator.lean").read_text()
    if gate.count("run_cmd do\n") != 1 or "[SimplyConnectedSpace M]" not in separator:
        raise ValueError("Unexpected proof/audit boundary")
    fixtures = {
        "extra_axiom": (gate.replace("run_cmd do\n",
            "axiom PoincareSeparation.sentinel : False\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareSeparation.sentinel"),
        "placeholder": (gate.replace("run_cmd do\n",
            "theorem PoincareSeparation.sentinel : False := by sorry\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "missing_ambient_simple_connectivity": (separator.replace("[SimplyConnectedSpace M]", ""),
                                                 "SimplyConnectedSpace"),
        "missing_hypersurface_connectedness": (separator.replace("[ConnectedSpace S]", ""),
                                                 "PreconnectedSpace"),
        "missing_compact_support_hypothesis": (phase.replace("[CompactSpace S]", ""), "CompactSpace"),
        "mere_continuous_map_not_collar": (phase.replace("hc : IsOpenEmbedding c", "hc : Continuous c"),
                                           "hc"),
        "incorrect_crossing_value": ("import CollarPhase\nexample :\n"
            "  PoincareSeparation.crossingHeight 0 = 0 := by\n"
            "  norm_num [PoincareSeparation.crossingHeight]\n", "unsolved goals"),
    }
    for label, (content, diagnostic) in fixtures.items():
        path = local / (label + ".lean")
        path.write_text(content)
        run(label, ["lake", "env", "lean", str(path)], error=diagnostic, timeout=300)
    print("Build, statement checks, axiom audit and all negative controls passed; full replay begins.", flush=True)
    t = time.monotonic()
    text = run("kernel-replay", ["lake", "env", "leanchecker", "--verbose", "--fresh", "SeparationAudit"],
               timeout=1800)
    elapsed = round(time.monotonic() - t, 2)
    if "replaying SeparationAudit with --fresh" not in text:
        raise RuntimeError("Missing final root replay confirmation")
    if sources() != config or dependencies() != pins or digest(Path(__file__)) != script_hash or digest(HELPER) != helper_hash:
        raise ValueError("Source, verifier or dependency changed during verification")
    result = {
        "status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED",
        "scope": "A compact path-connected two-sided collared hypersurface in a simply connected locally path-connected Hausdorff space has two path-connected open sides; a compact ambient sphere collar yields two simply connected capped closed sides",
        "started_at_utc": started, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version, "source_files": config["files"], "dependency_pins": pins,
        "production_theorems": config["production_theorems"], "regression_theorems": config["regression_theorems"],
        "axioms": axioms, "namespace_wide_audit": True, "default_build_pass": True,
        "allowed_dependency_warnings": warnings, "negative_controls": {k: "REJECTED" for k in fixtures},
        "full_fresh_kernel_replay": True, "replay_seconds": elapsed,
        "separating_regions_constructed": True, "both_regions_path_connected_proved": True,
        "original_separation_assumption_removed": True,
        "actual_compact_3d_cylinder_complete_endpoint_regression": True,
        "cylinder_claimed_closed_manifold": False,
        "collar_existence_proved": False, "ricci_surgery_or_metric_cap_constructed": False,
        "full_poincare_formalization": False, "eligible_complete_original_problem_submission": False,
        "independent_checker_implementation": False, "independent_human_review": False,
        "clean_full_dependency_rebuild": False, "reused_sources_byte_identical": True,
        "source_and_dependencies_checked_before_and_after": True,
        "verifier_hashes": {"verify.py": script_hash,
            "../../submissions/jsp-000007-dini-extinction/scripts/verify_topology_extension.py": helper_hash},
    }
    record.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "scope", "full_fresh_kernel_replay",
                                            "full_poincare_formalization")}, indent=2))


if __name__ == "__main__":
    main()
