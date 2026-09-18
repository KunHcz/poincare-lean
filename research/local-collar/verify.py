#!/usr/bin/env python3
"""Verify the compact local-to-global collar component, not full Poincare."""
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
SPEC = importlib.util.spec_from_file_location("uniform_collar_verification_helpers", HELPER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("The preserved helper is missing")
shared = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(shared)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def input_file(relative: str) -> Path:
    path = (ROOT / relative).resolve()
    if not path.is_relative_to(ROOT.resolve()) or not path.is_file():
        raise ValueError("Missing or escaping proof source: " + relative)
    return path


def sources() -> dict:
    manifest = json.loads((ROOT / "source-manifest.json").read_text())
    for rel, sha in manifest["files"].items():
        if digest(input_file(rel)) != sha:
            raise ValueError("Changed proof source: " + rel)
    lean = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*.lean")
            if ".lake" not in p.relative_to(ROOT).parts}
    if lean != {p for p in manifest["files"] if p.endswith(".lean")}:
        raise ValueError("Unexpected Lean source inventory")
    for rel, previous in manifest["reused_sources"].items():
        old = (ROOT.parent / previous).resolve()
        if not old.is_relative_to(ROOT.parent.resolve()) or digest(ROOT / rel) != digest(old):
            raise ValueError("Changed preserved proof: " + rel)
    names = manifest["production_theorems"] + manifest["regression_theorems"]
    if not manifest["production_theorems"] or not manifest["regression_theorems"]:
        raise ValueError("Both theorem inventories are required")
    if len(names) != len(set(names)):
        raise ValueError("Duplicate declaration inventory")
    return manifest


def dependencies() -> dict[str, str]:
    pins = {}
    for dep in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]:
        if dep["type"] != "git":
            raise ValueError("Unpinned dependency")
        path = ROOT / ".lake/packages" / dep["name"]
        sha = shared.checked(["git", "rev-parse", "HEAD"], path)
        if sha != dep["rev"] or shared.checked(
                ["git", "status", "--porcelain", "--untracked-files=no"], path):
            raise ValueError("Changed dependency: " + dep["name"])
        pins[dep["name"]] = sha
    if pins.get("mathlib") != shared.MATHLIB_COMMIT or pins.get("HatcherLib") != shared.HATCHER_COMMIT:
        raise ValueError("Unexpected mathematical dependencies")
    return pins


def main() -> None:
    out = ROOT / "verification-output"
    out.mkdir(exist_ok=True)
    record = out / "verification.json"
    record.write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    started = datetime.now(timezone.utc).isoformat()
    config = sources()
    pins = dependencies()
    version = shared.checked(["lake", "env", "lean", "--version"], ROOT)
    if "version 4.32.1," not in version or shared.LEAN_COMMIT not in version:
        raise ValueError("Wrong Lean compiler")

    def run(label: str, args: list[str], error: str | None = None, timeout: int = 900) -> str:
        proc = shared.run(args, ROOT, timeout=timeout)
        text = proc.stdout.replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")
        (out / (label + ".log")).write_text(text)
        if error is None:
            if proc.returncode:
                raise RuntimeError(label + " failed; see its log")
        elif not proc.returncode or error not in text or not re.search(r"error(?:\([^)]*\))?:", text):
            raise RuntimeError("Negative control was not rejected: " + label)
        return text

    warnings = shared.check_diagnostics(run("build", ["lake", "build"]))
    names = config["production_theorems"] + config["regression_theorems"]
    local = ROOT / ".lake/verification"
    local.mkdir(parents=True, exist_ok=True)
    audit = local / "AxiomInventory.lean"
    audit.write_text("import LocalCollarAudit\n" +
                     "".join("#print axioms " + name + "\n" for name in names))
    axioms = shared.parse_axioms(run("axioms", ["lake", "env", "lean", str(audit)]), names)
    statement = local / "Statements.lean"
    statement.write_text("""import LocalCollarAudit
#check @PoincareLocalCollar.exists_uniform_openEmbedding_band
#check @PoincareLocalCollar.exists_collar_of_C1_coordinates
#check @PoincareLocalCollar.coordinate_derivatives_separate_and_cap
#print PoincareLocalCollar.HasLocalOpenChartsAtZero
#print PoincareLocalCollar.HasInvertibleCoordinateDerivativesAtZero
#print PoincareLocalCollar.scaledCollar
#print PoincareLocalCollarTests.clippedCylinderFamily
#check PoincareLocalCollarTests.clipped_family_separates_and_caps
""")
    run("statements", ["lake", "env", "lean", str(statement)])
    (out / "statement-review-source.txt").write_text(statement.read_text())
    gate = (ROOT / "LocalCollarAudit.lean").read_text()
    core = (ROOT / "CompactCollar.lean").read_text()
    differential = (ROOT / "DifferentialCollar.lean").read_text()
    zero = "hzero : Injective (fun s => f (s, 0))"
    strict = "hder : HasStrictFDerivAt (b ∘ f ∘ a.symm) (L : E →L[ℝ] F) (a x)"
    if gate.count("run_cmd do\n") != 1 or zero not in core or strict not in differential:
        raise ValueError("Unexpected audit or hypothesis locations")
    fixtures = {
        "extra_axiom": (gate.replace("run_cmd do\n",
            "axiom PoincareLocalCollar.sentinel : False\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareLocalCollar.sentinel"),
        "placeholder": (gate.replace("run_cmd do\n",
            "theorem PoincareLocalCollar.sentinel : False := by sorry\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "missing_source_compactness": (core.replace("[CompactSpace S]", ""), "CompactSpace"),
        "missing_target_separation": (core.replace("[T2Space M]", ""), "T2Space"),
        "colliding_zero_section": (core.replace(zero, "hzero : True"), "hzero"),
        "missing_local_inverse": (core.replace("hlocal : HasLocalOpenChartsAtZero f", "hlocal : True"),
                                  "hlocal"),
        "unproved_coordinate_derivative": (differential.replace(strict, "hder : True"), "hder"),
    }
    for label, (source, diagnostic) in fixtures.items():
        path = local / (label + ".lean")
        path.write_text(source)
        run(label, ["lake", "env", "lean", str(path)], error=diagnostic, timeout=300)
    print("Build, exact statements, axiom audits and seven negative controls passed; full replay starts.",
          flush=True)
    replay_start = time.monotonic()
    text = run("kernel-replay", ["lake", "env", "leanchecker", "--verbose", "--fresh", "LocalCollarAudit"],
               timeout=1800)
    replay_seconds = round(time.monotonic() - replay_start, 2)
    if "replaying LocalCollarAudit with --fresh" not in text:
        raise RuntimeError("No full root replay marker")
    if sources() != config or dependencies() != pins:
        raise ValueError("Source or dependency changed during verification")
    result = {
        "status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED",
        "scope": "Uniform open collars from a continuous family with an injective compact zero section and pointwise local inverse or actual invertible C1 coordinate derivatives; separation and capped simple connectivity follow in the stated ambient spaces",
        "started_at_utc": started, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version, "source_files": config["files"], "dependency_pins": pins,
        "reused_sources": config["reused_sources"], "reused_sources_byte_identical": True,
        "production_theorems": config["production_theorems"],
        "regression_theorems": config["regression_theorems"], "axioms": axioms,
        "namespace_wide_audit": True, "default_build_pass": True,
        "allowed_dependency_warnings": warnings, "full_fresh_kernel_replay": True,
        "replay_seconds": replay_seconds, "negative_controls": {name: "REJECTED" for name in fixtures},
        "source_and_dependencies_checked_before_and_after": True,
        "uniform_collar_radius_constructed": True, "coordinate_inverse_function_theorem_applied": True,
        "concrete_noninjective_family_full_endpoint_test": True,
        "concrete_fold_and_colliding_sheet_counterexamples": True,
        "concrete_scalar_inverse_function_test": True,
        "concrete_3d_coordinate_derivative_full_endpoint_test": False,
        "transverse_family_constructed_for_arbitrary_embedded_sphere": False,
        "smooth_normal_field_or_exponential_map_constructed": False,
        "ricci_surgery_or_geometric_extinction_proved": False,
        "full_poincare_formalization": False, "eligible_complete_original_problem_submission": False,
        "independent_checker_implementation": False, "independent_human_review": False,
        "clean_full_dependency_source_rebuild": False,
        "verifier_hashes": {"verify.py": digest(Path(__file__)),
            "../../submissions/jsp-000007-dini-extinction/scripts/verify_topology_extension.py": digest(HELPER)},
    }
    record.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({k: result[k] for k in ("status", "scope", "full_fresh_kernel_replay",
                                            "full_poincare_formalization")}, indent=2))


if __name__ == "__main__":
    main()
