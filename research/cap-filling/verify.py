#!/usr/bin/env python3
"""Verify actual cap-filling topology; never assert full Poincare or prize eligibility."""
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
SPEC = importlib.util.spec_from_file_location("cap_filling_verification_helpers", HELPER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("The preserved verification helper is missing")
shared = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(shared)
ROOT_MODULE = "CapFillingAudit"


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def input_file(relative: str) -> Path:
    path = (ROOT / relative).resolve()
    if not path.is_relative_to(ROOT.resolve()) or not path.is_file():
        raise ValueError("Missing or escaping source: " + relative)
    return path


def check_sources() -> tuple[dict[str, str], list[str], list[str]]:
    config = json.loads((ROOT / "source-manifest.json").read_text())
    sources = config["files"]
    for relative, expected in sources.items():
        if digest(input_file(relative)) != expected:
            raise ValueError("Changed proof source: " + relative)
    actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*.lean")
              if ".lake" not in p.relative_to(ROOT).parts}
    if actual != {p for p in sources if p.endswith(".lean")}:
        raise ValueError("Unexpected Lean source inventory")
    declarations = config["production_theorems"]
    tests = config["regression_theorems"]
    if len(set(declarations + tests)) != len(declarations + tests):
        raise ValueError("Duplicate declaration inventory")
    if not declarations or not tests:
        raise ValueError("Both proof and regression inventories are required")
    return sources, declarations, tests


def check_dependencies() -> dict[str, str]:
    pins = {}
    for dep in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]:
        if dep["type"] != "git":
            raise ValueError("Unpinned local dependency")
        path = ROOT / ".lake/packages" / dep["name"]
        actual = shared.checked(["git", "rev-parse", "HEAD"], path)
        if actual != dep["rev"] or shared.checked(
                ["git", "status", "--porcelain", "--untracked-files=no"], path):
            raise ValueError("Changed dependency: " + dep["name"])
        pins[dep["name"]] = actual
    if pins.get("mathlib") != shared.MATHLIB_COMMIT or pins.get("HatcherLib") != shared.HATCHER_COMMIT:
        raise ValueError("Unexpected mathematical dependency pins")
    return pins


def main() -> None:
    output = ROOT / "verification-output"
    output.mkdir(exist_ok=True)
    record = output / "verification.json"
    record.write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    started = datetime.now(timezone.utc).isoformat()
    source, names, tests = check_sources()
    pins = check_dependencies()
    version = shared.checked(["lake", "env", "lean", "--version"], ROOT)
    if "version 4.32.1," not in version or shared.LEAN_COMMIT not in version:
        raise ValueError("Unexpected Lean compiler")

    def run(label: str, args: list[str], expected_error: str | None = None,
            timeout: int = 900) -> str:
        proc = shared.run(args, ROOT, timeout=timeout)
        text = proc.stdout.replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")
        (output / (label + ".log")).write_text(text)
        if expected_error is None:
            if proc.returncode:
                raise RuntimeError(label + " failed; see its log")
        elif not proc.returncode or expected_error not in text or not re.search(r"error(?:\([^)]*\))?:", text):
            raise RuntimeError(label + " was not rejected as required")
        return text

    warnings = shared.check_diagnostics(run("build", ["lake", "build"]))
    local = ROOT / ".lake/verification"
    local.mkdir(parents=True, exist_ok=True)
    audit = local / "AxiomInventory.lean"
    audit.write_text("import CapFillingAudit\n" +
                     "".join("#print axioms " + name + "\n" for name in names + tests))
    axioms = shared.parse_axioms(run("axioms", ["lake", "env", "lean", str(audit)]), names + tests)
    exact = local / "ExactStatements.lean"
    exact.write_text("""import CapFillingAudit
#check @PoincareConjecture.capped_piece_simplyConnected
#check @PoincareConjecture.both_capped_pieces_simplyConnected
#check @PoincareConjecture.capped_piece_simplyConnected_of_homeomorph
#print PoincareConjecture.BoundaryGluingRel
#print PoincareConjecture.BoundaryGluing
#print PoincareConjecture.BallAttachment
#print PoincareConjecture.ThreeBall
#print PoincareConjecture.Sphere2
""")
    run("statements", ["lake", "env", "lean", str(exact)])
    (output / "statement-review-source.txt").write_text(exact.read_text())
    started_replay = time.monotonic()
    replay = run("kernel-replay",
                 ["lake", "env", "leanchecker", "--verbose", "--fresh", ROOT_MODULE], timeout=1800)
    elapsed = round(time.monotonic() - started_replay, 2)
    if "replaying CapFillingAudit with --fresh" not in replay:
        raise RuntimeError("No final root replay confirmation")
    gate = (ROOT / "CapFillingAudit.lean").read_text()
    main_source = (ROOT / "CappingTheorem.lean").read_text()
    if gate.count("run_cmd do\n") != 1:
        raise ValueError("Unexpected audit placement")
    sc = "[SimplyConnectedSpace (BoundaryGluing i j)]"
    boundary = "(hj : IsClosedEmbedding j)"
    if sc not in main_source or boundary not in main_source:
        raise ValueError("Unexpected cap theorem assumptions")
    fixtures = {
        "extra_axiom": (gate.replace("run_cmd do\n",
            "axiom PoincareConjecture.capSentinel : False\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareConjecture.capSentinel"),
        "placeholder": (gate.replace("run_cmd do\n",
            "theorem PoincareConjecture.capSentinel : False := by sorry\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "missing_original_simple_connectivity": (main_source.replace(sc, ""),
                                                  "SimplyConnectedSpace"),
        "missing_closed_boundary_embedding": (main_source.replace(boundary, "(hj : True)"),
                                                "IsClosedEmbedding"),
        "collapsed_ball_radius": ("import CapFilling\nexample :\n"
            "    PoincareConjecture.ballAttachmentRadius (ContinuousMap.id PoincareConjecture.Sphere2)\n"
            "      (PoincareConjecture.ballAttachmentInr (ContinuousMap.id PoincareConjecture.Sphere2)\n"
            "        ⟨0, by simp⟩) = 1 := by\n"
            "  change ‖(0 : EuclideanSpace ℝ (Fin 3))‖ = 1\n  norm_num\n", "unsolved goals"),
    }
    for label, (content, diagnostic) in fixtures.items():
        path = local / (label + ".lean")
        path.write_text(content)
        run(label, ["lake", "env", "lean", str(path)], diagnostic, timeout=300)
    if check_sources() != (source, names, tests) or check_dependencies() != pins:
        raise ValueError("Proof or dependency changed during verification")
    result = {
        "status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED",
        "scope": "Simple connectivity of both actual ball-capped sides of a simply connected boundary adjunction, under explicit closed-embedding and normal/path-connected-piece hypotheses",
        "started_at_utc": started,
        "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version, "source_files": source, "dependency_pins": pins,
        "production_theorems": names, "regression_theorems": tests,
        "axioms": axioms, "namespace_wide_audit": True,
        "default_build_pass": True, "allowed_dependency_warnings": warnings,
        "full_fresh_kernel_replay": True, "replay_seconds": elapsed,
        "negative_controls": {label: "REJECTED" for label in fixtures},
        "actual_boundary_quotients_and_ball_constructed": True,
        "open_cover_and_loop_generation_derived": True,
        "concrete_doubled_ball_regression": True,
        "concrete_nonsimplyconnected_attachment_counterexample": True,
        "geometric_cut_identification_constructed": False,
        "ricci_surgery_or_curvature_control_constructed": False,
        "geometric_extinction_proved": False,
        "full_poincare_formalization": False,
        "eligible_complete_original_problem_submission": False,
        "independent_checker_implementation": False,
        "independent_human_review": False,
        "clean_full_dependency_rebuild": False,
        "source_and_dependencies_checked_before_and_after": True,
        "verifier_hashes": {"verify.py": digest(Path(__file__)),
            "../../submissions/jsp-000007-dini-extinction/scripts/verify_topology_extension.py": digest(HELPER)},
    }
    record.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ("status", "scope", "full_fresh_kernel_replay",
                                                  "full_poincare_formalization")}, indent=2))


if __name__ == "__main__":
    main()
