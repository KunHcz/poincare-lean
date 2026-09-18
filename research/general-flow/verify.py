#!/usr/bin/env python3
"""Verify the general smooth-flow component; never promote it to Poincare closure."""
from __future__ import annotations

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

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[1]
HELPER = REPOSITORY / "submissions/jsp-000007-dini-extinction/constant-curvature/scripts/verify.py"
SPEC = importlib.util.spec_from_file_location("general_flow_verification_helpers", HELPER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("The preserved verifier helper is missing")
shared = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(shared)
GEOMETRY_COMMIT = "1ccb5e688b253701690300867ffb20e467855d2b"
EXTENSION_BASE = "d88910233464ea6ff54bd55f92b7d5ea0b9034e8"
EXTENSION_ORIGIN = "f34543166960b38bed82a78a5bd583611cbcdf9d"
PATCH_FILES = {
    "DifferentialGeometry/Geometry/Curvature/CovGradRoughLap/HomFieldCurvatureJetDecomposition.lean",
    "DifferentialGeometry/Geometry/Flow/RicciFlow/Extension/Regularity.lean",
    "DifferentialGeometry/Geometry/Flow/RicciFlow/Extension/MaximalFlow.lean",
}
UPSTREAM_THEOREMS = [
    "DifferentialGeometry.PDE.RicciFlow.exists_maximal_forward_ricci_flow",
    "DifferentialGeometry.PDE.RicciFlow.exists_immortal_or_finite_singularity",
    "DifferentialGeometry.PDE.RicciFlow.ricci_flow_short_time_existence",
    "DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def checked(args: list[str], cwd: Path) -> str:
    proc = shared.run(args, cwd, timeout=300)
    if proc.returncode:
        raise RuntimeError("Command failed: " + proc.stdout)
    return proc.stdout.strip()


def safe_source(relative: str) -> Path:
    p = (ROOT / relative).resolve()
    if not p.is_relative_to(ROOT.resolve()) or not p.is_file():
        raise ValueError("Missing or escaping proof source: " + relative)
    return p


def check_sources() -> dict:
    manifest = json.loads((ROOT / "source-manifest.json").read_text())
    for relative, expected in manifest["files"].items():
        if digest(safe_source(relative)) != expected:
            raise ValueError("Changed submitted source: " + relative)
    actual = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*.lean")
              if ".lake" not in p.relative_to(ROOT).parts}
    if actual != {p for p in manifest["files"] if p.endswith(".lean")}:
        raise ValueError("Unexpected Lean source inventory")
    original = REPOSITORY / "submissions/jsp-000007-dini-extinction/scalar-flow-bounds/ScalarFlowBounds.lean"
    if digest(ROOT / "ScalarFlowBounds.lean") != digest(original):
        raise ValueError("The earlier scalar proof was modified")
    return manifest


def check_dependencies() -> dict[str, str]:
    pins = {}
    for dep in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]:
        if dep["type"] != "git":
            raise ValueError("Unpinned local dependency")
        path = ROOT / ".lake/packages" / dep["name"]
        revision = checked(["git", "rev-parse", "HEAD"], path)
        if revision != dep["rev"] or checked(
                ["git", "status", "--porcelain", "--untracked-files=no"], path):
            raise ValueError("Changed dependency: " + dep["name"])
        pins[dep["name"]] = revision
    if pins.get("DifferentialGeometry") != GEOMETRY_COMMIT or pins.get("mathlib") != shared.MATHLIB_COMMIT:
        raise ValueError("Unexpected mathematical dependency pins")
    geometry = ROOT / ".lake/packages/DifferentialGeometry"
    changed = set(checked(["git", "diff", "--name-only", EXTENSION_BASE, GEOMETRY_COMMIT], geometry).splitlines())
    if changed != PATCH_FILES:
        raise ValueError("The disclosed three-file dependency repair changed scope")
    checked(["git", "merge-base", "--is-ancestor", EXTENSION_ORIGIN, GEOMETRY_COMMIT], geometry)
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


def replay(out: Path, timeout: int = 7200, memory_mb: int = 24576) -> dict:
    start = time.monotonic()
    peak = 0
    guard = None
    env = os.environ.copy()
    env["LEAN_NUM_THREADS"] = "2"
    path = out / "kernel-replay.log"
    with path.open("w") as log:
        proc = subprocess.Popen(["lake", "env", "leanchecker", "--verbose", "--fresh",
                                 "GeneralRicciFlowAudit"], cwd=ROOT, env=env,
                                stdout=log, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            while proc.poll() is None:
                rows = subprocess.check_output(["ps", "-axo", "pgid=,rss="], text=True).splitlines()
                rss = sum(int(parts[1]) for row in rows
                          if len(parts := row.split()) == 2 and int(parts[0]) == proc.pid)
                peak = max(peak, rss)
                elapsed = time.monotonic() - start
                (out / "progress.json").write_text(json.dumps({"status": "RUNNING_NOT_VERIFIED",
                    "elapsed_seconds": round(elapsed), "rss_kib": rss, "peak_rss_kib": peak}, indent=2) + "\n")
                if elapsed > timeout or rss > memory_mb * 1024:
                    guard = "TIME_GUARD" if elapsed > timeout else "MEMORY_GUARD"
                    stop(proc)
                    break
                time.sleep(5)
            code = proc.wait()
        except BaseException:
            stop(proc)
            raise
    text = sanitize(path.read_text())
    path.write_text(text)
    result = {"exit_code": code, "elapsed_seconds": round(time.monotonic() - start, 2),
              "peak_rss_kib": peak, "memory_limit_mb": memory_mb, "time_limit_seconds": timeout,
              "guard": guard}
    (out / "kernel-replay-process.json").write_text(json.dumps(result, indent=2) + "\n")
    if code or guard or "replaying GeneralRicciFlowAudit with --fresh" not in text:
        raise RuntimeError("Complete general-flow root replay failed or did not finish")
    return result


def main() -> None:
    out = ROOT / "verification-output"
    out.mkdir(exist_ok=True)
    report = out / "verification.json"
    report.write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    started = datetime.now(timezone.utc).isoformat()
    sources = check_sources()
    pins = check_dependencies()
    version = checked(["lake", "env", "lean", "--version"], ROOT)
    if "version 4.33.1," not in version or shared.LEAN_COMMIT not in version:
        raise ValueError("Unexpected Lean compiler")

    def run(label: str, command: list[str], diagnostic: str | None = None, timeout: int = 600) -> str:
        proc = shared.run(command, ROOT, timeout=timeout)
        text = sanitize(proc.stdout)
        (out / (label + ".log")).write_text(text)
        if diagnostic is None:
            if proc.returncode:
                raise RuntimeError(label + " failed; see its log")
        elif not proc.returncode or diagnostic not in text or not re.search(r"error(?:\([^)]*\))?:", text):
            raise RuntimeError("Negative control did not fail as expected: " + label)
        return text

    run("build", ["lake", "--wfail", "build"], timeout=1800)
    names = sources["production_theorems"] + sources["regression_theorems"] + UPSTREAM_THEOREMS
    if not names or len(names) != len(set(names)):
        raise ValueError("Missing or duplicate theorem inventory")
    local = ROOT / ".lake/verification"
    local.mkdir(exist_ok=True)
    audit = local / "AxiomInventory.lean"
    audit.write_text("import GeneralRicciFlowAudit\n" +
                     "".join("#print axioms " + name + "\n" for name in names))
    axioms = shared.parse_axioms(run("axioms", ["lake", "env", "lean", str(audit)]), names)
    statement = local / "Statements.lean"
    statement.write_text("""import GeneralRicciFlowAudit
#check @PoincareGeneralFlow.initial_metric_and_maximal_flow
#check @PoincareGeneralFlow.maximal_endpoint_unique
#check @PoincareGeneralFlow.maximal_has_global_scalar_barrier
#check @PoincareGeneralFlow.finite_maximal_curvature_unbounded
#check @PoincareGeneralFlowTests.sphere_flow_has_positive_lifetime
#print DifferentialGeometry.PDE.RicciFlow.MaximalForwardRicciFlow
#print DifferentialGeometry.PDE.RicciFlow.FlowTo
#print DifferentialGeometry.PDE.RicciFlow.ImmortalFlow
#print DifferentialGeometry.PDE.RicciFlow.FiniteMaximalFlow
#print DifferentialGeometry.PDE.RicciFlow.IsSolutionOn
#print DifferentialGeometry.PDE.RicciFlow.ExtendsPastEndpoint
#print DifferentialGeometry.PDE.RicciFlow.IsMaximalAtEndpoint
#print DifferentialGeometry.PDE.RicciFlow.FormsSingularityAt
""")
    run("statements", ["lake", "env", "lean", str(statement)])
    (out / "statement-review-source.txt").write_text(statement.read_text())
    gate = (ROOT / "GeneralRicciFlowAudit.lean").read_text()
    source = (ROOT / "GeneralRicciFlow.lean").read_text()
    if gate.count("run_cmd do\n") != 1:
        raise ValueError("Unexpected audit boundary")
    finite_claim = """import GeneralRicciFlow
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff
example {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [CompactSpace M] (g0 : SmoothRiemannianMetric (𝓡 3) M) :
    Nonempty (FiniteMaximalFlow (I := 𝓡 3) g0) :=
  PoincareGeneralFlow.arbitrary_metric_maximal_flow g0
"""
    fixtures = {
        "extra_axiom": (gate.replace("run_cmd do\n",
            "axiom PoincareGeneralFlow.sentinel : False\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareGeneralFlow.sentinel"),
        "placeholder": (gate.replace("run_cmd do\n",
            "theorem PoincareGeneralFlow.sentinel : False := by sorry\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "discarded_immortal_branch": (finite_claim, "FiniteMaximalFlow"),
        "missing_initial_scalar_bound": (source.replace(
            "hinit : ∀ x : M, -6 ≤ metricScalarAt (I := 𝓡 3) g0 x", "hinit : True"), "hinit"),
        "time_outside_flow_domain": (source.replace("ht : P.IsDefinedAt t", "ht : True"), "ht"),
        "wrong_initial_metric": ("import GeneralRicciFlow\n"
            "open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow\n"
            "open scoped Manifold ContDiff\n"
            "example {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]\n"
            " [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]\n"
            " (g0 g1 : SmoothRiemannianMetric (𝓡 3) M)\n"
            " (P : MaximalForwardRicciFlow (I := 𝓡 3) g0) : P.metric 0 = g1 := P.metric_zero\n", "g1"),
    }
    for label, (text, diagnostic) in fixtures.items():
        path = local / (label + ".lean")
        path.write_text(text)
        run(label, ["lake", "env", "lean", str(path)], diagnostic=diagnostic, timeout=600)
    print("Default build, exact statement audit, theorem axioms and six negative controls passed; full root replay starts.", flush=True)
    process = replay(out)
    if check_sources() != sources or check_dependencies() != pins:
        raise ValueError("Sources or dependencies changed during verification")
    result = {
        "status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED",
        "scope": "Actual smooth initial metric and arbitrary-metric maximal forward Ricci flow, unique lifetime, finite/immortal distinction, canonical singular curvature and global scalar control",
        "started_at_utc": started, "completed_at_utc": datetime.now(timezone.utc).isoformat(),
        "lean_version": version, "source_files": sources["files"], "dependency_pins": pins,
        "dependency_general_extension_origin": {"commit": EXTENSION_ORIGIN,
            "git_author_name": "Arthur Freitas Ramos", "included_in_official_upstream_main": False},
        "dependency_repair_commit": GEOMETRY_COMMIT, "dependency_repair_files": sorted(PATCH_FILES),
        "production_theorems": sources["production_theorems"],
        "regression_theorems": sources["regression_theorems"],
        "audited_upstream_theorems": UPSTREAM_THEOREMS, "axioms": axioms,
        "namespace_wide_audit": True, "default_warning_as_error_build": True,
        "full_fresh_kernel_replay": True, "replay_process": process,
        "negative_controls": {label: "REJECTED" for label in fixtures},
        "source_and_dependencies_checked_before_and_after": True,
        "concrete_closed_nonempty_3sphere_existence_model": True,
        "explicit_closed_form_ricci_solution_computed": False,
        "positive_curvature_assumed": False, "finite_lifetime_assumed": False,
        "immortal_branch_eliminated": False, "general_surgery_constructed": False,
        "geometric_extinction_proved": False, "full_poincare_formalization": False,
        "eligible_complete_original_problem_submission": False,
        "independent_checker_implementation": False, "independent_human_review": False,
        "clean_full_dependency_rebuild": False,
        "verifier_hashes": {"verify.py": digest(Path(__file__)),
            "../../submissions/jsp-000007-dini-extinction/constant-curvature/scripts/verify.py": digest(HELPER)},
    }
    report.write_text(json.dumps(result, indent=2) + "\n")
    (out / "progress.json").write_text('{"status":"COMPLETED_SEE_VERIFICATION_RECORD"}\n')
    print(json.dumps({key: result[key] for key in ("status", "scope", "full_fresh_kernel_replay",
                                                   "full_poincare_formalization")}, indent=2))


if __name__ == "__main__":
    main()
