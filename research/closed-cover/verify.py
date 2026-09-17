#!/usr/bin/env python3
"""Verify the closed-cover/collar component, not unrestricted Poincare.

Stages can run separately on a bounded executor. Each later stage requires
identical source, verifier, dependency identities and hashed earlier logs.
Only `final` may write a successful verification record.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import time
import uuid

ROOT = Path(__file__).resolve().parent
REPOSITORY = ROOT.parents[1]
HELPER = REPOSITORY / "submissions/jsp-000007-dini-extinction/scripts/verify_topology_extension.py"
SPEC = importlib.util.spec_from_file_location("closed_cover_verified_helpers", HELPER)
if SPEC is None or SPEC.loader is None:
    raise RuntimeError("The preserved verifier helper is missing")
shared = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(shared)
OUT = ROOT / "verification-output"
STATE = ROOT / ".lake/verification-stages/state.json"
REUSED = ["CapFilling.lean", "PuncturedCap.lean", "AttachmentOpen.lean", "ConnectedCap.lean",
          "HomotopicFactorization.lean", "CappingTheorem.lean"]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def safe_path(relative: str) -> Path:
    path = (ROOT / relative).resolve()
    if not path.is_relative_to(ROOT.resolve()) or not path.is_file():
        raise ValueError("Missing or escaping source: " + relative)
    return path


def inputs() -> dict:
    config = json.loads((ROOT / "source-manifest.json").read_text())
    for rel, sha in config["files"].items():
        if digest(safe_path(rel)) != sha:
            raise ValueError("Changed source: " + rel)
    files = {str(p.relative_to(ROOT)) for p in ROOT.rglob("*.lean")
             if ".lake" not in p.relative_to(ROOT).parts}
    if files != {p for p in config["files"] if p.endswith(".lean")}:
        raise ValueError("Unexpected Lean file inventory")
    for rel in REUSED:
        if digest(ROOT / rel) != digest(ROOT.parent / "cap-filling" / rel):
            raise ValueError("The preserved cap proof was changed: " + rel)
    pins = {}
    for dep in json.loads((ROOT / "lake-manifest.json").read_text())["packages"]:
        if dep["type"] != "git":
            raise ValueError("Unpinned local dependency")
        p = ROOT / ".lake/packages" / dep["name"]
        sha = shared.checked(["git", "rev-parse", "HEAD"], p)
        if sha != dep["rev"] or shared.checked(
                ["git", "status", "--porcelain", "--untracked-files=no"], p):
            raise ValueError("Dependency changed: " + dep["name"])
        pins[dep["name"]] = sha
    if pins.get("mathlib") != shared.MATHLIB_COMMIT or pins.get("HatcherLib") != shared.HATCHER_COMMIT:
        raise ValueError("Wrong pinned mathematical dependencies")
    return {"config": config, "pins": pins,
            "verifiers": {"verify.py": digest(Path(__file__)),
                "../../submissions/jsp-000007-dini-extinction/scripts/verify_topology_extension.py": digest(HELPER)}}


def fingerprint(data: dict) -> str:
    return hashlib.sha256(json.dumps(data, sort_keys=True).encode()).hexdigest()


def load_stage(data: dict, required: str) -> dict:
    state = json.loads(STATE.read_text())
    if state["fingerprint"] != fingerprint(data) or state.get(required) is not True:
        raise ValueError("Earlier stage or its exact inputs do not match")
    for name, sha in state["log_hashes"].items():
        if digest(OUT / name) != sha:
            raise ValueError("Earlier evidence log changed: " + name)
    return state


def write_state(state: dict) -> None:
    STATE.write_text(json.dumps(state, indent=2) + "\n")


def run(label: str, command: list[str], timeout: int = 120, error: str | None = None) -> str:
    proc = shared.run(command, ROOT, timeout=timeout)
    text = proc.stdout.replace(str(ROOT), "$PROJECT").replace(str(Path.home()), "$HOME")
    (OUT / (label + ".log")).write_text(text)
    if error is None:
        if proc.returncode:
            raise RuntimeError(label + " failed; see its log")
    elif not proc.returncode or error not in text or not re.search(r"error(?:\([^)]*\))?:", text):
        raise RuntimeError("Negative control was not rejected: " + label)
    return text


def prepare() -> None:
    OUT.mkdir(exist_ok=True)
    STATE.parent.mkdir(parents=True, exist_ok=True)
    (OUT / "verification.json").write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    data = inputs()
    state = {"generation": str(uuid.uuid4()), "fingerprint": fingerprint(data),
             "started_at_utc": datetime.now(timezone.utc).isoformat(), "log_hashes": {}}
    write_state(state)
    version = shared.checked(["lake", "env", "lean", "--version"], ROOT)
    if "version 4.32.1," not in version or shared.LEAN_COMMIT not in version:
        raise ValueError("Wrong Lean compiler")
    run("build", ["lake", "--wfail", "build"])
    names = data["config"]["production_theorems"] + data["config"]["regression_theorems"]
    if not names or len(names) != len(set(names)):
        raise ValueError("Empty or duplicate declaration inventory")
    audit = STATE.parent / "Inventory.lean"
    audit.write_text("import ClosedCoverAudit\n" + "".join("#print axioms " + n + "\n" for n in names))
    axioms = shared.parse_axioms(run("axioms", ["lake", "env", "lean", str(audit)]), names)
    statement = STATE.parent / "Statements.lean"
    statement.write_text("""import ClosedCoverAudit
#check @PoincareClosedCover.closedCoverHomeomorph
#check @PoincareClosedCover.both_closed_cover_caps_simplyConnected
#check @PoincareClosedCover.caps_of_collared_separation_simplyConnected
#print PoincareConjecture.BoundaryGluingRel
#print PoincareConjecture.BoundaryGluing
#print PoincareClosedCover.sphericalBoundaryLeft
#print PoincareClosedCover.CollarTime
""")
    run("statements", ["lake", "env", "lean", str(statement)])
    (OUT / "statement-review-source.txt").write_text(statement.read_text())
    if inputs() != data:
        raise ValueError("Source changed during preparation")
    state.update({"prepare_pass": True, "lean_version": version, "axioms": axioms})
    for name in ["build.log", "axioms.log", "statements.log", "statement-review-source.txt"]:
        state["log_hashes"][name] = digest(OUT / name)
    write_state(state)
    print("PREPARE_PASS_NOT_FINAL: build, statement and axiom checks completed")


def kernel(timeout: int) -> None:
    data = inputs()
    state = load_stage(data, "prepare_pass")
    state["kernel_pass"] = False
    write_state(state)
    started = time.monotonic()
    text = run("kernel-replay", ["lake", "env", "leanchecker", "--verbose", "--fresh", "ClosedCoverAudit"],
               timeout=timeout)
    if "replaying ClosedCoverAudit with --fresh" not in text:
        raise ValueError("Missing complete root replay marker")
    if inputs() != data:
        raise ValueError("Source changed during kernel replay")
    state.update({"kernel_pass": True, "replay_seconds": round(time.monotonic() - started, 2)})
    state["log_hashes"]["kernel-replay.log"] = digest(OUT / "kernel-replay.log")
    write_state(state)
    print("KERNEL_PASS_NOT_FINAL: full root replay completed")


def final() -> None:
    data = inputs()
    state = load_stage(data, "kernel_pass")
    gate = (ROOT / "ClosedCoverAudit.lean").read_text()
    cover = (ROOT / "ClosedCover.lean").read_text()
    sides = (ROOT / "CutSides.lean").read_text()
    if gate.count("run_cmd do\n") != 1:
        raise ValueError("Unexpected audit boundary")
    fixtures = {
        "extra_axiom": (gate.replace("run_cmd do\n",
            "axiom PoincareClosedCover.sentinel : False\nrun_cmd do\n"),
            "non-whitelisted axiom PoincareClosedCover.sentinel"),
        "placeholder": (gate.replace("run_cmd do\n",
            "theorem PoincareClosedCover.sentinel : False := by sorry\nrun_cmd do\n"),
            "non-whitelisted axiom sorryAx"),
        "missing_cover": (cover.replace("hcover : A ∪ B = univ", "hcover : True"), "hcover"),
        "missing_original_simple_connectivity": (cover.replace("[SimplyConnectedSpace M]", ""),
                                                  "SimplyConnectedSpace"),
        "missing_disjointness": (sides.replace("hdisjoint : Disjoint U V", "hdisjoint : True"),
                                  "hdisjoint"),
        "missing_boundary_access": (sides.replace(
            "haccess : ∀ x ∈ A, x ∉ U → ∃ y ∈ U, JoinedIn A x y", "haccess : True"), "haccess"),
    }
    for label, (text, diagnostic) in fixtures.items():
        path = STATE.parent / (label + ".lean")
        path.write_text(text)
        run(label, ["lake", "env", "lean", str(path)], timeout=60, error=diagnostic)
    if inputs() != data:
        raise ValueError("Inputs changed during final verification")
    result = {"status": "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED",
        "scope": "Actual closed-cover boundary gluing and simply connected caps; closed-side connectivity derived from a supplied collared separation",
        "generation": state["generation"], "started_at_utc": state["started_at_utc"],
        "completed_at_utc": datetime.now(timezone.utc).isoformat(), "lean_version": state["lean_version"],
        "source_files": data["config"]["files"], "dependency_pins": data["pins"],
        "production_theorems": data["config"]["production_theorems"],
        "regression_theorems": data["config"]["regression_theorems"], "axioms": state["axioms"],
        "namespace_wide_audit": True, "default_warning_as_error_build": True,
        "full_fresh_kernel_replay": True, "replay_seconds": state["replay_seconds"],
        "negative_controls": {name: "REJECTED" for name in fixtures},
        "previous_cap_sources_byte_identical": True, "source_and_dependencies_checked_before_and_after": True,
        "actual_gluing_homeomorphism_constructed": True, "actual_closed_ball_cover_regression": True,
        "collar_and_separation_existence_proved": False, "concrete_full_collar_model_regression": False,
        "ricci_surgery_or_metric_cap_constructed": False, "full_poincare_formalization": False,
        "eligible_complete_original_problem_submission": False, "independent_checker_implementation": False,
        "independent_human_review": False, "clean_full_dependency_rebuild": False,
        "verifier_hashes": data["verifiers"]}
    (OUT / "verification.json").write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({key: result[key] for key in ["status", "scope", "full_fresh_kernel_replay",
                                                "full_poincare_formalization"]}, indent=2))


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--stage", choices=["prepare", "kernel", "final", "all"], default="all")
    parser.add_argument("--kernel-timeout", type=int, default=1800)
    options = parser.parse_args()
    if options.kernel_timeout <= 0:
        parser.error("Kernel timeout must be positive")
    OUT.mkdir(exist_ok=True)
    (OUT / "verification.json").write_text('{"status":"IN_PROGRESS_NOT_VERIFIED"}\n')
    if options.stage in ["prepare", "all"]:
        prepare()
    if options.stage in ["kernel", "all"]:
        kernel(options.kernel_timeout)
    if options.stage in ["final", "all"]:
        final()


if __name__ == "__main__":
    main()
