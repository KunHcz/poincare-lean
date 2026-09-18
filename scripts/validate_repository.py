#!/usr/bin/env python3
"""Check preserved research evidence; full-problem readiness is a separate gate."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED = {".git", ".lake", "verification-output", "__pycache__"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_completeness(state: dict, require_complete: bool) -> None:
    required = {
        "problem_id": "JSP-000007",
        "full_original_theorem_proved": False,
        "full_theorem_declaration": None,
        "full_theorem_root": None,
        "full_theorem_evidence": None,
        "submission_ready": False,
        "completed_component_checks_do_not_discharge_full_target": True,
    }
    for name, value in required.items():
        if state.get(name) != value or (isinstance(value, bool) and type(state.get(name)) is not bool):
            raise ValueError("Unverified full-theorem claim: " + name +
                             ". A flag cannot replace an exact-statement kernel check.")
    if require_complete:
        raise ValueError("NOT_READY: the full original Poincare theorem has no verified proof here")


def public_files(root: Path):
    for current, dirs, files in os.walk(root):
        dirs[:] = [d for d in dirs if d not in EXCLUDED]
        for filename in files:
            path = Path(current) / filename
            if path.suffix == ".pyc" or filename in {".DS_Store", ".git"}:
                continue
            if path.is_symlink():
                raise ValueError("Unexpected published symlink: " + str(path))
            yield path


def safe_path(root: Path, relative: str) -> Path:
    path = (root / relative).resolve()
    if not path.is_relative_to(root.resolve()) or not path.is_file():
        raise ValueError("Missing or escaping file reference: " + relative)
    return path


def check_record(package: Path, record_path: Path) -> int:
    record = json.loads(record_path.read_text())
    if record.get("status") != "LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED":
        raise ValueError("Incomplete local evidence: " + str(record_path))
    if record.get("full_poincare_formalization") is not False:
        raise ValueError("Component falsely claims full Poincare")
    if record.get("full_fresh_kernel_replay") is not True:
        raise ValueError("No completed fresh replay in " + str(record_path))
    bindings = record.get("source_files") or record.get("files")
    if not isinstance(bindings, dict) or not bindings:
        raise ValueError("Evidence has no source identities")
    count = 0
    for relative, value in bindings.items():
        expected = value["sha256"] if isinstance(value, dict) else value
        if sha256(safe_path(package, relative)) != expected:
            raise ValueError("Evidence source hash mismatch: " + relative)
        count += 1
    for relative, expected in record.get("verifier_hashes", {}).items():
        # An explicitly shared verifier may be a sibling; never allow escape from this repository.
        path = (package / relative).resolve()
        if not path.is_relative_to(ROOT) or not path.is_file() or sha256(path) != expected:
            raise ValueError("Verifier identity mismatch: " + relative)
        count += 1
    for name, axioms in record.get("axioms", {}).items():
        if set(axioms) - ALLOWED_AXIOMS:
            raise ValueError("Nonstandard recorded axiom: " + name)
    process = record.get("replay_process")
    if process and (process.get("exit_code") != 0 or process.get("guard") is not None):
        raise ValueError("Replay failed or stopped at a resource guard")
    return count


def validate(root: Path, require_complete: bool = False) -> dict:
    state = json.loads((root / "COMPLETENESS.json").read_text())
    check_completeness(state, require_complete)
    rules = json.loads((root / "RULES_BASELINE.json").read_text())
    if state["official_rule_commit"] != rules["commit"] or not rules["complete_original_problem_required"]:
        raise ValueError("Official submission rule baseline mismatch")
    provenance = json.loads((root / "MIGRATION_PROVENANCE.json").read_text())
    originals = provenance["copied_tracked_files"]
    for relative, info in originals.items():
        path = safe_path(root, relative)
        if sha256(path) != info["sha256"] or path.stat().st_size != info["bytes"]:
            raise ValueError("A migrated original was changed: " + relative)
    package = root / "submissions/jsp-000007-dini-extinction"
    bindings = check_record(package, package / "evidence/verification.json")
    for component in ["constant-curvature", "positive-ricci", "scalar-flow-bounds"]:
        bindings += check_record(package / component, package / component / "evidence/verification.json")
    for component in ["flow-chains", "cap-filling", "closed-cover", "collar-separation", "local-collar", "general-flow"]:
        research = root / "research" / component
        if research.is_dir():
            bindings += check_record(research, research / "evidence/verification.json")
    cfg = json.loads((package / "verification-config.json").read_text())
    for relative, expected in cfg["unchanged_files"].items():
        if sha256(safe_path(package, relative)) != expected:
            raise ValueError("Original analytic pin changed: " + relative)
    links = 0
    total_bytes = 0
    for path in public_files(root):
        data = path.read_bytes()
        total_bytes += len(data)
        text = data.decode("utf-8")
        if re.search(r"/Users/|/home/|ghp_[A-Za-z0-9]{20,}|BEGIN (?:RSA |OPENSSH )?PRIVATE KEY", text):
            # The regex literal in a checker is not an actual path or credential.
            if path.suffix != ".py":
                raise ValueError("Private path or secret marker in " + str(path.relative_to(root)))
        if path.suffix != ".md":
            continue
        for target in re.findall(r"\]\(([^)\s]+)\)", text):
            if "://" in target or target.startswith(("mailto:", "#")):
                continue
            relative, _, anchor = target.partition("#")
            resolved = (path.parent / relative).resolve()
            if not resolved.is_relative_to(root) or not resolved.is_file():
                raise ValueError("Broken local link: " + str(path.relative_to(root)) + " -> " + target)
            if anchor and anchor.startswith("JSP-") and f'id="{anchor}"' not in resolved.read_text():
                raise ValueError("Missing problem anchor: " + target)
            links += 1
    return {"status": "PASS_RESEARCH_INTEGRITY_NOT_FULL_PROOF",
            "migrated_files_unchanged": len(originals), "checked_source_evidence_bindings": bindings,
            "relative_links_checked": links, "public_bytes": total_bytes,
            "full_original_theorem_proved": False, "submission_ready": False}


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--require-complete", action="store_true")
    options = parser.parse_args()
    try:
        print(json.dumps(validate(ROOT, options.require_complete), indent=2))
    except (ValueError, KeyError, OSError, json.JSONDecodeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
