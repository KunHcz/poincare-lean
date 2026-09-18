import copy
import importlib.util
import json
from pathlib import Path
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location("validate_repository", ROOT / "scripts/validate_repository.py")
verify = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(verify)


class CompletenessTests(unittest.TestCase):
    def setUp(self):
        self.state = json.loads((ROOT / "COMPLETENESS.json").read_text())

    def test_honest_research_state_accepted(self):
        verify.check_completeness(self.state, False)

    def test_incomplete_submission_rejected(self):
        with self.assertRaisesRegex(ValueError, "NOT_READY"):
            verify.check_completeness(self.state, True)

    def test_boolean_flip_is_not_a_proof(self):
        for field in ["full_original_theorem_proved", "submission_ready"]:
            state = copy.deepcopy(self.state)
            state[field] = True
            with self.subTest(field=field), self.assertRaisesRegex(ValueError, "Unverified"):
                verify.check_completeness(state, False)

    def test_component_theorem_cannot_be_named_as_full_proof(self):
        for name in ["PoincareHamilton.positiveRicci_poincare",
                     "PoincareConjecture.capped_piece_simplyConnected"]:
            state = copy.deepcopy(self.state)
            state["full_theorem_declaration"] = name
            with self.subTest(theorem=name), self.assertRaisesRegex(ValueError, "Unverified"):
                verify.check_completeness(state, False)

    def test_cap_component_has_exact_source_bound_evidence(self):
        component = ROOT / "research/cap-filling"
        self.assertGreater(verify.check_record(component, component / "evidence/verification.json"), 8)
        record = json.loads((component / "evidence/verification.json").read_text())
        self.assertFalse(record["eligible_complete_original_problem_submission"])
        self.assertIn("PoincareConjecture.capped_piece_simplyConnected", record["production_theorems"])

    def test_string_false_is_rejected(self):
        self.state["submission_ready"] = "false"
        with self.assertRaises(ValueError):
            verify.check_completeness(self.state, False)

    def test_escaping_path_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaises(ValueError):
                verify.safe_path(Path(temp), "../outside")

    def test_worktree_git_pointer_is_not_published_source(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / ".git").write_text("gitdir: external-worktree-metadata\n")
            (root / "proof.lean").write_text("-- public proof source\n")
            self.assertEqual([p.name for p in verify.public_files(root)], ["proof.lean"])

    def test_closed_cover_component_has_source_bound_evidence(self):
        component = ROOT / "research/closed-cover"
        self.assertGreater(verify.check_record(component, component / "evidence/verification.json"), 10)
        record = json.loads((component / "evidence/verification.json").read_text())
        self.assertFalse(record["eligible_complete_original_problem_submission"])
        self.assertFalse(record["collar_and_separation_existence_proved"])
        self.assertIn("PoincareClosedCover.both_closed_cover_caps_simplyConnected", record["production_theorems"])

    def test_closed_cover_result_cannot_replace_full_poincare(self):
        self.state["full_theorem_declaration"] = "PoincareClosedCover.caps_of_collared_separation_simplyConnected"
        with self.assertRaisesRegex(ValueError, "Unverified"):
            verify.check_completeness(self.state, False)

    def test_separation_component_has_exact_source_bound_evidence(self):
        component = ROOT / "research/collar-separation"
        self.assertGreater(verify.check_record(component, component / "evidence/verification.json"), 15)
        record = json.loads((component / "evidence/verification.json").read_text())
        self.assertTrue(record["original_separation_assumption_removed"])
        self.assertTrue(record["actual_compact_3d_cylinder_complete_endpoint_regression"])
        self.assertFalse(record["collar_existence_proved"])
        self.assertFalse(record["eligible_complete_original_problem_submission"])
        self.assertIn("PoincareSeparation.sphere_collar_separates_and_caps", record["production_theorems"])

    def test_separation_result_cannot_replace_full_poincare(self):
        self.state["full_theorem_declaration"] = "PoincareSeparation.sphere_collar_separates_and_caps"
        with self.assertRaisesRegex(ValueError, "Unverified"):
            verify.check_completeness(self.state, False)

    def test_local_collar_source_bound_evidence(self):
        component = ROOT / "research/local-collar"
        self.assertGreater(verify.check_record(component, component / "evidence/verification.json"), 18)
        record = json.loads((component / "evidence/verification.json").read_text())
        self.assertTrue(record["uniform_collar_radius_constructed"])
        self.assertTrue(record["coordinate_inverse_function_theorem_applied"])
        self.assertFalse(record["transverse_family_constructed_for_arbitrary_embedded_sphere"])
        self.assertFalse(record["eligible_complete_original_problem_submission"])
        self.assertIn("PoincareLocalCollar.exists_collar_of_C1_coordinates", record["production_theorems"])

    def test_local_collar_result_cannot_replace_full_poincare(self):
        self.state["full_theorem_declaration"] = "PoincareLocalCollar.coordinate_derivatives_separate_and_cap"
        with self.assertRaisesRegex(ValueError, "Unverified"):
            verify.check_completeness(self.state, False)

    def test_general_flow_source_bound_evidence(self):
        component = ROOT / "research/general-flow"
        self.assertGreater(verify.check_record(component, component / "evidence/verification.json"), 5)
        record = json.loads((component / "evidence/verification.json").read_text())
        self.assertFalse(record["positive_curvature_assumed"])
        self.assertFalse(record["finite_lifetime_assumed"])
        self.assertFalse(record["immortal_branch_eliminated"])
        self.assertFalse(record["general_surgery_constructed"])
        self.assertIn("PoincareGeneralFlow.maximal_endpoint_unique", record["production_theorems"])

    def test_general_flow_is_not_a_complete_poincare_proof(self):
        self.state["full_theorem_declaration"] = "PoincareGeneralFlow.initial_metric_and_maximal_flow"
        with self.assertRaisesRegex(ValueError, "Unverified"):
            verify.check_completeness(self.state, False)

    def test_preserved_repository(self):
        result = verify.validate(ROOT)
        self.assertFalse(result["submission_ready"])
        self.assertGreater(result["migrated_files_unchanged"], 100)


if __name__ == "__main__":
    unittest.main()
