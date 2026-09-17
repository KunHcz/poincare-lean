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
        self.state["full_theorem_declaration"] = "PoincareHamilton.positiveRicci_poincare"
        with self.assertRaisesRegex(ValueError, "Unverified"):
            verify.check_completeness(self.state, False)

    def test_string_false_is_rejected(self):
        self.state["submission_ready"] = "false"
        with self.assertRaises(ValueError):
            verify.check_completeness(self.state, False)

    def test_escaping_path_is_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            with self.assertRaises(ValueError):
                verify.safe_path(Path(temp), "../outside")

    def test_preserved_repository(self):
        result = verify.validate(ROOT)
        self.assertFalse(result["submission_ready"])
        self.assertGreater(result["migrated_files_unchanged"], 100)


if __name__ == "__main__":
    unittest.main()
