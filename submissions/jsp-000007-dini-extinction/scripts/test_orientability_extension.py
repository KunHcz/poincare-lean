import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify_orientability_extension as verify


class OrientabilityVerifierTests(unittest.TestCase):
    def test_wrong_source_revision_rejected(self):
        with patch.object(verify.shared, "checked", return_value="wrong"):
            with self.assertRaisesRegex(RuntimeError, "Wrong source commit"):
                verify.check_checkout(Path("unused"))

    def test_modified_source_rejected(self):
        with patch.object(verify.shared, "checked", side_effect=[verify.SOURCE_COMMIT, " M file.lean"]):
            with self.assertRaisesRegex(RuntimeError, "Tracked source changes"):
                verify.check_checkout(Path("unused"))

    def test_exact_clean_source_accepted(self):
        with patch.object(verify.shared, "checked", side_effect=[verify.SOURCE_COMMIT, ""]):
            verify.check_checkout(Path("unused"))

    def test_local_dependency_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [{"type": "path"}]}))
            with self.assertRaisesRegex(RuntimeError, "Unpinned dependency"):
                verify.check_pins(root)

    def test_wrong_mathematical_dependency_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "lake-manifest.json").write_text(json.dumps({"packages": []}))
            with self.assertRaisesRegex(RuntimeError, "Unexpected mathematical dependencies"):
                verify.check_pins(root)

    def test_nonstandard_axiom_rejected(self):
        with self.assertRaises(ValueError):
            verify.shared.parse_axioms("'T' depends on axioms: [sorryAx]", ["T"])

    def test_unknown_warning_rejected(self):
        with self.assertRaises(ValueError):
            verify.shared.check_diagnostics("warning: an unreviewed warning")


if __name__ == "__main__":
    unittest.main()
