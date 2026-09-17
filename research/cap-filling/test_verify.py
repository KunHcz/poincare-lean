import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify


class CapVerificationTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(verify.shared.parse_axioms("'T' depends on axioms: [propext, Quot.sound]", ["T"]),
                         {"T": ["propext", "Quot.sound"]})

    def test_extra_axiom_rejected(self):
        with self.assertRaises(ValueError):
            verify.shared.parse_axioms("'T' depends on axioms: [sorryAx]", ["T"])

    def test_missing_or_duplicate_audit(self):
        for text in ["", "'T' does not depend on any axioms\n" * 2]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                verify.shared.parse_axioms(text, ["T"])

    def test_unexpected_warning_rejected(self):
        with self.assertRaises(ValueError):
            verify.shared.check_diagnostics("warning: an unrelated proof warning")

    def test_changed_source_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "T.lean").write_text("changed")
            (root / "source-manifest.json").write_text(json.dumps({"files": {"T.lean": "wrong"}}))
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(ValueError, "Changed proof source"):
                verify.check_sources()

    def test_unexpected_source_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "T.lean").write_text("original")
            (root / "Extra.lean").write_text("unexpected")
            (root / "source-manifest.json").write_text(json.dumps({
                "files": {"T.lean": hashlib.sha256(b"original").hexdigest()}}))
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(ValueError, "inventory"):
                verify.check_sources()

    def test_escaping_input_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp) / "inside"
            root.mkdir()
            (root.parent / "outside").write_text("not a source")
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(ValueError, "escaping"):
                verify.input_file("../outside")

    def test_unpinned_dependency_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [{"type": "path"}]}))
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(ValueError, "Unpinned"):
                verify.check_dependencies()


if __name__ == "__main__":
    unittest.main()
