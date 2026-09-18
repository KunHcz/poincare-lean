import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify


class GeneralFlowVerifierTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(verify.shared.parse_axioms("'T' depends on axioms: [propext, Quot.sound]", ["T"]),
                         {"T": ["propext", "Quot.sound"]})

    def test_nonstandard_axiom_rejected(self):
        with self.assertRaises(ValueError):
            verify.shared.parse_axioms("'T' depends on axioms: [sorryAx]", ["T"])

    def test_missing_or_duplicate_audit_rejected(self):
        for text in ["", "'T' does not depend on any axioms\n" * 2]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                verify.shared.parse_axioms(text, ["T"])

    def test_changed_source_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "T.lean").write_text("changed")
            (root / "source-manifest.json").write_text(json.dumps({"files": {"T.lean": "wrong"}}))
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(ValueError, "Changed submitted source"):
                verify.check_sources()

    def test_extra_source_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "T.lean").write_text("original")
            (root / "Extra.lean").write_text("unexpected")
            (root / "source-manifest.json").write_text(json.dumps({
                "files": {"T.lean": hashlib.sha256(b"original").hexdigest()}}))
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(ValueError, "inventory"):
                verify.check_sources()

    def test_source_escape_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "inside"
            root.mkdir()
            (root.parent / "outside").write_text("not public source")
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(ValueError, "escaping"):
                verify.safe_source("../outside")

    def test_unpinned_dependency_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [{"type": "path"}]}))
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(ValueError, "Unpinned"):
                verify.check_dependencies()


if __name__ == "__main__":
    unittest.main()
