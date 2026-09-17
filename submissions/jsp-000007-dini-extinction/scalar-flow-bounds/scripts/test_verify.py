import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify


class ScalarFlowVerifierTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(verify.shared.parse_axioms("'T' depends on axioms: [propext, Quot.sound]", ["T"]),
                         {"T": ["propext", "Quot.sound"]})

    def test_nonstandard_axiom_rejected(self):
        with self.assertRaises(ValueError):
            verify.shared.parse_axioms("'T' depends on axioms: [sorryAx]", ["T"])

    def test_missing_audit_rejected(self):
        with self.assertRaises(ValueError):
            verify.shared.parse_axioms("", ["T"])

    def test_changed_source_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "T.lean").write_text("changed")
            (root / "source-manifest.json").write_text(json.dumps({"files": {"T.lean": "wrong"}}))
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(RuntimeError, "Source differs"):
                verify.sources()

    def test_extra_lean_source_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "T.lean").write_text("original")
            (root / "source-manifest.json").write_text(json.dumps({
                "files": {"T.lean": hashlib.sha256(b"original").hexdigest()}}))
            (root / "Extra.lean").write_text("unexpected")
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(RuntimeError, "inventory"):
                verify.sources()

    def test_local_dependency_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [{"type": "path"}]}))
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(RuntimeError, "Unpinned"):
                verify.dependencies()


if __name__ == "__main__":
    unittest.main()
