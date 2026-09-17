import hashlib
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import json

import verify


class PositiveRicciVerifierTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(verify.shared.parse_axioms("'T' depends on axioms: [propext, Quot.sound]", ["T"]),
                         {"T": ["propext", "Quot.sound"]})

    def test_nonstandard_axiom_rejected(self):
        with self.assertRaises(ValueError):
            verify.shared.parse_axioms("'T' depends on axioms: [sorryAx]", ["T"])

    def test_duplicate_rejected(self):
        with self.assertRaises(ValueError):
            verify.shared.parse_axioms("'T' does not depend on any axioms\n" * 2, ["T"])

    def test_wrong_source_hash_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "T.lean").write_text("changed")
            (root / "source-manifest.json").write_text(json.dumps({"files": {"T.lean": "wrong"}}))
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(RuntimeError, "Source differs"):
                verify.check_source()

    def test_extra_lean_file_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "T.lean").write_text("original")
            digest = hashlib.sha256(b"original").hexdigest()
            (root / "source-manifest.json").write_text(json.dumps({"files": {"T.lean": digest}}))
            (root / "Extra.lean").write_text("unexpected")
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(RuntimeError, "inventory changed"):
                verify.check_source()

    def test_local_dependency_rejected(self):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "lake-manifest.json").write_text(json.dumps({"packages": [{"type": "path"}]}))
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(RuntimeError, "unpinned"):
                verify.check_pins()


if __name__ == "__main__":
    unittest.main()
