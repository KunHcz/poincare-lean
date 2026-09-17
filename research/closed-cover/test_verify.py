import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import verify


class ClosedCoverVerificationTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(verify.shared.parse_axioms("'T' depends on axioms: [propext, Quot.sound]", ["T"]),
                         {"T": ["propext", "Quot.sound"]})

    def test_placeholder_axiom_rejected(self):
        with self.assertRaises(ValueError):
            verify.shared.parse_axioms("'T' depends on axioms: [sorryAx]", ["T"])

    def test_missing_or_duplicate_audit_rejected(self):
        for text in ["", "'T' does not depend on any axioms\n" * 2]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                verify.shared.parse_axioms(text, ["T"])

    def test_fingerprint_is_order_independent(self):
        self.assertEqual(verify.fingerprint({"a": 1, "b": 2}), verify.fingerprint({"b": 2, "a": 1}))

    def test_changed_inputs_change_fingerprint(self):
        self.assertNotEqual(verify.fingerprint({"source": "first"}), verify.fingerprint({"source": "second"}))

    def test_missing_kernel_completion_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state = root / "state.json"
            state.write_text(json.dumps({"fingerprint": verify.fingerprint({}), "prepare_pass": True,
                                         "kernel_pass": False, "log_hashes": {}}))
            with patch.object(verify, "STATE", state), self.assertRaisesRegex(ValueError, "Earlier stage"):
                verify.load_stage({}, "kernel_pass")

    def test_changed_stage_log_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            state = root / "state.json"
            state.write_text(json.dumps({"fingerprint": verify.fingerprint({}), "kernel_pass": True,
                "log_hashes": {"kernel.log": hashlib.sha256(b"original").hexdigest()}}))
            (root / "kernel.log").write_text("changed")
            with patch.object(verify, "STATE", state), patch.object(verify, "OUT", root), \
                    self.assertRaisesRegex(ValueError, "log changed"):
                verify.load_stage({}, "kernel_pass")

    def test_escaping_source_rejected(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp) / "inside"
            root.mkdir()
            (root.parent / "outside").write_text("not a submitted source")
            with patch.object(verify, "ROOT", root), self.assertRaisesRegex(ValueError, "escaping"):
                verify.safe_path("../outside")


if __name__ == "__main__":
    unittest.main()
