"""Tests for the fail-closed parser used by the submission verification script."""
import unittest
from verify import parse_axioms


class AuditParserTests(unittest.TestCase):
    def test_standard_axioms(self):
        self.assertEqual(parse_axioms("'A' depends on axioms: [propext, Classical.choice, Quot.sound]", ["A"]),
                         {"A": ["propext", "Classical.choice", "Quot.sound"]})

    def test_empty(self):
        self.assertEqual(parse_axioms("'A' does not depend on any axioms", ["A"]), {"A": []})

    def test_missing(self):
        with self.assertRaises(ValueError):
            parse_axioms("", ["A"])

    def test_duplicate(self):
        with self.assertRaises(ValueError):
            parse_axioms("'A' does not depend on any axioms\n" * 2, ["A"])

    def test_unapproved(self):
        for axiom in ["sorryAx", "Lean.ofReduceBool", "PoincareConjecture.forged"]:
            with self.subTest(axiom=axiom), self.assertRaises(ValueError):
                parse_axioms(f"'A' depends on axioms: [{axiom}]", ["A"])

    def test_exact_name(self):
        with self.assertRaises(ValueError):
            parse_axioms("'AB' does not depend on any axioms", ["A"])


if __name__ == "__main__":
    unittest.main()
