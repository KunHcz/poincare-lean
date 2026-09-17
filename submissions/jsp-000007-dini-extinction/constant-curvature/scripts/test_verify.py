import unittest

from verify import parse_axioms


class AxiomParsingTests(unittest.TestCase):
    def test_allowed(self):
        self.assertEqual(parse_axioms("'T' depends on axioms: [propext, Classical.choice, Quot.sound]", ["T"]),
                         {"T": ["propext", "Classical.choice", "Quot.sound"]})

    def test_multiline(self):
        self.assertEqual(parse_axioms("'T'\ndepends on axioms:\n[propext,\n Quot.sound]", ["T"]),
                         {"T": ["propext", "Quot.sound"]})

    def test_no_axioms(self):
        self.assertEqual(parse_axioms("'T' does not depend on any axioms", ["T"]), {"T": []})

    def test_missing(self):
        with self.assertRaises(ValueError):
            parse_axioms("", ["T"])

    def test_duplicate(self):
        with self.assertRaises(ValueError):
            parse_axioms("'T' does not depend on any axioms\n" * 2, ["T"])

    def test_exact_name(self):
        with self.assertRaises(ValueError):
            parse_axioms("'TT' does not depend on any axioms", ["T"])

    def test_rejects_nonstandard_axioms(self):
        for name in ["sorryAx", "Lean.ofReduceBool", "PoincareHamilton.forged"]:
            with self.subTest(name=name), self.assertRaises(ValueError):
                parse_axioms(f"'T' depends on axioms: [{name}]", ["T"])


if __name__ == "__main__":
    unittest.main()
