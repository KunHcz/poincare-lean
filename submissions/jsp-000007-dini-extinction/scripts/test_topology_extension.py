"""Failure-mode tests for the additive upstream topology verifier."""
import unittest
from verify_topology_extension import parse_axioms, check_diagnostics, KNOWN_WARNING


class TopologyEvidenceTests(unittest.TestCase):
    def test_wrapped_axioms(self):
        self.assertEqual(parse_axioms("'A'\ndepends on axioms:\n[propext, Quot.sound]", ["A"]),
                         {"A": ["propext", "Quot.sound"]})

    def test_extra_axiom(self):
        for name in ["sorryAx", "Lean.ofReduceBool", "PoincareConjecture.fake"]:
            with self.subTest(name=name), self.assertRaises(ValueError):
                parse_axioms(f"'A' depends on axioms: [{name}]", ["A"])

    def test_missing_and_duplicate(self):
        for text in ["", "'AB' does not depend on any axioms",
                     "'A' does not depend on any axioms\n" * 2]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                parse_axioms(text, ["A"])

    def test_known_pinned_warning(self):
        self.assertEqual(check_diagnostics(KNOWN_WARNING), [KNOWN_WARNING])

    def test_clean(self):
        self.assertEqual(check_diagnostics("Build completed successfully."), [])

    def test_other_warning_formats(self):
        for text in ["warning: another warning", "File.lean:1:0: warning: unused variable",
                     "File.lean:1:0: warning(lean.foo): unrecognized condition"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                check_diagnostics(text)

    def test_error_formats(self):
        for text in ["error: failure", "error(lean.synthInstanceFailed): missing assumption",
                     "File.lean:1:0: error(lean.foo): failure", "File.lean:1:0: error: failure"]:
            with self.subTest(text=text), self.assertRaises(ValueError):
                check_diagnostics(text)


if __name__ == "__main__":
    unittest.main()
