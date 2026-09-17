"""Independent exhaustive finite set models, not a substitute for Lean topology.

Every pair of subsets of sets of size 0 through 5 is checked: 1,365 pairs.
This exercises the exact equivalence relation and the complementary-side
identities used by the formal proof; it makes no continuous-manifold claim.
"""
import itertools
import unittest


def subsets(universe):
    items = sorted(universe)
    return [set(items[i] for i in range(len(items)) if mask & (1 << i))
            for mask in range(1 << len(items))]


def glued_classes(left, right):
    parent = {("L", x): ("L", x) for x in left}
    parent.update({("R", x): ("R", x) for x in right})

    def root(node):
        while parent[node] != node:
            parent[node] = parent[parent[node]]
            node = parent[node]
        return node

    for x in left & right:
        parent[root(("R", x))] = root(("L", x))
    classes = {}
    for node in parent:
        classes.setdefault(root(node), set()).add(node)
    return list(classes.values())


class FiniteClosedCoverModels(unittest.TestCase):
    def test_every_small_cover_quotient_and_missing_cover(self):
        count = 0
        for n in range(6):
            universe = set(range(n))
            for left, right in itertools.product(subsets(universe), repeat=2):
                classes = glued_classes(left, right)
                values = []
                for equivalence_class in classes:
                    point_values = {point for _, point in equivalence_class}
                    self.assertEqual(len(point_values), 1)
                    values.append(next(iter(point_values)))
                self.assertEqual(len(values), len(set(values)))
                self.assertEqual(set(values), left | right)
                self.assertEqual(set(values) == universe, left | right == universe)
                count += 1
        self.assertEqual(count, 1365)

    def test_every_small_complementary_side_identity(self):
        count = 0
        for n in range(6):
            universe = set(range(n))
            for u, v in itertools.product(subsets(universe), repeat=2):
                a, b = universe - v, universe - u
                self.assertEqual(a & b, universe - (u | v))
                self.assertEqual(a | b == universe, not (u & v))
                if not (u & v):
                    self.assertTrue(u <= a)
                    self.assertTrue(v <= b)
                count += 1
        self.assertEqual(count, 1365)


if __name__ == "__main__":
    unittest.main()
