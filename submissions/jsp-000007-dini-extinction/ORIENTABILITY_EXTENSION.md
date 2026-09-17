# Additive orientability extension

This is the same JSP-000007 application, extended by a proof of the
orientability step for **arbitrary simply connected C1 three-manifolds**.
There is no curvature, compactness, spherical-presentation or surgery
hypothesis in this new theorem. It is still a component of the general
Poincare proof, not a proof of that entire proposition or a new prize claim
for the older analytic and topological components.

The exact immutable source is
[`d5cf293fcee9164a449fcc833d049d51aab52bc3`](https://github.com/KunHcz/Poincare-Conjecture/tree/d5cf293fcee9164a449fcc833d049d51aab52bc3/PoincareConjecture),
proposed in the same [upstream PR #34](https://github.com/frenzymath/Poincare-Conjecture/pull/34).
The older `f07c59b...` topology snapshot and the separately pinned
constant-curvature package remain unchanged.

## What the formal statement actually means

The source constructs the orientation double cover from the determinants of
the **actual tangent-bundle coordinate changes** in Mathlib. Those changes
are derivatives of the manifold's original chart transitions. The proof
establishes the nonzero determinants, their sign cocycle, continuity, genuine
two-point fibres, and covering property. None of those conclusions is a
supplied orientation certificate.

Lifting the identity map of the simply connected base constructs a continuous
section. Its local coordinates supply compatible orientation signs. In
three dimensions these are realized by the identity or negative identity of
the tangent model. The companion theorem produces actual continuous local
frame changes that square to the identity and make every transformed
tangent-transition determinant strictly positive.

This is the standard positive-transition criterion for orientability of the
tangent bundle. The exposed predicate is `HasPositiveOrientationAtlas`;
the submission does not claim to instantiate a pre-existing Mathlib global
manifold-orientability class. The criterion is stated explicitly and is
backed by the literal invertible-frame conclusion, not by an opaque marker.
See the [statement correspondence](https://github.com/KunHcz/Poincare-Conjecture/blob/d5cf293fcee9164a449fcc833d049d51aab52bc3/PoincareConjecture/ORIENTABILITY_VALIDATION.md).

The general topological Poincare target is unchanged byte-for-byte. The
three-dimensional smoothability bridge is not supplied by this C1 result.
Neither the full Ricci-surgery argument nor the full Poincare theorem is
claimed complete.

## Reproduce

```sh
cd submissions/jsp-000007-dini-extinction
python3 -m unittest discover -s scripts -p 'test_orientability_extension.py' -v
python3 scripts/verify_orientability_extension.py
```

The verifier checks out the pinned public commit under an ignored local
directory, or accepts `--checkout /path/to/an/existing/clean/exact/checkout`.
It rejects a wrong revision or changed tracked source rather than resetting
the supplied directory. It reuses the unchanged process, warning and axiom
parsers from the earlier topology verifier.

The fixed source uses Lean 4.32.1 and the same Mathlib/Hatcher pins as the
topology extension. Its default build includes all old regressions and the
new seven orientability regressions, followed by the namespace-wide axiom
audit. The new regressions include a genuine two-chart bundle with negative
transition determinant; its compatible orientations must use opposite
signs. A separate theorem verifies that every orientation-cover fibre
contains two different lifts of the same base point.

The extension verifier audits all 60 production theorems in that snapshot,
identifies the 15 new orientation theorems, and runs a full
`leanchecker --verbose --fresh PoincareConjectureTests` replay. It requires
rejection of an added axiom, a placeholder, removal of simple connectivity,
and changing the sign-gluing rule to the identity. Source and dependency
pins are checked again after execution.

Actual local outcomes are recorded separately in
[the extension evidence](evidence/orientability-extension/verification.json).
This is Lean's own kernel, not an independently implemented checker or
designated prize review. The unchanged Hatcher `unitCircleCov` style warning
is recorded explicitly; no other warning is accepted by the verifier.

A requested blueprint graph-structure check was blocked by the local
execution permission layer and was not run. The extension does not report
that check as passed. The Lean proof, source identity, axiom audit and kernel
replay are separate checks and are reported on their own evidence.

This is AI-assisted formalization of the classical orientation-cover
argument, not a new mathematical discovery. Mathlib and the source authors
retain their attribution. The proposed formalizer remains
`RECIPIENT-jsp-000007-dini-extinction-A`, pending the operator's confirmation.
No eligibility decision, formalization priority, award amount or payment is
asserted.
