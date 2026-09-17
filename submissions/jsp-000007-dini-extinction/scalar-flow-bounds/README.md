# Geometric scalar bounds for the general three-dimensional Ricci-flow route

This component proves scalar-curvature estimates for **genuine compact smooth
three-dimensional Ricci flows without a positive-curvature assumption**. It
connects the scalar estimates needed in the extinction argument to the actual
evolving metric, rather than assuming an abstract scalar differential
inequality. It belongs to the same JSP-000007 application as the existing
analysis, topology, orientability and restricted geometric components.

**It does not construct a Ricci flow or a surgery flow, prove geometric finite
extinction, or close the unrestricted Poincare theorem.** The existence of a
smooth flow segment satisfying the metric Ricci-flow equation is an input.
No connectedness, simple-connectivity, spherical-quotient, positive-Ricci or
positive-scalar assumption is used for these estimates.

## Actual formal input

The manifold carries the original Mathlib charted-space and smooth structure
modeled on real three-space, together with compactness and the Hausdorff
property. `S : SolutionOn ... D` is the upstream metric-family object.
`IsSolutionOn S` requires its metric Ricci-flow equation and regularity.
The proof's scalar curvature is `S.scalar`, defined by the original metric's
Ricci contraction, not a free scalar function attached to the data.

The relevant input predicate includes smoothness of the metric and its
canonical connection, the metric evolution equation, and time/space
continuity and differentiability conditions. It does **not** include the
claimed lower bound, its scalar evolution formula, an initial scalar minimum,
a maximum-principle conclusion, or a future extinction certificate. The
scalar evolution is obtained by the pinned `smoothOfSol` and intrinsic
evolution theorems; the comparison regularity, compact value set, Lipschitz
constant, and intrinsic Ricci trace estimate are all produced inside the
local proof.

## Completed statements

The source is [ScalarFlowBounds.lean](ScalarFlowBounds.lean). For any
nonpositive initial scalar lower bound `c`, it proves throughout the
closed-open smooth flow interval:

```text
R(0,x) >= c  implies  R(t,x) >= c / (1 - (2/3)c t).
```

The normalized case `normalized_scalar_lower_bound` gives the exact estimate
used by the submitted extinction comparison:

```text
R(0,x) >= -6  implies  R(t,x) >= -6 / (1 + 4t).
```

The initial time `t = 0` is included; positive-time use of the maximum
principle is handled separately. Compactness supplies a nonpositive lower
bound for the actual initial metric, giving the initial-metric-independent
estimate `universal_scalar_lower_bound`:

```text
0 < t  implies  R(t,x) >= -3 / (2t).
```

The rational barrier satisfies an exact restart identity. Hence a later
smooth segment beginning at global time `a` with the inherited bound
`R_new(0,x) >= -6/(1+4a)` obeys

```text
R_new(u,x) >= -6 / (1 + 4(a+u)).
```

This proves that using a fresh segment does not reset the global barrier
clock. It does not assert that a geometric surgery has produced this segment
or preserved its inherited initial bound. That geometric surgery obligation
remains separate and is recorded as unproved in the evidence.

## Statement and regression checks

There are 13 production theorems and eight regression theorems. The
[regression module](ScalarFlowBoundsTests.lean) checks the exact initial
constant and value at time one, the restart clock, why negative time cannot
be admitted, and a scalar counterexample showing that continuity alone is
not a Ricci-flow estimate. Two endpoint regressions are written literally
using `metricScalarAt` of `S.base.metric`, exposing the geometric meaning of
the bound.

The scalar counterexample is explicitly not a geometric Ricci-flow model.
No new concrete flow, such as a sphere or torus solution, is constructed by
this package. The theorem is a universally quantified estimate conditional
on the real smooth metric evolution, not a new existence theorem.

## Reproduce

This standalone root retains Lean 4.33.1, compiler
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474` and DifferentialGeometry
`ad76f2f1dfb959f4d8fc46fac9ed9feffdf497d9`. The latter contains the previously
disclosed single-file proof-cost fix in
[geometry PR #78](https://github.com/qinz1yang/differential-geometry/pull/78);
its original geometric theorem statements and definitions are unchanged.
All pins are in [lake-manifest.json](lake-manifest.json).

```sh
cd submissions/jsp-000007-dini-extinction/scalar-flow-bounds
lake exe cache get
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier checks the complete source inventory and hashes, the Lean
compiler, every dependency revision and tracked file state, the full default
build with warnings as errors, all 21 explicit production/regression axiom
dependencies and both namespaces. It then runs
`leanchecker --verbose --fresh ScalarFlowBoundsAudit` and requires rejection
of extra axioms, placeholders, replacing the actual solution hypothesis by
`True`, deleting the normalized initial bound, and an incorrect barrier
value. The final source and dependency identities are checked again.

The [completed verification record](evidence/verification.json) identifies
the actual outcomes. A time/resource guard or incomplete run is not a pass.
The verifier reuses the unchanged command/axiom helpers in the earlier
constant-curvature package, while maintaining an independent source root,
import closure and evidence record. Earlier package records are not
rewritten or treated as verification of this package.

All fresh replays use Lean's own kernel, not a separately implemented checker
or designated expert review. Dependency caches may be reused; the record
does not claim a clean from-source rebuild of every dependency. There is no
official prize approval, priority ruling, award amount or payment claim.

## Attribution and remaining scope

The scalar maximum-principle estimates are classical Ricci-flow mathematics.
The underlying intrinsic scalar evolution, tensor inequalities, maximum
principle and regularity formalizations are credited to the independent
DifferentialGeometry authors, with Lean and Mathlib retaining their credit.
The local contribution removes the need to supply the auxiliary analytic
conditions separately, derives the actual metric estimates for the general
smooth-flow input, and checks the normalized and restarted constants. This
is not a new discovery of the scalar-curvature inequality. See [NOTICE](NOTICE).

This is an AI-assisted submission with a direct interest in the outcome.
The existing placeholder `RECIPIENT-jsp-000007-dini-extinction-A` remains
unconfirmed. Full surgery existence/control, preservation across caps,
geometric width/extinction, topology reconstruction and three-dimensional
smoothability remain outstanding in the overall application. The
unrestricted Poincare target is not changed to assume one of those results.
