# Constant-positive-sectional-curvature case of JSP-000007

This additive component proves the sphere conclusion for a **closed, simply
connected smooth three-manifold admitting a constant-positive-sectional-curvature
metric**. Unlike the earlier quotient endgame, its endpoint does not assume a
spherical quotient presentation: that presentation is obtained from the pinned
upstream classification theorem, then its actual projection is proved to be a
diffeomorphism.

**The curvature condition remains an explicit restriction.** This is not the
unrestricted topological Poincare theorem, not its positive-Ricci-curvature
case, and not a Pinnacle closure claim. It is part of the same JSP-000007
application, not a second claim for the analytic or topological work already
submitted. Eligibility and attribution remain for the prize operator to decide.

## Exact endpoint

The production statements are in
[SphericalSpaceForm.lean](PoincareHamilton/SphericalSpaceForm.lean).
`constantPositiveCurvature_poincare` concludes an actual diffeomorphism to the
standard three-sphere, and `constantPositiveCurvature_homeomorph_sphere`
concludes a homeomorphism on the same underlying topology.

The assumptions are Mathlib's topological and smooth manifold structures,
simple connectivity, and these unchanged upstream predicates:

```lean
isClosedThreeManifold (I := 𝓡 3) (M := M)
admitsConstantPositiveSectionalCurvature (I := 𝓡 3) (M := M)
```

The first supplies compactness, connectedness, absence of boundary and
dimension three. The second supplies a genuine smooth Riemannian metric `g`,
a real constant `c > 0`, and the pointwise curvature identity

```text
Rm_g(X,Y,Y,X) = c (g(X,X) g(Y,Y) - g(X,Y)^2).
```

The [literal-metric regression](PoincareHamiltonTests.lean) expands that
second predicate using the actual upstream curvature tensor. It does not
replace it with a certificate that the conclusion is true. Other regressions
construct the round sphere's closedness and constant-curvature metric and
check that the constructed diffeomorphism really is the supplied projection.
These geometric witness tests do not purport to add a new proof of the
three-sphere's simple connectivity.

## The integration gap actually filled

The upstream `RoundQuotientData` permits an orthogonal representation with a
kernel. Its presenting group therefore cannot simply be asserted trivial.
[RoundQuotient.lean](PoincareHamilton/RoundQuotient.lean) instead derives
surjectivity of the projection derivative at every lift, starting from the
provided smooth local sections and orbit transitivity. The inverse function
theorem gives a local diffeomorphism. Compactness gives a covering; path
lifting and simple connectivity of the base make it injective. The resulting
global diffeomorphism eliminates the quotient without adding faithfulness,
freeness, or projection invertibility as extra hypotheses.

## Pinned reproduction

This component has its own Lake root. It does not upgrade or replace the
original analytic and topology snapshots, which remain on Lean 4.32.1.

- Lean **4.33.1**, compiler `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`.
- DifferentialGeometry `1b535dd102b94cc42b107cca27059687888f08b3`.
- Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.
- All other Git dependencies are pinned in [lake-manifest.json](lake-manifest.json).

```sh
cd submissions/jsp-000007-dini-extinction/constant-curvature
lake exe cache get
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier checks source hashes and every dependency revision and tracked
file state before and after the run. It builds every default target with
warnings treated as errors, audits the two complete local namespaces and nine
named critical declarations, and invokes:

```sh
lake env leanchecker --verbose --fresh PoincareHamiltonAudit
```

It also requires rejection of injected axioms, placeholder proofs, removal of
the curvature condition, and removal of simple connectivity. The generated
negative fixtures stay under ignored `.lake/verification/`. A run marks its
report incomplete before starting and only records success after all checks.
The [source manifest](source-manifest.json) fixes the proof/configuration files;
the [verification record](evidence/verification.json) includes their hashes.

`leanchecker` uses Lean's own kernel implementation, not a second independent
checker. Compiled dependency caches may be reused before full fresh-environment
kernel replay. Neither a clean from-source rebuild of every dependency nor
designated human review is claimed. Prize-repository record tests do not
execute this Lean proof and are not an award decision.

## Attribution and remaining scope

The mathematics is classical constant-curvature classification, not a new
solution to Poincare. The substantial upstream metric, curvature, covering,
and classification formalization belongs to the
[DifferentialGeometry authors](https://github.com/qinz1yang/differential-geometry/tree/1b535dd102b94cc42b107cca27059687888f08b3).
Mathlib and Lean retain their respective authorship. This applicant's
contribution is the checked projection/recognition integration and supporting
tests, not a claim to have written those dependencies. See [NOTICE](NOTICE).

This is an AI-assisted self-submission with a direct interest in the outcome;
the existing placeholder `RECIPIENT-jsp-000007-dini-extinction-A` remains
unconfirmed. No mathematical-discovery priority, formalization priority,
review signature, award tier, allocation or payment is asserted.

General Ricci flow with surgery, geometric extinction, reconstruction, and
three-dimensional smoothability remain outside the proved endpoint. The
unrestricted target is not weakened by adding the curvature premise. An
unverified positive-Ricci integration and the unfinished cap-filling candidate
are deliberately excluded from this package.
