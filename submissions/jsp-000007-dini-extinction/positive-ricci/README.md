# Positive-Ricci case of JSP-000007

## Exact contribution and remaining restriction

The endpoint proves: a closed, simply connected smooth three-manifold that
admits a **genuine positive-Ricci Riemannian metric** is diffeomorphic to the
standard three-sphere. Its underlying topology is therefore homeomorphic to
the standard sphere as well. The endpoint does not assume a spherical
presentation, a constant-curvature metric, a flow, or the sphere conclusion.

The positive-Ricci metric is nevertheless an explicit additional hypothesis.
**This is not the unrestricted topological Poincare theorem**, and it does
not prove that every closed simply connected three-manifold has such a
metric. General surgery, geometric extinction, reconstruction, and the
topological smoothability bridge remain separate obligations.

The theorem is `PoincareHamilton.positiveRicci_poincare` in
[PositiveRicci.lean](PoincareHamilton/PositiveRicci.lean). Its two geometric
predicates are unchanged upstream definitions. `isClosedThreeManifold`
supplies compactness, connectedness, boundarylessness and real dimension
three. `admitsPositiveRicci` supplies a smooth metric `g` whose actual Ricci
tensor satisfies `Ric_g(v,v) > 0` for every nonzero tangent vector at every
point. The [literal-metric regressions](PoincareHamiltonTests.lean) expand the
latter condition, using the original `metricRicciAt` tensor.
The [Lean-expanded statements](evidence/statements.log) record the actual
elaborated hypotheses and the underlying definitions, including the
four-dimensional ambient space of the target unit three-sphere. This is
supporting statement-fidelity evidence, not designated human review.

## Attribution: integration is not the Hamilton formalization

The classical geometric result is Richard Hamilton's 1982 theorem,
[*Three-manifolds with positive Ricci curvature*](https://projecteuclid.org/journals/journal-of-differential-geometry/volume-17/issue-2/Three-manifolds-with-positive-Ricci-curvature/10.4310/jdg/1214436922.short).
The substantial Lean formalization of that result and its geometric-analysis
infrastructure is the independent work documented by Bennett Chow, Yuan Liao
and Ziyang Qin in [their 2026 paper](https://arxiv.org/abs/2608.21502).
That work is a dependency, **not the applicant's original formalization**.
The paper describes its own release; it is cited for authorship and the
mathematical route, not as verification of this package's newer source pin.

The applicant's contribution here is the checked integration with the
projection/covering sphere-recognition proof, literal-condition regression
checks, reproducibility evidence, and a proof-cost repair needed for local
verification. The actual quotient projection is shown locally invertible
from its provided smooth sections and orbit-transitivity data, then globally
invertible by compactness and simple connectivity. No faithful-group-action
hypothesis is added. Earlier covering arguments are reused and are not
claimed a second time as new work.

The same application already includes the analytic, topology, orientability,
and constant-curvature components. This is an additive restricted-case
extension, not a separate priority or payment claim. Classical solver credit
and all library authorship are retained. See [NOTICE](NOTICE).

## Disclosed dependency repair

This root pins DifferentialGeometry to
`ad76f2f1dfb959f4d8fc46fac9ed9feffdf497d9`, the applicant's
[upstream PR #78](https://github.com/qinz1yang/differential-geometry/pull/78),
based on upstream `1b535dd102b94cc42b107cca27059687888f08b3`.
Exactly one source file differs: `HomFieldCurvatureJetDecomposition.lean`.
Its large concrete tensor rewrite is factored through an additive-group
identity; all 17 original theorem/lemma signatures were preserved. No
geometric definition, theorem assumption, project axiom or placeholder was
introduced. This repair is disclosed rather than silently replacing the
published source. The earlier constant-curvature evidence retains its
original, unmodified geometry pin.

The formal Hamilton dependency target was built successfully on the repaired
checkout before the integration. A source build is distinct from the fresh
kernel-replay result in this package's verification record.

## Reproduction

The fixed toolchain is Lean 4.33.1, compiler
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; Mathlib is
`0df444a360eaa60ab8c11dca51a86af692955474`. All dependencies are Git-pinned
in [lake-manifest.json](lake-manifest.json). Requirements are Git, elan,
Python 3.9 or newer, and a POSIX environment providing `ps` process-group
statistics. The first geometry build and full kernel replay are substantial.

```sh
cd submissions/jsp-000007-dini-extinction/positive-ricci
lake exe cache get
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier rejects wrong source hashes, untracked extra Lean files, wrong
dependency revisions, tracked dependency edits, and a dependency repair
outside its disclosed file. It performs the warning-as-error default build,
the explicit transitive axiom inventory, the namespace-wide audit, and
`leanchecker --verbose --fresh PoincareHamiltonAudit`. It also requires
rejection of an added axiom, a placeholder, deletion of Ricci positivity,
and deletion of simple connectivity. Sources and pins are checked again at
the end. Its resource guards never turn an unfinished run into success.

[The verification record](evidence/verification.json) is the authority for
the actual completed local run. The default import closure has three local
regression theorems. It does not contain a separate explicit round-sphere
Ricci calculation, and the record deliberately marks that additional model
test false. The earlier constant-curvature package and its geometric witness
tests retain their own independent source and evidence; they are not silently
presented as part of this endpoint's replay.

Both checkers use Lean's own kernel implementation. No independent checker
implementation, designated human review, clean rebuild of every dependency
from source, or official prize approval is claimed. The applicant is an
AI-assisted formalizer with a direct interest in the outcome; the placeholder
`RECIPIENT-jsp-000007-dini-extinction-A` remains unconfirmed. Eligibility,
formalization priority, allocation and payment remain undetermined.
