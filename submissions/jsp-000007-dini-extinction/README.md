# JSP-000007: analytic, topological, and restricted geometric formalizations

**Newly completed restricted case:** the [positive-Ricci package](positive-ricci/README.md)
proves the sphere conclusion under an explicit positive-Ricci metric
hypothesis. Its full fresh kernel replay and negative controls have finished;
the [source-bound record](positive-ricci/evidence/verification.json) reports
the actual checks. It does not remove that geometric hypothesis or prove
the unrestricted topological Poincare theorem.

**Extended submission:** the [additive topology supplement](TOPOLOGY_EXTENSION.md)
provides an immutable 45-theorem upstream snapshot, including three additional
topological endgame components, and a separate executable verifier. The original
15-theorem analytic package described below remains unchanged and reproducible.
Neither version proves the full Poincare theorem.

**Additional geometric case:** the separate
[constant-positive-curvature component](constant-curvature/README.md)
proves the sphere conclusion with an explicit genuine constant-positive-
sectional-curvature metric hypothesis, without assuming a spherical
presentation. It has its own pinned Lean 4.33.1 package and verification.
It is not the unrestricted theorem or a second claim for the earlier work.
The scope described below is the original analytic snapshot.

The later [orientability extension](ORIENTABILITY_EXTENSION.md) adds the
orientation-double-cover and positive-tangent-frame proof for general
simply connected C1 three-manifolds. It is pinned and verified separately;
the original sources and earlier evidence are not replaced.

## Original analytic snapshot

This is a **self-submitted proof and evidence package for award-intake and
eligibility review**, related to the [Poincare conjecture entry](../../problems/catalog-0001-0100.md#JSP-000007).
It contains complete Lean proofs of three analytic steps used in a
finite-extinction proof architecture. **It is not a formalization of the
Poincare theorem, a geometric special case of that theorem, or a Pinnacle
closure claim.**

The request is to assess the exact completed component described in
[STATEMENT.md](STATEMENT.md), including whether it is independently awardable
as a formalization/community contribution. No award amount, tier, mathematical
discovery priority, confirmed recipient, or entitlement is asserted.
The main geometric prerequisites remain outside the submitted proof.

## What is submitted

- Upper right Dini comparison for continuous, possibly nondifferentiable
  subsolutions, including derivation of the required local Lipschitz estimate
  from a C1 right-hand side.
- Comparison across any finite strict partition with downward jumps, explicitly
  controlling the final endpoint. A Lean counterexample demonstrates the missing
  endpoint hypothesis in the starting upstream blueprint.
- The exact scalar barrier for `w' = -2π + 3w/(1+4t)`: initial value, derivative,
  sensitivity to the initial width, eventual negativity, and a lifetime bound
  independent of the number and placement of partition points.

There are 15 production theorems, plus eight named regression theorems and two
regression examples. The default build audits the transitive axiom dependencies
of every declaration in the production and test namespaces. It allows only
`propext`, `Classical.choice`, and `Quot.sound`.

## Relationship to the upstream PR

The Lean source and Lake files are copied **without mathematical changes** from
commit `94e8e2d105155e21ca8a78716258c12d22b45562` of the Poincare development,
submitted in [frenzymath/Poincare-Conjecture PR #34](https://github.com/frenzymath/Poincare-Conjecture/pull/34).
The hashes are recorded in [verification-config.json](verification-config.json).
This awards submission and that upstream PR concern **the same contribution**,
not two independently originated results or two separate payment claims.
The upstream PR provides integration and review context; it is not treated as
prize entry or as evidence of maintainer acceptance.

`submissions/` is a proposed intake location, consistent with this applicant's
earlier proof-package PRs. It is not an announced official proof-package schema.
Please redirect the package if another intake location is required. No existing
catalog flags, candidate statuses, recipient profiles, or award decisions are changed.

## Reproduce

Requirements: Git, Python 3.9 or later for this package, and the pinned Lean
toolchain through elan. Repository-level record validation requires Python 3.10
or later, as documented in the repository's record guide.

```sh
cd submissions/jsp-000007-dini-extinction
lake exe cache get
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The verifier checks all pinned dependency revisions and unchanged source
hashes, removes only this package's generated build directory, rebuilds with
warnings as errors, explicitly audits all 15 production theorems, and runs:

```sh
lake env leanchecker --verbose --fresh PoincareConjectureTests
```

It also requires rejection of an injected extra axiom, an injected placeholder
proof, and an incorrect scalar initial value. The injected fixtures and build
products stay under the ignored `.lake/` directory. A new verification run
invalidates any previous success report before proceeding.

Lean is pinned to `v4.32.1`, compiler
`f054605aea4b840552cca2e725580bffd1e1b704`; Mathlib is pinned to
`520045ab14e26149ee970e2e617ca04b09bde5d6`. Other dependencies are pinned by
`lake-manifest.json`.

## Evidence and limits

See [evidence/verification.json](evidence/verification.json) for the local check
result and [evidence/axioms.log](evidence/axioms.log) for the explicit dependency
audit. Logs describe actual local checks, not designated prize verification.
The standard `leanchecker --fresh` uses the **same Lean kernel implementation**;
it is not an independently implemented checker. Dependency compilation caches
may be reused, followed by fresh-environment kernel replay; no complete
from-source dependency rebuild or second-machine human review is claimed.

Permanent independent archival, statement-fidelity review by designated
reviewers, formalization priority, and award eligibility remain unconfirmed.
The awards repository's CI checks records and links; it does not execute the
Lean package. Passing those checks is not an award decision.

## Attribution

This is an AI-assisted self-submission with a direct interest in the outcome.
The proposed formalizer is `RECIPIENT-jsp-000007-dini-extinction-A`, pending
the operator's confirmation. Classical mathematical credit remains with the
sources described in [PRIOR_ART.md](PRIOR_ART.md); no solver share for the
Poincare conjecture is claimed. No private contact, KYC, or payment information
is part of this package.

Code is supplied under [Apache-2.0](LICENSE), retaining upstream attribution in
[NOTICE](NOTICE). New submission documentation follows the repository's
[content license](../../LICENSE-CONTENT).
