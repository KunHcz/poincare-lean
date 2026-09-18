# Arbitrary-metric maximal smooth Ricci flow

This component produces an actual initial smooth metric and a maximal forward
Ricci flow on a compact smooth three-manifold, with no curvature-sign,
spherical-presentation, simple-connectivity or finite-lifetime assumption.
It integrates the independently authored general maximal-flow extension,
proves uniqueness of the lifetime and metric, and applies the earlier
geometric scalar estimates to that same existing flow.

**The maximal flow is either finite or immortal.** Its existence is not a
proof that every such flow reaches a surgery time or becomes extinct. Neither
branch is silently removed. This component is external research, not a
complete-original-problem prize submission or the topological Poincare proof.

## What is produced and what remains an input

The manifold is given with Mathlib's original topological and smooth
three-dimensional charted-space structures, compactness and Hausdorffness.
It is not merely a structure carrying a sphere-recognition certificate.

`initial_metric_exists` obtains a genuine `SmoothRiemannianMetric` from the
metric-existence theorem. `arbitrary_metric_maximal_flow` then constructs a
maximal flow for **every** specified initial smooth metric; the existence of
the flow or its initial curvature lower bound is not a separate premise.
The maximal-flow object has the original metric value at time zero and the
actual metric equation `∂g/∂t = -2 Ric(g)` on its domain. The canonical
connection and Ricci tensor cannot be assigned independently of that metric.

The new local integration proves:

- Restrictions to shorter intervals preserve the same metric family and
  the actual PDE. A finite view of an immortal solution is not a finite
  maximal solution.
- A finite maximal endpoint dominates any competing solution with the same
  initial metric. Finite maximal and immortal solutions cannot coexist for
  that initial metric. Consequently every maximal solution has the same
  endpoint, including the finite/infinite distinction, and the same metric
  throughout the defined time interval.
- One nonpositive initial scalar constant, obtained by compactness, controls
  the actual maximal metric for every defined time. The normalized bound
  `R >= -6/(1+4t)` and the positive-time bound `R >= -3/(2t)` follow from the
  unchanged previously checked geometric scalar component.
- In the finite maximal branch, the canonical Riemann tensor norm is
  unbounded. This is a singularity statement, not a blow-up-model
  classification or a construction of surgery past that singularity.

The unrestricted original target is a *topological* three-manifold theorem.
Supplying a smooth structure here does not discharge the topological-to-
smooth bridge. The full target declaration and readiness flag are unchanged.

## Exact source and attribution

The substantial short-time Ricci-flow, PDE, regularity and curvature
formalizations belong to the DifferentialGeometry authors. The arbitrary
maximal-flow extension was authored by **Arthur Freitas Ramos**, beginning
at `f34543166960b38bed82a78a5bd583611cbcdf9d`, proposed in
[upstream PR #77](https://github.com/qinz1yang/differential-geometry/pull/77).
The present pin is a checked
fork integration, not a claim that this applicant wrote that extension or
that it was part of the original upstream main branch.

The pinned dependency is
[`KunHcz/differential-geometry@1ccb5e688b253701690300867ffb20e467855d2b`](https://github.com/KunHcz/differential-geometry/tree/1ccb5e688b253701690300867ffb20e467855d2b).
Relative to `d88910233464ea6ff54bd55f92b7d5ea0b9034e8`, the disclosed repair
changes exactly the three files recorded in the verification evidence:
`HomFieldCurvatureJetDecomposition.lean`, `Extension/Regularity.lean`, and
`Extension/MaximalFlow.lean`. The checker verifies this scope and the original
extension's ancestry. Authorship of the maximal existence argument remains
with its originator; the local integration, uniqueness results, repair and
source-bound checks are identified separately. See [NOTICE](NOTICE).

Lean is pinned to 4.33.1, compiler
`819816b2e0a3bf405af45ae5c7af2491d8f5bee6`, and Mathlib to
`0df444a360eaa60ab8c11dca51a86af692955474`. All dependency revisions are in
`lake-manifest.json`. The copied `ScalarFlowBounds.lean` is checked
byte-for-byte against the earlier immutable component.

## Reproduce and inspect the actual statements

```sh
cd research/general-flow
lake exe cache get
python3 -m unittest -v test_verify
python3 verify.py
```

The verifier builds the complete default targets with warnings as errors,
prints the fully elaborated main statements and definitions of the flow,
maximality, extension, PDE and singularity objects, and audits all 15 local
production theorems, seven regressions and four critical upstream theorems.
The default audit additionally checks the complete local proof, regression
and reused scalar namespaces.

The full root replay is
`leanchecker --verbose --fresh GeneralRicciFlowAudit`. The recorded run
completed with exit zero in **4418.70 seconds**, with no time or memory guard
firing. The verifier checks source/configuration and verifier hashes and
all ten dependency revisions/tracked states before and after execution.
The [source-bound verification record](evidence/verification.json) and
[expanded statements](evidence/statements.log) are the evidence, not the
mere presence of a successful import.

The genuine standard three-sphere supplies a concrete nonempty model with
distinct points. Its initial metric and maximal flow are obtained from the
existence theorem, and a positive time in that flow's actual domain is
proved. Another regression exposes the literal metric PDE at every point
and pair of tangent vectors. This is not an explicit closed-form numerical
solution of Ricci flow.

Six negative controls reject an added axiom, a placeholder, claiming only
the finite branch from the finite-or-immortal result, removing the initial
scalar bound, using a time outside the flow domain, and substituting a
different initial metric. In particular, the immortal alternative is not
excluded by a misleading type alias or by treating a finite restriction as
a maximal endpoint.

The replay uses Lean's own kernel implementation; no independent software
checker, expert review or official prize certification is asserted.
Dependency build caches may be reused, and the record does not claim a
clean from-source rebuild of every dependency.

## Remaining Poincare obligations

The existence of a maximal **smooth** flow does not construct a flow with
surgery, prove canonical-neighbourhood descriptions, produce metric caps,
or guarantee geometric finite extinction. Width production/evolution,
continuation through the singular regions, topological reconstruction and
the three-dimensional smoothing bridge remain separate work. The finite
and immortal branches are both retained in the formal statement.

The current official rules accept only complete original-problem solutions.
This intermediate component therefore remains in the external research
repository, with no catalog-status, claim-issue or payment request. Reused
proofs and ownership of a fork are not new mathematical authorship or an
independent duplicate contribution.
