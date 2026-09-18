# Poincare formalization work

**The full topological Poincare theorem is not proved in this repository.**
This is the working source and evidence repository for a continuing
formalization project, not a completed prize application.

The target remains: every closed, simply connected topological three-manifold
is homeomorphic to the standard three-sphere. No smooth atlas, positive
curvature, Ricci-flow construction or spherical presentation may be added to
that target as an unproved assumption.

## Current result and eligibility

The Justin Sun Prize's external-submission rules at
[`82be4c4913b8fe394d68d1391f4c221fde947211`](https://github.com/TheJustinSunPrize/awards/blob/82be4c4913b8fe394d68d1391f4c221fde947211/CONTRIBUTING.md)
accept complete original-problem solutions only. They exclude special cases,
intermediate results and incomplete formalizations, and require catalog
references rather than proof source in the awards repository. The associated
awards PR #438 is not a ready or eligible complete-proof submission.

Earlier statements in the preserved package documents about seeking a
component-level award are **superseded** by [the current rule assessment](STATUS.md).
They are historical provenance, not an attempt to request an exception.
The existing proofs remain useful work toward the original target.

## Verified working components

| Component | Proved scope | Source and evidence |
| --- | --- | --- |
| Dini comparison and scalar lifetime barrier | Real-analysis comparison, finite downward jumps including the terminal endpoint, and the scalar extinction ODE | [Analytic snapshot](submissions/jsp-000007-dini-extinction/STATEMENT.md) |
| Topological endgame | Smooth finite sphere quotients, mapping-torus fundamental groups, and elimination of nontrivial free-product factors | [Topology snapshot](submissions/jsp-000007-dini-extinction/TOPOLOGY_EXTENSION.md) |
| Orientability | A genuine determinant-sign double cover and positive local tangent-frame transitions for simply connected C1 three-manifolds | [Orientability snapshot](submissions/jsp-000007-dini-extinction/ORIENTABILITY_EXTENSION.md) |
| Constant positive sectional curvature | Sphere recognition under that explicit metric restriction | [Constant-curvature root](submissions/jsp-000007-dini-extinction/constant-curvature/README.md) |
| Positive Ricci curvature | Sphere recognition using the independently authored Hamilton formalization, under an explicit positive-Ricci metric restriction | [Positive-Ricci root](submissions/jsp-000007-dini-extinction/positive-ricci/README.md) |
| General smooth-flow scalar estimates | The actual metric scalar bounds `R >= -6/(1+4t)` and `R >= -3/(2t)`, and the inherited global restart clock, without curvature positivity | [Scalar-flow root](submissions/jsp-000007-dini-extinction/scalar-flow-bounds/README.md) |
| Arbitrary-metric maximal smooth flow | Produces the initial metric and finite-or-immortal maximal flow, proves unique lifetime/metric and attaches scalar bounds; general existence is credited to the independently authored extension | [General-flow root](research/general-flow/README.md) |
| Finite regular-segment chains | A global scalar bound across changing manifolds, from explicit surviving-region and nonnegative-cap inequalities; the construction of those geometric transitions is not proved | [Finite-chain root](research/flow-chains/README.md) |
| Topological ball capping | Both capped sides of an explicitly simply connected boundary gluing are simply connected; open sets, retraction homotopy and loop generation are constructed | [Cap-filling root](research/cap-filling/README.md) |
| Closed-cover cutting | Derives the original-space gluing homeomorphism for actual closed subsets; a supplied two-sided collar gives closed-side paths and capped simple connectivity | [Closed-cover root](research/closed-cover/README.md) |
| Collar-derived separation | Constructs two path-connected open sides and capped simple connectivity from an actual compact sphere collar, without assuming separation | [Separation root](research/collar-separation/README.md) |
| Local inverse to uniform collar | Constructs a positive-width collar from an actual continuous family with an injective compact zero section and pointwise inverse data; real C1 coordinate derivatives supply that data | [Local-collar root](research/local-collar/README.md) |

The scalar-flow package's complete local replay finished successfully, as
recorded in its [source-bound evidence](submissions/jsp-000007-dini-extinction/scalar-flow-bounds/evidence/verification.json).
It assumes a genuine smooth Ricci flow on each regular segment; it does not
prove that surgery constructs such segments or preserves the cap bound.
No declaration count or successful build is a percentage completion claim.

The new cap-filling theorem concerns the actual adjunction quotients of
normal pieces along closed embedded two-spheres. It does not assume a
fundamental-group decomposition, but it still requires the geometric pieces
and their cutting identification as inputs. It is not the construction of
Ricci surgery or the final connected-sum reconstruction.

## Reproduction

Each linked component has its own pinned toolchain and verifier. The original
analysis/topology snapshots use Lean 4.32.1; the geometric roots use Lean 4.33.1.
They are not falsely represented as a single already-assembled proof.

```sh
python3 scripts/validate_repository.py
python3 -m unittest discover -s tests -v

cd submissions/jsp-000007-dini-extinction/scalar-flow-bounds
lake exe cache get
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify.py
```

The repository validator checks migrated source identities, every local
evidence-to-source binding it can resolve, links and declared completion
state. It does not replace Lean proof checking. Its submission-readiness
check intentionally fails while the full theorem is absent:

```sh
python3 scripts/validate_repository.py --require-complete
```

Full source/dependency replays use Lean's own kernel implementation. They are
not designated human review, a separate checker implementation, an award
decision, or proof that the current Lean version is immune to all bugs.

## Attribution and preservation

The earlier public proof/evidence package was relocated from the applicant's
awards fork at `2e5df508d0fc71da3e1f65b9557567e2160c72f2`, without changing
the recorded source and verifier bytes. [Migration provenance](MIGRATION_PROVENANCE.json)
identifies all original files. The completed scalar package was added after
its own final checks. Build caches, credentials, private data and unreviewed
local candidate work are not published here.

Hamilton's large formalization and the DifferentialGeometry library are
independent dependencies, not this applicant's original work. Perelman,
Hamilton, Morgan--Tian, Hatcher, Lean, Mathlib and the contributing libraries
retain their credit. Each package preserves its license and notice. No
priority, solver share or prize allocation is asserted.
