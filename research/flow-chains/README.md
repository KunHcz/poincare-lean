# Scalar bounds along changing-manifold Ricci-flow chains

This is working mathematics toward the general surgery argument. It is not
an eligible full-original-problem submission and is not added to the awards
repository.

## Exact result

Let `S j` be a genuine smooth Ricci flow on a compact smooth three-manifold
`M j`. The manifolds may differ from one segment to the next; no identification
of their topology is assumed. Segment `j` is used for a nonnegative duration
strictly shorter than its regular-flow horizon. Its global start time is

```text
a + duration(0) + ... + duration(j-1),
```

where `a >= 0` is the initial global time. Given the normalized initial scalar
bound and the explicitly stated transition conditions below,
`normalized_bound_from_survivor_and_cap_data` proves, for every segment in
any finite chain and every local time in its closed used interval:

```text
R_j(u,x) >= -6 / (1 + 4 (a + elapsed(j) + u)).
```

The proof uses the actual metric-family scalar curvature and `IsSolutionOn`
for each regular segment. It invokes the existing metric scalar comparison,
whose source is copied unchanged and hash-checked, then inducts over the
finite chain. The elapsed clock is not reset at each transition. Zero-duration
segments and the one-segment case are included.

## Transition assumptions: stated, not proved surgery geometry

For each transition there is a predicate identifying the surviving region in
the next manifold and a map from that region to the preceding manifold.
The new scalar on surviving points is no smaller than at the corresponding
old terminal point. On newly inserted cap points, scalar curvature is
nonnegative. The code proves from these pointwise facts that every nonpositive
old lower bound survives the transition. It does not assume the final global
estimate as its transfer hypothesis.

These are useful sufficient conditions, not a theorem that a geometric
Ricci surgery has been constructed or meets them. Constructing the caps,
establishing their curvature estimates, arranging the surviving-region
identification, continuing the flow and proving geometric extinction remain
outstanding. No Ricci-flow model is newly constructed by this package.

The local scalar-transfer tests use elementary sets to check the transfer
logic; they are not presented as three-manifold or Ricci-flow examples.
In particular, a test with a new negative cap demonstrates the failure of
the claimed lower-bound preservation when the cap condition is omitted.

## Verification

The package has five new production theorems and five regression theorems.
It uses the same Lean 4.33.1 and pinned DifferentialGeometry/Mathlib versions
as the earlier scalar-flow package. No previous source or evidence record is
rewritten.

```sh
cd research/flow-chains
lake exe cache get
python3 verify.py
```

The verifier checks all source/dependency identities and the unchanged reused
scalar source, builds with warnings as errors, audits the full transitive
axiom set of all ten declarations and the proof namespaces, and runs a fresh
`leanchecker` replay of the actual root. It requires rejection of extra axioms,
placeholder proofs, removal of the cap bound, replacement of the flow equation
with `True`, and a reset global clock. Completed results are in
[the evidence record](evidence/verification.json).

The fresh replay uses Lean's own kernel, not an independently implemented
checker or a prize review. Successful verification establishes this exact
conditional finite-chain theorem, not existence of a surgery flow or full
Poincare. The unrestricted completion gate remains false.

## Attribution

The scalar comparison source and its geometric dependencies are reused with
their original credit and licenses. The new work is the finite-chain
integration allowing different manifolds, the retained-point/cap transfer
lemma and its regression checks. No rediscovery or duplicate credit is
claimed for classical scalar estimates, Hamilton's theorem, or the earlier
covering and scalar components. The code is under the included Apache-2.0
license; repository prose follows the root content license.
