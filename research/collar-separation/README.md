# A collared sphere separates, and both capped sides are simply connected

This component **removes the separation assumption** from the preceding
closed-cover/collar interface. The two complementary open regions and their
path connectivity are now constructed from a given actual sphere collar in
a simply connected space. They are not inputs or abstract certificates.

It does not construct the collar, a metric surgery, or a full Poincare proof.
This is external research, not an eligible intermediate prize submission.

## Exact statement

The general separation result, `exists_pathConnected_separation_of_collar`,
takes a compact path-connected Hausdorff space `S`, a simply connected locally
path-connected Hausdorff space `M`, and an actual open embedding

```text
c : S × (-1,1) → M.
```

It constructs nonempty, path-connected, disjoint open sets `U,V` whose union
is the complement of the central slice `c(S × {0})`. Negative collar slices
lie in `U`; positive slices lie in `V`. Neither separation, a component count,
nor an ambient real-valued separator is assumed.

For the actual standard Euclidean two-sphere and compact `M`, the endpoint
`sphere_collar_separates_and_caps` additionally constructs its boundary
parametrization and applies the earlier genuine ball-attachment proofs. It
returns the two regions, the original central-slice homeomorphism, and simple
connectivity of the two capped closed sides.

Its geometric input is only the stated open sphere collar. It does not take
the complementary regions, their connectivity, a gluing homeomorphism,
normality or boundary-embedding certificates, a fundamental-group
decomposition, or cap simple connectivity as additional assumptions.

The exact elaborated statements are printed in
[the statement log](evidence/statements.log). The unrestricted original
topological Poincare proposition and its readiness flag remain unchanged.

## Construction and proof

The local crossing height is the concrete clipped real function

```text
h(t) = min(1, max(0, t + 1/2)).
```

Taking this modulo one gives a map to the actual additive circle `ℝ/ℤ`.
It is zero near both ends of the collar, with compact support in
`S × [-1/2,1/2]`. Therefore it extends continuously by zero outside the
open-embedded collar. Its half-period fibre is proved to be exactly the
central hypersurface; no extra points are silently included.

Simple connectivity of `M` lets this concrete map lift through the real
cover of the circle. The lift is normalized to `1/2` at one central point.
Uniqueness of covering lifts on the connected collar then forces the lift
to equal `h(t)` on the entire collar. Consequently its real half-level is
exactly the central hypersurface. Its strict sublevel and superlevel sets
produce a nonempty disjoint open separation with the correct collar signs.

To prove these sides path connected, each collar half is parametrized by
`S × (0,1)`, so its trace on its open side is path connected. If a side had
another path component, the union of those other components would be an
open-and-closed subset of the connected ambient space: its complement is
the principal component, the opposite side, and the open collar. This is
impossible. Thus both generated open sides are path connected.

Finally, the central slice is homeomorphic to the original standard
two-sphere by its actual inclusion. The preserved closed-cover and capping
proofs produce both simply connected capped sides. The new result genuinely
supplies a previously missing separation step; it is not a renamed
conditional invocation of the preceding interface.

## A real full-input regression model

`SeparationTests.lean` constructs the compact three-dimensional cylinder

```text
S² × [-2,2]
```

with its literal central open collar. The standard two-sphere's simple
connectivity is obtained from the pinned, independently authored Hatcher
formalization. The interval is contractible, yielding a homotopy equivalence
of the cylinder with `S²`. Product neighbourhood bases establish its local
path connectivity. Its collar is the actual interval inclusion, proved to
be an open embedding.

This model instantiates every input of the full separation-and-capping
endpoint. It is not a record carrying the desired conclusion as an extra
field. The cylinder has boundary: it is expressly **not** presented as a
closed Poincare manifold, an actual Ricci flow or a constructed surgery.

Eight named regression theorems check the clipped coordinate endpoints,
their equality on the circle but inequality on the real lift, the exact
half-period fibre, the actual collar embedding, disconnectedness of the
central complement, and the full two-cap endpoint in that cylinder.

## Reproduction and evidence

The package has 23 new named production theorems, eight named regression
theorems and explicit maps/homeomorphisms. Eight prior cap/closed-cover source
files are copied unchanged and checked byte-for-byte on every run; their
declarations are not counted as new results.

Lean `v4.32.1`, compiler `f054605aea4b840552cca2e725580bffd1e1b704`, Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6` and Hatcher
`bb91a091f0b968f8bbe8d861e025a88d82b161be` are pinned. Every dependency
revision and tracked source state is checked before and after verification.

```sh
cd research/collar-separation
lake exe cache get
python3 -m unittest -v test_verify
python3 verify.py
```

The verifier checks the complete source inventory, runs the default build,
prints the actual endpoint statements and model definitions, audits every
named new theorem and the complete new and inherited namespaces, rejects
seven invalid-proof mutations, and replays the full import closure with

```sh
lake env leanchecker --verbose --fresh SeparationAudit
```

The invalid variants add an axiom or placeholder, remove ambient simple
connectivity, remove hypersurface connectedness or compactness, replace the
open embedding by a merely continuous map, or give the crossing function an
incorrect central value. These checks are not allowed to pass merely because
a process started or produced a log header. The source, verifier and dependency
identities are checked again before a successful record is written.

[The verification record](evidence/verification.json) reports actual local
outcomes. The sole pre-existing Hatcher `unitCircleCov` definition-style
warning is accepted by exact text; new local warnings are rejected. Fresh
replay uses Lean's own kernel, not a separately implemented checker or
designated expert review. Cached dependencies may be reused, and a clean
from-source rebuild of every dependency is not claimed.

## Attribution and remaining proof obligations

This is formalization of the classical circle-lifting separation argument,
not a new mathematical discovery. Mathlib's additive-circle covering,
lifting uniqueness, compact-support extension and topology, Hatcher's
standard-sphere proof, and the preserved earlier cap results retain their
authors' credit. See [NOTICE](NOTICE).

An actual collar is still an input. Its existence in the required geometric
setting, construction and continuation/control of general Ricci surgery,
geometric width and finite extinction, connected-sum recognition, and the
three-dimensional topological-to-smooth bridge are not proved by this
component. Removing the separation premise does not mark those separate
obligations solved. The full-original-theorem submission gate stays false.
