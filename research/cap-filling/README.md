# Simple connectivity after filling a spherical boundary

This component proves a topological cap-replacement step needed in the
Poincare surgery/endgame route. It uses standard spheres, closed balls and
adjunction quotients, and does not assume a conclusion about fundamental
groups, an already-constructed retraction, or a loop-generation certificate.

It is **not the full Poincare theorem** and is not eligible as an intermediate
prize submission under the current official rules. This code and its evidence
stay in the external research repository; no awards catalog flag is changed.

## Exact statement

Let `i : S² → X` and `j : S² → Y` be continuous closed embeddings. The retained
space `X` is normal and path connected; the complementary space `Y` is normal.
Define

```text
BoundaryGluing i j = (X ⊔ Y) / (i(s) ~ j(s), s ∈ S²)
BallAttachment i  = (X ⊔ B³) / (i(s) ~ s,    s ∈ S² = ∂B³).
```

Both have the quotient topology. `S²` is the unit sphere in real three-space,
and `B³` is its standard closed unit ball. The main result is:

```lean
PoincareConjecture.capped_piece_simplyConnected
```

If `BoundaryGluing i j` is simply connected, then `BallAttachment i` is simply
connected. There is **no assumption that `X` is already simply connected**.
The two-sided theorem `both_capped_pieces_simplyConnected` proves the same
for both capped pieces when `Y` is path connected too. An actual quotient
homeomorphism exchanges the two sides.

The corollary `capped_piece_simplyConnected_of_homeomorph` accepts a supplied
homeomorphism from a simply connected original space to the boundary gluing.
Constructing that cutting identification for a smooth manifold and its
embedded separating sphere is not part of this result. Normality,
closed-embedding and piece-connectivity assumptions are exposed rather than
silently inferred for unspecified geometric objects.

## Proof and correspondence

The retained side and the new ball define a continuous radius function on
the attachment: it equals `1` on `X` and the ordinary Euclidean norm on `B³`.
Its open sets `radius > 0` and `radius < 1` cover the attachment. The latter
is homeomorphic to the open three-ball. A closed-ball-valued Tietze extension
provides coordinates inverse to the original ball inclusion; the ball is not
postulated to remain embedded without proof.

The former open set is homeomorphic to the adjunction of `X` and the
punctured closed ball. Radial expansion

```text
(t,b) ↦ (1 - t + t / ‖b‖) b
```

stays in the punctured ball, fixes the boundary, and at time one sends `b`
to `b/‖b‖`. It descends through the actual quotient, including its time
parameter, to a deformation onto the retained side. The overlap of the two
open sets is the image of `S² × (0,1)` under `(s,r) ↦ r s`, proving its path
connectivity. These open-set and homotopy properties are derived, not extra
inputs to the main theorem.

The **proved surjectivity** part of the pinned Hatcher van Kampen library
shows that loops in the punctured retained neighbourhood generate all loops
of the filled space: the other open set is simply connected. This proof
does not use or claim a completed van Kampen kernel theorem.

A closed-ball-valued extension over `Y` constructs a continuous map from the
original gluing to the filled space that agrees with the retained inclusion.
The punctured neighbourhood's generating map is homotopic to a factorization
through the original simply connected space. Naturality in the fundamental
groupoid handles the moving basepoint, so its loops are null-homotopic. The
derived surjectivity then makes every loop of the filled space trivial.

The files separate these obligations:

- `CapFilling.lean`: quotient, Tietze and actual two-open-set framework.
- `PuncturedCap.lean`, `AttachmentOpen.lean`: radial deformation and its
  identification with the actual punctured open subspace.
- `ConnectedCap.lean`: cap and overlap topology.
- `HomotopicFactorization.lean`, `CappingTheorem.lean`: basepoint transport,
  one-sided and two-sided cap-preservation results.

## Tests and reproduction

The package has 42 named production theorems and nine named regression
theorems, plus its explicit maps, homotopies and homeomorphisms. The tests
include a quotient of two closed three-balls glued along their corresponding
boundary points. Its simple connectivity is obtained by applying the main
cap theorem to a concretely recognized original gluing. No identification
of that double with the standard three-sphere is required or asserted.

A second test attaches a ball to `S² × S¹` along `S² × {1}` and constructs a
retraction onto its remaining circle. Its fundamental group is therefore
nontrivial. This is an actual adjunction-space counterexample to an
unrestricted “all ball attachments are simply connected” claim, not an
example of a smooth cut manifold or a Ricci surgery.

```sh
cd research/cap-filling
lake exe cache get
python3 -m unittest -v test_verify
python3 verify.py
```

Lean is pinned to `v4.32.1`, compiler
`f054605aea4b840552cca2e725580bffd1e1b704`, Mathlib to
`520045ab14e26149ee970e2e617ca04b09bde5d6`, and the Hatcher reference to
`bb91a091f0b968f8bbe8d861e025a88d82b161be`. Every dependency revision and
tracked-file state is checked, along with the exact source manifest.

The verifier builds the default targets, prints the fully elaborated main
statements and definitions, audits all named theorems and the complete
production/test namespaces, and runs
`leanchecker --verbose --fresh CapFillingAudit`. It also requires failure
after an extra axiom or placeholder is inserted, original simple
connectivity or a closed boundary embedding is removed, or the ball centre
is incorrectly asserted to have boundary radius.

The [verification record](evidence/verification.json) and accompanying logs
report actual local outcomes. The one pre-existing Hatcher `unitCircleCov`
definition-style warning is accepted by exact text; new warnings are rejected.
Fresh replay uses Lean's own kernel implementation, not independent checker
software or designated human review. Cached dependency builds may be reused;
the record does not claim a full clean dependency rebuild.

## Attribution and remaining obligations

This is a formalization of the classical cap-filling/topological argument,
not a new mathematical discovery. The proved Hatcher van Kampen
surjectivity, circle fundamental group, Mathlib homotopy/groupoid machinery,
Tietze extension and standard topology retain their authors' credit.
The applicant's existing unpublished cap candidate and earlier checked
basepoint-independence helper were extended here; reusing those arguments is
not counted as a second independent contribution. See [NOTICE](NOTICE).

No Ricci-flow or metric cap is constructed, no curvature preservation or
geometric extinction is established, and no general three-dimensional
smoothability or connected-sum reconstruction theorem is proved. The complete
original Poincare proposition and its final proof remain unfilled. The
repository's full-submission gate stays false.
