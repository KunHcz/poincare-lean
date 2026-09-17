# Closed-cover reconstruction and collared cutting

This component removes two inputs left by the earlier ball-capping theorem:
a homeomorphism between an actual closed decomposition and its boundary
adjunction, and path connectivity of the closed sides when a two-sided
collar reaches path-connected open regions.

It is not the full topological Poincare theorem. Separation and collar
existence remain explicit geometric inputs. The current prize rules accept
complete original-problem proofs only; this component belongs in the external
research repository, not in an awards source or catalog submission.

## Actual closed-cover reconstruction

For a compact Hausdorff space `M` and closed sets `A,B` covering `M`, define

```text
Q = (A ⊔ B) / (the two copies of x are identified exactly when x ∈ A ∩ B).
```

`closedCoverHomeomorph` constructs `Q ≃ₜ M`. Its map is the original subtype
inclusion on each side, not a chosen unidentified bijection. Points on the
same side with the same image were already equal. Equal images from opposite
sides lie in the actual intersection, exactly where the quotient identifies
them. The covering condition gives surjectivity. Compactness of the quotient
and Hausdorffness of the target give continuity of the inverse.

When an actual homeomorphism `S² ≃ₜ A ∩ B` parametrizes the common boundary,
`boundaryGluingReparam` transfers the construction to the standard sphere
parameter. Compactness and Hausdorffness also supply normality of the closed
sides and closed embeddings of the attaching sphere.

Thus `both_closed_cover_caps_simplyConnected` proves: if the original `M`
is simply connected and the two closed sides are path connected, attaching
a standard closed three-ball to each side gives two simply connected
spaces. No original gluing homeomorphism, fundamental-group decomposition,
normality certificate or boundary-embedding certificate is an extra input.

## From actual open regions and a supplied collar

Let `U,V` be disjoint, path-connected open subsets, with the remaining set
parametrized by a standard two-sphere. Set `A = M \ V` and `B = M \ U`.
Their closedness, covering property and boundary intersection are proved
from these set relations.

A supplied open embedding `c : S² × (-1,1) → M` has its zero slice on the
given sphere, negative slices in `U`, and positive slices in `V`. This is the
actual collar map, not a claim about loop triviality. The paths
`t ↦ c(s,-t/2)` and `t ↦ c(s,t/2)` reach the corresponding open region from
each boundary point while staying on the closed side. They prove path
connectivity of the closed sides. Mere closure membership is not substituted
for actual paths.

`caps_of_collared_separation_simplyConnected` combines these constructions
with the preserved cap proof. It does not separately assume closed-side
path connectivity or the original-space gluing identification. It still
requires the literal separation and collar data. **It does not prove that
an arbitrary sphere separates, construct a collar, construct a smooth cut
manifold, build metric surgery caps, or preserve their curvature.**

## Tests and statement fidelity

There are 13 new named production theorems and nine regression theorems,
besides explicit maps and homeomorphisms. Tests cover disjoint two-point
covers, duplicate copies of overlap points, failure of surjectivity without
a covering condition, exact half-collar endpoints, and a genuine closed
three-ball covered by itself and its standard spherical boundary. The latter
exercises both cap conclusions without supplying a gluing homeomorphism.

A separate concrete model exercising every full three-dimensional collar
hypothesis is not constructed here; the verification record says so. The
collar theorem is kernel-checked under its literal geometric hypotheses,
not established by a numerical example.

Two independent Python model tests enumerate all 1,365 pairs of subsets
of finite sets of size zero through five. They check the exact quotient
relation and complementary-side identities. These finite tests are not a
substitute for the general topological Lean proof.

Negative mutations remove the covering condition, original simple
connectivity, disjointness, or the boundary-access paths, or add an axiom or
placeholder. Each must fail. Verifier unit tests reject mismatched source
identities, incomplete kernel stages and changed earlier logs.

## Reproduce

Lean `v4.32.1`, compiler `f054605aea4b840552cca2e725580bffd1e1b704`, Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`, and Hatcher
`bb91a091f0b968f8bbe8d861e025a88d82b161be` are pinned. The six copied cap
proof files are checked byte-for-byte against the preserved sibling
component on every run; their repeated declarations are not new results.

```sh
cd research/closed-cover
lake exe cache get
python3 -m unittest -v test_verify
python3 verify.py
```

A bounded executor may perform the identical verification in three stages:

```sh
python3 verify.py --stage prepare
python3 verify.py --stage kernel
python3 verify.py --stage final
```

Later stages require the earlier stage, identical source/configuration and
verifier hashes, unchanged dependency identities, and hashes of the earlier
logs. Only the final stage writes success. Preparation builds all default
targets with warnings as errors, prints actual endpoint statements and
quotient definitions, and audits all new named theorems. The default Lean
audit traverses the two new namespaces and the reused cap namespace.
The kernel stage runs `leanchecker --verbose --fresh ClosedCoverAudit`.
The final stage checks all negative mutations and the input identities again.

The [verification record](evidence/verification.json) reports actual local
outcomes. This uses Lean's own kernel, not independently implemented checker
software or designated expert/prize review. Dependency caches may be reused;
a clean rebuild of every dependency is not claimed.

## Attribution and remaining obligations

The topology is classical. This component constructs and checks the actual
closed-cover identification and its collar-to-cap connection. The earlier
cap proof, Hatcher's proved van Kampen surjectivity, Mathlib's quotient,
compactness, homotopy and groupoid machinery retain their authors' credit.
See [NOTICE](NOTICE).

General separation and collar existence, Ricci surgery and its continuation,
geometric width/extinction, connected-sum recognition, and the topological-to-
smooth three-dimensional bridge remain separate obligations. The original
Poincare target and its submission-readiness state are unchanged.
