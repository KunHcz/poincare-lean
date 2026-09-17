# Current scope and complete-proof submission gate

## Rule snapshot

Checked against TheJustinSunPrize/awards commit
`82be4c4913b8fe394d68d1391f4c221fde947211` of September 17, 2026.
The [contribution instructions](https://github.com/TheJustinSunPrize/awards/blob/82be4c4913b8fe394d68d1391f4c221fde947211/CONTRIBUTING.md)
and [PR template](https://github.com/TheJustinSunPrize/awards/blob/82be4c4913b8fe394d68d1391f4c221fde947211/.github/PULL_REQUEST_TEMPLATE.md)
require:

- A complete solution of the original problem, not special cases or intermediate lemmas.
- For a Lean reference, a complete proof at an exact public repository, branch and 40-character commit.
- Changes only to the relevant existing catalog's solver/Lean/attribution/publication information.
- No proof code, project files, dependencies, archives or binaries in the awards PR.
- Maintainer review; a submitter or repository owner is not automatically a solver or formalization author.

These repository instructions are the current submission requirement even
though the website's broader v1.0 assessment page mentions partial-progress
tiers. No eligibility exception is assumed. The current component work is
not submitted as a complete proof and does not change the official catalog's
`Lean proof` or `Eligible to claim` fields.

## Proof obligations still open

The unrestricted target is the `TopologicalPoincareStatement` in the primary
source pinned at `d5cf293fcee9164a449fcc833d049d51aab52bc3`. That is the type
of the desired proof, not an inhabitant of it.

The following obligations remain, independently of the completed component
replays: general Ricci flow with surgery and its continuation/control;
production of the geometric width and its evolution; preservation across
caps and surgery; geometric finite extinction; topological reconstruction
and the required connected-sum calculation; and the three-dimensional
topological-to-smooth bridge. Ordinary positive-Ricci classification cannot
remove these obligations by adding a metric-sign hypothesis to the target.

The new scalar-flow estimates connect real metric curvature to the analytic
barrier and preserve its elapsed-time clock when a regular segment is
restarted. The finite-chain extension derives the inherited bound from
explicit pointwise inequalities on surviving regions and nonnegative caps,
allowing different manifolds in successive segments. The regular flows and
these geometric transition inequalities remain inputs; the surgery theorem
constructing them has not been proved here.

The cap-filling component now proves preservation of simple connectivity
when either or both normal path-connected sides of a simply connected
boundary adjunction are capped by standard closed three-balls. It constructs
the topological quotient, its open cover, radial deformation and generating
loop map. It does not construct a manifold cut/collar identification, metric
caps, curvature bounds, or a connected-sum recognition theorem. Those
remaining geometric and reconstruction obligations are not discharged by
this topology result.

The closed-cover component now derives the boundary-adjunction homeomorphism
from an actual compact Hausdorff closed cover, rather than taking a gluing
homeomorphism as an input. It also derives path connectivity of complementary
closed sides from given path-connected open regions and an actual two-sided
open-embedded collar. Its final cap theorem therefore removes those previously
separate caller obligations. Existence of the separating sphere and collar,
the metric surgery construction, curvature control and the unrestricted
Poincare proof remain distinct unproved obligations here.

## Disposition of the previous award PR

Awards PR #438 is retained as the same contribution's historical thread and
changed to a draft. Its source-file diff was removed at
`a7b83b3d4788262621542757a6deed0bee805c60`, after the external source copy
was published and read back. The net diff against the current official main
is empty. No ready-for-review assertion is made while the unrestricted proof
is absent. Historical branches and commits remain available; no force push
or destruction of proof history is used.

A future eligible revision must name a real theorem with exactly the full
original proposition and verified transitive proof dependencies, identify
its authors accurately, and supply the public repository/branch/commit
triple. Only then may the same PR make the allowed catalog edits and be
marked ready. The current machine-readable gate remains false.
