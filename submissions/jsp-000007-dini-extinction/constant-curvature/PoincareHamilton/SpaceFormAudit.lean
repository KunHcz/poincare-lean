import PoincareHamilton.SphericalSpaceForm
import Lean.Util.CollectAxioms

/-!
# Audit for the constant-positive-curvature integration

The target remains a genuine closed simply connected smooth three-manifold
with a constant-positive-sectional-curvature metric. The unrestricted
Poincare theorem and the positive-Ricci flow are not imported by this audit.
-/

#print axioms PoincareHamilton.roundQuotient_proj_surjective
#print axioms PoincareHamilton.roundQuotient_mfderiv_surjective
#print axioms PoincareHamilton.roundQuotient_proj_localDiffeomorph
#print axioms PoincareHamilton.roundQuotientDiffeomorph
#print axioms PoincareHamilton.diffeomorph_sphere_of_sphericalSpaceForm
#print axioms PoincareHamilton.constantPositiveCurvature_poincare
#print axioms PoincareHamilton.constantPositiveCurvature_homeomorph_sphere

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`PoincareHamilton).isPrefixOf name then
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "{name} depends on non-whitelisted axiom {axiomName}"
      count := count + 1
  if count == 0 then
    throwError "No integration declarations were audited"

