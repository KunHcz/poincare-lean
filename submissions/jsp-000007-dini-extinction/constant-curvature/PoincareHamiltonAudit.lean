import PoincareHamilton.SpaceFormAudit
import PoincareHamiltonTests

/-! The final default target audits the production and regression namespaces
after all imports have been elaborated. It does not import PositiveRicci. -/

#print axioms DifferentialGeometry.Geometry.constant_positive_sectional_curvature_implies_spherical_space_form
#print axioms PoincareHamiltonTests.literal_metric_endpoint

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut production := 0
  let mut regression := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`PoincareHamilton).isPrefixOf name || (`PoincareHamiltonTests).isPrefixOf name then
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "{name} depends on non-whitelisted axiom {axiomName}"
      if (`PoincareHamilton).isPrefixOf name then
        production := production + 1
      else
        regression := regression + 1
  if production == 0 || regression == 0 then
    throwError "A required namespace was not audited"
