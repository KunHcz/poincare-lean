import LocalCollarTests
import Lean.Util.CollectAxioms

#print axioms PoincareLocalCollar.exists_uniform_openEmbedding_band
#print axioms PoincareLocalCollar.local_open_chart_of_strict_coordinate_derivative
#print axioms PoincareLocalCollar.exists_collar_of_C1_coordinates
#print axioms PoincareLocalCollar.coordinate_derivatives_separate_and_cap
#print axioms PoincareLocalCollarTests.clipped_family_separates_and_caps
#print axioms PoincareLocalCollarTests.polynomial_has_local_open_chart

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut production := 0
  let mut regression := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`PoincareLocalCollar).isPrefixOf name || (`PoincareLocalCollarTests).isPrefixOf name ||
        (`PoincareConjecture).isPrefixOf name || (`PoincareClosedCover).isPrefixOf name ||
        (`PoincareSeparation).isPrefixOf name || (`PoincareSeparationTests).isPrefixOf name then
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "{name} depends on non-whitelisted axiom {ax}"
      if (`PoincareLocalCollar).isPrefixOf name then
        production := production + 1
      if (`PoincareLocalCollarTests).isPrefixOf name then
        regression := regression + 1
  if production == 0 || regression == 0 then
    throwError "Required new production and regression namespaces must both be nonempty"
