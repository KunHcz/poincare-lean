import SeparationTests
import Lean.Util.CollectAxioms

#print axioms PoincareSeparation.globalCrossing
#print axioms PoincareSeparation.exists_global_crossing_lift
#print axioms PoincareSeparation.exists_pathConnected_separation_of_collar
#print axioms PoincareSeparation.sphere_collar_separates_and_caps
#print axioms PoincareSeparationTests.actual_cylinder_both_caps_simplyConnected

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut production := 0
  let mut regression := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`PoincareSeparation).isPrefixOf name || (`PoincareSeparationTests).isPrefixOf name ||
        (`PoincareClosedCover).isPrefixOf name || (`PoincareConjecture).isPrefixOf name then
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "{name} depends on non-whitelisted axiom {axiomName}"
      if (`PoincareSeparation).isPrefixOf name then
        production := production + 1
      if (`PoincareSeparationTests).isPrefixOf name then
        regression := regression + 1
  if production == 0 || regression == 0 then
    throwError "Production and actual-model test namespaces must both be nonempty"
