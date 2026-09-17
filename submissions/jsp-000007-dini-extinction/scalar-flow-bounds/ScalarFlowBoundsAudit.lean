import ScalarFlowBoundsTests
import Lean.Util.CollectAxioms

#print axioms PoincareScalarFlow.scalar_lower_bound_on_slab
#print axioms PoincareScalarFlow.normalized_scalar_lower_bound
#print axioms PoincareScalarFlow.universal_scalar_lower_bound
#print axioms PoincareScalarFlow.scalar_lower_bound_after_restart
#print axioms PoincareScalarFlowTests.literal_metric_normalized_bound

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut production := 0
  let mut regression := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`PoincareScalarFlow).isPrefixOf name || (`PoincareScalarFlowTests).isPrefixOf name then
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "{name} depends on non-whitelisted axiom {axiomName}"
      if (`PoincareScalarFlow).isPrefixOf name then
        production := production + 1
      else
        regression := regression + 1
  if production == 0 || regression == 0 then
    throwError "The required production or regression namespace was empty"
