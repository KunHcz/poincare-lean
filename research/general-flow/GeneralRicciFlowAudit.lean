import GeneralRicciFlowTests
import Lean.Util.CollectAxioms

#print axioms DifferentialGeometry.PDE.RicciFlow.exists_maximal_forward_ricci_flow
#print axioms DifferentialGeometry.PDE.RicciFlow.exists_immortal_or_finite_singularity
#print axioms PoincareGeneralFlow.initial_metric_and_maximal_flow
#print axioms PoincareGeneralFlow.maximal_endpoint_unique
#print axioms PoincareGeneralFlow.maximal_universal_scalar_bound
#print axioms PoincareGeneralFlowTests.sphere_flow_has_positive_lifetime

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut production := 0
  let mut tests := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`PoincareGeneralFlow).isPrefixOf name || (`PoincareGeneralFlowTests).isPrefixOf name ||
        (`PoincareScalarFlow).isPrefixOf name then
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "{name} depends on non-whitelisted axiom {ax}"
      if (`PoincareGeneralFlow).isPrefixOf name then
        production := production + 1
      if (`PoincareGeneralFlowTests).isPrefixOf name then
        tests := tests + 1
  if production == 0 || tests == 0 then
    throwError "Both local proof and regression namespaces must be nonempty"
