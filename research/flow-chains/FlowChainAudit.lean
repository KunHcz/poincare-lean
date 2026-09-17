import FlowChainTests
import Lean.Util.CollectAxioms

#print axioms PoincareFlowChains.normalized_bound_on_finite_chain
#print axioms PoincareFlowChains.normalized_bound_from_survivor_and_cap_data
#print axioms PoincareFlowChains.transfer_of_survivors_and_nonnegative_caps

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut seen := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`PoincareFlowChains).isPrefixOf name || (`PoincareFlowChainsTests).isPrefixOf name then
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "{name} depends on non-whitelisted axiom {ax}"
      seen := seen + 1
  if seen == 0 then
    throwError "The expected proof namespaces were empty"
