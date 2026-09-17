import PoincareHamiltonTests
import Lean.Util.CollectAxioms

#print axioms DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_positive_ricci
#print axioms PoincareHamilton.positiveRicci_poincare
#print axioms PoincareHamiltonTests.literal_positive_ricci_endpoint
#print axioms PoincareHamiltonTests.literal_positive_ricci_homeomorph

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
    throwError "A required production or regression namespace was empty"
