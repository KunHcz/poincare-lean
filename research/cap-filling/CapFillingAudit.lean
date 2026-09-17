import CapFillingTests
import Lean.Util.CollectAxioms

#print axioms PoincareConjecture.capped_piece_simplyConnected
#print axioms PoincareConjecture.capped_piece_simplyConnected_of_homeomorph
#print axioms PoincareConjecture.ballAttachment_simplyConnected_of_retained
#print axioms PoincareCapTests.doubled_closed_ball_simplyConnected
#print axioms PoincareCapTests.circle_product_attachment_not_simplyConnected

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut production := 0
  let mut tests := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`PoincareConjecture).isPrefixOf name || (`PoincareCapTests).isPrefixOf name then
      for axiomName in (← Lean.collectAxioms name) do
        unless allowed.contains axiomName do
          throwError "{name} depends on non-whitelisted axiom {axiomName}"
      if (`PoincareConjecture).isPrefixOf name then
        production := production + 1
      else
        tests := tests + 1
  if production == 0 || tests == 0 then
    throwError "Required proof and test namespaces must both be nonempty"
