import ClosedCoverTests
import Lean.Util.CollectAxioms

#print axioms PoincareClosedCover.closedCoverHomeomorph
#print axioms PoincareClosedCover.both_closed_cover_caps_simplyConnected
#print axioms PoincareClosedCover.caps_of_collared_separation_simplyConnected
#print axioms PoincareClosedCoverTests.actual_closed_ball_cover_caps

run_cmd do
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut newProofs := 0
  let mut regressions := 0
  for (name, _) in (← Lean.getEnv).constants.toList do
    if (`PoincareClosedCover).isPrefixOf name || (`PoincareClosedCoverTests).isPrefixOf name ||
        (`PoincareConjecture).isPrefixOf name then
      for ax in (← Lean.collectAxioms name) do
        unless allowed.contains ax do
          throwError "{name} depends on non-whitelisted axiom {ax}"
      if (`PoincareClosedCover).isPrefixOf name then
        newProofs := newProofs + 1
      if (`PoincareClosedCoverTests).isPrefixOf name then
        regressions := regressions + 1
  if newProofs == 0 || regressions == 0 then
    throwError "The new proof and regression namespaces must both be nonempty"
