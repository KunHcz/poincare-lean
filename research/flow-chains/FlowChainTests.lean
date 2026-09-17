import FlowChainBounds

open Set PoincareFlowChains

namespace PoincareFlowChainsTests

theorem elapsed_three_units : elapsed (fun _ => (1 : ℝ)) 3 = 3 := by
  norm_num [elapsed]

/-- A zero-duration segment is allowed without changing the global time. -/
theorem elapsed_zero_segment : elapsed (fun j => if j = 1 then (0 : ℝ) else 2) 3 = 4 := by
  norm_num [elapsed]

/-- Removing points cannot lower the minimum of the scalar on the remaining
points. This exercises genuinely different underlying spaces. -/
theorem restriction_preserves_bounds {A : Type*} (r : A → ℝ) (p : A → Prop) :
    PreservesNonpositiveBounds r (fun x : {a // p a} => r x) := by
  intro b _ h x
  exact h x

/-- An all-cap region with nonnegative scalar preserves every nonpositive
bound; no false bijection with the previous space is needed. -/
theorem all_nonnegative_caps : PreservesNonpositiveBounds (fun _ : Empty => (0 : ℝ))
    (fun b : Bool => if b then (1 : ℝ) else 0) := by
  intro b hb _ y
  cases y <;> simp <;> linarith

/-- A newly inserted negative cap can violate the inherited bound. -/
theorem negative_cap_counterexample :
    ¬ PreservesNonpositiveBounds (fun _ : Unit => (-1 : ℝ))
      (fun y : Bool => if y then (-2 : ℝ) else -1) := by
  intro h
  have bad := h (-1) (by norm_num) (fun _ => le_rfl) true
  norm_num at bad

end PoincareFlowChainsTests
