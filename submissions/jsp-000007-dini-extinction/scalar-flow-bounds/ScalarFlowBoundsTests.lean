import ScalarFlowBounds

/-! Regression tests keep the exact constants, the initial time, the global
restart clock, and the actual metric scalar curvature visible. -/

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature PoincareScalarFlow
open scoped Manifold ContDiff

namespace PoincareScalarFlowTests

theorem normalized_initial_exact : scalarLowerBarrier 3 (-6) 0 = -6 := by
  norm_num [scalarLowerBarrier]

theorem normalized_time_one_exact : scalarLowerBarrier 3 (-6) 1 = -(6 / 5 : ℝ) := by
  norm_num [scalarLowerBarrier]

/-- A segment starting at global time one inherits `-6/5`; its local time
one corresponds to global time two, rather than resetting the initial bound. -/
theorem restart_keeps_global_time :
    scalarLowerBarrier 3 (-(6 / 5 : ℝ)) 1 = scalarLowerBarrier 3 (-6) 2 := by
  norm_num [scalarLowerBarrier]

theorem negative_time_cannot_be_allowed :
    ¬ scalarLowerBarrier 3 (-6) (-1) ≤ 0 := by
  norm_num [scalarLowerBarrier]

/-- Continuity alone does not imply the scalar evolution estimate. This
is a counterexample at the scalar-interface level, not a Ricci-flow model. -/
theorem constant_scalar_is_not_enough :
    ∃ f : ℝ → ℝ, Continuous f ∧ f 0 = -6 ∧
      ¬ -6 / (1 + 4 * (1 : ℝ)) ≤ f 1 := by
  exact ⟨fun _ => -6, continuous_const, rfl, by norm_num⟩

theorem universal_bound_is_weaker (t : ℝ) (ht : 0 < t) :
    -(3 / (2 * t)) ≤ -6 / (1 + 4 * t) := by
  simpa only [normalized_barrier] using barrier_ge_universal (c := -6) (by norm_num) ht

/-- Statement fidelity: this result refers to the actual metric's scalar
curvature tensor contraction, not an unconstrained scalar-valued field. -/
theorem literal_metric_normalized_bound
    {M : Type*} [TopologicalSpace M] [ChartedSpace Model3 M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
    {omega : ℝ} (homega : 0 < omega)
    (S : SolutionOn (I := 𝓡 3) (M := M) (RealTimeInterval.closedOpen 0 omega homega))
    (hS : IsSolutionOn (I := 𝓡 3) S)
    (hinit : ∀ x : M, -6 ≤ metricScalarAt (I := 𝓡 3) (S.base.metric 0) x)
    {t : ℝ} (ht : 0 ≤ t) (htomega : t < omega) (x : M) :
    -6 / (1 + 4 * t) ≤ metricScalarAt (I := 𝓡 3) (S.base.metric t) x :=
  normalized_scalar_lower_bound homega S hS hinit ht htomega x

/-- The unrestricted-in-initial-scalar-sign estimate applies to the same
actual metric scalar, with no lower bound supplied by the caller. -/
theorem literal_metric_universal_bound
    {M : Type*} [TopologicalSpace M] [ChartedSpace Model3 M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
    {omega : ℝ} (homega : 0 < omega)
    (S : SolutionOn (I := 𝓡 3) (M := M) (RealTimeInterval.closedOpen 0 omega homega))
    (hS : IsSolutionOn (I := 𝓡 3) S)
    {t : ℝ} (ht : 0 < t) (htomega : t < omega) (x : M) :
    -(3 / (2 * t)) ≤ metricScalarAt (I := 𝓡 3) (S.base.metric t) x :=
  universal_scalar_lower_bound homega S hS ht htomega x

end PoincareScalarFlowTests
