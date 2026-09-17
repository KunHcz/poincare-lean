import PoincareHamilton.SphericalSpaceForm
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.PositiveRicci.Hamilton

/-!
# Poincare conclusion for positive-Ricci closed three-manifolds

This is an integration of the independently authored Hamilton formalization
with the actual smooth quotient-covering endgame. The positive-Ricci metric
is explicitly required; no claim is made that every simply connected
topological three-manifold admits such a metric.
-/

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold
open scoped Manifold ContDiff

namespace PoincareHamilton

universe u

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [SigmaCompactSpace M] [T2Space M] [SimplyConnectedSpace M]

/-- Full conclusion for the stated positive-Ricci class, not the general
topological Poincare conjecture. Hamilton's theorem is imported as a checked
theorem, not assumed as an axiom or passed as a hypothesis. -/
theorem positiveRicci_poincare
    (hM : isClosedThreeManifold (I := 𝓡 3) (M := M))
    (hpos : admitsPositiveRicci (I := 𝓡 3) (M := M)) :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Sphere3) := by
  exact diffeomorph_sphere_of_sphericalSpaceForm
    (DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_positive_ricci
      (I := 𝓡 3) (M := M) hM hpos).2

end PoincareHamilton
