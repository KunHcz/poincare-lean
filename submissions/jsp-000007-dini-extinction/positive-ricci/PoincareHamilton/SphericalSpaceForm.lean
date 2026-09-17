import PoincareHamilton.RoundQuotient
import DifferentialGeometry.Geometry.Metric.Sphere.SpaceForm

/-!
# Recognition from a genuine constant-positive-curvature metric

This module integrates the fixed upstream space-form classification with
the independently constructed quotient-projection diffeomorphism. It does
not depend on the Hamilton positive-Ricci flow module. Constant sectional
curvature is an explicit restriction on the class of manifolds covered.

The upstream metric and curvature predicates are used unchanged. In
particular, a spherical quotient presentation or a homeomorphism to a sphere
is not included in the constant-curvature theorem's assumptions.
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

omit [IsManifold (𝓡 3) ∞ M] [SigmaCompactSpace M] [T2Space M] in
/-- Eliminate the actual upstream quotient model by proving that its own
projection is a diffeomorphism. No faithful-action assumption is added. -/
theorem diffeomorph_sphere_of_sphericalSpaceForm
    (h : isSphericalSpaceForm (I := 𝓡 3) (M := M)) :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Sphere3) := by
  obtain ⟨S⟩ := h
  let : SimplyConnectedSpace S.data.Q :=
    S.equiv.toHomeomorph.symm.toHomotopyEquiv.simplyConnectedSpace
  exact ⟨S.equiv.trans (roundQuotientDiffeomorph S.data).symm⟩

/-- The full sphere conclusion for the explicit constant-positive-sectional
curvature class, without assuming a quotient presentation. This is not the
unrestricted Poincare theorem. -/
theorem constantPositiveCurvature_poincare
    (hM : isClosedThreeManifold (I := 𝓡 3) (M := M))
    (hconst : admitsConstantPositiveSectionalCurvature (I := 𝓡 3) (M := M)) :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Sphere3) := by
  exact diffeomorph_sphere_of_sphericalSpaceForm
    (constant_positive_sectional_curvature_implies_spherical_space_form
      (I := 𝓡 3) (M := M) hM hconst)

/-- The associated homeomorphism uses the manifold's unchanged topology. -/
theorem constantPositiveCurvature_homeomorph_sphere
    (hM : isClosedThreeManifold (I := 𝓡 3) (M := M))
    (hconst : admitsConstantPositiveSectionalCurvature (I := 𝓡 3) (M := M)) :
    Nonempty (M ≃ₜ Sphere3) := by
  obtain ⟨e⟩ := constantPositiveCurvature_poincare hM hconst
  exact ⟨e.toHomeomorph⟩

end PoincareHamilton
