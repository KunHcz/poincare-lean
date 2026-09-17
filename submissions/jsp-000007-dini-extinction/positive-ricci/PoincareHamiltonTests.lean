import PoincareHamilton

/-!
Regression statements for the positive-Ricci endpoint. The input below is a
genuine smooth metric and its pointwise Ricci tensor, not a spherical model
or a claim that the conclusion already holds. The separate curvature-case
package retains its actual round-metric witnesses.
-/

open DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold
open PoincareHamilton
open scoped Manifold ContDiff

namespace PoincareHamiltonTests

/-- The metric-level endpoint with its complete pointwise geometric hypothesis. -/
theorem literal_positive_ricci_endpoint
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [SimplyConnectedSpace M]
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (hpos : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < metricRicciAt (I := 𝓡 3) (M := M) g x (vec2 (I := 𝓡 3) v v)) :
    Nonempty (M ≃ₘ⟮𝓡 3, 𝓡 3⟯ Sphere3) := by
  exact positiveRicci_poincare
    ⟨inferInstance, inferInstance, inferInstance, by simp⟩ ⟨g, hpos⟩

/-- The topological consequence is on the original space and topology. -/
theorem literal_positive_ricci_homeomorph
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [SimplyConnectedSpace M]
    (g : SmoothRiemannianMetric (𝓡 3) M)
    (hpos : ∀ x : M, ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
      0 < metricRicciAt (I := 𝓡 3) (M := M) g x (vec2 (I := 𝓡 3) v v)) :
    Nonempty (M ≃ₜ Sphere3) :=
  (literal_positive_ricci_endpoint g hpos).map Diffeomorph.toHomeomorph

/-- The projection used to recognize the resulting quotient is the same map
whose local sections are provided by the geometric classification. -/
theorem quotient_projection_is_the_constructed_map
    (D : RoundQuotientData (EuclideanSpace ℝ (Fin 4)) 3)
    [SimplyConnectedSpace D.Q] (q : Sphere3) :
    roundQuotientDiffeomorph D q = D.proj q := rfl

end PoincareHamiltonTests
