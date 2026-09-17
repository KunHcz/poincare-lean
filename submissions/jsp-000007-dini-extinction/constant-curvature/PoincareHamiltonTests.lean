import PoincareHamilton.SphericalSpaceForm

/-!
# Statement and geometric regression checks

The round sphere supplies actual witnesses for the geometric hypotheses.
The literal-metric regression below checks the endpoint with the upstream
curvature tensor, rather than with a quotient-presentation certificate.
-/

open Function Set Metric
open DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.ThreeManifold
open PoincareHamilton
open scoped Manifold ContDiff

namespace PoincareHamiltonTests

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

/-- A concrete witness for the closed three-manifold hypothesis. -/
theorem standardSphere_closed : isClosedThreeManifold (I := 𝓡 3) (M := Sphere3) := by
  exact ⟨inferInstance, inferInstance, inferInstance, by simp⟩

/-- A concrete positive-curvature metric, not an assumed classification. -/
theorem standardSphere_constantPositiveCurvature :
    admitsConstantPositiveSectionalCurvature (I := 𝓡 3) (M := Sphere3) := by
  exact ⟨roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3),
    roundMetric_constPosSec⟩

/-- The constructed diffeomorphism is the actual supplied projection. -/
theorem actual_projection (D : RoundQuotientData (EuclideanSpace ℝ (Fin 4)) 3)
    [SimplyConnectedSpace D.Q] (q : Sphere3) :
    roundQuotientDiffeomorph D q = D.proj q := rfl

/-- Its inverse is an inverse to that same projection. -/
theorem projection_inverse (D : RoundQuotientData (EuclideanSpace ℝ (Fin 4)) 3)
    [SimplyConnectedSpace D.Q] (q : D.Q) :
    D.proj ((roundQuotientDiffeomorph D).symm q) = q :=
  (roundQuotientDiffeomorph D).apply_symm_apply q

/-- Expanded metric formulation: no spherical model, surgery data, or final
homeomorphism occurs among the assumptions. -/
theorem literal_metric_endpoint
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [CompactSpace M] [SigmaCompactSpace M] [T2Space M] [SimplyConnectedSpace M]
    (g : SmoothRiemannianMetric (𝓡 3) M) (c : ℝ) (hc : 0 < c)
    (hcurv : ∀ x : M, ∀ X Y : TangentSpace (𝓡 3) x,
      metricRm04StdAt (I := 𝓡 3) (M := M) g x X Y Y X =
        c * (g.inner x X X * g.inner x Y Y - g.inner x X Y * g.inner x X Y)) :
    Nonempty (M ≃ₜ Sphere3) := by
  apply constantPositiveCurvature_homeomorph_sphere
    (M := M) (hM := ⟨inferInstance, inferInstance, inferInstance, by simp⟩)
  exact ⟨g, c, hc, hcurv⟩

end PoincareHamiltonTests
