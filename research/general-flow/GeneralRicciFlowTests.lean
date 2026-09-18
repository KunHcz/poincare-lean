import GeneralRicciFlow
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
Concrete model and equation-fidelity tests for the unrestricted-in-metric
smooth-flow component. The sphere test produces an actual initial metric and
maximal flow; no curvature sign or finite endpoint is supplied as an input.
The existence statement does not evaluate the metric or construct an explicit
closed-form solution of the PDE.
-/

open Set DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature PoincareGeneralFlow
open scoped Manifold ContDiff

namespace PoincareGeneralFlowTests

abbrev StandardSphere3 := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

/-- The model is nonempty and has distinct points, so the existence test
does not use an empty or collapsed manifold. -/
theorem sphere_model_has_distinct_points : ∃ x y : StandardSphere3, x ≠ y := by
  refine ⟨⟨EuclideanSpace.single 0 1, by simp⟩,
    ⟨EuclideanSpace.single 0 (-1), by simp⟩, ?_⟩
  intro h
  have h0 := congrArg (fun s : StandardSphere3 => s.val 0) h
  norm_num at h0

/-- All the topological/manifold inputs are instantiated by the genuine
standard sphere, without assuming the existence of a flow or initial metric. -/
theorem sphere_initial_metric_and_maximal_flow :
    ∃ g0 : SmoothRiemannianMetric (𝓡 3) StandardSphere3,
      Nonempty (MaximalForwardRicciFlow (I := 𝓡 3) (M := StandardSphere3) g0) :=
  initial_metric_and_maximal_flow (M := StandardSphere3)

/-- The constructed flow has a genuine positive time interval of existence
and its value at time zero is exactly the supplied metric. -/
theorem sphere_flow_has_positive_lifetime :
    ∃ g0 : SmoothRiemannianMetric (𝓡 3) StandardSphere3,
      ∃ P : MaximalForwardRicciFlow (I := 𝓡 3) (M := StandardSphere3) g0,
        P.metric 0 = g0 ∧ ∃ t > 0, P.IsDefinedAt t := by
  obtain ⟨g0, ⟨P⟩⟩ := sphere_initial_metric_and_maximal_flow
  refine ⟨g0, P, P.metric_zero, ?_⟩
  cases P with
  | finite P =>
    refine ⟨P.T / 2, by linarith [P.flow.hT], ?_⟩
    change 0 ≤ P.T / 2 ∧ P.T / 2 < P.T
    constructor <;> linarith [P.flow.hT]
  | immortal P => exact ⟨1, by norm_num, ⟨by norm_num, trivial⟩⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Model3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]

omit [CompactSpace M] in
/-- This is the literal metric Ricci-flow equation, not a certificate named
`flow`: it holds at every point, pair of tangent vectors and defined time. -/
theorem maximal_flow_satisfies_literal_metric_PDE
    {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : MaximalForwardRicciFlow (I := 𝓡 3) (M := M) g0)
    {t : ℝ} (ht : P.IsDefinedAt t) (x : M) (v w : TangentSpace (𝓡 3) x) :
    HasDerivWithinAt (fun s : ℝ => (P.metric s).inner x v w)
      ((-2 : ℝ) * ricciTensor (I := 𝓡 3) (P.metric t) x v w) (Ici 0) t := by
  obtain ⟨T, Q, htT, hmetric⟩ := maximal_has_finite_view P ht
  have heq : P.metric = Q.S.family.metric := funext hmetric
  rw [heq]
  exact Q.pde t ⟨ht.1, htT⟩ x v w

/-- Maximality, not the word `finite`, is what rules out further lifespan. -/
theorem maximal_and_immortal_cannot_coexist {g0 : SmoothRiemannianMetric (𝓡 3) M} :
    ¬ (Nonempty (FiniteMaximalFlow (I := 𝓡 3) (M := M) g0) ∧
        Nonempty (ImmortalFlow (I := 𝓡 3) (M := M) g0)) := by
  rintro ⟨⟨P⟩, ⟨Q⟩⟩
  exact (finite_maximal_excludes_immortal P).false Q

/-- A genuine immortal solution restricted to a finite interval can never
be promoted to the finite maximal branch. This is a proved conditional
counter-check, not an asserted construction of an immortal example. -/
theorem finite_view_of_immortal_is_not_maximal {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : ImmortalFlow (I := 𝓡 3) (M := M) g0) (T : ℝ) (hT : 0 < T) :
    ¬ IsMaximalAtEndpoint (I := 𝓡 3) hT (restrictImmortal P T hT).S := by
  intro hmax
  let Q : FiniteMaximalFlow (I := 𝓡 3) (M := M) g0 := ⟨T, restrictImmortal P T hT, hmax⟩
  exact (finite_maximal_excludes_immortal Q).false P

/-- The scalar bound applies to the real maximal metric at a positive
time; this test does not assume a scalar differential inequality. -/
theorem literal_scalar_bound {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : MaximalForwardRicciFlow (I := 𝓡 3) (M := M) g0)
    (t : ℝ) (ht : P.IsDefinedAt t) (hpos : 0 < t) (x : M) :
    -(3 / (2 * t)) ≤ metricScalarAt (I := 𝓡 3) (P.metric t) x :=
  maximal_universal_scalar_bound P ht hpos x

end PoincareGeneralFlowTests
