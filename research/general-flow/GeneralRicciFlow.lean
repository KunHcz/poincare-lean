import DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.MaximalFlow
import DifferentialGeometry.Geometry.Metric.MetricExistence
import ScalarFlowBounds
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Actual maximal forward Ricci flows from arbitrary initial metrics

The underlying geometric analysis belongs to DifferentialGeometry and the
arbitrary-maximal-flow extension by Arthur Freitas Ramos. This component
checks and integrates that extension, adds endpoint uniqueness, and connects
the resulting actual flows to the previously verified scalar bounds.

Neither positive curvature nor finite lifetime nor simple connectivity is
an input. The result explicitly retains the immortal branch. Eliminating
that branch for the Poincare setting and passing through singularities are
NOT consequences claimed here.
-/

open Set Bundle
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff

noncomputable section

namespace PoincareGeneralFlow

abbrev Model3 := EuclideanSpace ℝ (Fin 3)

private instance : NeZero (Module.finrank ℝ Model3) := ⟨by simp [Model3]⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Model3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]

/-- The initial metric is constructed from the genuine smooth tangent
bundle, not supplied as a positive-curvature or spherical certificate. -/
theorem initial_metric_exists : Nonempty (SmoothRiemannianMetric (𝓡 3) M) :=
  DifferentialGeometry.Geometry.nonempty_smoothRiemannianMetric (I := 𝓡 3) (M := M)

/-- The actual maximal smooth-flow object exists for every initial metric.
Its two constructors distinguish a finite maximal interval from an immortal
solution; the latter is not silently discarded. -/
theorem arbitrary_metric_maximal_flow (g0 : SmoothRiemannianMetric (𝓡 3) M) :
    Nonempty (MaximalForwardRicciFlow (I := 𝓡 3) (M := M) g0) :=
  exists_maximal_forward_ricci_flow g0

theorem initial_metric_and_maximal_flow :
    ∃ g0 : SmoothRiemannianMetric (𝓡 3) M,
      Nonempty (MaximalForwardRicciFlow (I := 𝓡 3) (M := M) g0) := by
  obtain ⟨g0⟩ := initial_metric_exists (M := M)
  exact ⟨g0, arbitrary_metric_maximal_flow g0⟩

/-- Restriction keeps the original metric family, including the initial
value; its PDE and joint regularity are restricted to a shorter interval. -/
def restrictFlowTo {g0 : SmoothRiemannianMetric (𝓡 3) M} {T U : ℝ}
    (P : FlowTo (I := 𝓡 3) (M := M) g0 T) (hU : 0 < U) (hUT : U ≤ T) :
    FlowTo (I := 𝓡 3) (M := M) g0 U := by
  let S : SolutionOn (I := 𝓡 3) (M := M) (RealTimeInterval.closedOpen 0 U hU) :=
    { base := P.S.base }
  have hj : ∀ (x0 : M) (i j : Fin (Module.finrank ℝ Model3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := 𝓡 3)
          (S.family.metric p.1) x0 p.2 i j)
        (Ico 0 U ×ˢ (trivializationAt Model3 (TangentSpace (𝓡 3)) x0).baseSet) := by
    intro x0 i j
    exact (P.joint x0 i j).mono (fun p hp => ⟨⟨hp.1.1, hp.1.2.trans_le hUT⟩, hp.2⟩)
  have hpde : ∀ t ∈ Ico 0 U, ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      HasDerivWithinAt (fun s : ℝ => (S.family.metric s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := 𝓡 3) (S.family.metric t) x v w) (Ici 0) t := by
    intro t ht x v w
    exact P.pde t ⟨ht.1, ht.2.trans_le hUT⟩ x v w
  have hsol : IsSolutionOn (I := 𝓡 3) S :=
    solutionOn_of_joint (I := 𝓡 3) hU S.family.metric hj hpde
  exact ⟨hU, S, hsol, P.start, hj, hpde⟩

omit [CompactSpace M] in
@[simp] theorem restrictFlowTo_metric {g0 : SmoothRiemannianMetric (𝓡 3) M} {T U : ℝ}
    (P : FlowTo (I := 𝓡 3) (M := M) g0 T) (hU : 0 < U) (hUT : U ≤ T) (t : ℝ) :
    (restrictFlowTo P hU hUT).S.family.metric t = P.S.family.metric t := rfl

/-- A finite view of an immortal solution does not turn it into a finite
maximal solution. Its metric and PDE remain those of the same original flow. -/
def restrictImmortal {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : ImmortalFlow (I := 𝓡 3) (M := M) g0) (T : ℝ) (hT : 0 < T) :
    FlowTo (I := 𝓡 3) (M := M) g0 T := by
  let S : SolutionOn (I := 𝓡 3) (M := M) (RealTimeInterval.closedOpen 0 T hT) :=
    { base := P.S.base }
  have hj : ∀ (x0 : M) (i j : Fin (Module.finrank ℝ Model3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ) ∞
        (fun p : ℝ × M => Integral.Measure.chartGramMatrix (I := 𝓡 3)
          (S.family.metric p.1) x0 p.2 i j)
        (Ico 0 T ×ˢ (trivializationAt Model3 (TangentSpace (𝓡 3)) x0).baseSet) := by
    intro x0 i j
    exact (P.joint x0 i j).mono (fun p hp => ⟨hp.1.1, hp.2⟩)
  have hpde : ∀ t ∈ Ico 0 T, ∀ x : M, ∀ v w : TangentSpace (𝓡 3) x,
      HasDerivWithinAt (fun s : ℝ => (S.family.metric s).inner x v w)
        ((-2 : ℝ) * ricciTensor (I := 𝓡 3) (S.family.metric t) x v w) (Ici 0) t := by
    intro t ht x v w
    exact P.pde t ht.1 x v w
  have hsol : IsSolutionOn (I := 𝓡 3) S :=
    solutionOn_of_joint (I := 𝓡 3) hT S.family.metric hj hpde
  exact ⟨hT, S, hsol, P.start, hj, hpde⟩

omit [CompactSpace M] in
@[simp] theorem restrictImmortal_metric {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : ImmortalFlow (I := 𝓡 3) (M := M) g0) (T : ℝ) (hT : 0 < T) (t : ℝ) :
    (restrictImmortal P T hT).S.family.metric t = P.S.family.metric t := rfl

omit [CompactSpace M] in
/-- Agreement of metrics entails agreement of the canonical Levi-Civita
connections and Ricci tensors; these fields cannot be assigned independently. -/
theorem solution_agrees_of_metrics {D E : RealTimeInterval}
    (S : SolutionOn (I := 𝓡 3) (M := M) D) (T : SolutionOn (I := 𝓡 3) (M := M) E)
    (U : Set ℝ) (h : ∀ t ∈ U, S.family.metric t = T.family.metric t) :
    SolutionAgreesOn (I := 𝓡 3) S T U := by
  intro t ht
  have hm : S.base.metric t = T.base.metric t := h t ht
  refine ⟨h t ht, ?_, ?_⟩
  · change leviCivitaConnectionOfMetric (I := 𝓡 3) (S.base.metric t) =
      leviCivitaConnectionOfMetric (I := 𝓡 3) (T.base.metric t)
    rw [hm]
  · change metricRicci (I := 𝓡 3) (S.base.metric t) = metricRicci (I := 𝓡 3) (T.base.metric t)
    rw [hm]

/-- A finite maximal endpoint dominates every other smooth solution with
the same initial metric, not just solutions already identified with it. -/
theorem finite_maximal_dominates {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : FiniteMaximalFlow (I := 𝓡 3) (M := M) g0) {U : ℝ}
    (Q : FlowTo (I := 𝓡 3) (M := M) g0 U) : U ≤ P.T := by
  by_contra h
  have hTU : P.T < U := lt_of_not_ge h
  have heps : 0 < U - P.T := sub_pos.mpr hTU
  have hwide : 0 < P.T + (U - P.T) := by linarith [Q.hT]
  let Q' := restrictFlowTo Q hwide (by linarith : P.T + (U - P.T) ≤ U)
  apply P.maximal
  refine ⟨U - P.T, heps, hwide, Q'.S, Q'.isSol, ?_⟩
  apply solution_agrees_of_metrics
  intro t ht
  exact flow_to_eq P.flow Q' ht.1 ht.2 (by linarith [ht.2])

theorem finite_maximal_excludes_immortal {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : FiniteMaximalFlow (I := 𝓡 3) (M := M) g0) :
    IsEmpty (ImmortalFlow (I := 𝓡 3) (M := M) g0) := by
  refine ⟨fun Q => ?_⟩
  have ht : 0 < P.T + 1 := by linarith [P.flow.hT]
  have h := finite_maximal_dominates P (restrictImmortal Q (P.T + 1) ht)
  linarith

/-- The maximal lifetime is unique, including the distinction between a
finite endpoint and infinite existence. No finite-lifetime premise is added. -/
theorem maximal_endpoint_unique {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P Q : MaximalForwardRicciFlow (I := 𝓡 3) (M := M) g0) : P.endpoint = Q.endpoint := by
  cases P with
  | finite P =>
    cases Q with
    | finite Q =>
      exact congrArg TimeEndpoint.finite (le_antisymm
        (finite_maximal_dominates Q P.flow) (finite_maximal_dominates P Q.flow))
    | immortal Q => exact False.elim ((finite_maximal_excludes_immortal P).false Q)
  | immortal P =>
    cases Q with
    | finite Q => exact False.elim ((finite_maximal_excludes_immortal Q).false P)
    | immortal Q => rfl

theorem maximal_metric_unique {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P Q : MaximalForwardRicciFlow (I := 𝓡 3) (M := M) g0)
    (t : ℝ) (ht : P.IsDefinedAt t) : P.metric t = Q.metric t := by
  have hQ : Q.IsDefinedAt t := by
    change 0 ≤ t ∧ TimeEndpoint.upperLt t Q.endpoint
    rw [← maximal_endpoint_unique P Q]
    exact ht
  exact MaximalForwardRicciFlow.metric_eq P Q t ht hQ

omit [CompactSpace M] in
/-- Every time in the maximal domain has a genuine finite solution view.
The metric is the same, not a different local approximation. -/
theorem maximal_has_finite_view {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : MaximalForwardRicciFlow (I := 𝓡 3) (M := M) g0)
    {t : ℝ} (ht : P.IsDefinedAt t) :
    ∃ T : ℝ, ∃ Q : FlowTo (I := 𝓡 3) (M := M) g0 T,
      t < T ∧ ∀ s : ℝ, P.metric s = Q.S.family.metric s := by
  cases P with
  | finite P => exact ⟨P.T, P.flow, ht.2, fun _ => rfl⟩
  | immortal P =>
    have hT : 0 < t + 1 := by linarith [ht.1]
    exact ⟨t + 1, restrictImmortal P (t + 1) hT, by linarith, fun _ => rfl⟩

/-- The earlier scalar estimate now applies to an existing maximal flow,
not a separately postulated scalar-valued evolution or supplied flow chain. -/
theorem maximal_normalized_scalar_bound {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : MaximalForwardRicciFlow (I := 𝓡 3) (M := M) g0)
    (hinit : ∀ x : M, -6 ≤ metricScalarAt (I := 𝓡 3) g0 x)
    {t : ℝ} (ht : P.IsDefinedAt t) (x : M) :
    -6 / (1 + 4 * t) ≤ metricScalarAt (I := 𝓡 3) (P.metric t) x := by
  obtain ⟨T, Q, htT, hmetric⟩ := maximal_has_finite_view P ht
  rw [hmetric t]
  exact PoincareScalarFlow.normalized_scalar_lower_bound Q.hT Q.S Q.isSol
    (by
      intro y
      change -6 ≤ metricScalarAt (I := 𝓡 3) (Q.S.family.metric 0) y
      rw [Q.start]
      exact hinit y) ht.1 htT x

theorem maximal_universal_scalar_bound {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : MaximalForwardRicciFlow (I := 𝓡 3) (M := M) g0)
    {t : ℝ} (ht : P.IsDefinedAt t) (htpos : 0 < t) (x : M) :
    -(3 / (2 * t)) ≤ metricScalarAt (I := 𝓡 3) (P.metric t) x := by
  obtain ⟨T, Q, htT, hmetric⟩ := maximal_has_finite_view P ht
  rw [hmetric t]
  exact PoincareScalarFlow.universal_scalar_lower_bound Q.hT Q.S Q.isSol htpos htT x

/-- Compactness yields one initial scalar lower bound that controls the
same maximal metric at every defined time. The constant is chosen before
the time and point, so this is not a time-dependent family of lower bounds. -/
theorem maximal_has_global_scalar_barrier {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : MaximalForwardRicciFlow (I := 𝓡 3) (M := M) g0) :
    ∃ c ≤ 0, ∀ t : ℝ, P.IsDefinedAt t → ∀ x : M,
      scalarLowerBarrier 3 c t ≤ metricScalarAt (I := 𝓡 3) (P.metric t) x := by
  obtain ⟨T0, Q0, _, _⟩ := maximal_has_finite_view P P.zero_defined
  obtain ⟨c, hc, h0⟩ := PoincareScalarFlow.exists_initial_nonpositive_scalar_bound Q0.S
  have hg0 : ∀ x : M, c ≤ metricScalarAt (I := 𝓡 3) g0 x := by
    intro x
    have h := h0 x
    change c ≤ metricScalarAt (I := 𝓡 3) (Q0.S.family.metric 0) x at h
    simpa only [Q0.start] using h
  refine ⟨c, hc, ?_⟩
  intro t ht x
  obtain ⟨T, Q, htT, hm⟩ := maximal_has_finite_view P ht
  rw [hm t]
  apply PoincareScalarFlow.scalar_lower_bound Q.hT Q.S Q.isSol hc _ ht.1 htT x
  intro y
  change c ≤ metricScalarAt (I := 𝓡 3) (Q.S.family.metric 0) y
  rw [Q.start]
  exact hg0 y

/-- The finite alternative has unbounded canonical Riemann curvature.
This is a genuine geometric singularity statement, but not a surgery
construction and not yet a proved convergence rate or blow-up model. -/
theorem finite_maximal_curvature_unbounded {g0 : SmoothRiemannianMetric (𝓡 3) M}
    (P : FiniteMaximalFlow (I := 𝓡 3) (M := M) g0) :
    ∀ K : ℝ, ∃ t : ℝ, ∃ x : M, 0 ≤ t ∧ t < P.T ∧
      K < Tensor0SBundle.normSq0S (I := 𝓡 3) (P.flow.S.family.metric t) x 4
        (P.flow.S.base.rm04 t x) :=
  rmUnbounded_of_maximal (I := 𝓡 3) (by simp) P.flow.isSol P.maximal
    (rm04Realizes_metric (I := 𝓡 3) P.flow.S)

end PoincareGeneralFlow
