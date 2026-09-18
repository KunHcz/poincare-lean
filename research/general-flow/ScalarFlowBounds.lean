import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Regularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Preservation.ScalarLowerBound
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Tactic

/-!
# Scalar bounds for genuine three-dimensional Ricci flows

The only evolution hypothesis is the upstream `IsSolutionOn` predicate for
the actual metric family. Its scalar evolution, spatial regularity and
trace inequality are derived, not assumed as an abstract scalar ODE.
There is no positive-Ricci, positive-scalar, spherical-quotient or
simple-connectivity hypothesis.

In particular, an initial scalar bound `R ≥ -6` gives the exact estimate
`R(t) ≥ -6 / (1 + 4t)` used in the submitted extinction comparison. Compactness
also yields the initial-independent bound `R(t) ≥ -3 / (2t)` at positive times.
The source identities and maximum-principle implementation are credited to
the pinned DifferentialGeometry and Mathlib dependencies.
-/

open Set Function
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic
open scoped Manifold ContDiff

noncomputable section

namespace PoincareScalarFlow

theorem barrier_denominator_pos {c t : ℝ} (hc : c ≤ 0) (ht : 0 ≤ t) :
    0 < 1 - (2 / 3 : ℝ) * c * t := by
  have hct := mul_nonpos_of_nonpos_of_nonneg hc ht
  nlinarith

theorem barrier_nonpos {c t : ℝ} (hc : c ≤ 0) (ht : 0 ≤ t) :
    scalarLowerBarrier 3 c t ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg hc (barrier_denominator_pos hc ht).le

/-- Restarting the rational barrier does not reset its global clock. -/
theorem barrier_restart {c a u : ℝ} (hc : c ≤ 0) (ha : 0 ≤ a) :
    scalarLowerBarrier 3 (scalarLowerBarrier 3 c a) u = scalarLowerBarrier 3 c (a + u) := by
  have hd0 := (barrier_denominator_pos hc ha).ne'
  unfold scalarLowerBarrier
  rw [div_div]
  congr 1
  calc
    (1 - (2 / 3 : ℝ) * c * a) * (1 - (2 / 3 : ℝ) * (c / (1 - (2 / 3 : ℝ) * c * a)) * u) =
        (1 - (2 / 3 : ℝ) * c * a) - (2 / 3 : ℝ) *
          ((c / (1 - (2 / 3 : ℝ) * c * a)) * (1 - (2 / 3 : ℝ) * c * a)) * u := by ring
    _ = (1 - (2 / 3 : ℝ) * c * a) - (2 / 3 : ℝ) * c * u := by
      rw [div_mul_cancel₀ _ hd0]
    _ = 1 - (2 / 3 : ℝ) * c * (a + u) := by ring

theorem barrier_ge_universal {c t : ℝ} (hc : c ≤ 0) (ht : 0 < t) :
    -(3 / (2 * t)) ≤ scalarLowerBarrier 3 c t := by
  unfold scalarLowerBarrier
  rw [← neg_div, div_le_div_iff₀ (mul_pos (by norm_num) ht)
    (barrier_denominator_pos hc ht.le)]
  nlinarith

theorem normalized_barrier (t : ℝ) :
    scalarLowerBarrier 3 (-6) t = -6 / (1 + 4 * t) := by
  unfold scalarLowerBarrier
  congr 1
  ring

abbrev Model3 := EuclideanSpace ℝ (Fin 3)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Model3 M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [CompactSpace M]
  {D : RealTimeInterval}

/-- The original metric family and its canonical Levi-Civita connection,
not a replacement family with a postulated scalar field. -/
def metricConnectionFamily (S : SolutionOn (I := 𝓡 3) (M := M) D) :
    MetricConnectionFamily (I := 𝓡 3) (M := M) ℝ where
  metric := S.base.metric
  connection := S.base.connection
  metricCompatible t :=
    leviCivitaConnectionOfMetric_isMetricCompatible (I := 𝓡 3) (S.base.metric t)

omit [CompactSpace M] in
/-- Cauchy--Schwarz for the actual Ricci tensor and its scalar contraction.
No global tangent frame or positive-curvature condition is required. -/
theorem scalar_trace_bound (S : SolutionOn (I := 𝓡 3) (M := M) D) (t : ℝ) (x : M) :
    (1 / 3 : ℝ) * (S.scalar t x) ^ 2 ≤
      normSq0S (I := 𝓡 3) (S.family.metric t) x 2 (S.ricci t x) := by
  let : Nonempty (DifferentialGeometry.Tensor.Coordinates.CoordinateIdx (𝕜 := ℝ) Model3) :=
    ⟨⟨0, by simp [Model3]⟩⟩
  let basis := DifferentialGeometry.Tensor.Coordinates.coordinateFrameAtToBasis (I := 𝓡 3) x
  let gInv := fun i j =>
    DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChartComponent
      (I := 𝓡 3) (S.family.metric t) x i j (extChartAt (𝓡 3) x x)
  have hinv : MetricInverseInBasisGen (I := 𝓡 3) (S.family.metric t) x basis gInv := by
    exact DifferentialGeometry.Tensor.Coordinates.inverseMetricFlatModelInChart_metricInverseInBasis_center
      (I := 𝓡 3) (S.family.metric t) x
  have h := metricTracePair0SAt_sq_div_rank_le_normSq0S
    (I := 𝓡 3) (S.family.metric t) basis gInv hinv (S.ricciAt t x)
  simpa [DifferentialGeometry.Tensor.Coordinates.CoordinateIdx,
    ← SolutionOn.scalar_eq_metricTrace] using h

/-- A compact time-slab scalar comparison for the actual flow.
The auxiliary maximum-principle regularity and Lipschitz estimates are all
constructed inside this proof rather than added to the theorem assumptions. -/
theorem scalar_lower_bound_on_slab
    (S : SolutionOn (I := 𝓡 3) (M := M) D) (hS : IsSolutionOn (I := 𝓡 3) S)
    (T c : ℝ) (hT : 0 < T)
    (hslab : Icc 0 T ⊆ D.carrier)
    (hregular : ∀ t ∈ Icc 0 T, 0 < t → t ∈ D.regular)
    (hden : ∀ t ∈ Icc 0 T, 0 < 1 - (2 / 3 : ℝ) * c * t)
    (hinit : ∀ x : M, c ≤ S.scalar 0 x) :
    ∀ t ∈ Icc 0 T, ∀ x : M, scalarLowerBarrier 3 c t ≤ S.scalar t x := by
  have hu : ContinuousOn (fun p : ℝ × M => S.scalar p.1 p.2) (spacetimeSlab (M := M) T) :=
    hS.scalarCont.mono (fun p hp => ⟨hslab hp.1, hp.2⟩)
  have hb : ContinuousOn (scalarLowerBarrier 3 c) (Icc 0 T) := by
    intro t ht
    exact (scalarLowerBarrier_hasDerivWithinAt (Icc 0 T) 3 c t (by norm_num)
      (hden t ht).ne').continuousWithinAt
  have hcompact := scalarWeakMaximumPrincipleValueSet_isCompact
    T S.scalar (scalarLowerBarrier 3 c) hu hb
  obtain ⟨K, hK⟩ := exists_scalarLowerReaction_lipschitzOn_valueSet
    (M := M) 3 T S.scalar (scalarLowerBarrier 3 c) hcompact
  have hsmooth := smoothOfSol (I := 𝓡 3) S hS
  let G := metricConnectionFamily S
  have hreg := scalarRegOfSmooth (I := 𝓡 3) S hsmooth G T 3 c K
    (fun t ht => hslab ht) (fun _ _ => rfl) (fun t ht => (hden t ht).ne')
  have hevol := scalar_evolution_of_smooth_solution (I := 𝓡 3) S hsmooth G
    (fun _ => rfl) (fun _ => rfl)
  exact scalar_curvature_lower_bound_of_scalarEvolution_of_regularity
    (I := 𝓡 3) G T 3 c hT (by norm_num) S.scalar
    (fun t x => laplacianAt (I := 𝓡 3) G t (S.scalar t) x)
    (fun t x => normSq0S (I := 𝓡 3) (S.family.metric t) x 2 (S.ricci t x)) K
    hslab hregular hden hreg hevol
    (ScalarLaplacianRealizesHeatOperatorOn.of_laplacianAt (fun _ _ _ => rfl))
    (fun t _ x => scalar_trace_bound S t x) hinit hK

/-- Any nonpositive initial scalar bound propagates throughout the actual
closed-open flow interval, with no sign condition on the Ricci tensor. -/
theorem scalar_lower_bound
    {omega : ℝ} (homega : 0 < omega)
    (S : SolutionOn (I := 𝓡 3) (M := M) (RealTimeInterval.closedOpen 0 omega homega))
    (hS : IsSolutionOn (I := 𝓡 3) S)
    {c : ℝ} (hc : c ≤ 0) (hinit : ∀ x : M, c ≤ S.scalar 0 x)
    {t : ℝ} (ht : 0 ≤ t) (htomega : t < omega) (x : M) :
    scalarLowerBarrier 3 c t ≤ S.scalar t x := by
  by_cases ht0 : t = 0
  · subst t
    simpa using hinit x
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    apply scalar_lower_bound_on_slab S hS t c htpos
      (fun s hs => show s ∈ Ico 0 omega from ⟨hs.1, hs.2.trans_lt htomega⟩)
      (fun s hs hspos => show s ∈ Ioo 0 omega from ⟨hspos, hs.2.trans_lt htomega⟩)
      (fun _ hs => barrier_denominator_pos hc hs.1) hinit t ⟨ht, le_rfl⟩ x

/-- The exact geometric scalar bound used by the extinction comparison. -/
theorem normalized_scalar_lower_bound
    {omega : ℝ} (homega : 0 < omega)
    (S : SolutionOn (I := 𝓡 3) (M := M) (RealTimeInterval.closedOpen 0 omega homega))
    (hS : IsSolutionOn (I := 𝓡 3) S)
    (hinit : ∀ x : M, -6 ≤ S.scalar 0 x)
    {t : ℝ} (ht : 0 ≤ t) (htomega : t < omega) (x : M) :
    -6 / (1 + 4 * t) ≤ S.scalar t x := by
  simpa only [normalized_barrier] using
    scalar_lower_bound homega S hS (by norm_num : (-6 : ℝ) ≤ 0) hinit ht htomega x

/-- Compactness supplies a nonpositive scalar lower bound for the initial
metric; no minimum or lower bound is an additional geometric assumption. -/
theorem exists_initial_nonpositive_scalar_bound (S : SolutionOn (I := 𝓡 3) (M := M) D) :
    ∃ c ≤ 0, ∀ x : M, c ≤ S.scalar 0 x := by
  have hc : Continuous (S.scalar 0) := (scalarSmoothOfSol (I := 𝓡 3) S 0).continuous
  obtain ⟨b, hb⟩ := (isCompact_univ.image hc).bddBelow
  refine ⟨min b 0, min_le_right _ _, ?_⟩
  intro x
  exact (min_le_left _ _).trans (hb ⟨x, mem_univ _, rfl⟩)

/-- An initial-metric-independent bound for every positive time of a
compact smooth three-dimensional Ricci flow. -/
theorem universal_scalar_lower_bound
    {omega : ℝ} (homega : 0 < omega)
    (S : SolutionOn (I := 𝓡 3) (M := M) (RealTimeInterval.closedOpen 0 omega homega))
    (hS : IsSolutionOn (I := 𝓡 3) S)
    {t : ℝ} (ht : 0 < t) (htomega : t < omega) (x : M) :
    -(3 / (2 * t)) ≤ S.scalar t x := by
  obtain ⟨c, hc, hinit⟩ := exists_initial_nonpositive_scalar_bound S
  exact (barrier_ge_universal hc ht).trans
    (scalar_lower_bound homega S hS hc hinit ht.le htomega x)

/-- The global barrier is preserved when a smooth flow segment is restarted
at a later global time with the appropriate inherited initial scalar bound. -/
theorem scalar_lower_bound_after_restart
    {omega : ℝ} (homega : 0 < omega)
    (S : SolutionOn (I := 𝓡 3) (M := M) (RealTimeInterval.closedOpen 0 omega homega))
    (hS : IsSolutionOn (I := 𝓡 3) S)
    {c a : ℝ} (hc : c ≤ 0) (ha : 0 ≤ a)
    (hinit : ∀ x : M, scalarLowerBarrier 3 c a ≤ S.scalar 0 x)
    {u : ℝ} (hu : 0 ≤ u) (huomega : u < omega) (x : M) :
    scalarLowerBarrier 3 c (a + u) ≤ S.scalar u x := by
  rw [← barrier_restart hc ha (u := u)]
  exact scalar_lower_bound homega S hS (barrier_nonpos hc ha) hinit hu huomega x

/-- The normalized estimate retains the elapsed global time after restarting
a smooth segment. Producing the new segment and proving the inherited
initial bound during surgery are deliberately not asserted by this theorem. -/
theorem normalized_scalar_lower_bound_after_restart
    {omega : ℝ} (homega : 0 < omega)
    (S : SolutionOn (I := 𝓡 3) (M := M) (RealTimeInterval.closedOpen 0 omega homega))
    (hS : IsSolutionOn (I := 𝓡 3) S)
    {a : ℝ} (ha : 0 ≤ a)
    (hinit : ∀ x : M, -6 / (1 + 4 * a) ≤ S.scalar 0 x)
    {u : ℝ} (hu : 0 ≤ u) (huomega : u < omega) (x : M) :
    -6 / (1 + 4 * (a + u)) ≤ S.scalar u x := by
  simpa only [normalized_barrier] using scalar_lower_bound_after_restart homega S hS
    (c := -6) (by norm_num) ha (by simpa only [normalized_barrier] using hinit) hu huomega x

end PoincareScalarFlow
