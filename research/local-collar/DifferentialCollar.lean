import UniformCollar
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

/-!
# Coordinate derivatives supply the local inverse data

The inverse function theorem is applied to the actual coordinate expression
of the supplied family. It constructs its local open embedding rather than
assuming that embedding. CompactCollar then produces a single global width.
The input family and its invertible transverse coordinate derivatives still
need to be constructed for a general embedded sphere; this is not hidden as
an already-proved smooth tubular-neighbourhood theorem.
-/

open Function Set Topology
open scoped ContinuousMap

noncomputable section

namespace PoincareLocalCollar

variable {X Y E F : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Actual invertible coordinate derivative at a point produces an open
neighbourhood on which the original map, not just its coordinate formula,
is an open embedding. -/
theorem local_open_chart_of_strict_coordinate_derivative
    (f : C(X, Y)) (x : X)
    (a : OpenPartialHomeomorph X E) (b : OpenPartialHomeomorph Y F)
    (ha : x ∈ a.source) (hb : f x ∈ b.source)
    (L : E ≃L[ℝ] F)
    (hder : HasStrictFDerivAt (b ∘ f ∘ a.symm) (L : E →L[ℝ] F) (a x)) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ IsOpenEmbedding (U.restrict f) := by
  let ar := a.restr (f ⁻¹' b.source)
  let g := hder.toOpenPartialHomeomorph (b ∘ f ∘ a.symm)
  let e := (ar.trans g).trans b.symm
  have har : x ∈ ar.source := by
    refine ⟨ha, ?_⟩
    rw [(b.open_source.preimage f.continuous).interior_eq]
    exact hb
  have hxg : ar x ∈ g.source := hder.mem_toOpenPartialHomeomorph_source
  have hvalue : g (ar x) = b (f x) := by
    change b (f (a.symm (a x))) = b (f x)
    rw [a.left_inv ha]
  have he : x ∈ e.source := by
    refine ⟨⟨har, hxg⟩, ?_⟩
    change g (ar x) ∈ b.target
    rw [hvalue]
    exact b.map_source hb
  have heq : EqOn f e e.source := by
    intro y hy
    have hya : y ∈ a.source := hy.1.1.1
    have hyb : y ∈ f ⁻¹' b.source := @interior_subset _ _ (f ⁻¹' b.source) y hy.1.1.2
    change f y = b.symm (b (f (a.symm (a y))))
    rw [a.left_inv hya, b.left_inv hyb]
  refine ⟨e.source, e.open_source, he, ?_⟩
  have hf : e.source.restrict f = e.source.restrict e := by
    funext y
    exact heq y.property
  rw [hf]
  exact e.isOpenEmbedding_restrict

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

/-- Derivatives are stated on the literal coordinate expressions of the
same family. An isomorphism of tangent spaces is not silently replaced by
a local-homeomorphism or full-collar conclusion. -/
def HasInvertibleCoordinateDerivativesAtZero (f : C(S × ℝ, M)) (E F : Type*)
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Prop :=
  ∀ s : S, ∃ (a : OpenPartialHomeomorph (S × ℝ) E)
    (b : OpenPartialHomeomorph M F) (L : E ≃L[ℝ] F),
    (s, 0) ∈ a.source ∧ f (s, 0) ∈ b.source ∧
      HasStrictFDerivAt (b ∘ f ∘ a.symm) (L : E →L[ℝ] F) (a (s, 0))

theorem localCharts_of_coordinate_derivatives (f : C(S × ℝ, M))
    (hder : HasInvertibleCoordinateDerivativesAtZero f E F) : HasLocalOpenChartsAtZero f := by
  intro s
  obtain ⟨a, b, L, ha, hb, hf⟩ := hder s
  exact local_open_chart_of_strict_coordinate_derivative f (s, 0) a b ha hb L hf

/-- A single positive-width collar follows from pointwise coordinate
inverse-function data along the compact embedded zero section. -/
theorem exists_collar_of_coordinate_derivatives [CompactSpace S] [T2Space M]
    (f : C(S × ℝ, M)) (hzero : Injective (fun s => f (s, 0)))
    (hder : HasInvertibleCoordinateDerivativesAtZero f E F) :
    ∃ r > 0, IsOpenEmbedding (scaledCollar f r) :=
  exists_scaled_open_collar f hzero (localCharts_of_coordinate_derivatives f hder)

/-- Ordinary C1 coordinate regularity and its actual invertible derivative
are enough; callers need not provide strict differentiability or local
topological inverses separately. -/
theorem localCharts_of_C1_coordinates (f : C(S × ℝ, M))
    (hC1 : ∀ s : S, ∃ (a : OpenPartialHomeomorph (S × ℝ) E)
      (b : OpenPartialHomeomorph M F) (L : E ≃L[ℝ] F),
      (s, 0) ∈ a.source ∧ f (s, 0) ∈ b.source ∧
      ContDiffAt ℝ 1 (b ∘ f ∘ a.symm) (a (s, 0)) ∧
      HasFDerivAt (b ∘ f ∘ a.symm) (L : E →L[ℝ] F) (a (s, 0))) :
    HasLocalOpenChartsAtZero f := by
  apply localCharts_of_coordinate_derivatives (E := E) (F := F) f
  intro s
  obtain ⟨a, b, L, ha, hb, hc, hd⟩ := hC1 s
  exact ⟨a, b, L, ha, hb, hc.hasStrictFDerivAt' hd (by norm_num)⟩

theorem exists_collar_of_C1_coordinates [CompactSpace S] [T2Space M]
    (f : C(S × ℝ, M)) (hzero : Injective (fun s => f (s, 0)))
    (hC1 : ∀ s : S, ∃ (a : OpenPartialHomeomorph (S × ℝ) E)
      (b : OpenPartialHomeomorph M F) (L : E ≃L[ℝ] F),
      (s, 0) ∈ a.source ∧ f (s, 0) ∈ b.source ∧
      ContDiffAt ℝ 1 (b ∘ f ∘ a.symm) (a (s, 0)) ∧
      HasFDerivAt (b ∘ f ∘ a.symm) (L : E →L[ℝ] F) (a (s, 0))) :
    ∃ r > 0, IsOpenEmbedding (scaledCollar f r) :=
  exists_scaled_open_collar f hzero (localCharts_of_C1_coordinates f hC1)

open PoincareConjecture PoincareClosedCover in
/-- The literal differential hypothesis yields the complete local-family
topological consequence. No uniform width, global collar, complementary
regions or closed-side connectivity is a premise. -/
theorem coordinate_derivatives_separate_and_cap
    [CompactSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (f : C(Sphere2 × ℝ, M)) (hzero : Injective (fun s => f (s, 0)))
    (hder : HasInvertibleCoordinateDerivativesAtZero f E F) :
    ∃ r > 0, IsOpenEmbedding (scaledCollar f r) ∧
      ∃ (U V : Set M) (e : Sphere2 ≃ₜ ↥((U ∪ V)ᶜ)),
        IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧ Disjoint U V ∧
        (∀ s, (e s : M) = f (s, 0)) ∧
        (∀ s (t : CollarTime), (t : ℝ) < 0 → scaledCollar f r (s, t) ∈ U) ∧
        (∀ s (t : CollarTime), 0 < (t : ℝ) → scaledCollar f r (s, t) ∈ V) ∧
        (let e' := e.trans (complementBoundaryHomeomorph U V)
         SimplyConnectedSpace (BallAttachment (sphericalBoundaryLeft Vᶜ Uᶜ e')) ∧
           SimplyConnectedSpace (BallAttachment (sphericalBoundaryRight Vᶜ Uᶜ e'))) :=
  local_family_separates_and_caps f hzero (localCharts_of_coordinate_derivatives f hder)

end PoincareLocalCollar
