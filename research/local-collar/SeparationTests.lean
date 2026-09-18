import SeparatedCapping
import HatcherLib.Ch1.Sphere
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Regression models for the actual collar theorem

The compact cylinder S² × [-2,2] supplies a genuine three-dimensional
collar satisfying every input of the separation-and-capping endpoint.
This cylinder has boundary and is not claimed to be a closed Poincare
manifold or a newly constructed Ricci surgery.
-/

open Function Set Topology
open PoincareSeparation PoincareClosedCover PoincareConjecture
open scoped ContinuousMap Manifold

noncomputable section

namespace PoincareSeparationTests

theorem crossing_at_negative_edge : crossingHeight (-(1 / 2)) = 0 :=
  crossingHeight_lower le_rfl

theorem crossing_at_positive_edge : crossingHeight (1 / 2) = 1 :=
  crossingHeight_upper le_rfl

theorem circle_glues_both_edges :
    (crossingHeight (-(1 / 2)) : PeriodicCircle) = (crossingHeight (1 / 2) : PeriodicCircle) := by
  rw [crossing_at_negative_edge, crossing_at_positive_edge, AddCircle.coe_zero, AddCircle.coe_period]

theorem real_lift_distinguishes_edges :
    crossingHeight (-(1 / 2)) ≠ crossingHeight (1 / 2) := by
  rw [crossing_at_negative_edge, crossing_at_positive_edge]
  exact zero_ne_one

theorem half_fiber_is_unique (t : ℝ) :
    (crossingHeight t : PeriodicCircle) = ((1 / 2 : ℝ) : PeriodicCircle) ↔ t = 0 :=
  crossingCircle_half_iff t

abbrev ThickInterval := ↥(Icc (-2 : ℝ) 2)
abbrev CompactCylinder := Sphere2 × ThickInterval

instance thickInterval_contractible : ContractibleSpace ThickInterval :=
  (convex_Icc (-2 : ℝ) 2).contractibleSpace ⟨0, by norm_num⟩

instance sphere2_simplyConnected : SimplyConnectedSpace Sphere2 :=
  HatcherLib.standardSphereSimplyConnected 0

instance cylinder_simplyConnected : SimplyConnectedSpace CompactCylinder := by
  obtain ⟨h⟩ := ContractibleSpace.hequiv_unit ThickInterval
  let e := ((ContinuousMap.HomotopyEquiv.refl Sphere2).prodCongr h).trans
    (Homeomorph.prodUnique Sphere2 Unit).toHomotopyEquiv
  exact e.simplyConnectedSpace

instance sphere2_locallyPathConnected : LocallyPathConnectedSpace Sphere2 := by
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
  exact ChartedSpace.locallyPathConnectedSpace (H := EuclideanSpace ℝ (Fin 2)) (M := Sphere2)

instance thickInterval_locallyPathConnected : LocallyPathConnectedSpace ThickInterval :=
  (convex_Icc (-2 : ℝ) 2).locallyPathConnectedSpace

instance cylinder_locallyPathConnected : LocallyPathConnectedSpace CompactCylinder := by
  apply LocallyPathConnectedSpace.of_bases
    (fun p : CompactCylinder => by
      rw [nhds_prod_eq]
      exact (path_connected_basis p.1).prod (path_connected_basis p.2))
  intro p uv huv
  exact huv.1.2.prod huv.2.2

def cylinderCollar : Sphere2 × CollarTime → CompactCylinder :=
  fun p => (p.1, ⟨p.2, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩)

theorem cylinderCollar_isOpenEmbedding : IsOpenEmbedding cylinderCollar := by
  have hincl : Ioo (-1 : ℝ) 1 ⊆ Icc (-2 : ℝ) 2 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsecond : IsOpenEmbedding (Set.inclusion hincl) :=
    IsOpenEmbedding.inclusion hincl (isOpen_Ioo.preimage continuous_subtype_val)
  exact IsOpenEmbedding.id.prodMap hsecond

theorem actual_cylinder_complement_is_disconnected :
    ¬ IsPreconnected (centralSphere cylinderCollar)ᶜ :=
  central_complement_not_preconnected cylinderCollar cylinderCollar_isOpenEmbedding

/-- Full endpoint regression using a concrete compact cylinder, not an
uninhabited abstract structure carrying the conclusion as a premise. -/
theorem actual_cylinder_both_caps_simplyConnected :
    ∃ (U V : Set CompactCylinder) (e : Sphere2 ≃ₜ ↥((U ∪ V)ᶜ)),
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧ Disjoint U V ∧
      (∀ s, (e s : CompactCylinder) = cylinderCollar (s, collarCentre)) ∧
      (∀ s (t : CollarTime), (t : ℝ) < 0 → cylinderCollar (s, t) ∈ U) ∧
      (∀ s (t : CollarTime), 0 < (t : ℝ) → cylinderCollar (s, t) ∈ V) ∧
      (let e' := e.trans (complementBoundaryHomeomorph U V)
       SimplyConnectedSpace (BallAttachment (sphericalBoundaryLeft Vᶜ Uᶜ e')) ∧
       SimplyConnectedSpace (BallAttachment (sphericalBoundaryRight Vᶜ Uᶜ e'))) :=
  sphere_collar_separates_and_caps cylinderCollar cylinderCollar_isOpenEmbedding

end PoincareSeparationTests
