import CutSides
import Mathlib.Analysis.Convex.Contractible

/-! Concrete regressions for the quotient and cap conclusions. The actual
closed three-ball supplies a nonempty spherical-intersection model; finite
spaces test disjoint/duplicate covers and reject an omitted-cover claim.
-/

open Set Function Topology PoincareConjecture PoincareClosedCover
open scoped ContinuousMap unitInterval

noncomputable section

namespace PoincareClosedCoverTests

def twoPointCover : ClosedCoverAdjunction ({false} : Set Bool) {true} ≃ₜ Bool :=
  closedCoverHomeomorph _ _ isClosed_singleton isClosed_singleton
    (by ext b; cases b <;> simp)

theorem twoPointCover_left :
    twoPointCover (boundaryGluingInl
      (intersectionLeft ({false} : Set Bool) {true})
      (intersectionRight ({false} : Set Bool) {true}) ⟨false, rfl⟩) = false := rfl

theorem twoPointCover_right :
    twoPointCover (boundaryGluingInr
      (intersectionLeft ({false} : Set Bool) {true})
      (intersectionRight ({false} : Set Bool) {true}) ⟨true, rfl⟩) = true := rfl

/-- Duplicate copies of the same point are identified by the actual
intersection relation, not treated as separate original points. -/
theorem duplicate_cover_identifies_overlap (b : Bool) :
    boundaryGluingInl (intersectionLeft (univ : Set Bool) univ)
      (intersectionRight (univ : Set Bool) univ) ⟨b, mem_univ _⟩ =
    boundaryGluingInr (intersectionLeft (univ : Set Bool) univ)
      (intersectionRight (univ : Set Bool) univ) ⟨b, mem_univ _⟩ :=
  boundaryGluing_boundary_eq (intersectionLeft (univ : Set Bool) univ)
    (intersectionRight (univ : Set Bool) univ) ⟨b, mem_univ _, mem_univ _⟩

/-- Missing a point of the original space makes reconstruction impossible. -/
theorem covering_condition_is_necessary :
    ¬ Surjective (closedCoverProjection ({false} : Set Bool) {false}) := by
  intro h
  obtain ⟨q, hq⟩ := h true
  induction q using Quot.ind with
  | _ z =>
    cases z with
    | inl b =>
      change (b : Bool) = true at hq
      have hb : (b : Bool) = false := b.property
      have hbad : false = true := hb.symm.trans hq
      cases hbad
    | inr b =>
      change (b : Bool) = true at hq
      have hb : (b : Bool) = false := b.property
      have hbad : false = true := hb.symm.trans hq
      cases hbad

instance closedBall_contractible : ContractibleSpace ThreeBall :=
  (convex_closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1).contractibleSpace ⟨0, by simp⟩

def ballBoundary : Set ThreeBall := {b | ‖(b : EuclideanSpace ℝ (Fin 3))‖ = 1}

def ballBoundaryIntersection : Sphere2 ≃ₜ ↥((univ : Set ThreeBall) ∩ ballBoundary) where
  toFun s := ⟨sphere2BoundaryInclusion s, mem_univ _, mem_sphere_zero_iff_norm.mp s.property⟩
  invFun x := ⟨x.val.val, mem_sphere_zero_iff_norm.mpr x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := sphere2BoundaryInclusion.continuous.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem ballBoundary_isClosed : IsClosed ballBoundary :=
  isClosed_eq (continuous_norm.comp continuous_subtype_val) continuous_const

theorem ballBoundary_pathConnected : IsPathConnected ballBoundary := by
  have hrange : Set.range sphere2BoundaryInclusion = ballBoundary := by
    ext b
    constructor
    · rintro ⟨s, rfl⟩
      exact mem_sphere_zero_iff_norm.mp s.property
    · intro hb
      exact ⟨⟨b.val, mem_sphere_zero_iff_norm.mpr hb⟩, rfl⟩
  rw [← hrange]
  exact isPathConnected_range sphere2BoundaryInclusion.continuous

/-- Both cap conclusions apply to a concrete compact simply connected
space and its actual spherical boundary. No original gluing equivalence
or boundary-embedding certificate is supplied to the endpoint. -/
theorem actual_closed_ball_cover_caps :
    SimplyConnectedSpace (BallAttachment
      (sphericalBoundaryLeft univ ballBoundary ballBoundaryIntersection)) ∧
    SimplyConnectedSpace (BallAttachment
      (sphericalBoundaryRight univ ballBoundary ballBoundaryIntersection)) :=
  both_closed_cover_caps_simplyConnected univ ballBoundary isClosed_univ ballBoundary_isClosed
    (by simp) ballBoundaryIntersection isPathConnected_univ ballBoundary_pathConnected

theorem positive_half_stays_inside : (positiveHalfTime (1 : I) : ℝ) = (1 / 2 : ℝ) := rfl

theorem negative_half_stays_inside : (negativeHalfTime (1 : I) : ℝ) = -(1 / 2 : ℝ) := by
  change -(1 : ℝ) / 2 = -(1 / 2 : ℝ)
  ring

end PoincareClosedCoverTests
