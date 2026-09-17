import CappingTheorem
import HatcherLib.Ch1.Circle

/-!
These tests use actual quotient spaces and standard Euclidean balls.
The doubled-ball case applies the cap-preservation theorem to a concrete
simply connected original gluing. The circle-product example shows that
attaching a ball does not make an arbitrary retained space simply connected.
The latter is an adjunction-space counterexample, not a Ricci-surgery model.
-/

open Function Set Topology PoincareConjecture
open scoped ContinuousMap unitInterval

noncomputable section

namespace PoincareCapTests

instance closedThreeBall_contractible : ContractibleSpace ThreeBall :=
  (convex_closedBall (0 : BallModel) 1).contractibleSpace ⟨0, by simp⟩

theorem boundaryInclusion_isClosedEmbedding : IsClosedEmbedding sphere2BoundaryInclusion := by
  apply sphere2BoundaryInclusion.continuous.isClosedEmbedding
  intro a b h
  apply Subtype.ext
  exact congrArg (fun z : ThreeBall => (z : BallModel)) h

/-- Gluing in the attaching sphere itself is literally the original retained
ball. This supplies the original space for the non-vacuous capping test. -/
def boundaryOnlyHomeomorph :
    BoundaryGluing sphere2BoundaryInclusion (ContinuousMap.id Sphere2) ≃ₜ ThreeBall := by
  let F := boundaryGluingDesc sphere2BoundaryInclusion (ContinuousMap.id Sphere2)
    (ContinuousMap.id ThreeBall) sphere2BoundaryInclusion (fun _ => rfl)
  let G := boundaryGluingInl sphere2BoundaryInclusion (ContinuousMap.id Sphere2)
  refine {
    toFun := F
    invFun := G
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := F.continuous
    continuous_invFun := G.continuous }
  · intro q
    induction q using Quot.ind with
    | _ z =>
      cases z with
      | inl b => rfl
      | inr s => exact boundaryGluing_boundary_eq sphere2BoundaryInclusion (ContinuousMap.id Sphere2) s
  · intro b
    rfl

/-- The actual quotient of two closed three-balls with their corresponding
boundary points identified is simply connected. No sphere recognition is
used or claimed for this test. -/
theorem doubled_closed_ball_simplyConnected :
    SimplyConnectedSpace (BallAttachment sphere2BoundaryInclusion) := by
  letI : SimplyConnectedSpace (BoundaryGluing sphere2BoundaryInclusion (ContinuousMap.id Sphere2)) :=
    boundaryOnlyHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  exact capped_piece_simplyConnected sphere2BoundaryInclusion (ContinuousMap.id Sphere2)
    boundaryInclusion_isClosedEmbedding (Homeomorph.refl Sphere2).isClosedEmbedding

/-- Exercise both sides of the cut: the two outputs are the doubled ball
and the ball attached directly to its own boundary sphere. -/
theorem two_different_caps_simplyConnected :
    SimplyConnectedSpace (BallAttachment sphere2BoundaryInclusion) ∧
      SimplyConnectedSpace (BallAttachment (ContinuousMap.id Sphere2)) := by
  letI : SimplyConnectedSpace (BoundaryGluing sphere2BoundaryInclusion (ContinuousMap.id Sphere2)) :=
    boundaryOnlyHomeomorph.toHomotopyEquiv.simplyConnectedSpace
  exact both_capped_pieces_simplyConnected sphere2BoundaryInclusion (ContinuousMap.id Sphere2)
    boundaryInclusion_isClosedEmbedding (Homeomorph.refl Sphere2).isClosedEmbedding

theorem cap_center_is_not_retained (i : C(Sphere2, ThreeBall)) :
    ballAttachmentInr i ⟨0, by simp⟩ ∉ ballAttachmentRetainedOpen i := by
  change ¬ (0 : ℝ) < ‖(0 : BallModel)‖
  simp

theorem cap_center_and_boundary_are_distinct (i : C(Sphere2, ThreeBall)) :
    ballAttachmentInr i ⟨0, by simp⟩ ≠ ballAttachmentInl i (i sphere2Point) := by
  intro h
  have hr := congrArg (ballAttachmentRadius i) h
  change ‖(0 : BallModel)‖ = 1 at hr
  norm_num at hr

theorem boundary_is_identified_exactly_as_specified (i : C(Sphere2, ThreeBall)) (s : Sphere2) :
    ballAttachmentInl i (i s) = ballAttachmentInr i (sphere2BoundaryInclusion s) :=
  boundaryGluing_boundary_eq i sphere2BoundaryInclusion s

theorem radial_deformation_fixes_retained_side (i : C(Sphere2, ThreeBall)) (t : I) (x : ThreeBall) :
    puncturedAttachmentDeformation i (t, puncturedAttachmentInl i x) = puncturedAttachmentInl i x :=
  puncturedAttachmentDeformation_fixed i t x

def sphereCircleAttaching : C(Sphere2, Sphere2 × Circle) :=
  ⟨fun s => (s, 1), continuous_id.prodMk continuous_const⟩

def residualCircleProjection : C(BallAttachment sphereCircleAttaching, Circle) :=
  boundaryGluingDesc sphereCircleAttaching sphere2BoundaryInclusion
    ⟨Prod.snd, continuous_snd⟩ (ContinuousMap.const ThreeBall 1) (fun _ => rfl)

def residualCircleSection : C(Circle, BallAttachment sphereCircleAttaching) :=
  (ballAttachmentInl sphereCircleAttaching).comp
    ⟨fun z => (sphere2Point, z), continuous_const.prodMk continuous_id⟩

theorem residualCircle_retracts :
    residualCircleProjection.comp residualCircleSection = ContinuousMap.id Circle := by
  ext z
  rfl

/-- A genuinely nontrivial circle loop survives the ball attachment, so
the simply connected original-space input cannot just be discarded. -/
theorem circle_product_attachment_not_simplyConnected :
    ¬ SimplyConnectedSpace (BallAttachment sphereCircleAttaching) := by
  intro h
  letI := h
  have hsurj : Surjective (FundamentalGroup.map (ContinuousMap.id Circle) (1 : Circle)) := by
    intro g
    refine ⟨g, ?_⟩
    change Path.Homotopic.Quotient.map g (ContinuousMap.id Circle) = g
    induction g using Path.Homotopic.Quotient.ind with
    | mk p =>
      change Path.Homotopic.Quotient.mk (p.map (ContinuousMap.id Circle).continuous) =
        Path.Homotopic.Quotient.mk p
      apply congrArg Path.Homotopic.Quotient.mk
      ext t
      rfl
  haveI : SimplyConnectedSpace Circle := simplyConnected_of_loop_generating_factorization
    residualCircleSection (ContinuousMap.id Circle) residualCircleProjection residualCircle_retracts 1 hsurj
  have htrivial : Subsingleton (Multiplicative ℤ) :=
    HatcherLib.geometricCircleFundamentalGroupMulEquiv.surjective.subsingleton
  exact (zero_ne_one : (0 : ℤ) ≠ 1)
    (congrArg Multiplicative.toAdd (htrivial.elim (Multiplicative.ofAdd 0) (Multiplicative.ofAdd 1)))

end PoincareCapTests
