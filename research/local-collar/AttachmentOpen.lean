import PuncturedCap

open Function Set Topology
open scoped ContinuousMap unitInterval

noncomputable section

namespace PoincareConjecture

def sphere2Point : Sphere2 := ⟨EuclideanSpace.single 0 1, by simp⟩

variable {X : Type*} [TopologicalSpace X]

/-- The natural inclusion of the punctured adjunction quotient into the full
ball attachment, with the original retained-side and ball-side maps. -/
def puncturedAttachmentFill (i : C(Sphere2, X)) : C(PuncturedBallAttachment i, BallAttachment i) :=
  boundaryGluingDesc i sphere2PuncturedInclusion (ballAttachmentInl i)
    ((ballAttachmentInr i).comp ⟨Subtype.val, continuous_subtype_val⟩)
    (fun s => boundaryGluing_boundary_eq i sphere2BoundaryInclusion s)

@[simp] theorem puncturedAttachmentFill_inl (i : C(Sphere2, X)) (x : X) :
    puncturedAttachmentFill i (puncturedAttachmentInl i x) = ballAttachmentInl i x := rfl

@[simp] theorem puncturedAttachmentFill_inr (i : C(Sphere2, X)) (b : PuncturedThreeBall) :
    puncturedAttachmentFill i (puncturedAttachmentInr i b) = ballAttachmentInr i b.1 := rfl

theorem puncturedAttachmentFill_mem (i : C(Sphere2, X)) (q : PuncturedBallAttachment i) :
    puncturedAttachmentFill i q ∈ ballAttachmentRetainedOpen i := by
  induction q using Quot.ind with
  | _ z =>
    cases z with
    | inl x => exact (zero_lt_one : (0 : ℝ) < 1)
    | inr b => exact b.property

/-- This raw inverse is intentionally not asserted continuous at the removed
centre. The value there is irrelevant; continuity is proved exactly on the
open retained-plus-punctured-ball region. -/
def ballAttachmentUnfill (i : C(Sphere2, X)) : BallAttachment i → PuncturedBallAttachment i := by
  classical
  let g : ThreeBall → PuncturedBallAttachment i := fun b =>
    if h : 0 < ‖(b : BallModel)‖ then puncturedAttachmentInr i ⟨b, h⟩
    else puncturedAttachmentInl i (i sphere2Point)
  refine Quot.lift (Sum.elim (puncturedAttachmentInl i) g) ?_
  intro a b h
  cases h with
  | glue s =>
    change puncturedAttachmentInl i (i s) = g (sphere2BoundaryInclusion s)
    have hs : 0 < ‖(sphere2BoundaryInclusion s : BallModel)‖ := by
      change 0 < ‖(s : BallModel)‖
      rw [mem_sphere_zero_iff_norm.mp s.property]
      exact zero_lt_one
    simp only [g, dif_pos hs]
    exact boundaryGluing_boundary_eq i sphere2PuncturedInclusion s

@[simp] theorem ballAttachmentUnfill_inl (i : C(Sphere2, X)) (x : X) :
    ballAttachmentUnfill i (ballAttachmentInl i x) = puncturedAttachmentInl i x := rfl

@[simp] theorem ballAttachmentUnfill_inr (i : C(Sphere2, X)) (b : PuncturedThreeBall) :
    ballAttachmentUnfill i (ballAttachmentInr i b.1) = puncturedAttachmentInr i b := by
  simp [ballAttachmentUnfill, ballAttachmentInr, boundaryGluingInr, b.property]

theorem ballAttachmentUnfill_fill (i : C(Sphere2, X)) (q : PuncturedBallAttachment i) :
    ballAttachmentUnfill i (puncturedAttachmentFill i q) = q := by
  induction q using Quot.ind with
  | _ z =>
    cases z with
    | inl x => rfl
    | inr b => exact ballAttachmentUnfill_inr i b

theorem puncturedAttachmentFill_unfill (i : C(Sphere2, X)) (q : BallAttachment i)
    (hq : q ∈ ballAttachmentRetainedOpen i) :
    puncturedAttachmentFill i (ballAttachmentUnfill i q) = q := by
  induction q using Quot.ind with
  | _ z =>
    cases z with
    | inl x => rfl
    | inr b =>
      change 0 < ‖(b : BallModel)‖ at hq
      change puncturedAttachmentFill i (ballAttachmentUnfill i (ballAttachmentInr i b)) = _
      rw [ballAttachmentUnfill_inr i ⟨b, hq⟩]
      rfl

theorem continuousOn_ballAttachmentUnfill (i : C(Sphere2, X)) :
    ContinuousOn (ballAttachmentUnfill i) (ballAttachmentRetainedOpen i) := by
  apply (isQuotientMap_quot_mk.continuousOn_isOpen_iff
    (ballAttachmentRetainedOpen_isOpen i)).2
  apply ((ballAttachmentRetainedOpen_isOpen i).preimage continuous_quot_mk).continuousOn_iff.mpr
  intro z hz
  cases z with
  | inl x =>
    apply (IsOpenEmbedding.inl.continuousAt_iff).mp
    exact (puncturedAttachmentInl i).continuous.continuousAt
  | inr b =>
    apply (IsOpenEmbedding.inr.continuousAt_iff).mp
    have hb : 0 < ‖(b : BallModel)‖ := hz
    have hopen : IsOpen {b : ThreeBall | 0 < ‖(b : BallModel)‖} :=
      isOpen_lt continuous_const (continuous_norm.comp continuous_subtype_val)
    apply (hopen.isOpenEmbedding_subtypeVal.continuousAt_iff (x := ⟨b, hb⟩)).mp
    have heq : (fun z : PuncturedThreeBall =>
        ballAttachmentUnfill i (ballAttachmentInr i z.1)) = puncturedAttachmentInr i := by
      funext z
      exact ballAttachmentUnfill_inr i z
    change ContinuousAt (fun z : PuncturedThreeBall =>
      ballAttachmentUnfill i (ballAttachmentInr i z.1)) _
    rw [heq]
    exact (puncturedAttachmentInr i).continuous.continuousAt

/-- Removing the cap centre gives the genuine punctured adjunction space.
The result holds for any attaching map; no collar or homotopy-equivalence
certificate is assumed. -/
def puncturedAttachmentHomeomorph (i : C(Sphere2, X)) :
    PuncturedBallAttachment i ≃ₜ ballAttachmentRetainedOpen i where
  toFun q := ⟨puncturedAttachmentFill i q, puncturedAttachmentFill_mem i q⟩
  invFun q := ballAttachmentUnfill i q
  left_inv := ballAttachmentUnfill_fill i
  right_inv q := Subtype.ext (puncturedAttachmentFill_unfill i q q.property)
  continuous_toFun := (puncturedAttachmentFill i).continuous.subtype_mk _
  continuous_invFun := (continuousOn_iff_continuous_restrict).mp (continuousOn_ballAttachmentUnfill i)

end PoincareConjecture
