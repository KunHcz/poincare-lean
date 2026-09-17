import CapFilling
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Topology.Homotopy.Basic
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
import HatcherLib.Ch0.HomotopyExtension

open Function Set Topology
open scoped ContinuousMap unitInterval

noncomputable section

namespace PoincareConjecture

abbrev BallModel := EuclideanSpace ℝ (Fin 3)
abbrev PuncturedThreeBall := {b : ThreeBall // 0 < ‖(b : BallModel)‖}

def sphere2PuncturedInclusion : C(Sphere2, PuncturedThreeBall) := by
  refine ⟨fun s => ⟨sphere2BoundaryInclusion s, ?_⟩, ?_⟩
  · change 0 < ‖(s : BallModel)‖
    rw [mem_sphere_zero_iff_norm.mp s.property]
    exact zero_lt_one
  · apply Continuous.subtype_mk
    exact sphere2BoundaryInclusion.continuous

def puncturedBallDirection : C(PuncturedThreeBall, Sphere2) := by
  refine ⟨fun b => ⟨‖(b.1 : BallModel)‖⁻¹ • (b.1 : BallModel), ?_⟩, ?_⟩
  · simp only [mem_sphere_zero_iff_norm, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr b.property), inv_mul_cancel₀ b.property.ne']
  · apply Continuous.subtype_mk
    have hv : Continuous (fun b : PuncturedThreeBall => (b.1 : BallModel)) :=
      continuous_subtype_val.comp continuous_subtype_val
    exact (hv.norm.inv₀ (fun b => b.property.ne')).smul hv

@[simp] theorem puncturedBallDirection_boundary (s : Sphere2) :
    puncturedBallDirection (sphere2PuncturedInclusion s) = s := by
  apply Subtype.ext
  change ‖(s : BallModel)‖⁻¹ • (s : BallModel) = s
  rw [mem_sphere_zero_iff_norm.mp s.property]
  simp

/-- Push a nonzero point radially outwards without ever hitting the centre. -/
def puncturedBallExpansion : C(I × PuncturedThreeBall, PuncturedThreeBall) := by
  let coefficient := fun p : I × PuncturedThreeBall =>
    1 - (p.1 : ℝ) + (p.1 : ℝ) * ‖(p.2.1 : BallModel)‖⁻¹
  have hcoeff (p : I × PuncturedThreeBall) : 0 ≤ coefficient p := by
    dsimp [coefficient]
    exact add_nonneg (sub_nonneg.mpr p.1.property.2)
      (mul_nonneg p.1.property.1 (inv_nonneg.mpr (norm_nonneg _)))
  have hnorm (p : I × PuncturedThreeBall) :
      ‖coefficient p • (p.2.1 : BallModel)‖ =
        (1 - (p.1 : ℝ)) * ‖(p.2.1 : BallModel)‖ + (p.1 : ℝ) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hcoeff p)]
    dsimp [coefficient]
    rw [add_mul, mul_assoc, inv_mul_cancel₀ p.2.property.ne', mul_one]
  have hupper (p : I × PuncturedThreeBall) : ‖coefficient p • (p.2.1 : BallModel)‖ ≤ 1 := by
    rw [hnorm]
    have hb : ‖(p.2.1 : BallModel)‖ ≤ 1 := mem_closedBall_zero_iff.mp p.2.1.property
    have ht0 := p.1.property.1
    have ht1 := p.1.property.2
    nlinarith
  have hlower (p : I × PuncturedThreeBall) : 0 < ‖coefficient p • (p.2.1 : BallModel)‖ := by
    rw [hnorm]
    have hb0 := p.2.property
    have hb1 : ‖(p.2.1 : BallModel)‖ ≤ 1 := mem_closedBall_zero_iff.mp p.2.1.property
    have ht0 := p.1.property.1
    have ht1 := p.1.property.2
    nlinarith
  refine ⟨fun p => ⟨⟨coefficient p • (p.2.1 : BallModel),
    mem_closedBall_zero_iff.mpr (hupper p)⟩, hlower p⟩, ?_⟩
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hv : Continuous (fun p : I × PuncturedThreeBall => (p.2.1 : BallModel)) :=
    continuous_subtype_val.comp (continuous_subtype_val.comp continuous_snd)
  have ht : Continuous (fun p : I × PuncturedThreeBall => (p.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hc : Continuous coefficient :=
    (continuous_const.sub ht).add (ht.mul (hv.norm.inv₀ (fun p => p.2.property.ne')))
  exact hc.smul hv

@[simp] theorem puncturedBallExpansion_zero (b : PuncturedThreeBall) :
    puncturedBallExpansion (0, b) = b := by
  apply Subtype.ext
  apply Subtype.ext
  simp [puncturedBallExpansion]

@[simp] theorem puncturedBallExpansion_one (b : PuncturedThreeBall) :
    puncturedBallExpansion (1, b) = sphere2PuncturedInclusion (puncturedBallDirection b) := by
  apply Subtype.ext
  apply Subtype.ext
  simp [puncturedBallExpansion, sphere2PuncturedInclusion, sphere2BoundaryInclusion,
    puncturedBallDirection]

@[simp] theorem puncturedBallExpansion_boundary (t : I) (s : Sphere2) :
    puncturedBallExpansion (t, sphere2PuncturedInclusion s) = sphere2PuncturedInclusion s := by
  apply Subtype.ext
  apply Subtype.ext
  change (1 - (t : ℝ) + (t : ℝ) * ‖(s : BallModel)‖⁻¹) • (s : BallModel) = s
  rw [mem_sphere_zero_iff_norm.mp s.property]
  simp

variable {X : Type*} [TopologicalSpace X]

abbrev PuncturedBallAttachment (i : C(Sphere2, X)) := BoundaryGluing i sphere2PuncturedInclusion

def puncturedAttachmentInl (i : C(Sphere2, X)) : C(X, PuncturedBallAttachment i) :=
  boundaryGluingInl i sphere2PuncturedInclusion

def puncturedAttachmentInr (i : C(Sphere2, X)) : C(PuncturedThreeBall, PuncturedBallAttachment i) :=
  boundaryGluingInr i sphere2PuncturedInclusion

/-- The punctured attached ball retracts onto the retained space. -/
def puncturedAttachmentRetraction (i : C(Sphere2, X)) : C(PuncturedBallAttachment i, X) :=
  boundaryGluingDesc i sphere2PuncturedInclusion (.id X) (i.comp puncturedBallDirection)
    (fun s => by simp)

@[simp] theorem puncturedAttachmentRetraction_inl (i : C(Sphere2, X)) (x : X) :
    puncturedAttachmentRetraction i (puncturedAttachmentInl i x) = x := rfl

/-- A genuine homotopy on the quotient, fixing the retained side pointwise.
Its continuity is descended through the actual quotient times the unit interval. -/
def puncturedAttachmentDeformation (i : C(Sphere2, X)) :
    (ContinuousMap.id (PuncturedBallAttachment i)).Homotopy
      ((puncturedAttachmentInl i).comp (puncturedAttachmentRetraction i)) := by
  let raw : C((X ⊕ PuncturedThreeBall) × I, PuncturedBallAttachment i) :=
    ⟨fun p => p.1.elim (fun x => puncturedAttachmentInl i x)
      (fun b => puncturedAttachmentInr i (puncturedBallExpansion (p.2, b))), by
      apply HatcherLib.continuous_sumProd
      · exact (puncturedAttachmentInl i).continuous.comp continuous_fst
      · exact (puncturedAttachmentInr i).continuous.comp
          (puncturedBallExpansion.continuous.comp (continuous_snd.prodMk continuous_fst))⟩
  have hrel (t : I) : ∀ a b, BoundaryGluingRel i sphere2PuncturedInclusion a b →
      raw (a, t) = raw (b, t) := by
    intro a b h
    cases h with
    | glue s =>
      change puncturedAttachmentInl i (i s) =
        puncturedAttachmentInr i (puncturedBallExpansion (t, sphere2PuncturedInclusion s))
      rw [puncturedBallExpansion_boundary]
      exact boundaryGluing_boundary_eq i sphere2PuncturedInclusion s
  let F : C(I × PuncturedBallAttachment i, PuncturedBallAttachment i) :=
    ⟨fun p => Quot.liftOn p.2 (fun q => raw (q, p.1)) (hrel p.1), by
      apply isQuotientMap_quot_mk.continuous_lift_prod_right
      exact raw.continuous.comp continuous_swap⟩
  refine ⟨F, ?_, ?_⟩
  · intro q
    induction q using Quot.ind with
    | _ z =>
      cases z with
      | inl x => rfl
      | inr b => exact congrArg (puncturedAttachmentInr i) (puncturedBallExpansion_zero b)
  · intro q
    induction q using Quot.ind with
    | _ z =>
      cases z with
      | inl x => rfl
      | inr b =>
        change puncturedAttachmentInr i (puncturedBallExpansion (1, b)) =
          puncturedAttachmentInl i (i (puncturedBallDirection b))
        rw [puncturedBallExpansion_one]
        exact (boundaryGluing_boundary_eq i sphere2PuncturedInclusion (puncturedBallDirection b)).symm

@[simp] theorem puncturedAttachmentDeformation_fixed (i : C(Sphere2, X)) (t : I) (x : X) :
    puncturedAttachmentDeformation i (t, puncturedAttachmentInl i x) = puncturedAttachmentInl i x := rfl

end PoincareConjecture
