import PoincareHamilton.SimplyConnectedCover
import DifferentialGeometry.Geometry.Metric.Sphere.QuotientDescent
import DifferentialGeometry.Topology.Manifold.InverseFunctionTheorem
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Simply connected round quotient data

This file consumes the actual `RoundQuotientData` produced by the Hamilton
formalization. Its group representation need not be faithful, so group
triviality cannot be assumed or inferred directly. Instead we prove that
the supplied projection is a covering and then use simple connectivity of
its base to prove the projection is a diffeomorphism.

In particular, invertibility of the projection derivative is derived from
the supplied smooth local sections and orbit transitivity. It is not an
additional hypothesis about the quotient.
-/

open Function Set Metric DifferentialGeometry.Geometry
open scoped Manifold ContDiff Topology

namespace PoincareHamilton

abbrev Sphere3 := ↥(sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)

private instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by simp⟩

instance sphere3_pathConnectedSpace : PathConnectedSpace Sphere3 := by
  apply isPathConnected_iff_pathConnectedSpace.mp
  apply isPathConnected_sphere (E := EuclideanSpace ℝ (Fin 4)) ?_ 0 zero_le_one
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  norm_num

variable (D : RoundQuotientData (EuclideanSpace ℝ (Fin 4)) 3)

/-- Local sections supply surjectivity of the actual projection. -/
theorem roundQuotient_proj_surjective : Surjective D.proj := by
  intro x
  exact ⟨(D.sectionAt x).toSphere ⟨x, (D.sectionAt x).mem⟩,
    (D.sectionAt x).toSphere_proj ⟨x, (D.sectionAt x).mem⟩⟩

/-- The projection derivative is surjective everywhere, not only at the
preferred lifts selected by the local-section witnesses. -/
theorem roundQuotient_mfderiv_surjective (q : Sphere3) :
    Surjective (mfderiv (𝓡 3) (𝓡 3) D.proj q) := by
  let S := D.sectionAt (D.proj q)
  let r : S.W := ⟨D.proj q, S.mem⟩
  let q₀ := S.toSphere r
  have hq₀ : D.proj q₀ = D.proj q := S.toSphere_proj r
  have hinj₀ := S.dproj_inj D.proj_smooth r
  have hsurj₀ : Surjective (mfderiv (𝓡 3) (𝓡 3) D.proj q₀) :=
    LinearMap.injective_iff_surjective.mp hinj₀
  obtain ⟨γ, hγ⟩ := D.proj_eq_imp q₀ q hq₀
  let φ := sphereDiffeo (n := 3) (D.ρ γ)
  have hφ : MDifferentiableAt (𝓡 3) (𝓡 3) φ q₀ :=
    φ.contMDiff.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hp : MDifferentiableAt (𝓡 3) (𝓡 3) D.proj (φ q₀) :=
    D.proj_smooth.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  have hfun : D.proj ∘ (φ : Sphere3 → Sphere3) = D.proj := by
    funext x
    exact D.proj_smul γ x
  have hc := mfderiv_comp q₀ hp hφ
  rw [hfun] at hc
  have hcomp : Surjective
      ((mfderiv (𝓡 3) (𝓡 3) D.proj (φ q₀)).comp
        (mfderiv (𝓡 3) (𝓡 3) φ q₀)) := by
    rw [← hc]
    exact hsurj₀
  have hsurj : Surjective (mfderiv (𝓡 3) (𝓡 3) D.proj (φ q₀)) :=
    fun v => by
      obtain ⟨w, hw⟩ := hcomp v
      exact ⟨(mfderiv (𝓡 3) (𝓡 3) φ q₀) w, hw⟩
  have hφq : φ q₀ = q := hγ
  rwa [hφq] at hsurj

/-- Smooth local sections and the finite spherical action make the actual
projection a local diffeomorphism by the inverse function theorem. -/
theorem roundQuotient_proj_localDiffeomorph :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ D.proj := by
  rw [isLocalDiffeomorph_iff_isLocalDiffeomorphOn_univ]
  apply DifferentialGeometry.Coordinates.contMDiffOn_isLocalDiffeomorphOn_infty
    isOpen_univ D.proj_smooth.contMDiffOn
  intro q _
  have hdiff : MDifferentiableAt (𝓡 3) (𝓡 3) D.proj q := D.proj_smooth.mdifferentiableAt
    (by decide : (∞ : WithTop ℕ∞) ≠ 0)
  let A : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    mfderiv (𝓡 3) (𝓡 3) D.proj q
  have hder : HasFDerivWithinAt
      (writtenInExtChartAt (𝓡 3) (𝓡 3) q D.proj :
        EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      A univ ((extChartAt (𝓡 3) q) q) := by
    convert! hdiff.hasMFDerivAt.2 using 1
    exact (ModelWithCorners.Boundaryless.range_eq_univ (I := 𝓡 3)).symm
  have hfd : fderiv ℝ (writtenInExtChartAt (𝓡 3) (𝓡 3) q D.proj)
      ((extChartAt (𝓡 3) q) q) = A := hder.hasFDerivAt_of_univ.fderiv
  rw [hfd]
  have hsurj : Surjective A := roundQuotient_mfderiv_surjective D q
  have hinj : Injective A := LinearMap.injective_iff_surjective.mpr hsurj
  exact ⟨ContinuousLinearEquiv.ofBijective A
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj),
    ContinuousLinearEquiv.coe_ofBijective _ _ _⟩

/-- The real projection is a global diffeomorphism when its quotient is
simply connected. No faithful-action assumption is added. -/
noncomputable def roundQuotientDiffeomorph [SimplyConnectedSpace D.Q] :
    Sphere3 ≃ₘ⟮𝓡 3, 𝓡 3⟯ D.Q :=
  compactLocalDiffeomorphToSimplyConnected
    (roundQuotient_proj_localDiffeomorph D) (roundQuotient_proj_surjective D)

end PoincareHamilton
