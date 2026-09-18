import DifferentialCollar
import SeparationTests
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
The compact cylinder test uses a globally non-injective clipped family,
not an already globally embedded tube. The theorem itself selects a small
uniform width. Additional explicit counterexamples distinguish injectivity
of the zero section and local invertibility from mere continuity.
-/

open Function Set Topology
open PoincareConjecture PoincareClosedCover PoincareSeparationTests PoincareLocalCollar
open scoped ContinuousMap

noncomputable section

namespace PoincareLocalCollarTests

def clippedTime : C(ℝ, ThickInterval) := by
  refine ⟨fun t => ⟨max (-2) (min 2 t), ?_⟩, ?_⟩
  · exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  · apply Continuous.subtype_mk
    exact continuous_const.max (continuous_const.min continuous_id)

theorem clippedTime_eq (t : ℝ) (ht : t ∈ Icc (-2 : ℝ) 2) : (clippedTime t : ℝ) = t := by
  simp [clippedTime, min_eq_right ht.2, max_eq_right ht.1]

def clippedCylinderFamily : C(Sphere2 × ℝ, CompactCylinder) :=
  ⟨fun p => (p.1, clippedTime p.2), continuous_fst.prodMk (clippedTime.continuous.comp continuous_snd)⟩

theorem clipped_zero_injective : Injective (fun s => clippedCylinderFamily (s, 0)) := by
  intro s t h
  exact congrArg Prod.fst h

theorem clipped_family_not_globally_injective : ¬ Injective clippedCylinderFamily := by
  intro h
  have hc : clippedCylinderFamily (sphere2Point, 2) = clippedCylinderFamily (sphere2Point, 3) := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      norm_num [clippedCylinderFamily, clippedTime]
  have hbad := congrArg Prod.snd (h hc)
  norm_num at hbad

theorem clipped_family_has_local_charts : HasLocalOpenChartsAtZero clippedCylinderFamily := by
  intro s
  refine ⟨timeBand 1, timeBand_isOpen 1, zero_mem_timeBand (by norm_num) s, ?_⟩
  let e := bandCoordinates (S := Sphere2) 1 (by norm_num)
  have heq : (timeBand (S := Sphere2) 1).restrict clippedCylinderFamily = cylinderCollar ∘ e.symm := by
    funext p
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      have hp : |p.1.2| < 1 := by simpa only [mem_ball_zero_iff, Real.norm_eq_abs] using p.property.2
      have hp' := abs_lt.mp hp
      change (clippedTime p.1.2 : ℝ) = p.1.2 / 1
      rw [div_one]
      exact clippedTime_eq _ ⟨by linarith [hp'.1], by linarith [hp'.2]⟩
  rw [heq]
  exact cylinderCollar_isOpenEmbedding.comp e.symm.isOpenEmbedding

theorem clipped_family_uniform_collar_exists :
    ∃ r > 0, IsOpenEmbedding (scaledCollar clippedCylinderFamily r) :=
  exists_scaled_open_collar clippedCylinderFamily clipped_zero_injective clipped_family_has_local_charts

/-- Full local-family endpoint on the concrete compact cylinder. The input
map is not globally injective, and neither its radius nor its sides is
supplied to the theorem. The cylinder has boundary and is not a closed
Poincare-manifold example. -/
theorem clipped_family_separates_and_caps :
    ∃ r > 0, IsOpenEmbedding (scaledCollar clippedCylinderFamily r) ∧
      ∃ (U V : Set CompactCylinder) (e : Sphere2 ≃ₜ ↥((U ∪ V)ᶜ)),
        IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧ Disjoint U V ∧
        (∀ s, (e s : CompactCylinder) = clippedCylinderFamily (s, 0)) ∧
        (∀ s (t : CollarTime), (t : ℝ) < 0 → scaledCollar clippedCylinderFamily r (s, t) ∈ U) ∧
        (∀ s (t : CollarTime), 0 < (t : ℝ) → scaledCollar clippedCylinderFamily r (s, t) ∈ V) ∧
        (let e' := e.trans (complementBoundaryHomeomorph U V)
         SimplyConnectedSpace (BallAttachment (sphericalBoundaryLeft Vᶜ Uᶜ e')) ∧
           SimplyConnectedSpace (BallAttachment (sphericalBoundaryRight Vᶜ Uᶜ e'))) :=
  local_family_separates_and_caps clippedCylinderFamily clipped_zero_injective clipped_family_has_local_charts

def foldFamily : C(Unit × ℝ, ℝ) := ⟨fun p => p.2 ^ 2, continuous_snd.pow 2⟩

/-- Even an injective zero section does not prevent arbitrarily near
collisions when the transverse direction folds instead of being locally
invertible. -/
theorem folded_family_no_injective_band (r : ℝ) (hr : 0 < r) :
    ¬ Set.InjOn foldFamily (timeBand r) := by
  intro h
  have hp : ((), r / 2) ∈ timeBand r := by
    refine ⟨mem_univ _, ?_⟩
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_of_pos (by positivity : 0 < r / 2)]
    linarith
  have hn : ((), -(r / 2)) ∈ timeBand r := by
    refine ⟨mem_univ _, ?_⟩
    rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity : 0 < r / 2)]
    linarith
  have he : foldFamily ((), r / 2) = foldFamily ((), -(r / 2)) := by simp [foldFamily]
  have bad := congrArg Prod.snd (h hp hn he)
  linarith

def twoSheetFamily : C(Bool × ℝ, ℝ) := ⟨Prod.snd, continuous_snd⟩

def sheetChart (b : Bool) : {p : Bool × ℝ // p.1 = b} ≃ₜ ℝ where
  toFun p := p.1.2
  invFun t := ⟨(b, t), rfl⟩
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext p.property.symm rfl
  right_inv _ := rfl
  continuous_toFun := continuous_snd.comp continuous_subtype_val
  continuous_invFun := (continuous_const.prodMk continuous_id).subtype_mk _

theorem twoSheetFamily_local_charts : HasLocalOpenChartsAtZero twoSheetFamily := by
  intro b
  refine ⟨{p | p.1 = b}, ?_, rfl, (sheetChart b).isOpenEmbedding⟩
  exact (isOpen_discrete ({b} : Set Bool)).preimage continuous_fst

/-- Local inverses alone do not stop distinct zero-section sheets from
colliding. This finite compact counterexample isolates the zero-section
injectivity assumption. -/
theorem twoSheetFamily_no_injective_band (r : ℝ) (hr : 0 < r) :
    ¬ Set.InjOn twoSheetFamily (timeBand r) := by
  intro h
  have bad := congrArg Prod.fst (h (zero_mem_timeBand hr false) (zero_mem_timeBand hr true) rfl)
  cases bad

def foldedPolynomial : C(ℝ, ℝ) := ⟨fun x => x + x ^ 2, continuous_id.add (continuous_id.pow 2)⟩

theorem polynomial_not_globally_injective : ¬ Injective foldedPolynomial := by
  intro h
  have bad := h (a₁ := 0) (a₂ := -1) (by norm_num [foldedPolynomial])
  norm_num at bad

/-- The real inverse function theorem supplies an actual local chart from
the derivative 1 at zero, even though this polynomial is not globally
injective. This tests the differential bridge without assuming its output. -/
theorem polynomial_has_local_open_chart :
    ∃ U : Set ℝ, IsOpen U ∧ (0 : ℝ) ∈ U ∧ IsOpenEmbedding (U.restrict foldedPolynomial) := by
  have hi := hasStrictFDerivAt_id (𝕜 := ℝ) (0 : ℝ)
  apply local_open_chart_of_strict_coordinate_derivative foldedPolynomial 0
    (Homeomorph.refl ℝ).toOpenPartialHomeomorph (Homeomorph.refl ℝ).toOpenPartialHomeomorph
    (mem_univ _) (mem_univ _) (ContinuousLinearEquiv.refl ℝ ℝ)
  have h := hi.add (hi.mul hi)
  have heq : (id + id * id : ℝ → ℝ) = fun x => x + x * x := rfl
  rw [heq] at h
  simpa [foldedPolynomial, pow_two] using h

end PoincareLocalCollarTests
