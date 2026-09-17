import HatcherLib.Ch1.VanKampen
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Topology.TietzeExtension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Topology.CompactOpen

/-!
# Loop generation and continuous cap replacement

The endgame needs simple connectivity of the capped components, not the full
van Kampen free-product isomorphism. The results here isolate two actual
topological constructions: removing simply connected factors from the
loop-generation theorem, and extending boundary maps into genuine Euclidean
closed balls before descending them through the gluing quotient.

The geometric collar and the attachment open-cover identification are not
assumed to follow from these constructions. No connected-sum recognition or
Poincare theorem is asserted here.
-/

open Function Set Topology
open scoped ContinuousMap

noncomputable section

namespace PoincareConjecture

universe u v w

abbrev Sphere2 := ↥(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)

theorem simplyConnected_of_fundamentalGroup_subsingleton
    {M : Type*} [TopologicalSpace M] [PathConnectedSpace M] (x : M)
    [Subsingleton (FundamentalGroup M x)] : SimplyConnectedSpace M := by
  apply simply_connected_iff_loops_nullhomotopic.mpr
  refine ⟨inferInstance, ?_⟩
  intro y γ
  letI : Subsingleton (FundamentalGroup M y) :=
    (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected x y).surjective.subsingleton
  have hγ : (FundamentalGroup.fromPath ⟦γ⟧ : FundamentalGroup M y) =
      FundamentalGroup.fromPath ⟦Path.refl y⟧ := Subsingleton.elim _ _
  exact Quotient.eq.mp (congrArg FundamentalGroup.toPath hγ)


/-- If all cover members except one are simply connected, that member
already generates the whole ambient fundamental group. This uses the
proved subdivision/surjectivity part of van Kampen, not its unproved kernel
calculation in the reference project. -/
theorem coverInclusion_surjective_of_other_members_simplyConnected
    {M : Type u} [TopologicalSpace M] {x : M} {ι : Type v}
    (cover : HatcherLib.PathConnectedOpenCover x ι) (i₀ : ι)
    (hother : ∀ i, i ≠ i₀ → IsSimplyConnected (cover.carrier i)) :
    Surjective (FundamentalGroup.map (HatcherLib.coverInclusion cover i₀)
      ⟨x, cover.base_mem i₀⟩) := by
  let F := FundamentalGroup.map (HatcherLib.coverInclusion cover i₀)
    ⟨x, cover.base_mem i₀⟩
  intro a
  obtain ⟨z, rfl⟩ := HatcherLib.vanKampenMap_surjective cover a
  change ∃ y, F y = HatcherLib.vanKampenMap cover z
  induction z using Monoid.CoprodI.induction_on with
  | one => exact ⟨1, F.map_one.trans (HatcherLib.vanKampenMap cover).map_one.symm⟩
  | of i g =>
      by_cases hi : i = i₀
      · subst i
        refine ⟨g, ?_⟩
        simp only [HatcherLib.vanKampenMap, HatcherLib.freeProductLift, Monoid.CoprodI.lift_of]
        rfl
      · letI : SimplyConnectedSpace (cover.carrier i) := hother i hi
        have hg : g = 1 := Subsingleton.elim _ _
        refine ⟨1, ?_⟩
        rw [hg, Monoid.CoprodI.of.map_one]
        exact F.map_one.trans (HatcherLib.vanKampenMap cover).map_one.symm
  | mul z z' hz hz' =>
      obtain ⟨g, hg⟩ := hz
      obtain ⟨g', hg'⟩ := hz'
      exact ⟨g * g', (F.map_mul g g').trans
        ((congrArg₂ (fun a b => a * b) hg hg').trans
          ((HatcherLib.vanKampenMap cover).map_mul z z').symm)⟩

/-- A two-open-set cap-filling criterion: adjoining the simply connected
open cap creates no new fundamental-group generators. -/
theorem inclusion_surjective_of_simplyConnected_cap
    {M : Type u} [TopologicalSpace M] {U V : Set M}
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hUpc : IsPathConnected U) (hVsc : IsSimplyConnected V)
    (hinter : IsPathConnected (U ∩ V)) (x : M) (hx : x ∈ U ∩ V) :
    Surjective (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(U, M))
      ⟨x, hx.1⟩) := by
  let cover : HatcherLib.PathConnectedOpenCover x Bool := {
    carrier := fun i => if i then V else U
    isOpen := by intro i; cases i <;> assumption
    cover := by
      intro y _
      have hy : y ∈ U ∪ V := hcover.symm ▸ mem_univ y
      rcases hy with hy | hy
      · exact mem_iUnion.mpr ⟨false, hy⟩
      · exact mem_iUnion.mpr ⟨true, hy⟩
    base_mem := by intro i; cases i; exact hx.1; exact hx.2
    pathConnected := by intro i; cases i; exact hUpc; exact hVsc.isPathConnected
    interPathConnected := by
      intro i j
      cases i <;> cases j
      · simpa using hUpc
      · exact hinter
      · simpa [inter_comm] using hinter
      · simpa using hVsc.isPathConnected }
  exact coverInclusion_surjective_of_other_members_simplyConnected cover false (by
    intro i hi
    cases i
    · exact False.elim (hi rfl)
    · exact hVsc)

section Gluing

variable {C : Type u} {X : Type v} {Y : Type w}
  [TopologicalSpace X] [TopologicalSpace Y]

/-- The generating relation identifies exactly the prescribed boundary pairs. -/
inductive BoundaryGluingRel (i : C → X) (j : C → Y) : X ⊕ Y → X ⊕ Y → Prop
  | glue (c : C) : BoundaryGluingRel i j (.inl (i c)) (.inr (j c))

/-- Actual topological adjunction quotient, not a structure postulating its
homotopy properties. -/
abbrev BoundaryGluing (i : C → X) (j : C → Y) := Quot (BoundaryGluingRel i j)

def boundaryGluingInl (i : C → X) (j : C → Y) : C(X, BoundaryGluing i j) :=
  ⟨fun x => Quot.mk _ (.inl x), continuous_quot_mk.comp continuous_inl⟩

def boundaryGluingInr (i : C → X) (j : C → Y) : C(Y, BoundaryGluing i j) :=
  ⟨fun y => Quot.mk _ (.inr y), continuous_quot_mk.comp continuous_inr⟩

theorem boundaryGluing_boundary_eq (i : C → X) (j : C → Y) (c : C) :
    boundaryGluingInl i j (i c) = boundaryGluingInr i j (j c) :=
  Quot.sound (BoundaryGluingRel.glue c)

/-- Continuous maps agreeing on the identified boundary descend through the
actual quotient topology. -/
def boundaryGluingDesc {Z : Type*} [TopologicalSpace Z]
    (i : C → X) (j : C → Y) (f : C(X, Z)) (g : C(Y, Z))
    (h : ∀ c, f (i c) = g (j c)) : C(BoundaryGluing i j, Z) := by
  let heq : ∀ a b, BoundaryGluingRel i j a b → Sum.elim f g a = Sum.elim f g b := by
    intro a b hab
    cases hab with
    | glue c => exact h c
  exact ⟨Quot.lift (Sum.elim f g) heq, continuous_quot_lift heq (f.continuous.sumElim g.continuous)⟩

@[simp] theorem boundaryGluingDesc_inl {Z : Type*} [TopologicalSpace Z]
    (i : C → X) (j : C → Y) (f : C(X, Z)) (g : C(Y, Z))
    (h : ∀ c, f (i c) = g (j c)) (x : X) :
    boundaryGluingDesc i j f g h (boundaryGluingInl i j x) = f x := rfl

/-- Replacing a normal attached piece by an extension-space cap admits a
continuous map which is exactly the identity on the retained piece. The
extension is derived from the closed boundary embedding by Tietze. -/
theorem exists_boundaryGluing_capReplacement
    {B : Type*} [TopologicalSpace C] [TopologicalSpace B]
    [TietzeExtension.{w} B] [NormalSpace Y]
    (i : C → X) (j : C → Y) (hj : IsClosedEmbedding j) (k : C(C, B)) :
    ∃ R : C(BoundaryGluing i j, BoundaryGluing i k),
      R.comp (boundaryGluingInl i j) = boundaryGluingInl i k := by
  obtain ⟨e, he⟩ := k.exists_extension hj
  let R := boundaryGluingDesc i j (boundaryGluingInl i k)
    ((boundaryGluingInr i k).comp e) (by
      intro c
      change boundaryGluingInl i k (i c) = boundaryGluingInr i k (e (j c))
      have hec : e (j c) = k c := DFunLike.congr_fun he c
      rw [hec]
      exact boundaryGluing_boundary_eq i k c)
  exact ⟨R, by ext x; rfl⟩

end Gluing

section ClosedBall

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The standard radial retraction onto the actual closed unit ball. -/
noncomputable def closedUnitBallRetraction : E → ↥(Metric.closedBall (0 : E) 1) :=
  fun x => ⟨(max 1 ‖x‖)⁻¹ • x, by
    have hpos : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    simp only [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hpos), ← div_eq_inv_mul]
    exact (div_le_one hpos).mpr (le_max_right _ _)⟩

theorem continuous_closedUnitBallRetraction : Continuous (closedUnitBallRetraction (E := E)) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.max continuous_norm).inv₀
    (fun x => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left 1 ‖x‖)))).smul continuous_id

theorem closedUnitBallRetraction_coe (x : Metric.closedBall (0 : E) 1) :
    closedUnitBallRetraction (x : E) = x := by
  have hx : ‖(x : E)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using x.property
  apply Subtype.ext
  simp [closedUnitBallRetraction, max_eq_left hx]

/-- Genuine Euclidean closed balls satisfy the extension property used in
cap replacement, via the displayed radial retraction. -/
theorem euclidean_closedUnitBall_tietze (n : ℕ) :
    TietzeExtension.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) := by
  letI : TietzeExtension.{u} (EuclideanSpace ℝ (Fin n)) :=
    TietzeExtension.of_homeo (EuclideanSpace.equiv (Fin n) ℝ).toHomeomorph
  apply TietzeExtension.of_retract
    (⟨Subtype.val, continuous_subtype_val⟩ :
      C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1, EuclideanSpace ℝ (Fin n)))
    ⟨closedUnitBallRetraction, continuous_closedUnitBallRetraction⟩
  apply ContinuousMap.ext
  intro x
  exact closedUnitBallRetraction_coe x

end ClosedBall

section FundamentalGroupDescent

/-- A retained piece generates the capped space's loops, and its map into
the capped space factors through a simply connected original space. Then
the capped space is simply connected. Surjectivity here concerns the actual
fundamental-group map, not just surjectivity of the continuous map. -/
theorem simplyConnected_of_loop_generating_factorization
    {X M Q : Type*} [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace Q]
    [SimplyConnectedSpace M] [PathConnectedSpace Q]
    (a : C(X, M)) (j : C(X, Q)) (R : C(M, Q)) (h : R.comp a = j)
    (x : X) (hsurj : Surjective (FundamentalGroup.map j x)) : SimplyConnectedSpace Q := by
  subst j
  have hone (g : FundamentalGroup Q ((R.comp a) x)) : g = 1 := by
    obtain ⟨u, rfl⟩ := hsurj g
    have hcomp : FundamentalGroup.map (R.comp a) x u =
        FundamentalGroup.map R (a x) (FundamentalGroup.map a x u) := by
      exact Path.Homotopic.Quotient.map_comp
    rw [hcomp]
    have hu : FundamentalGroup.map a x u = 1 := Subsingleton.elim _ _
    rw [hu]
    exact (FundamentalGroup.map R (a x)).map_one
  letI : Subsingleton (FundamentalGroup Q ((R.comp a) x)) :=
    ⟨fun g h => (hone g).trans (hone h).symm⟩
  exact simplyConnected_of_fundamentalGroup_subsingleton ((R.comp a) x)

end FundamentalGroupDescent

section BallAttachment

abbrev ThreeBall := ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) 1)
abbrev OpenThreeBall := ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) 1)

/-- The actual sphere inclusion into the boundary of the closed three-ball. -/
def sphere2BoundaryInclusion : C(Sphere2, ThreeBall) :=
  ⟨fun s => ⟨s.val, Metric.sphere_subset_closedBall s.property⟩,
    continuous_subtype_val.subtype_mk _⟩

variable {X : Type u} [TopologicalSpace X]

/-- Attach the standard three-ball by identifying its boundary with the
supplied map of the standard two-sphere. -/
abbrev BallAttachment (i : C(Sphere2, X)) := BoundaryGluing i sphere2BoundaryInclusion

def ballAttachmentInl (i : C(Sphere2, X)) : C(X, BallAttachment i) :=
  boundaryGluingInl i sphere2BoundaryInclusion

def ballAttachmentInr (i : C(Sphere2, X)) : C(ThreeBall, BallAttachment i) :=
  boundaryGluingInr i sphere2BoundaryInclusion

/-- The radial coordinate extends over the quotient by taking value one on
the retained piece. This produces an actual open cover without assuming a
collar or a manifold structure on the adjunction quotient. -/
def ballAttachmentRadius (i : C(Sphere2, X)) : C(BallAttachment i, ℝ) :=
  boundaryGluingDesc i sphere2BoundaryInclusion (.const X 1)
    ⟨fun b => ‖(b : EuclideanSpace ℝ (Fin 3))‖,
      continuous_norm.comp continuous_subtype_val⟩ (by
      intro s
      exact (show ‖(s : EuclideanSpace ℝ (Fin 3))‖ = 1 by
        simpa only [Metric.mem_sphere, dist_zero_right] using s.property).symm)

@[simp] theorem ballAttachmentRadius_inl (i : C(Sphere2, X)) (x : X) :
    ballAttachmentRadius i (ballAttachmentInl i x) = 1 := rfl

@[simp] theorem ballAttachmentRadius_inr (i : C(Sphere2, X)) (b : ThreeBall) :
    ballAttachmentRadius i (ballAttachmentInr i b) = ‖(b : EuclideanSpace ℝ (Fin 3))‖ := rfl

theorem ballAttachmentRadius_bounds (i : C(Sphere2, X)) (q : BallAttachment i) :
    ballAttachmentRadius i q ∈ Icc (0 : ℝ) 1 := by
  induction q using Quot.ind with
  | _ z =>
      rcases z with x | b
      · exact ⟨zero_le_one, le_rfl⟩
      · change 0 ≤ ‖(b : EuclideanSpace ℝ (Fin 3))‖ ∧ ‖(b : EuclideanSpace ℝ (Fin 3))‖ ≤ 1
        exact ⟨norm_nonneg _, by
          simpa only [Metric.mem_closedBall, dist_zero_right] using b.property⟩

def ballAttachmentRetainedOpen (i : C(Sphere2, X)) : Set (BallAttachment i) :=
  {q | 0 < ballAttachmentRadius i q}

def ballAttachmentCapOpen (i : C(Sphere2, X)) : Set (BallAttachment i) :=
  {q | ballAttachmentRadius i q < 1}

theorem ballAttachmentRetainedOpen_isOpen (i : C(Sphere2, X)) :
    IsOpen (ballAttachmentRetainedOpen i) :=
  isOpen_lt continuous_const (ballAttachmentRadius i).continuous

theorem ballAttachmentCapOpen_isOpen (i : C(Sphere2, X)) :
    IsOpen (ballAttachmentCapOpen i) :=
  isOpen_lt (ballAttachmentRadius i).continuous continuous_const

theorem ballAttachment_opens_cover (i : C(Sphere2, X)) :
    ballAttachmentRetainedOpen i ∪ ballAttachmentCapOpen i = univ := by
  apply eq_univ_of_forall
  intro q
  change 0 < ballAttachmentRadius i q ∨ ballAttachmentRadius i q < 1
  by_cases h : 0 < ballAttachmentRadius i q
  · exact Or.inl h
  · exact Or.inr (lt_of_le_of_lt (le_of_not_gt h) zero_lt_one)

/-- A closed embedded attaching sphere supplies continuous ball coordinates
on the retained piece by Tietze extension. These descend to a map which is
the identity on the whole attached ball. -/
theorem exists_ballAttachment_coordinates [NormalSpace X]
    (i : C(Sphere2, X)) (hi : IsClosedEmbedding i) :
    ∃ c : C(BallAttachment i, ThreeBall), c.comp (ballAttachmentInr i) = .id ThreeBall := by
  letI : TietzeExtension.{u} ThreeBall := euclidean_closedUnitBall_tietze 3
  obtain ⟨e, he⟩ := sphere2BoundaryInclusion.exists_extension hi
  let c := boundaryGluingDesc i sphere2BoundaryInclusion e (.id ThreeBall) (by
    intro s
    exact DFunLike.congr_fun he s)
  exact ⟨c, by apply ContinuousMap.ext; intro b; rfl⟩

/-- The cap is an actual open ball, not a hypothesized simply connected
subspace. Its coordinates come from a continuous extension across the
retained side and are inverse to the original ball inclusion. -/
noncomputable def ballAttachmentCapHomeomorph [NormalSpace X]
    (i : C(Sphere2, X)) (hi : IsClosedEmbedding i) :
    ballAttachmentCapOpen i ≃ₜ OpenThreeBall := by
  let c := Classical.choose (exists_ballAttachment_coordinates i hi)
  have hc := Classical.choose_spec (exists_ballAttachment_coordinates i hi)
  have hcb (b : ThreeBall) : c (ballAttachmentInr i b) = b := DFunLike.congr_fun hc b
  have hcap (q : BallAttachment i) (hq : q ∈ ballAttachmentCapOpen i) :
      ‖(c q : EuclideanSpace ℝ (Fin 3))‖ < 1 ∧ ballAttachmentInr i (c q) = q := by
    induction q using Quot.ind with
    | _ z =>
        rcases z with x | b
        · exact False.elim (lt_irrefl (1 : ℝ) hq)
        · change ‖(c (ballAttachmentInr i b) : EuclideanSpace ℝ (Fin 3))‖ < 1 ∧
            ballAttachmentInr i (c (ballAttachmentInr i b)) = ballAttachmentInr i b
          rw [hcb]
          exact ⟨hq, rfl⟩
  refine {
    toFun := fun q => ⟨(c q : EuclideanSpace ℝ (Fin 3)), by
      simpa only [Metric.mem_ball, dist_zero_right] using (hcap q q.property).1⟩
    invFun := fun b => ⟨ballAttachmentInr i ⟨b.val, Metric.ball_subset_closedBall b.property⟩,
      by exact mem_ball_zero_iff.mp b.property⟩
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := ?_
    continuous_invFun := ?_ }
  · intro q
    apply Subtype.ext
    exact (hcap q q.property).2
  · intro b
    apply Subtype.ext
    change (c (ballAttachmentInr i ⟨b.val, Metric.ball_subset_closedBall b.property⟩) :
      EuclideanSpace ℝ (Fin 3)) = b.val
    exact congrArg (fun z : ThreeBall => (z : EuclideanSpace ℝ (Fin 3)))
      (hcb ⟨b.val, Metric.ball_subset_closedBall b.property⟩)
  · exact (continuous_subtype_val.comp (c.continuous.comp continuous_subtype_val)).subtype_mk _
  · exact ((ballAttachmentInr i).continuous.comp
      (continuous_subtype_val.subtype_mk _)).subtype_mk _

end BallAttachment

end PoincareConjecture
