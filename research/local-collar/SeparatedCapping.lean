import SeparationComponents

/-!
# Capping the two sides of a collared sphere

The theorem constructs the complementary open regions and their boundary
parametrization from a given open collar. It does not assume separation or
path connectivity of the complement's pieces, unlike the preceding version
of the topology interface. Collar existence remains an explicit geometric
input; general Ricci surgery and the Poincare endpoint are not proved here.
-/

open Function Set Topology
open scoped ContinuousMap

noncomputable section

namespace PoincareSeparation

open PoincareClosedCover PoincareConjecture

variable {S M : Type*} [TopologicalSpace S] [CompactSpace S]
  [TopologicalSpace M] [T2Space M]

/-- The original central slice parametrizes its actual image homeomorphically. -/
def centralSliceHomeomorph (c : S × CollarTime → M) (hc : IsOpenEmbedding c) :
    S ≃ₜ centralSphere c := by
  have hinj : Injective (fun s => c (s, collarCentre)) := by
    intro a b h
    exact congrArg Prod.fst (hc.injective h)
  let e := Equiv.ofInjective (fun s => c (s, collarCentre)) hinj
  have hcont : Continuous e := by
    apply Continuous.subtype_mk
    exact hc.continuous.comp (continuous_id.prodMk continuous_const)
  exact e.toHomeomorphOfContinuousClosed hcont hcont.isClosedMap

@[simp] theorem centralSliceHomeomorph_coe (c : S × CollarTime → M) (hc : IsOpenEmbedding c) (s : S) :
    ((centralSliceHomeomorph c hc s : centralSphere c) : M) = c (s, collarCentre) := rfl

/-- Complete topological conclusion for a supplied sphere collar: the two
open regions, their path connectivity, their exact spherical boundary and
the simple connectivity of both genuine capped closed sides are obtained
inside the proof. No separation data is supplied by the caller. -/
theorem sphere_collar_separates_and_caps
    [CompactSpace M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (c : Sphere2 × CollarTime → M) (hc : IsOpenEmbedding c) :
    ∃ (U V : Set M) (e : Sphere2 ≃ₜ ↥((U ∪ V)ᶜ)),
      IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧ Disjoint U V ∧
      (∀ s, (e s : M) = c (s, collarCentre)) ∧
      (∀ s (t : CollarTime), (t : ℝ) < 0 → c (s, t) ∈ U) ∧
      (∀ s (t : CollarTime), 0 < (t : ℝ) → c (s, t) ∈ V) ∧
      (let e' := e.trans (complementBoundaryHomeomorph U V)
       SimplyConnectedSpace (BallAttachment (sphericalBoundaryLeft Vᶜ Uᶜ e')) ∧
       SimplyConnectedSpace (BallAttachment (sphericalBoundaryRight Vᶜ Uᶜ e'))) := by
  obtain ⟨U, V, hU, hV, hpathU, hpathV, hd, hcover, hn, hp⟩ :=
    exists_pathConnected_separation_of_collar c hc
  have heq : centralSphere c = (U ∪ V)ᶜ := by rw [hcover, compl_compl]
  let e := (centralSliceHomeomorph c hc).trans (Homeomorph.setCongr heq)
  have hcentre (s : Sphere2) : (e s : M) = c (s, collarCentre) := rfl
  refine ⟨U, V, e, hU, hV, hpathU, hpathV, hd, hcentre, hn, hp, ?_⟩
  exact caps_of_collared_separation_simplyConnected U V hU hV hd hpathU hpathV
    e c hc (fun s => (hcentre s).symm) hn hp

end PoincareSeparation
