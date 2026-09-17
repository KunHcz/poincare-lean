import CappingTheorem
import Mathlib.Topology.Separation.Hausdorff

/-!
# Recovering a compact space from an actual closed cover

The map from the boundary adjunction to the original space is constructed
from the original subtype inclusions. Its injectivity follows from the
actual intersection, and its surjectivity from the cover. Compactness and
Hausdorffness supply inverse continuity. No gluing homeomorphism or
fundamental-group isomorphism is an input.
-/

open Function Set Topology
open scoped ContinuousMap

noncomputable section

namespace PoincareClosedCover

open PoincareConjecture

variable {M : Type*} [TopologicalSpace M]

def intersectionLeft (A B : Set M) : C(↥(A ∩ B), A) :=
  ⟨fun x => ⟨x.1, x.2.1⟩, continuous_subtype_val.subtype_mk _⟩

def intersectionRight (A B : Set M) : C(↥(A ∩ B), B) :=
  ⟨fun x => ⟨x.1, x.2.2⟩, continuous_subtype_val.subtype_mk _⟩

abbrev ClosedCoverAdjunction (A B : Set M) :=
  BoundaryGluing (intersectionLeft A B) (intersectionRight A B)

def closedCoverProjection (A B : Set M) : C(ClosedCoverAdjunction A B, M) :=
  boundaryGluingDesc (intersectionLeft A B) (intersectionRight A B)
    ⟨Subtype.val, continuous_subtype_val⟩ ⟨Subtype.val, continuous_subtype_val⟩
    (fun _ => rfl)

@[simp] theorem closedCoverProjection_left (A B : Set M) (a : A) :
    closedCoverProjection A B (boundaryGluingInl (intersectionLeft A B) (intersectionRight A B) a) = a := rfl

@[simp] theorem closedCoverProjection_right (A B : Set M) (b : B) :
    closedCoverProjection A B (boundaryGluingInr (intersectionLeft A B) (intersectionRight A B) b) = b := rfl

/-- No two different points of the original space are collapsed by the
intersection relation. This holds before closedness or compactness is used. -/
theorem closedCoverProjection_injective (A B : Set M) :
    Injective (closedCoverProjection A B) := by
  intro q r
  induction q using Quot.ind with
  | _ u =>
    induction r using Quot.ind with
    | _ v =>
      intro h
      cases u with
      | inl a =>
        cases v with
        | inl a' =>
          have hh : a = a' := Subtype.ext h
          cases hh
          rfl
        | inr b =>
          change (a : M) = b at h
          let c : ↥(A ∩ B) := ⟨a, a.property, h.symm ▸ b.property⟩
          have hb : intersectionRight A B c = b := Subtype.ext h
          exact (boundaryGluing_boundary_eq (intersectionLeft A B) (intersectionRight A B) c).trans
            (congrArg (boundaryGluingInr (intersectionLeft A B) (intersectionRight A B)) hb)
      | inr b =>
        cases v with
        | inl a =>
          change (b : M) = a at h
          let c : ↥(A ∩ B) := ⟨a, a.property, h ▸ b.property⟩
          have hb : intersectionRight A B c = b := Subtype.ext h.symm
          exact ((boundaryGluing_boundary_eq (intersectionLeft A B) (intersectionRight A B) c).trans
            (congrArg (boundaryGluingInr (intersectionLeft A B) (intersectionRight A B)) hb)).symm
        | inr b' =>
          have hh : b = b' := Subtype.ext h
          cases hh
          rfl

theorem closedCoverProjection_surjective (A B : Set M) (hcover : A ∪ B = univ) :
    Surjective (closedCoverProjection A B) := by
  intro x
  have hx : x ∈ A ∪ B := by rw [hcover]; trivial
  rcases hx with hA | hB
  · exact ⟨boundaryGluingInl (intersectionLeft A B) (intersectionRight A B) ⟨x, hA⟩, rfl⟩
  · exact ⟨boundaryGluingInr (intersectionLeft A B) (intersectionRight A B) ⟨x, hB⟩, rfl⟩

/-- The genuine closed-cover quotient is homeomorphic to the original
compact Hausdorff space, not merely bijective or homotopy equivalent. -/
def closedCoverHomeomorph [CompactSpace M] [T2Space M]
    (A B : Set M) (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = univ) :
    ClosedCoverAdjunction A B ≃ₜ M := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  let f := closedCoverProjection A B
  let e := Equiv.ofBijective f ⟨closedCoverProjection_injective A B,
    closedCoverProjection_surjective A B hcover⟩
  refine { toEquiv := e, continuous_toFun := f.continuous, continuous_invFun := ?_ }
  rw [continuous_iff_isClosed]
  intro s hs
  have he : e.symm ⁻¹' s = e '' s := by
    ext x
    constructor
    · intro hx
      exact ⟨e.symm x, hx, e.apply_symm_apply x⟩
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
  change IsClosed (e.symm ⁻¹' s)
  rw [he]
  exact f.continuous.isClosedMap s hs

/-- Reparametrizing the attaching locus by an actual homeomorphism does
not change the quotient space or its original-side inclusions. -/
def boundaryGluingReparam
    {S T X Y : Type*} [TopologicalSpace S] [TopologicalSpace T]
    [TopologicalSpace X] [TopologicalSpace Y]
    (e : S ≃ₜ T) (i : C(T, X)) (j : C(T, Y)) :
    BoundaryGluing (i.comp ⟨e, e.continuous⟩) (j.comp ⟨e, e.continuous⟩) ≃ₜ BoundaryGluing i j := by
  let F := boundaryGluingDesc (i.comp ⟨e, e.continuous⟩) (j.comp ⟨e, e.continuous⟩)
    (boundaryGluingInl i j) (boundaryGluingInr i j)
    (fun s => boundaryGluing_boundary_eq i j (e s))
  let G := boundaryGluingDesc i j
    (boundaryGluingInl (i.comp ⟨e, e.continuous⟩) (j.comp ⟨e, e.continuous⟩))
    (boundaryGluingInr (i.comp ⟨e, e.continuous⟩) (j.comp ⟨e, e.continuous⟩))
    (fun t => by simpa using boundaryGluing_boundary_eq (i.comp ⟨e, e.continuous⟩) (j.comp ⟨e, e.continuous⟩) (e.symm t))
  refine {
    toFun := F
    invFun := G
    left_inv := ?_
    right_inv := ?_
    continuous_toFun := F.continuous
    continuous_invFun := G.continuous }
  · intro q
    induction q using Quot.ind with
    | _ z => cases z <;> rfl
  · intro q
    induction q using Quot.ind with
    | _ z => cases z <;> rfl

def sphericalBoundaryLeft (A B : Set M) (e : Sphere2 ≃ₜ ↥(A ∩ B)) : C(Sphere2, A) :=
  (intersectionLeft A B).comp ⟨e, e.continuous⟩

def sphericalBoundaryRight (A B : Set M) (e : Sphere2 ≃ₜ ↥(A ∩ B)) : C(Sphere2, B) :=
  (intersectionRight A B).comp ⟨e, e.continuous⟩

def sphericalClosedCoverHomeomorph [CompactSpace M] [T2Space M]
    (A B : Set M) (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = univ)
    (e : Sphere2 ≃ₜ ↥(A ∩ B)) :
    BoundaryGluing (sphericalBoundaryLeft A B e) (sphericalBoundaryRight A B e) ≃ₜ M :=
  (boundaryGluingReparam e (intersectionLeft A B) (intersectionRight A B)).trans
    (closedCoverHomeomorph A B hA hB hcover)

theorem sphericalBoundaryLeft_isClosedEmbedding [T2Space M]
    (A B : Set M) (e : Sphere2 ≃ₜ ↥(A ∩ B)) : IsClosedEmbedding (sphericalBoundaryLeft A B e) := by
  apply (sphericalBoundaryLeft A B e).continuous.isClosedEmbedding
  intro x y h
  apply e.injective
  apply Subtype.ext
  exact congrArg (fun a : A => (a : M)) h

theorem sphericalBoundaryRight_isClosedEmbedding [T2Space M]
    (A B : Set M) (e : Sphere2 ≃ₜ ↥(A ∩ B)) : IsClosedEmbedding (sphericalBoundaryRight A B e) := by
  apply (sphericalBoundaryRight A B e).continuous.isClosedEmbedding
  intro x y h
  apply e.injective
  apply Subtype.ext
  exact congrArg (fun b : B => (b : M)) h

/-- The previous cap theorem now applies to an actual closed cover of the
original space. Neither a cutting/gluing homeomorphism nor normality of
its pieces nor a boundary-embedding certificate is an extra hypothesis. -/
theorem both_closed_cover_caps_simplyConnected
    [CompactSpace M] [T2Space M] [SimplyConnectedSpace M]
    (A B : Set M) (hA : IsClosed A) (hB : IsClosed B) (hcover : A ∪ B = univ)
    (e : Sphere2 ≃ₜ ↥(A ∩ B)) (hpathA : IsPathConnected A) (hpathB : IsPathConnected B) :
    SimplyConnectedSpace (BallAttachment (sphericalBoundaryLeft A B e)) ∧
      SimplyConnectedSpace (BallAttachment (sphericalBoundaryRight A B e)) := by
  letI : CompactSpace A := isCompact_iff_compactSpace.mp hA.isCompact
  letI : CompactSpace B := isCompact_iff_compactSpace.mp hB.isCompact
  letI : PathConnectedSpace A := isPathConnected_iff_pathConnectedSpace.mp hpathA
  letI : PathConnectedSpace B := isPathConnected_iff_pathConnectedSpace.mp hpathB
  let H := sphericalClosedCoverHomeomorph A B hA hB hcover e
  letI : SimplyConnectedSpace (BoundaryGluing (sphericalBoundaryLeft A B e)
      (sphericalBoundaryRight A B e)) := H.toHomotopyEquiv.simplyConnectedSpace
  exact both_capped_pieces_simplyConnected (sphericalBoundaryLeft A B e) (sphericalBoundaryRight A B e)
    (sphericalBoundaryLeft_isClosedEmbedding A B e) (sphericalBoundaryRight_isClosedEmbedding A B e)

end PoincareClosedCover
