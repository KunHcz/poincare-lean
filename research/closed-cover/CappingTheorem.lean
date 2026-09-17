import ConnectedCap
import HomotopicFactorization

/-!
# Simple connectivity survives replacing the complementary side by a ball

The original space is the genuine boundary adjunction of the retained side
and a normal complementary side. The new space is the genuine attachment of
the standard closed three-ball. The proof constructs the cap-replacement
map, the two-open-set cover, the cap/intersection topology, and the homotopy
needed to transfer loop triviality. No fundamental-group isomorphism,
loop-generation property, retraction or collar is assumed as an input.

Realizing a cut manifold as this adjunction and obtaining its boundary
embeddings is a separate geometric input. This theorem is not a construction
of Ricci surgery and does not identify a three-manifold with the three-sphere.
-/

open Function Set Topology
open scoped ContinuousMap unitInterval

noncomputable section

namespace PoincareConjecture

universe u v

variable {X : Type u} [TopologicalSpace X]

/-- The actual inclusion of the punctured retained neighbourhood is
homotopic, in the full attachment, to its retraction through the retained
piece. The homotopy may move its basepoint; no based retraction is assumed. -/
def retainedOpenDeformation (i : C(Sphere2, X)) :
    (⟨Subtype.val, continuous_subtype_val⟩ : C(ballAttachmentRetainedOpen i, BallAttachment i)).Homotopy
      ((ballAttachmentInl i).comp
        ((puncturedAttachmentRetraction i).comp (puncturedAttachmentHomeomorph i).symm)) := by
  let e := puncturedAttachmentHomeomorph i
  let H := puncturedAttachmentDeformation i
  refine { toFun := fun p => puncturedAttachmentFill i (H (p.1, e.symm p.2))
           continuous_toFun := ?_
           map_zero_left := ?_
           map_one_left := ?_ }
  · exact (puncturedAttachmentFill i).continuous.comp
      (H.continuous.comp (continuous_fst.prodMk (e.symm.continuous.comp continuous_snd)))
  · intro q
    rw [H.apply_zero]
    exact congrArg Subtype.val (e.apply_symm_apply q)
  · intro q
    rw [H.apply_one]
    rfl

/-- If the retained side is simply connected, attaching a genuine closed
three-ball along a closed embedded two-sphere yields a simply connected
space. The open-cap and punctured-neighbourhood conditions are proved. -/
theorem ballAttachment_simplyConnected_of_retained
    [NormalSpace X] [SimplyConnectedSpace X]
    (i : C(Sphere2, X)) (hi : IsClosedEmbedding i) : SimplyConnectedSpace (BallAttachment i) := by
  letI := ballAttachment_pathConnected i hi
  obtain ⟨q, hq⟩ := (ballAttachment_overlap_pathConnected i).nonempty
  let U := ballAttachmentRetainedOpen i
  let a : C(U, X) := (puncturedAttachmentRetraction i).comp
    (puncturedAttachmentHomeomorph i).symm
  let j : C(U, BallAttachment i) := ⟨Subtype.val, continuous_subtype_val⟩
  have hsurj := inclusion_surjective_of_simplyConnected_cap
    (ballAttachmentRetainedOpen_isOpen i) (ballAttachmentCapOpen_isOpen i)
    (ballAttachment_opens_cover i) (ballAttachmentRetainedOpen_pathConnected i)
    (ballAttachmentCapOpen_simplyConnected i hi) (ballAttachment_overlap_pathConnected i) q hq
  exact simplyConnected_of_loop_generating_homotopic_factorization
    a j (ballAttachmentInl i) (retainedOpenDeformation i) ⟨q, hq.1⟩ hsurj

/-- Replacing the complementary normal space by a standard three-ball
preserves simple connectivity of the full boundary gluing. This applies
even when the retained piece is not known simply connected in advance.

Both spaces in the statement are explicit topological quotients of disjoint
unions. The attaching sphere and the ball are the usual Euclidean ones. -/
theorem capped_piece_simplyConnected
    [NormalSpace X] [PathConnectedSpace X]
    {Y : Type v} [TopologicalSpace Y] [NormalSpace Y]
    (i : C(Sphere2, X)) (j : C(Sphere2, Y))
    (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j)
    [SimplyConnectedSpace (BoundaryGluing i j)] : SimplyConnectedSpace (BallAttachment i) := by
  letI : TietzeExtension.{v} ThreeBall := euclidean_closedUnitBall_tietze 3
  obtain ⟨R, hR⟩ := exists_boundaryGluing_capReplacement
    (i := (i : Sphere2 → X)) (j := (j : Sphere2 → Y)) hj sphere2BoundaryInclusion
  letI := ballAttachment_pathConnected i hi
  obtain ⟨q, hq⟩ := (ballAttachment_overlap_pathConnected i).nonempty
  let U := ballAttachmentRetainedOpen i
  let r : C(U, X) := (puncturedAttachmentRetraction i).comp
    (puncturedAttachmentHomeomorph i).symm
  let a : C(U, BoundaryGluing i j) := (boundaryGluingInl i j).comp r
  let inc : C(U, BallAttachment i) := ⟨Subtype.val, continuous_subtype_val⟩
  have hfactor : (ballAttachmentInl i).comp r = R.comp a := by
    ext p
    exact (DFunLike.congr_fun hR (r p)).symm
  have H : inc.Homotopy (R.comp a) := by
    rw [← hfactor]
    exact retainedOpenDeformation i
  have hsurj := inclusion_surjective_of_simplyConnected_cap
    (ballAttachmentRetainedOpen_isOpen i) (ballAttachmentCapOpen_isOpen i)
    (ballAttachment_opens_cover i) (ballAttachmentRetainedOpen_pathConnected i)
    (ballAttachmentCapOpen_simplyConnected i hi) (ballAttachment_overlap_pathConnected i) q hq
  exact simplyConnected_of_loop_generating_homotopic_factorization a inc R H ⟨q, hq.1⟩ hsurj

/-- A geometric cutting identification may be supplied as an actual
homeomorphism. The homeomorphism is not replaced by an abstract assertion
about fundamental groups or a conclusion-equivalent certificate. -/
theorem capped_piece_simplyConnected_of_homeomorph
    [NormalSpace X] [PathConnectedSpace X]
    {Y : Type v} [TopologicalSpace Y] [NormalSpace Y]
    {M : Type*} [TopologicalSpace M] [SimplyConnectedSpace M]
    (i : C(Sphere2, X)) (j : C(Sphere2, Y))
    (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j)
    (e : M ≃ₜ BoundaryGluing i j) : SimplyConnectedSpace (BallAttachment i) := by
  letI : SimplyConnectedSpace (BoundaryGluing i j) := e.symm.toHomotopyEquiv.simplyConnectedSpace
  exact capped_piece_simplyConnected i j hi hj

/-- Swapping the two sides is a homeomorphism of the actual boundary
adjunction spaces, not a symmetry assumption on their fundamental groups. -/
def boundaryGluingSwap
    {Y : Type v} [TopologicalSpace Y]
    (i : C(Sphere2, X)) (j : C(Sphere2, Y)) : BoundaryGluing i j ≃ₜ BoundaryGluing j i := by
  let F := boundaryGluingDesc i j (boundaryGluingInr j i) (boundaryGluingInl j i)
    (fun s => (boundaryGluing_boundary_eq j i s).symm)
  let G := boundaryGluingDesc j i (boundaryGluingInr i j) (boundaryGluingInl i j)
    (fun s => (boundaryGluing_boundary_eq i j s).symm)
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

/-- For a simply connected glued space with two normal path-connected
pieces and a closed embedded two-sphere on each side, capping both pieces
with genuine three-balls produces two simply connected spaces. -/
theorem both_capped_pieces_simplyConnected
    [NormalSpace X] [PathConnectedSpace X]
    {Y : Type v} [TopologicalSpace Y] [NormalSpace Y] [PathConnectedSpace Y]
    (i : C(Sphere2, X)) (j : C(Sphere2, Y))
    (hi : IsClosedEmbedding i) (hj : IsClosedEmbedding j)
    [SimplyConnectedSpace (BoundaryGluing i j)] :
    SimplyConnectedSpace (BallAttachment i) ∧ SimplyConnectedSpace (BallAttachment j) := by
  refine ⟨capped_piece_simplyConnected i j hi hj, ?_⟩
  letI : SimplyConnectedSpace (BoundaryGluing j i) :=
    (boundaryGluingSwap i j).symm.toHomotopyEquiv.simplyConnectedSpace
  exact capped_piece_simplyConnected j i hj hi

end PoincareConjecture
