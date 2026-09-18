import ClosedCover
import Mathlib.Topology.Homotopy.Basic

/-!
# Actual complementary sides with a supplied two-sided collar

A pair of disjoint open regions gives a closed cover by their complementary
closed sides. A genuine open-embedded collar supplies paths from the cutting
sphere into each region, proving path connectivity of those closed sides.
The preceding closed-cover construction then supplies the gluing
homeomorphism and the two capped simple-connectivity conclusions.

Existence of the separating sphere and of its collar is not asserted here.
-/

open Function Set Topology
open scoped ContinuousMap unitInterval

noncomputable section

namespace PoincareClosedCover

open PoincareConjecture

variable {M : Type*} [TopologicalSpace M]

/-- Path connectivity of an open region extends to a larger side when
actual paths reach the region from all added boundary points. Mere closure
membership is not used as a substitute for such paths. -/
theorem isPathConnected_of_boundary_access
    {A U : Set M} (hU : IsPathConnected U) (hUA : U ⊆ A)
    (haccess : ∀ x ∈ A, x ∉ U → ∃ y ∈ U, JoinedIn A x y) : IsPathConnected A := by
  have reach : ∀ x ∈ A, ∃ y ∈ U, JoinedIn A x y := by
    intro x hx
    by_cases hxu : x ∈ U
    · exact ⟨x, hxu, ⟨Path.refl x, fun _ => hx⟩⟩
    · exact haccess x hx hxu
  apply isPathConnected_iff.mpr
  refine ⟨hU.nonempty.mono hUA, ?_⟩
  intro x hx y hy
  obtain ⟨u, hu, hxu⟩ := reach x hx
  obtain ⟨v, hv, hyv⟩ := reach y hy
  exact (hxu.trans ((hU.joinedIn u hu v hv).mono hUA)).trans hyv.symm

/-- A continuous half-collar produces, rather than assumes, the required
boundary-access paths. -/
theorem complementSide_pathConnected_of_halfCollar
    (U V : Set M) (hdisjoint : Disjoint U V) (hU : IsPathConnected U)
    (e : Sphere2 → M)
    (hboundary : ∀ x, x ∉ U → x ∉ V → ∃ s, e s = x)
    (c : C(Sphere2 × I, M)) (hzero : ∀ s, c (s, 0) = e s)
    (hpositive : ∀ s (t : I), 0 < (t : ℝ) → c (s, t) ∈ U) : IsPathConnected Vᶜ := by
  have hUV : U ⊆ Vᶜ := fun x hx => fun hv => Set.disjoint_left.mp hdisjoint hx hv
  apply isPathConnected_of_boundary_access hU hUV
  intro x hx hxU
  obtain ⟨s, hs⟩ := hboundary x hxU hx
  have hend : c (s, 1) ∈ U := hpositive s 1 (by norm_num)
  let p : Path x (c (s, 1)) := {
    toFun := fun t => c (s, t)
    continuous_toFun := c.continuous.comp (continuous_const.prodMk continuous_id)
    source' := (hzero s).trans hs
    target' := rfl }
  refine ⟨c (s, 1), hend, p, ?_⟩
  intro t
  by_cases ht : t = 0
  · subst t
    change c (s, 0) ∈ Vᶜ
    rw [hzero, hs]
    exact hx
  · have htpos : 0 < (t : ℝ) := by
      have hn : (t : ℝ) ≠ 0 := by
        intro hh
        apply ht
        exact Subtype.ext hh
      exact lt_of_le_of_ne t.property.1 (Ne.symm hn)
    exact hUV (hpositive s t htpos)

abbrev CollarTime := ↥(Ioo (-1 : ℝ) 1)

def collarCentre : CollarTime := ⟨0, by norm_num⟩

def positiveHalfTime : C(I, CollarTime) := by
  refine ⟨fun t => ⟨(t : ℝ) / 2, ?_⟩, ?_⟩
  · constructor <;> nlinarith [t.property.1, t.property.2]
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.div_const 2

def negativeHalfTime : C(I, CollarTime) := by
  refine ⟨fun t => ⟨-(t : ℝ) / 2, ?_⟩, ?_⟩
  · constructor <;> nlinarith [t.property.1, t.property.2]
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.neg.div_const 2

@[simp] theorem positiveHalfTime_zero : positiveHalfTime 0 = collarCentre := by
  apply Subtype.ext
  norm_num [positiveHalfTime, collarCentre]

@[simp] theorem negativeHalfTime_zero : negativeHalfTime 0 = collarCentre := by
  apply Subtype.ext
  norm_num [negativeHalfTime, collarCentre]

/-- This is the literal De Morgan identification, with the same underlying
point and topology; no geometric cutting identification is hidden here. -/
def complementBoundaryHomeomorph (U V : Set M) :
    ↥((U ∪ V)ᶜ) ≃ₜ ↥(Vᶜ ∩ Uᶜ) where
  toFun x := ⟨x, fun hv => x.property (Or.inr hv), fun hu => x.property (Or.inl hu)⟩
  invFun x := ⟨x, fun h => h.elim x.property.2 x.property.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _
  continuous_invFun := continuous_subtype_val.subtype_mk _

/-- The required paths are consequences of the supplied actual collar
map. An open embedding is stronger than the continuity used by this step;
we do not claim to construct that embedding or prove separation. -/
theorem complementary_closed_sides_pathConnected
    (U V : Set M) (hdisjoint : Disjoint U V)
    (hU : IsPathConnected U) (hV : IsPathConnected V)
    (e : Sphere2 ≃ₜ ↥((U ∪ V)ᶜ))
    (c : Sphere2 × CollarTime → M) (hc : IsOpenEmbedding c)
    (hcentre : ∀ s, c (s, collarCentre) = (e s : M))
    (hnegative : ∀ s (t : CollarTime), (t : ℝ) < 0 → c (s, t) ∈ U)
    (hpositive : ∀ s (t : CollarTime), 0 < (t : ℝ) → c (s, t) ∈ V) :
    IsPathConnected Vᶜ ∧ IsPathConnected Uᶜ := by
  let neg : C(Sphere2 × I, M) :=
    ⟨fun p => c (p.1, negativeHalfTime p.2),
      hc.continuous.comp (continuous_fst.prodMk (negativeHalfTime.continuous.comp continuous_snd))⟩
  let pos : C(Sphere2 × I, M) :=
    ⟨fun p => c (p.1, positiveHalfTime p.2),
      hc.continuous.comp (continuous_fst.prodMk (positiveHalfTime.continuous.comp continuous_snd))⟩
  have hboundary : ∀ x, x ∉ U → x ∉ V → ∃ s, (e s : M) = x := by
    intro x hxu hxv
    obtain ⟨s, hs⟩ := e.surjective ⟨x, fun h => h.elim hxu hxv⟩
    exact ⟨s, congrArg Subtype.val hs⟩
  constructor
  · apply complementSide_pathConnected_of_halfCollar U V hdisjoint hU
      (fun s => (e s : M)) hboundary neg
    · intro s
      change c (s, negativeHalfTime 0) = (e s : M)
      rw [negativeHalfTime_zero]
      exact hcentre s
    · intro s t ht
      exact hnegative s (negativeHalfTime t) (by change -(t : ℝ) / 2 < 0; linarith)
  · apply complementSide_pathConnected_of_halfCollar V U hdisjoint.symm hV
      (fun s => (e s : M)) (fun x hxv hxu => hboundary x hxu hxv) pos
    · intro s
      change c (s, positiveHalfTime 0) = (e s : M)
      rw [positiveHalfTime_zero]
      exact hcentre s
    · intro s t ht
      exact hpositive s (positiveHalfTime t) (by change 0 < (t : ℝ) / 2; linarith)

/-- A compact simply connected space split into two path-connected open
regions by a collared standard two-sphere has simply connected capped
closed sides. The closed-cover gluing homeomorphism, normality, boundary
embeddings and closed-side path connectivity are derived internally. -/
theorem caps_of_collared_separation_simplyConnected
    [CompactSpace M] [T2Space M] [SimplyConnectedSpace M]
    (U V : Set M) (hUopen : IsOpen U) (hVopen : IsOpen V)
    (hdisjoint : Disjoint U V) (hU : IsPathConnected U) (hV : IsPathConnected V)
    (e : Sphere2 ≃ₜ ↥((U ∪ V)ᶜ))
    (c : Sphere2 × CollarTime → M) (hc : IsOpenEmbedding c)
    (hcentre : ∀ s, c (s, collarCentre) = (e s : M))
    (hnegative : ∀ s (t : CollarTime), (t : ℝ) < 0 → c (s, t) ∈ U)
    (hpositive : ∀ s (t : CollarTime), 0 < (t : ℝ) → c (s, t) ∈ V) :
    let e' := e.trans (complementBoundaryHomeomorph U V)
    SimplyConnectedSpace (BallAttachment (sphericalBoundaryLeft Vᶜ Uᶜ e')) ∧
      SimplyConnectedSpace (BallAttachment (sphericalBoundaryRight Vᶜ Uᶜ e')) := by
  have hcover : Vᶜ ∪ Uᶜ = (univ : Set M) := by
    apply Set.eq_univ_iff_forall.mpr
    intro x
    by_cases hxv : x ∈ V
    · exact Or.inr (fun hxu => Set.disjoint_left.mp hdisjoint hxu hxv)
    · exact Or.inl hxv
  obtain ⟨hA, hB⟩ := complementary_closed_sides_pathConnected U V hdisjoint hU hV
    e c hc hcentre hnegative hpositive
  exact both_closed_cover_caps_simplyConnected Vᶜ Uᶜ hVopen.isClosed_compl hUopen.isClosed_compl
    hcover (e.trans (complementBoundaryHomeomorph U V)) hA hB

end PoincareClosedCover
