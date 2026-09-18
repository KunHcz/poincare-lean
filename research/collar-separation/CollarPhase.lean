import CutSides
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Topology.Connected.LocallyPathConnected

/-!
# A circle-valued crossing map for an actual compact two-sided collar

Inside the collar the map traverses the additive circle once. It is zero
near both ends, so it extends continuously by zero outside the collar.
The preimage of the half-period is exactly the central hypersurface. No
global separation of the complement is assumed in the construction.
-/

open Function Set Topology Filter
open scoped ContinuousMap

noncomputable section

namespace PoincareSeparation

open PoincareClosedCover PoincareConjecture

abbrev PeriodicCircle := AddCircle (1 : ℝ)

def crossingHeight (t : ℝ) : ℝ := min 1 (max 0 (t + 1 / 2))

theorem crossingHeight_continuous : Continuous crossingHeight :=
  continuous_const.min (continuous_const.max (continuous_id.add continuous_const))

theorem crossingHeight_nonneg (t : ℝ) : 0 ≤ crossingHeight t := by
  exact le_min (by norm_num) (le_max_left _ _)

theorem crossingHeight_le_one (t : ℝ) : crossingHeight t ≤ 1 := min_le_left _ _

theorem crossingHeight_lower {t : ℝ} (ht : t ≤ -(1 / 2)) : crossingHeight t = 0 := by
  simp only [crossingHeight, max_eq_left (by linarith : t + 1 / 2 ≤ 0)]
  norm_num

theorem crossingHeight_upper {t : ℝ} (ht : 1 / 2 ≤ t) : crossingHeight t = 1 := by
  apply min_eq_left
  exact (by linarith : (1 : ℝ) ≤ t + 1 / 2).trans (le_max_right _ _)

theorem crossingHeight_middle {t : ℝ} (ht : t ∈ Icc (-(1 / 2)) (1 / 2)) :
    crossingHeight t = t + 1 / 2 := by
  rw [crossingHeight, max_eq_right (by linarith [ht.1]), min_eq_right (by linarith [ht.2])]

theorem halfPeriod_ne_zero : ((1 / 2 : ℝ) : PeriodicCircle) ≠ 0 := by
  intro h
  have hh := (AddCircle.coe_eq_zero_iff_of_mem_Ico
    (p := (1 : ℝ)) (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 1)).mp h
  norm_num at hh

theorem crossingCircle_half_iff (t : ℝ) :
    (crossingHeight t : PeriodicCircle) = ((1 / 2 : ℝ) : PeriodicCircle) ↔ t = 0 := by
  constructor
  · intro h
    have hlo : -(1 / 2 : ℝ) < t := by
      by_contra hh
      rw [crossingHeight_lower (le_of_not_gt hh), AddCircle.coe_zero] at h
      exact halfPeriod_ne_zero h.symm
    have hup : t < (1 / 2 : ℝ) := by
      by_contra hh
      rw [crossingHeight_upper (le_of_not_gt hh), AddCircle.coe_period] at h
      exact halfPeriod_ne_zero h.symm
    rw [crossingHeight_middle ⟨hlo.le, hup.le⟩] at h
    have heq := (AddCircle.coe_eq_coe_iff_of_mem_Ico
      (p := (1 : ℝ)) (a := 0) (by constructor <;> linarith : t + 1 / 2 ∈ Ico 0 (0 + 1))
      (by norm_num : (1 / 2 : ℝ) ∈ Ico 0 (0 + 1))).mp h
    linarith
  · rintro rfl
    congr 1
    norm_num [crossingHeight]

def localCrossing (S : Type*) [TopologicalSpace S] : C(S × CollarTime, PeriodicCircle) :=
  ⟨fun p => (crossingHeight (p.2 : ℝ) : PeriodicCircle),
    continuous_quotient_mk'.comp (crossingHeight_continuous.comp
      (continuous_subtype_val.comp continuous_snd))⟩

/-- Compactness of the hypersurface keeps the transition support inside a
compact subcollar, even though the full collar is an open interval. -/
theorem localCrossing_hasCompactSupport (S : Type*) [TopologicalSpace S]
    [CompactSpace S] [T2Space S] : HasCompactSupport (localCrossing S) := by
  let J : S × ↥(Icc (-(1 / 2 : ℝ)) (1 / 2)) → S × CollarTime :=
    fun p => (p.1, ⟨p.2, by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩)
  have hJ : Continuous J := by
    apply Continuous.prodMk continuous_fst
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_snd
  have hcompact : IsCompact (Set.range J) := isCompact_range hJ
  apply HasCompactSupport.intro hcompact
  intro p hp
  have hout : (p.2 : ℝ) ∉ Icc (-(1 / 2 : ℝ)) (1 / 2) := by
    intro ht
    apply hp
    exact ⟨(p.1, ⟨p.2, ht⟩), rfl⟩
  by_cases hl : (p.2 : ℝ) < -(1 / 2 : ℝ)
  · change (crossingHeight (p.2 : ℝ) : PeriodicCircle) = 0
    rw [crossingHeight_lower hl.le, AddCircle.coe_zero]
  · have hu : (1 / 2 : ℝ) < (p.2 : ℝ) := by
      by_contra hh
      exact hout ⟨le_of_not_gt hl, le_of_not_gt hh⟩
    change (crossingHeight (p.2 : ℝ) : PeriodicCircle) = 0
    rw [crossingHeight_upper hu.le, AddCircle.coe_period]

/-- Zero extension along the given open embedding. The support condition
is proved for the local crossing map, not assumed for a desired separator. -/
theorem continuous_extend_zero_of_openEmbedding
    {A B Z : Type*} [TopologicalSpace A] [TopologicalSpace B] [T2Space B]
    [TopologicalSpace Z] [Zero Z] (j : A → B) (hj : IsOpenEmbedding j)
    (f : C(A, Z)) (hs : HasCompactSupport f) : Continuous (j.extend f 0) := by
  apply continuous_of_tsupport
  intro b hb
  obtain ⟨a, _, rfl⟩ := hs.tsupport_extend_zero_subset hj.continuous hb
  rw [← hj.continuousAt_iff, Function.extend_comp hj.injective]
  exact f.continuous.continuousAt

variable {S M : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S]
  [TopologicalSpace M] [T2Space M]

def globalCrossing (c : S × CollarTime → M) (hc : IsOpenEmbedding c) : C(M, PeriodicCircle) :=
  ⟨c.extend (localCrossing S) 0,
    continuous_extend_zero_of_openEmbedding c hc (localCrossing S) (localCrossing_hasCompactSupport S)⟩

@[simp] theorem globalCrossing_on_collar (c : S × CollarTime → M) (hc : IsOpenEmbedding c)
    (s : S) (t : CollarTime) :
    globalCrossing c hc (c (s, t)) = (crossingHeight (t : ℝ) : PeriodicCircle) := by
  exact congrFun (Function.extend_comp hc.injective (localCrossing S) 0) (s, t)

theorem globalCrossing_off_collar (c : S × CollarTime → M) (hc : IsOpenEmbedding c)
    {x : M} (hx : x ∉ Set.range c) : globalCrossing c hc x = 0 := by
  exact Function.extend_apply' _ _ _ hx

def centralSphere (c : S × CollarTime → M) : Set M := Set.range (fun s => c (s, collarCentre))

/-- The half-period level is exactly the central hypersurface, not a
possibly larger set selected by an abstract separator. -/
theorem globalCrossing_half_fiber (c : S × CollarTime → M) (hc : IsOpenEmbedding c) (x : M) :
    globalCrossing c hc x = ((1 / 2 : ℝ) : PeriodicCircle) ↔ x ∈ centralSphere c := by
  constructor
  · intro h
    have hx : x ∈ Set.range c := by
      by_contra hh
      rw [globalCrossing_off_collar c hc hh] at h
      exact halfPeriod_ne_zero h.symm
    obtain ⟨⟨s, t⟩, rfl⟩ := hx
    rw [globalCrossing_on_collar] at h
    have ht : t = collarCentre := Subtype.ext ((crossingCircle_half_iff (t : ℝ)).mp h)
    exact ⟨s, by rw [ht]⟩
  · rintro ⟨s, rfl⟩
    rw [globalCrossing_on_collar]
    exact (crossingCircle_half_iff _).mpr rfl

end PoincareSeparation
