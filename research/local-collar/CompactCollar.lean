import SeparatedCapping
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Tactic

/-!
# Uniform collars from local invertibility along a compact zero section

The input is a continuous family near a compact embedded zero section. Its
open embeddings are only local at individual zero-section points; a global
injectivity strip, uniform radius and full collar are not input certificates.
Compactness and separation of distinct zero-section images construct one
positive-width strip on which the original family is an open embedding.
-/

open Function Set Filter Topology
open scoped ContinuousMap

noncomputable section

namespace PoincareLocalCollar

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

def timeBand (r : ℝ) : Set (S × ℝ) := univ ×ˢ Metric.ball 0 r

theorem timeBand_isOpen (r : ℝ) : IsOpen (timeBand (S := S) r) :=
  isOpen_univ.prod Metric.isOpen_ball

omit [TopologicalSpace S] in
theorem zero_mem_timeBand {r : ℝ} (hr : 0 < r) (s : S) : (s, 0) ∈ timeBand r :=
  ⟨mem_univ _, by simpa using hr⟩

/-- Every open neighbourhood of a compact zero section contains a uniform
positive-width product band; the width is chosen after the whole section. -/
theorem exists_uniform_band_subset [CompactSpace S]
    (W : Set (S × ℝ)) (hW : IsOpen W) (hzero : ∀ s, (s, 0) ∈ W) :
    ∃ r > 0, timeBand r ⊆ W := by
  have h : ∀ᶠ t : ℝ in 𝓝 0, ∀ s ∈ (univ : Set S), (s, t) ∈ W :=
    isCompact_univ.eventually_forall_of_forall_eventually
      (fun s _ => (hW.preimage continuous_swap).mem_nhds (hzero s))
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp h
  exact ⟨r, hr, fun p hp => hsub hp.2 p.1 (mem_univ _)⟩

/-- Distinct zero-section points have distinct nearby images by Hausdorff
separation; near equal zero-section points, the local injectivity hypothesis
rules out collisions. Compactness makes the neighbourhood uniform. -/
theorem exists_uniform_injective_band [CompactSpace S] [T2Space M]
    (f : C(S × ℝ, M)) (hzero : Injective (fun s => f (s, 0)))
    (hlocal : ∀ s, ∃ U ∈ 𝓝 (s, (0 : ℝ)), Set.InjOn f U) :
    ∃ r > 0, Set.InjOn f (timeBand r) := by
  let left : ((ℝ × ℝ) × (S × S)) → S × ℝ := fun z => (z.2.1, z.1.1)
  let right : ((ℝ × ℝ) × (S × S)) → S × ℝ := fun z => (z.2.2, z.1.2)
  have hleft : Continuous left :=
    (continuous_fst.comp continuous_snd).prodMk (continuous_fst.comp continuous_fst)
  have hright : Continuous right :=
    (continuous_snd.comp continuous_snd).prodMk (continuous_snd.comp continuous_fst)
  have hevent : ∀ p ∈ (univ : Set (S × S)),
      ∀ᶠ z : (ℝ × ℝ) × (S × S) in 𝓝 ((0, 0), p),
        f (left z) = f (right z) → left z = right z := by
    intro p _
    by_cases hp : p.1 = p.2
    · obtain ⟨U, hU, hinj⟩ := hlocal p.1
      have hL : ∀ᶠ z in 𝓝 ((0, 0), p), left z ∈ U := hleft.continuousAt hU
      have hR : ∀ᶠ z in 𝓝 ((0, 0), p), right z ∈ U := by
        apply hright.continuousAt
        simpa only [right, hp] using hU
      filter_upwards [hL, hR] with z hzL hzR
      exact hinj hzL hzR
    · have hne : f (left ((0, 0), p)) ≠ f (right ((0, 0), p)) :=
        fun heq => hp (hzero heq)
      have h := (isOpen_ne_fun (f.continuous.comp hleft) (f.continuous.comp hright)).mem_nhds hne
      filter_upwards [h] with z hz
      exact fun heq => (hz heq).elim
  have h : ∀ᶠ t : ℝ × ℝ in 𝓝 (0, 0), ∀ p ∈ (univ : Set (S × S)),
      f (p.1, t.1) = f (p.2, t.2) → (p.1, t.1) = (p.2, t.2) :=
    isCompact_univ.eventually_forall_of_forall_eventually hevent
  obtain ⟨A, hA, B, hB, hAB⟩ := mem_nhds_prod_iff.mp h
  obtain ⟨r, hr, hrAB⟩ := Metric.mem_nhds_iff.mp (inter_mem hA hB)
  refine ⟨r, hr, ?_⟩
  intro p hp q hq heq
  exact hAB (show (p.2, q.2) ∈ A ×ˢ B from ⟨(hrAB hp.2).1, (hrAB hq.2).2⟩)
    (p.1, q.1) (mem_univ _) heq

/-- The local-chart assumption is expressed in ordinary topology: every
zero-section point has an open neighbourhood on which the original family
is an open embedding. These neighbourhoods need not share a width. -/
def HasLocalOpenChartsAtZero (f : S × ℝ → M) : Prop :=
  ∀ s : S, ∃ U : Set (S × ℝ), IsOpen U ∧ (s, 0) ∈ U ∧ IsOpenEmbedding (U.restrict f)

theorem localCharts_injectiveAtZero (f : S × ℝ → M) (hlocal : HasLocalOpenChartsAtZero f) :
    ∀ s, ∃ U ∈ 𝓝 (s, (0 : ℝ)), Set.InjOn f U := by
  intro s
  obtain ⟨U, hU, hsU, he⟩ := hlocal s
  exact ⟨U, hU.mem_nhds hsU, Set.injOn_iff_injective.mpr he.injective⟩

theorem localCharts_open_neighbourhood (f : S × ℝ → M) (hlocal : HasLocalOpenChartsAtZero f) :
    ∃ W : Set (S × ℝ), IsOpen W ∧ (∀ s, (s, 0) ∈ W) ∧ IsLocalHomeomorphOn f W := by
  choose U hopen hmem hemb using hlocal
  refine ⟨⋃ s, U s, isOpen_iUnion hopen, fun s => mem_iUnion.mpr ⟨s, hmem s⟩, ?_⟩
  apply (isLocalHomeomorphOn_iff_isOpenEmbedding_restrict (f := f) (⋃ s, U s)).mpr
  intro p hp
  obtain ⟨s, hs⟩ := mem_iUnion.mp hp
  exact ⟨U s, (hopen s).mem_nhds hs, hemb s⟩

/-- A uniform open collar is constructed from the local inverses and
the injectivity of the compact zero section. No global tubular map is
assumed in this statement. -/
theorem exists_uniform_openEmbedding_band [CompactSpace S] [T2Space M]
    (f : C(S × ℝ, M)) (hzero : Injective (fun s => f (s, 0)))
    (hlocal : HasLocalOpenChartsAtZero f) :
    ∃ r > 0, IsOpenEmbedding ((timeBand (S := S) r).restrict f) := by
  obtain ⟨r, hr, hinj⟩ := exists_uniform_injective_band f hzero (localCharts_injectiveAtZero f hlocal)
  obtain ⟨W, hW, hWzero, hlocW⟩ := localCharts_open_neighbourhood f hlocal
  obtain ⟨s, hs, hsW⟩ := exists_uniform_band_subset W hW hWzero
  let d := min r s
  have hd : 0 < d := lt_min hr hs
  have hdr : timeBand (S := S) d ⊆ timeBand r :=
    Set.prod_mono subset_rfl (Metric.ball_subset_ball (min_le_left _ _))
  have hds : timeBand (S := S) d ⊆ timeBand s :=
    Set.prod_mono subset_rfl (Metric.ball_subset_ball (min_le_right _ _))
  have hinjD : Injective ((timeBand (S := S) d).restrict f) := by
    intro x y heq
    exact Subtype.ext (hinj (hdr x.property) (hdr y.property) heq)
  have hlocD : IsLocalHomeomorph ((timeBand (S := S) d).restrict f) := by
    apply isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
    exact hlocW.comp
      (timeBand_isOpen d).isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
      (fun p _ => hsW (hds p.property))
  exact ⟨d, hd, hlocD.isOpenEmbedding_of_injective hinjD⟩

end PoincareLocalCollar
