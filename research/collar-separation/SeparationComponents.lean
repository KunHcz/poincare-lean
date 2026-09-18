import CollarSeparator

/-!
# The two generated sides are path connected

A connected collar trace meets every possible open-side component: an
additional component would be clopen in the connected ambient space. This
derives the path-connectivity hypotheses formerly supplied by a caller.
-/

open Function Set Topology Filter
open scoped ContinuousMap

noncomputable section

namespace PoincareSeparation

open PoincareClosedCover PoincareConjecture

/-- An open side with a connected trace in an open neighbourhood of the
separating set has only one path component. No path-component count is an
input: an additional component would disconnect the ambient space. -/
theorem open_side_pathConnected_of_trace
    {M : Type*} [TopologicalSpace M] [ConnectedSpace M] [LocallyPathConnectedSpace M]
    {U V N W : Set M} (hU : IsOpen U) (hV : IsOpen V) (hW : IsOpen W)
    (hd : Disjoint U V) (hcover : U ∪ V = Nᶜ) (hNW : N ⊆ W)
    (htrace : IsPathConnected (W ∩ U)) : IsPathConnected U := by
  obtain ⟨p, hpW, hpU⟩ := htrace.nonempty
  let C := pathComponentIn U p
  let E := U \ C
  have hC : IsOpen C := hU.pathComponentIn p
  have hcore : W ∩ U ⊆ C := htrace.subset_pathComponentIn ⟨hpW, hpU⟩ (fun _ h => h.2)
  have hEopen : IsOpen E := by
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    apply Filter.mem_of_superset ((hU.pathComponentIn x).mem_nhds (mem_pathComponentIn_self hx.1))
    intro y hy
    refine ⟨pathComponentIn_subset hy, ?_⟩
    intro hCy
    exact hx.2 (hCy.trans hy.symm)
  have hEcomp : Eᶜ = C ∪ V ∪ W := by
    ext x
    constructor
    · intro hx
      by_cases hxU : x ∈ U
      · have hxC : x ∈ C := by
          by_contra hh
          exact hx ⟨hxU, hh⟩
        exact Or.inl (Or.inl hxC)
      · by_cases hxV : x ∈ V
        · exact Or.inl (Or.inr hxV)
        · apply Or.inr
          apply hNW
          by_contra hxN
          have hxUV : x ∈ U ∪ V := by rw [hcover]; exact hxN
          exact hxUV.elim hxU hxV
    · intro hx hxE
      rcases hx with (hxC | hxV) | hxW
      · exact hxE.2 hxC
      · exact Set.disjoint_left.mp hd hxE.1 hxV
      · exact hxE.2 (hcore ⟨hxW, hxE.1⟩)
  have hEclosed : IsClosed E := by
    rw [← isOpen_compl_iff, hEcomp]
    exact (hC.union hV).union hW
  have hUC : U ⊆ C := by
    intro x hx
    by_contra hxc
    have hall := (show IsClopen E from ⟨hEclosed, hEopen⟩).eq_univ ⟨x, hx, hxc⟩
    have hpE : p ∈ E := by rw [hall]; trivial
    exact hpE.2 (mem_pathComponentIn_self hpU)
  have hCU : C = U := Set.Subset.antisymm pathComponentIn_subset hUC
  rw [← hCU]
  exact isPathConnected_pathComponentIn hpU

abbrev PositiveCollarParameter := ↥(Ioo (0 : ℝ) 1)

instance positiveCollarParameter_pathConnected : PathConnectedSpace PositiveCollarParameter :=
  isPathConnected_iff_pathConnectedSpace.mp ((convex_Ioo (0 : ℝ) 1).isPathConnected
    ⟨1 / 2, by norm_num⟩)

variable {S M : Type*} [TopologicalSpace S] [PathConnectedSpace S]
  [TopologicalSpace M]

def collarNegativeParam (c : S × CollarTime → M) (hc : Continuous c) :
    C(S × PositiveCollarParameter, M) := by
  refine ⟨fun p => c (p.1, ⟨-(p.2 : ℝ), by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩), ?_⟩
  apply hc.comp
  apply Continuous.prodMk continuous_fst
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp continuous_snd).neg

def collarPositiveParam (c : S × CollarTime → M) (hc : Continuous c) :
    C(S × PositiveCollarParameter, M) := by
  refine ⟨fun p => c (p.1, ⟨(p.2 : ℝ), by constructor <;> linarith [p.2.property.1, p.2.property.2]⟩), ?_⟩
  apply hc.comp
  apply Continuous.prodMk continuous_fst
  apply Continuous.subtype_mk
  exact continuous_subtype_val.comp continuous_snd

omit [PathConnectedSpace S] in
theorem collar_negative_trace_range (c : S × CollarTime → M) (hc : Continuous c)
    {U V : Set M} (hd : Disjoint U V) (hcover : U ∪ V = (centralSphere c)ᶜ)
    (hn : ∀ s (t : CollarTime), (t : ℝ) < 0 → c (s, t) ∈ U)
    (hp : ∀ s (t : CollarTime), 0 < (t : ℝ) → c (s, t) ∈ V) :
    Set.range (collarNegativeParam c hc) = Set.range c ∩ U := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨s, r⟩, rfl⟩
    refine ⟨⟨(s, ⟨-(r : ℝ), by constructor <;> linarith [r.property.1, r.property.2]⟩), rfl⟩, ?_⟩
    exact hn _ _ (neg_neg_of_pos r.property.1)
  · rintro x ⟨⟨⟨s, t⟩, rfl⟩, hxU⟩
    have ht : (t : ℝ) < 0 := by
      by_contra hh
      rcases eq_or_lt_of_le (le_of_not_gt hh) with hzero | hpos
      · have htzero : t = collarCentre := Subtype.ext hzero.symm
        have hxnot : c (s, t) ∉ centralSphere c := by
          change c (s, t) ∈ (centralSphere c)ᶜ
          rw [← hcover]
          exact Or.inl hxU
        exact hxnot ⟨s, by rw [htzero]⟩
      · exact Set.disjoint_left.mp hd hxU (hp s t hpos)
    refine ⟨(s, ⟨-(t : ℝ), by constructor <;> linarith [t.property.1]⟩), ?_⟩
    change c (s, _) = c (s, t)
    congr 1
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact neg_neg _

omit [PathConnectedSpace S] in
theorem collar_positive_trace_range (c : S × CollarTime → M) (hc : Continuous c)
    {U V : Set M} (hd : Disjoint U V) (hcover : U ∪ V = (centralSphere c)ᶜ)
    (hn : ∀ s (t : CollarTime), (t : ℝ) < 0 → c (s, t) ∈ U)
    (hp : ∀ s (t : CollarTime), 0 < (t : ℝ) → c (s, t) ∈ V) :
    Set.range (collarPositiveParam c hc) = Set.range c ∩ V := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨s, r⟩, rfl⟩
    refine ⟨⟨(s, ⟨(r : ℝ), by constructor <;> linarith [r.property.1, r.property.2]⟩), rfl⟩, ?_⟩
    exact hp _ _ r.property.1
  · rintro x ⟨⟨⟨s, t⟩, rfl⟩, hxV⟩
    have ht : 0 < (t : ℝ) := by
      by_contra hh
      rcases eq_or_lt_of_le (le_of_not_gt hh) with hzero | hneg
      · have htzero : t = collarCentre := Subtype.ext hzero
        have hxnot : c (s, t) ∉ centralSphere c := by
          change c (s, t) ∈ (centralSphere c)ᶜ
          rw [← hcover]
          exact Or.inr hxV
        exact hxnot ⟨s, by rw [htzero]⟩
      · exact Set.disjoint_left.mp hd (hn s t hneg) hxV
    exact ⟨(s, ⟨(t : ℝ), ht, t.property.2⟩), rfl⟩

/-- Every compact path-connected collared hypersurface in a simply
connected ambient space has two nonempty path-connected open sides,
with the expected negative/positive collar assignments. -/
theorem exists_pathConnected_separation_of_collar
    [CompactSpace S] [T2Space S] [T2Space M]
    [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (c : S × CollarTime → M) (hc : IsOpenEmbedding c) :
    ∃ U V : Set M, IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
      Disjoint U V ∧ U ∪ V = (centralSphere c)ᶜ ∧
      (∀ s (t : CollarTime), (t : ℝ) < 0 → c (s, t) ∈ U) ∧
      (∀ s (t : CollarTime), 0 < (t : ℝ) → c (s, t) ∈ V) := by
  obtain ⟨U, V, hU, hV, _, _, hd, hcover, hn, hp⟩ := exists_open_separation_of_collar c hc
  have hN : centralSphere c ⊆ Set.range c := by rintro x ⟨s, rfl⟩; exact ⟨(s, collarCentre), rfl⟩
  have htraceU : IsPathConnected (Set.range c ∩ U) := by
    rw [← collar_negative_trace_range c hc.continuous hd hcover hn hp]
    exact isPathConnected_range (collarNegativeParam c hc.continuous).continuous
  have htraceV : IsPathConnected (Set.range c ∩ V) := by
    rw [← collar_positive_trace_range c hc.continuous hd hcover hn hp]
    exact isPathConnected_range (collarPositiveParam c hc.continuous).continuous
  exact ⟨U, V, hU, hV, open_side_pathConnected_of_trace hU hV hc.isOpen_range hd hcover hN htraceU,
    open_side_pathConnected_of_trace hV hU hc.isOpen_range hd.symm
      (by rw [union_comm]; exact hcover) hN htraceV, hd, hcover, hn, hp⟩

end PoincareSeparation
