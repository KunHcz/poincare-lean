import CollarPhase
import Mathlib.Topology.Order.IntermediateValue

/-!
# A collared compact connected hypersurface separates a simply connected space

The actual circle-valued collar crossing lifts to a continuous real-valued
function on the simply connected ambient space. Covering uniqueness fixes
its values on the whole connected collar. Its half-level is exactly the
given hypersurface, and its strict sublevel/superlevel sets give a nontrivial
open separation of the complement. Neither those regions nor a separating
function is an input.
-/

open Function Set Topology
open scoped ContinuousMap

noncomputable section

namespace PoincareSeparation

open PoincareClosedCover PoincareConjecture

instance collarTime_connected : ConnectedSpace CollarTime :=
  isConnected_iff_connectedSpace.mp ((convex_Ioo (-1 : ℝ) 1).isConnected ⟨0, by norm_num⟩)

variable {S M : Type*} [TopologicalSpace S] [CompactSpace S] [T2Space S] [ConnectedSpace S]
  [TopologicalSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]

/-- Simple connectivity supplies the real lift. It agrees on the whole
collar with the specified local crossing coordinate, not only at one point. -/
theorem exists_global_crossing_lift (c : S × CollarTime → M) (hc : IsOpenEmbedding c) :
    ∃ H : C(M, ℝ),
      (∀ x, (H x : PeriodicCircle) = globalCrossing c hc x) ∧
      ∀ s t, H (c (s, t)) = crossingHeight (t : ℝ) := by
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  let p₀ : S × CollarTime := (s₀, collarCentre)
  have hbase : ((1 / 2 : ℝ) : PeriodicCircle) = globalCrossing c hc (c p₀) := by
    rw [globalCrossing_on_collar]
    congr 1
    norm_num [p₀, collarCentre, crossingHeight]
  obtain ⟨H, hH, _⟩ := (AddCircle.isCoveringMap_coe (1 : ℝ)).existsUnique_continuousMap_lifts
    (globalCrossing c hc) (c p₀) (1 / 2) hbase
  refine ⟨H, fun x => congrFun hH.2 x, ?_⟩
  have heq : (fun p : S × CollarTime => H (c p)) =
      (fun p => crossingHeight (p.2 : ℝ)) := by
    exact (AddCircle.isCoveringMap_coe (1 : ℝ)).eq_of_comp_eq
      (H.continuous.comp hc.continuous)
      (crossingHeight_continuous.comp (continuous_subtype_val.comp continuous_snd))
      (by funext p; exact (congrFun hH.2 (c p)).trans (globalCrossing_on_collar c hc p.1 p.2))
      p₀ (hH.1.trans (by norm_num [p₀, collarCentre, crossingHeight]))
  intro s t
  exact congrFun heq (s, t)

omit [ConnectedSpace S] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M] in
/-- The generated real height has exactly the prescribed central fibre. -/
theorem lift_half_fiber
    (c : S × CollarTime → M) (hc : IsOpenEmbedding c) (H : C(M, ℝ))
    (hlift : ∀ x, (H x : PeriodicCircle) = globalCrossing c hc x)
    (hon : ∀ s t, H (c (s, t)) = crossingHeight (t : ℝ)) (x : M) :
    H x = 1 / 2 ↔ x ∈ centralSphere c := by
  constructor
  · intro hx
    apply (globalCrossing_half_fiber c hc x).mp
    rw [← hlift, hx]
  · rintro ⟨s, rfl⟩
    rw [hon]
    norm_num [collarCentre, crossingHeight]

/-- The negative and positive collar slices lie in different open sides
of the complement. This does not require a connected-complement assumption. -/
theorem exists_open_separation_of_collar
    (c : S × CollarTime → M) (hc : IsOpenEmbedding c) :
    ∃ U V : Set M, IsOpen U ∧ IsOpen V ∧ U.Nonempty ∧ V.Nonempty ∧ Disjoint U V ∧
      U ∪ V = (centralSphere c)ᶜ ∧
      (∀ s (t : CollarTime), (t : ℝ) < 0 → c (s, t) ∈ U) ∧
      (∀ s (t : CollarTime), 0 < (t : ℝ) → c (s, t) ∈ V) := by
  obtain ⟨H, hlift, hon⟩ := exists_global_crossing_lift c hc
  let U := {x : M | H x < 1 / 2}
  let V := {x : M | 1 / 2 < H x}
  have hneg (s : S) (t : CollarTime) (ht : (t : ℝ) < 0) : c (s, t) ∈ U := by
    change H (c (s, t)) < 1 / 2
    rw [hon]
    apply lt_of_le_of_lt (min_le_right _ _)
    exact max_lt (by norm_num) (by linarith)
  have hpos (s : S) (t : CollarTime) (ht : 0 < (t : ℝ)) : c (s, t) ∈ V := by
    change 1 / 2 < H (c (s, t))
    rw [hon]
    apply lt_min (by norm_num)
    exact lt_of_lt_of_le (by linarith : (1 / 2 : ℝ) < (t : ℝ) + 1 / 2) (le_max_right _ _)
  obtain ⟨s₀⟩ := (inferInstance : Nonempty S)
  refine ⟨U, V, isOpen_lt H.continuous continuous_const, isOpen_lt continuous_const H.continuous,
    ⟨c (s₀, ⟨-(1 / 4), by norm_num⟩), hneg s₀ _ (by norm_num)⟩,
    ⟨c (s₀, ⟨1 / 4, by norm_num⟩), hpos s₀ _ (by norm_num)⟩,
    ?_, ?_, hneg, hpos⟩
  · apply Set.disjoint_left.mpr
    intro x hxU hxV
    change H x < 1 / 2 at hxU
    change 1 / 2 < H x at hxV
    exact lt_asymm hxU hxV
  · ext x
    change (H x < 1 / 2 ∨ 1 / 2 < H x) ↔ x ∉ centralSphere c
    rw [← ne_iff_lt_or_gt]
    exact not_congr (lift_half_fiber c hc H hlift hon x)

/-- A compact connected collared hypersurface cannot have connected
complement in a simply connected, locally path-connected Hausdorff space. -/
theorem central_complement_not_preconnected
    (c : S × CollarTime → M) (hc : IsOpenEmbedding c) :
    ¬ IsPreconnected (centralSphere c)ᶜ := by
  obtain ⟨U, V, hU, hV, hnU, hnV, hd, hcover, _, _⟩ := exists_open_separation_of_collar c hc
  intro h
  have hs := h.subset_or_subset hU hV hd (by rw [← hcover])
  rcases hs with hs | hs
  · obtain ⟨v, hv⟩ := hnV
    have hcV : v ∈ (centralSphere c)ᶜ := by rw [← hcover]; exact Or.inr hv
    exact Set.disjoint_left.mp hd (hs hcV) hv
  · obtain ⟨u, hu⟩ := hnU
    have hcU : u ∈ (centralSphere c)ᶜ := by rw [← hcover]; exact Or.inl hu
    exact Set.disjoint_left.mp hd hu (hs hcU)

end PoincareSeparation
