import CompactCollar

open Function Set Topology
open scoped ContinuousMap

noncomputable section

namespace PoincareLocalCollar

open PoincareConjecture PoincareClosedCover PoincareSeparation

variable {S M : Type*} [TopologicalSpace S] [TopologicalSpace M]

omit [TopologicalSpace S] [TopologicalSpace M] in
theorem scaled_time_mem_ball {r : ℝ} (hr : 0 < r) (t : CollarTime) :
    r * (t : ℝ) ∈ Metric.ball (0 : ℝ) r := by
  rw [mem_ball_zero_iff, Real.norm_eq_abs, abs_mul, abs_of_pos hr]
  have ht : |(t : ℝ)| < 1 := abs_lt.mpr t.property
  simpa using mul_lt_mul_of_pos_left ht hr

/-- Actual rescaling, with the same source points and a strictly positive
scale, identifies the standard collar domain with the proven injective band. -/
def bandCoordinates (r : ℝ) (hr : 0 < r) : S × CollarTime ≃ₜ timeBand (S := S) r where
  toFun p := ⟨(p.1, r * (p.2 : ℝ)), mem_univ _, scaled_time_mem_ball hr p.2⟩
  invFun p := (p.1.1, ⟨p.1.2 / r, by
    have ht : |p.1.2| < r := by simpa only [mem_ball_zero_iff, Real.norm_eq_abs] using p.property.2
    apply abs_lt.mp
    rw [abs_div, abs_of_pos hr]
    exact (div_lt_one hr).mpr ht⟩)
  left_inv p := by
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change r * (p.2 : ℝ) / r = (p.2 : ℝ)
      simp [hr.ne']
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change r * (p.1.2 / r) = p.1.2
      field_simp
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_fst.prodMk (continuous_const.mul (continuous_subtype_val.comp continuous_snd))
  continuous_invFun := by
    apply Continuous.prodMk
    · exact continuous_fst.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact (continuous_snd.comp continuous_subtype_val).div_const r

def scaledCollar (f : C(S × ℝ, M)) (r : ℝ) : C(S × CollarTime, M) :=
  ⟨fun p => f (p.1, r * (p.2 : ℝ)),
    f.continuous.comp (continuous_fst.prodMk
      (continuous_const.mul (continuous_subtype_val.comp continuous_snd)))⟩

@[simp] theorem scaledCollar_zero (f : C(S × ℝ, M)) (r : ℝ) (s : S) :
    scaledCollar f r (s, collarCentre) = f (s, 0) := by
  simp [scaledCollar, collarCentre]

theorem exists_scaled_open_collar [CompactSpace S] [T2Space M]
    (f : C(S × ℝ, M)) (hzero : Injective (fun s => f (s, 0)))
    (hlocal : HasLocalOpenChartsAtZero f) :
    ∃ r > 0, IsOpenEmbedding (scaledCollar f r) := by
  obtain ⟨r, hr, he⟩ := exists_uniform_openEmbedding_band f hzero hlocal
  exact ⟨r, hr, he.comp (bandCoordinates (S := S) r hr).isOpenEmbedding⟩

/-- The global collar and complementary regions are outputs of the local
invertibility hypotheses, not assumed data. The central embedding remains
the original zero section of the supplied family. -/
theorem local_family_separates_and_caps
    [CompactSpace M] [T2Space M] [SimplyConnectedSpace M] [LocallyPathConnectedSpace M]
    (f : C(Sphere2 × ℝ, M)) (hzero : Injective (fun s => f (s, 0)))
    (hlocal : HasLocalOpenChartsAtZero f) :
    ∃ r > 0, IsOpenEmbedding (scaledCollar f r) ∧
      ∃ (U V : Set M) (e : Sphere2 ≃ₜ ↥((U ∪ V)ᶜ)),
        IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧ Disjoint U V ∧
        (∀ s, (e s : M) = f (s, 0)) ∧
        (∀ s (t : CollarTime), (t : ℝ) < 0 → scaledCollar f r (s, t) ∈ U) ∧
        (∀ s (t : CollarTime), 0 < (t : ℝ) → scaledCollar f r (s, t) ∈ V) ∧
        (let e' := e.trans (complementBoundaryHomeomorph U V)
         SimplyConnectedSpace (BallAttachment (sphericalBoundaryLeft Vᶜ Uᶜ e')) ∧
           SimplyConnectedSpace (BallAttachment (sphericalBoundaryRight Vᶜ Uᶜ e'))) := by
  obtain ⟨r, hr, he⟩ := exists_scaled_open_collar f hzero hlocal
  obtain ⟨U, V, e, hoU, hoV, hpU, hpV, hd, hc, hn, hp, hcaps⟩ :=
    sphere_collar_separates_and_caps (scaledCollar f r) he
  exact ⟨r, hr, he, U, V, e, hoU, hoV, hpU, hpV, hd,
    fun s => (hc s).trans (scaledCollar_zero f r s), hn, hp, hcaps⟩

end PoincareLocalCollar
