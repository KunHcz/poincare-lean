import ScalarFlowBounds

/-!
# Scalar control along finite chains of regular Ricci-flow segments

Each segment below is an actual metric Ricci flow. Its underlying manifold
may change between segments. The transition hypothesis is the explicit
preservation of nonpositive scalar lower bounds, not an assumption that the
final global estimate holds. A geometric transition satisfying the usual
surviving-region and nonnegative-cap conditions has this property.

The theorem does not construct surgery or the caps, and therefore does not
claim to close the surgery-existence or Poincare obligations. It proves the
finite-chain analytic consequence once those stated geometric inputs exist.
-/

open Set PoincareScalarFlow
open DifferentialGeometry DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace PoincareFlowChains

/-- A transition does not lose any scalar lower bound at or below zero.
The two spaces need not be equal, homeomorphic, connected or nonempty. -/
def PreservesNonpositiveBounds {A B : Type*} (rA : A → ℝ) (rB : B → ℝ) : Prop :=
  ∀ b ≤ 0, (∀ x, b ≤ rA x) → ∀ y, b ≤ rB y

/-- On the surviving region the new scalar is no smaller than at its old
point; new caps have nonnegative scalar. These explicit geometric conditions
suffice for the scalar-bound transition used by the chain theorem. -/
theorem transfer_of_survivors_and_nonnegative_caps
    {A B : Type*} (rA : A → ℝ) (rB : B → ℝ)
    (survives : B → Prop) (oldPoint : {y // survives y} → A)
    (hkeep : ∀ y : {y // survives y}, rA (oldPoint y) ≤ rB y)
    (hcap : ∀ y, ¬ survives y → 0 ≤ rB y) : PreservesNonpositiveBounds rA rB := by
  intro b hb hA y
  by_cases hy : survives y
  · exact (hA (oldPoint ⟨y, hy⟩)).trans (hkeep ⟨y, hy⟩)
  · exact hb.trans (hcap y hy)

theorem transfer_comp {A B C : Type*} {rA : A → ℝ} {rB : B → ℝ} {rC : C → ℝ}
    (hAB : PreservesNonpositiveBounds rA rB) (hBC : PreservesNonpositiveBounds rB rC) :
    PreservesNonpositiveBounds rA rC := by
  intro b hb hA
  exact hBC b hb (hAB b hb hA)

/-- Elapsed time before segment `j`; it does not restart at a transition. -/
def elapsed (duration : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => elapsed duration j + duration j

theorem elapsed_nonnegative {duration : ℕ → ℝ} {n : ℕ}
    (hduration : ∀ j < n, 0 ≤ duration j) : 0 ≤ elapsed duration n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact add_nonneg (ih (fun j hj => hduration j (Nat.lt_succ_of_lt hj)))
      (hduration n (Nat.lt_succ_self n))

variable {M : ℕ → Type*}
  [∀ j, TopologicalSpace (M j)] [∀ j, ChartedSpace Model3 (M j)]
  [∀ j, IsManifold (𝓡 3) ∞ (M j)] [∀ j, T2Space (M j)] [∀ j, CompactSpace (M j)]

/-- The normalized scalar bound with the original global time holds in every
segment of a finite chain, even if the topology or connected components change.

All analytic flow hypotheses are attached to actual metric families, and all
transition hypotheses are stated separately. In particular, geometric surgery
preservation and existence are not disguised as completed theorems here. -/
theorem normalized_bound_on_finite_chain
    (omega duration : ℕ → ℝ) (homega : ∀ j, 0 < omega j)
    (S : ∀ j, SolutionOn (I := 𝓡 3) (M := M j)
      (RealTimeInterval.closedOpen 0 (omega j) (homega j)))
    {n : ℕ} (hS : ∀ j ≤ n, IsSolutionOn (I := 𝓡 3) (S j))
    (hduration : ∀ j ≤ n, 0 ≤ duration j)
    (hinside : ∀ j ≤ n, duration j < omega j)
    {a : ℝ} (ha : 0 ≤ a)
    (hinit : ∀ x : M 0, -6 / (1 + 4 * a) ≤ (S 0).scalar 0 x)
    (htransfer : ∀ j < n,
      PreservesNonpositiveBounds ((S j).scalar (duration j)) ((S (j + 1)).scalar 0)) :
    ∀ j ≤ n, ∀ u ∈ Icc 0 (duration j), ∀ x : M j,
      -6 / (1 + 4 * (a + elapsed duration j + u)) ≤ (S j).scalar u x := by
  have htime : ∀ j ≤ n, 0 ≤ a + elapsed duration j := by
    intro j hj
    exact add_nonneg ha (elapsed_nonnegative (fun k hk => hduration k (by omega)))
  intro j
  induction j with
  | zero =>
    intro hj u hu x
    simpa only [elapsed, add_zero] using
      normalized_scalar_lower_bound_after_restart (homega 0) (S 0) (hS 0 hj)
        ha hinit hu.1 (hu.2.trans_lt (hinside 0 hj)) x
  | succ j ih =>
    intro hj u hu x
    have hjle : j ≤ n := by omega
    have hjlt : j < n := by omega
    have hclock : a + elapsed duration (j + 1) = a + elapsed duration j + duration j := by
      simp only [elapsed]
      ring
    have hterminal : ∀ y : M j,
        -6 / (1 + 4 * (a + elapsed duration (j + 1))) ≤ (S j).scalar (duration j) y := by
      intro y
      rw [hclock]
      exact ih hjle (duration j) ⟨hduration j hjle, le_rfl⟩ y
    have hnonpos : -6 / (1 + 4 * (a + elapsed duration (j + 1))) ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (by norm_num)
        (by have := htime (j + 1) hj; linarith)
    have hnext := htransfer j hjlt (-6 / (1 + 4 * (a + elapsed duration (j + 1)))) hnonpos hterminal
    exact normalized_scalar_lower_bound_after_restart (homega (j + 1)) (S (j + 1)) (hS (j + 1) hj)
      (htime (j + 1) hj) hnext hu.1 (hu.2.trans_lt (hinside (j + 1) hj)) x

/-- The same chain bound with literal scalar conditions on retained points
and inserted caps. No separately supplied global barrier-preservation
certificate is required. The cap construction itself remains an open
geometric obligation rather than a conclusion of this theorem. -/
theorem normalized_bound_from_survivor_and_cap_data
    (omega duration : ℕ → ℝ) (homega : ∀ j, 0 < omega j)
    (S : ∀ j, SolutionOn (I := 𝓡 3) (M := M j)
      (RealTimeInterval.closedOpen 0 (omega j) (homega j)))
    {n : ℕ} (hS : ∀ j ≤ n, IsSolutionOn (I := 𝓡 3) (S j))
    (hduration : ∀ j ≤ n, 0 ≤ duration j)
    (hinside : ∀ j ≤ n, duration j < omega j)
    {a : ℝ} (ha : 0 ≤ a)
    (hinit : ∀ x : M 0, -6 / (1 + 4 * a) ≤ (S 0).scalar 0 x)
    (survives : ∀ j, M (j + 1) → Prop)
    (oldPoint : ∀ j, {y // survives j y} → M j)
    (hkeep : ∀ j < n, ∀ y : {y // survives j y},
      (S j).scalar (duration j) (oldPoint j y) ≤ (S (j + 1)).scalar 0 y)
    (hcap : ∀ j < n, ∀ y, ¬ survives j y → 0 ≤ (S (j + 1)).scalar 0 y) :
    ∀ j ≤ n, ∀ u ∈ Icc 0 (duration j), ∀ x : M j,
      -6 / (1 + 4 * (a + elapsed duration j + u)) ≤ (S j).scalar u x := by
  apply normalized_bound_on_finite_chain omega duration homega S hS hduration hinside ha hinit
  intro j hj
  exact transfer_of_survivors_and_nonnegative_caps _ _ (survives j) (oldPoint j)
    (hkeep j hj) (hcap j hj)

end PoincareFlowChains
