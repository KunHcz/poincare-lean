import CapFilling
import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps

open Function CategoryTheory
open scoped ContinuousMap

namespace PoincareConjecture

/-- The basepoint is allowed to move during the homotopy. Naturality of
the actual fundamental-groupoid map handles that transport, so no global
basepoint convention or unproved fundamental-group isomorphism is needed. -/
theorem simplyConnected_of_loop_generating_homotopic_factorization
    {X M Q : Type*} [TopologicalSpace X] [TopologicalSpace M] [TopologicalSpace Q]
    [SimplyConnectedSpace M] [PathConnectedSpace Q]
    (a : C(X, M)) (j : C(X, Q)) (R : C(M, Q))
    (H : j.Homotopy (R.comp a)) (x : X)
    (hsurj : Surjective (FundamentalGroup.map j x)) : SimplyConnectedSpace Q := by
  have hcomp (u : FundamentalGroup X x) : FundamentalGroup.map (R.comp a) x u = 1 := by
    have hmap : FundamentalGroup.map (R.comp a) x u =
        FundamentalGroup.map R (a x) (FundamentalGroup.map a x u) :=
      Path.Homotopic.Quotient.map_comp
    rw [hmap, show FundamentalGroup.map a x u = 1 from Subsingleton.elim _ _]
    exact (FundamentalGroup.map R (a x)).map_one
  have hone (v : FundamentalGroup Q (j x)) : v = 1 := by
    obtain ⟨u, rfl⟩ := hsurj v
    let η := FundamentalGroupoidFunctor.homotopicMapsNatIso H
    have hnatural := η.naturality
      (show FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk x from u)
    change FundamentalGroup.map j x u ≫ η.app (FundamentalGroupoid.mk x) =
      η.app (FundamentalGroupoid.mk x) ≫ FundamentalGroup.map (R.comp a) x u at hnatural
    rw [hcomp] at hnatural
    apply (cancel_mono (η.app (FundamentalGroupoid.mk x))).mp
    exact (hnatural.trans (Category.comp_id _)).trans (Category.id_comp _).symm
  letI : Subsingleton (FundamentalGroup Q (j x)) :=
    ⟨fun v w => (hone v).trans (hone w).symm⟩
  exact simplyConnected_of_fundamentalGroup_subsingleton (j x)

end PoincareConjecture
