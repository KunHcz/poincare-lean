# Exact formal claim and relation to JSP-000007

## Original problem and scope boundary

JSP-000007 asks whether every closed, simply connected three-manifold is
homeomorphic to the three-sphere. This package **does not prove that statement**.
It does not construct Ricci flow with surgery, define a geometric min-max width,
derive that width's differential inequality, identify its surgery transport,
or reconstruct the final three-manifold topology.

The completed objects are real-analysis components used in the primary
Poincare blueprint. Their ordinary mathematical antecedents are Morgan--Tian,
*Ricci Flow and the Poincare Conjecture*, Lemma 2.22 and Section 18.3.2.
The implementation, endpoint correction, proof assembly, and regression
evidence are the submitted formalization contribution.

This is not presented as a new parameter bound or a newly solved family of
three-manifolds. Whether a completed analytic component within the larger
formalization is separately eligible is a question for the prize operator.

## 1. Forward Dini comparison

[RightDini.lean](PoincareConjecture/Analysis/RightDini.lean) defines
`UpperRightDiniLE f t c` as: for every real `r > c`, the secant slope
`(f(z)-f(t))/(z-t)` is eventually less than `r` as `z` approaches `t` from
the right. There is no differentiability hypothesis on `f`, nor a real-valued
limsup convention that silently imposes boundedness.

`PoincareConjecture.dini_le_of_contDiffOn` proves:
if `f` and `G` are continuous on `[a,b]`, `ψ` is C1 within `[a,b] × R`,
`D+f(t) ≤ ψ(t,f(t))` on `[a,b)`, `G` has right derivative `ψ(t,G(t))`
there, and `f(a) ≤ G(a)`, then `f(t) ≤ G(t)` throughout `[a,b]`.

The one-sided Lipschitz estimate is derived on a compact rectangle containing
both graphs. It is not inserted as a substitute for the stated C1 hypothesis.
The proof uses the strict barrier `G(t) + ε exp((L+1)(t-a))` with Mathlib's
one-sided fencing theorem and then lets `ε` decrease to zero.

## 2. Finite jumps, including the terminal endpoint

[FiniteJumps.lean](PoincareConjecture/Analysis/FiniteJumps.lean), theorem
`PoincareConjecture.dini_le_of_finite_jumps`, replaces continuity of `f` on
the entire interval by continuity on each `[τ(j),τ(j+1))`, for a finite
partition strictly increasing only on `0,...,n`. It retains the preceding
Dini/ODE conditions and assumes no upward jump at **every** right endpoint:

```lean
∀ j < n, LowerSemicontinuousWithinAt f (Iio (τ (j + 1))) (τ (j + 1))
```

This says that each value is no greater than its left liminf; it allows
oscillation and does not require an actual left limit. The conclusion is the
closed-interval comparison, including `τ(n)`. The zero-segment case is included.

The original upstream blueprint constrained only interior endpoints. Its
closed-interval conclusion fails for `ψ = G = 0` and `f(t)=0` for `t<1`,
`f(1)=1` on `[0,1]`. The regression theorem
`PoincareConjectureTests.endpoint_control_is_necessary` formalizes this
counterexample. Other regression theorems verify comparison for a downward
step at an interior point and prove that the step is genuinely discontinuous.
This is a blueprint gap, not an error attributed to Perelman's proof.

## 3. Scalar lifetime bound

[ScalarBarrier.lean](PoincareConjecture/Extinction/ScalarBarrier.lean) defines

```text
extinctionRHS(t,w) = -2π + 3w/(1+4t)
C(s,A) = (A + 2π(1+4s))/(1+4s)^(3/4)
extinctionBarrier(s,A,t) = C(s,A)(1+4t)^(3/4) - 2π(1+4t).
```

The initial value and derivative are explicitly checked for the stated
nonnegative time domain. Eventual negativity follows from
`(1+4t)^(-1/4) → 0`, not from numerical sampling.

The final production theorem is
`PoincareConjecture.exists_width_lifetime_bound`:
for every `s ≥ 0` and real initial bound `A`, there is `T > s` such that,
for **any** real function `W`, finite partition `τ` and length `n`, if
`τ(0)=s`, `T ≤ τ(n)`, the partition is strict, `W` has the half-open
continuity and no-upward-jump conditions above, its upper right Dini
derivative is bounded by `extinctionRHS(t,W(t))`, and `W(τ(0)) ≤ A`, then
`W(τ(n)) < 0`.

Consequently a nonnegative width satisfying those assumptions cannot survive
to that time. The theorem's time bound is chosen **before** `W`, `τ`, and
`n`, so it is uniform in all surgery partitions. The geometric production
of such a width remains outside this submission, explicitly as hypotheses
rather than disguised definitions or added axioms.

## Trusted and unproved material

The source inventory is all 15 production theorems listed in
[verification-config.json](verification-config.json). No production source
imports `Mathlib.Geometry.Manifold.PoincareConjecture` or invokes its
`proof_wanted` declaration. No claim relies on an axiom for the final theorem.
The namespace-wide audit in the default test build rejects any transitive
axiom other than `propext`, `Classical.choice`, and `Quot.sound`.

Proposed completed scope: three analytic components. Not proposed: full or
substantial resolution of the original JSP-000007 proposition. No percentage
completion of the full formalization is assigned.
