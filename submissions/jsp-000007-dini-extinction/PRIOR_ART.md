# Attribution and prior-art limits

## Classical mathematics

The Poincare theorem is credited to Grigori Perelman, building on Richard
Hamilton's Ricci-flow program, as already recorded in the official catalog.
The relevant primary sources include Perelman's
[finite-extinction paper](https://arxiv.org/abs/math/0307245) and John Morgan
and Gang Tian's [Ricci Flow and the Poincare Conjecture](https://arxiv.org/html/math/0607607v2).
The latter supplies Lemma 2.22, Section 18.3.2, and Claims 18.21--18.22 used
for statement correspondence. The submitted analytic statements are not
claimed as new mathematical discoveries.

## Formalization antecedents

The implementation depends on the pinned Mathlib library, notably its
one-sided fencing theorem in `Mathlib/Analysis/Calculus/MeanValue.lean`,
C1-on-compact Lipschitz results, real powers, and derivative/asymptotic APIs.
Those library authors retain credit; using these components is not a claim
to have independently formalized all underlying analysis.

The starting Poincare repository was
`frenzymath/Poincare-Conjecture@bb91a091f0b968f8bbe8d861e025a88d82b161be`.
The submitted source is the same contribution published in
[`94e8e2d105155e21ca8a78716258c12d22b45562`](https://github.com/KunHcz/Poincare-Conjecture/tree/94e8e2d105155e21ca8a78716258c12d22b45562/PoincareConjecture)
and proposed to that repository in [PR #34](https://github.com/frenzymath/Poincare-Conjecture/pull/34).
The endpoint issue was recorded as [Issue #33](https://github.com/frenzymath/Poincare-Conjecture/issues/33).
These timestamps provide traceability, not an established prize-priority ruling.

At intake preparation on 2026-09-17, GitHub searches in the awards repository
for `JSP-000007` and `Poincare` returned no matching earlier entries. These
were bounded, index-dependent searches, not exhaustive global proof-library
searches. Absence of those matches does not establish novelty or priority.

## Eligibility request, not an eligibility assertion

The [published rules](https://www.hejustinsun.com/prize/rules) distinguish
verified closures, other contributions, and completion status. This package
requests assessment of the exact analytic formalization component, not the
Pinnacle closure of JSP-000007. In particular, the partial-progress wording
about parameter bounds or special cases is **not** asserted to automatically
cover formalization infrastructure.

Please determine whether this completed component is independently eligible,
whether a different entry scope is needed, and how a 2026 formalization of
previously established mathematics is handled. The applicant has not received
an authoritative eligibility or allocation decision for this contribution.
The earlier qualification question under awards PR #85 concerned another
problem; it is not an approval for this one.

This is an AI-assisted self-submission. The proposed formalizer remains
`RECIPIENT-jsp-000007-dini-extinction-A` pending confirmation. No formal
solver attribution for the Poincare theorem, external review signature, or
permanent independent archive is claimed.
