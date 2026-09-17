# Additive topology extension to the same JSP-000007 submission

This supplement extends the completed formalization scope submitted in this
PR. It does **not** submit a second claim for the original analytic work and
does **not** assert a completed Poincare theorem or an established award.
The original 15-theorem analytic package and its verification snapshot remain
unchanged. The extension is supplied as an immutable public upstream source
with a separate executable verifier and evidence record.

## Exact additional mathematical results

The source is
[`KunHcz/Poincare-Conjecture@f07c59b825f344fa7577907f2427e0aad47704a1`](https://github.com/KunHcz/Poincare-Conjecture/tree/f07c59b825f344fa7577907f2427e0aad47704a1/PoincareConjecture).
It is the same applicant's contribution proposed to
[upstream PR #34](https://github.com/frenzymath/Poincare-Conjecture/pull/34).

Three additional endgame components are proved:

1. **A simply connected spherical space form is diffeomorphic to the standard
   three-sphere.** The input is an actual finite free continuous action on the
   sphere and its orbit quotient, optionally together with a smooth presentation
   of the manifold as that quotient. Path-lifting monodromy proves the acting
   group trivial. Smooth transition maps, the actual quotient projection, and
   local inverse branches are proved smooth for the canonical quotient atlas;
   they are not inserted as replacement assumptions.
2. **The two standard sphere-bundle models have infinite cyclic fundamental
   group.** The construction uses the actual integer-action mapping torus,
   establishes its quotient covering, and computes the fundamental group at
   every basepoint. The untwisted model is explicitly homeomorphic to
   `Sphere2 × Circle`; the twisted model uses the antipodal map of the actual
   two-sphere. The integer action is free because it translates the real
   coordinate, not because freeness is postulated.
3. **Trivial free products have trivial factors.** The proof uses Mathlib's
   actual indexed free product and its verified canonical injections. It also
   gives basepoint-change and simple-connectivity adapters and excludes
   infinite cyclic factors. A geometric connected-sum fundamental-group
   decomposition is **not** proved or silently substituted by this algebra.

The full extended source has **45 production theorems**: the original 15 plus
30 added theorem declarations. It also includes proof-bearing homeomorphism,
diffeomorphism and group-isomorphism definitions, which are not counted as
theorem declarations. These are six checked nodes in the larger blueprint,
not a percentage estimate of progress toward the full Poincare proof.

The authoritative statement correspondence and remaining hypotheses are in
[the pinned topology validation document](https://github.com/KunHcz/Poincare-Conjecture/blob/f07c59b825f344fa7577907f2427e0aad47704a1/PoincareConjecture/TOPOLOGY_VALIDATION.md).

## Reproduce the extension independently of the original package

With the pinned Lean toolchain available through elan:

```sh
cd submissions/jsp-000007-dini-extinction
python3 -m unittest discover -s scripts -p 'test_*.py' -v
python3 scripts/verify_topology_extension.py
```

The extension verifier fetches the immutable source into its own ignored
directory. It never updates an existing checkout to another revision and
does not replace the original package's Lean files. To use an existing clean
checkout at the exact pinned commit, pass `--checkout /path/to/checkout`.

It checks the compiler version and every manifest dependency's revision and
tracked-source cleanliness, runs the upstream default build, audits all 45
production theorems, and runs a fresh-environment replay of the full imported
and local test graph:

```sh
lake env leanchecker --verbose --fresh PoincareConjectureTests
```

The default test graph additionally audits every declaration in the production
and regression namespaces. Injected project axioms, an injected placeholder
proof, and removal of the finite action's freeness assumption must all be
rejected. Seven new verifier unit tests cover missing/duplicate axiom output,
nonstandard axioms, wrapped output and diagnostic formats, alongside the
original six verifier tests.

The exact source uses Lean 4.32.1 and Mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6`. The reused Hatcher sphere proof is
pinned to the reference subdirectory at
`bb91a091f0b968f8bbe8d861e025a88d82b161be`. One existing style warning about
`unitCircleCov` in that unchanged Hatcher revision is disclosed and allowed;
all other build warnings fail the extension verifier.

See [the extension verification record](evidence/topology-extension/verification.json),
[the complete explicit axiom log](evidence/topology-extension/axioms.log), and
[the fresh replay log](evidence/topology-extension/kernel-replay.log).
Only a completed verification record with status
`LOCAL_VERIFIED_NOT_OFFICIALLY_REVIEWED` represents successful local validation;
an in-progress record is not success.

## Scope, provenance and award request

The statement `PoincareConjecture.TopologicalPoincareStatement` records the
full topological target without positive-Ricci, smooth-atlas, spherical-model
or surgery-existence hypotheses. It is a **definition of the target, not a
proof**. The general surgery-flow construction, geometric width inequality,
finite-extinction argument, connected-sum reconstruction and the
three-dimensional smoothability bridge are not supplied by this extension.

These are formalizations of classical mathematics, not newly discovered
solutions. Perelman, Hamilton, Morgan--Tian, Hatcher and the relevant Mathlib
and reference-project authors retain their mathematical and library credit.
In particular, the existing Hatcher proof of simple connectivity of spheres
is reused, not claimed as this applicant's new work. See also
[the original prior-art disclosure](PRIOR_ART.md).

The new verification is an incremental dependency build followed by fresh
Lean-kernel replay. It is not a complete from-source dependency rebuild, an
independently implemented proof checker, designated human review, or permanent
independent archival. The award repository's record CI does not execute this
Lean verifier and does not determine mathematical acceptance.

We ask the prize operator to assess the independently completed scope of
these analytic and topological components as a formalization/community
contribution, and to direct it to a different entry scope if required. No
particular tier, amount, eligibility, allocation, priority or solver share for
the full Poincare theorem is asserted. The self-submission and conflict of
interest disclosure remain unchanged, as does the provisional placeholder
`RECIPIENT-jsp-000007-dini-extinction-A`. No candidate or award record,
recipient profile, review signature, or announcement is modified.
