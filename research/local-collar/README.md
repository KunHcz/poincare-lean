# A uniform collar from local inverse-function data

This component constructs a single positive-width open collar from a
continuous family with an injective compact zero section and local inverse
data at each point of that section. The width, global injectivity strip,
open collar and subsequent separating regions are not premises. It also
uses the real inverse function theorem to obtain the local data from actual
invertible coordinate derivatives, including ordinary C1 hypotheses.

It is **not** a collar-existence theorem for every embedded sphere, and it
does not complete the original Poincare theorem. A transverse family with
the required pointwise properties still has to be produced for a general
embedded sphere. The current prize rules exclude intermediate results, so
this component stays in the external research repository.

## Exact topological input and output

Let `S` be compact, `M` Hausdorff, and

```text
f : S × R → M
```

be a genuine continuous function. Its zero section `s ↦ f(s,0)` is injective.
At each `(s,0)`, there is an actual open neighbourhood on which the
restriction of the original `f` is an open embedding. Those neighbourhoods
may depend on `s`; no common width or global injectivity is assumed. These
conditions are exposed as `HasLocalOpenChartsAtZero`.

`exists_uniform_openEmbedding_band` produces `r > 0` such that `f` is an
open embedding on `S × (-r,r)`. Rescaling by the actual positive scalar `r`
gives `exists_scaled_open_collar` on the standard domain `S × (-1,1)`.
`scaledCollar_zero` checks that its central embedding is exactly the original
zero section, not a replacement sphere.

The compactness argument treats every pair of zero-section points. Near a
coincident pair, local injectivity rules out collisions. Near a distinct
pair, continuity and Hausdorff separation of their different images do the
same. Compactness of `S × S` makes that pairwise neighbourhood uniform.
A second compactness argument places the same sufficiently thin band inside
the union of local charts. There the restricted map is a local
homeomorphism; global injectivity makes it an open embedding.

In a compact, simply connected, locally path-connected Hausdorff ambient
space, `local_family_separates_and_caps` applies this construction with
`S = S²` to the previously verified separation and capping chain. It
produces two nonempty path-connected open sides, a parameterization of
their actual common spherical boundary, and simple connectivity of both
standard ball-capped sides.

## Differential input is checked, not renamed as a local inverse

`local_open_chart_of_strict_coordinate_derivative` starts with actual
partial-homeomorphism coordinates `a` and `b` around a source point and its
image, and the strict derivative of the literal function

```text
b ∘ f ∘ a⁻¹.
```

If that derivative is a continuous linear equivalence between the Banach
model spaces, Mathlib's inverse function theorem constructs its local
inverse. The proof restricts the source to points whose images really lie
in the target coordinate chart, composes the actual partial homeomorphisms,
and checks that the resulting open embedding is the original `f`.

`exists_collar_of_C1_coordinates` derives strict differentiability from
ordinary C1 coordinate regularity and the actual invertible derivative.
`coordinate_derivatives_separate_and_cap` connects the corresponding strict
coordinate data directly to the sphere separation/capping endpoint.

The coordinate maps are explicit open partial homeomorphisms; the component
does not silently assert they belong to an unspecified smooth atlas. For a
geometric application the caller must supply the actual family and valid
coordinates/derivative statements in its intended manifold structure. No
smooth normal field, exponential map, transverse vector-field flow, or
local family for an arbitrary smooth sphere is constructed here. These
remaining input-production obligations are distinct from the now-proved
local-to-global collar step.

## Concrete models and counterexamples

The new component has 17 named production theorems and 11 named regression
theorems, in addition to its explicit maps and homeomorphisms. Reused theorem
declarations are not counted as new results.

The full topological endpoint is tested on the genuine compact cylinder
`S² × [-2,2]` using the family `(s,t) ↦ (s, clip(t,-2,2))`. This family is
proved **not globally injective**. Actual local charts near its zero section
are verified, and the theorem chooses the uniform collar radius and derives
both capped conclusions. The cylinder has boundary; it is not presented as
a closed Poincare manifold or an example of Ricci surgery.

Two independent geometric failures are formalized. The folded family
`((),t) ↦ t²` has collisions on every positive-width band, demonstrating
the role of local invertibility. The two-sheet family `(b,t) ↦ t` for
`b : Bool` has genuine local charts but different zero-section sheets
coincide; it too has no injective positive-width band. Thus a mere
continuous map or local inverse without the embedded zero section is not
enough.

The differential bridge is tested on `x ↦ x+x²`: it is proved globally
noninjective, while its actual derivative `1` at zero yields a local open
chart through the proved inverse-function bridge. A separate concrete
three-dimensional model instantiating every coordinate-derivative premise
of the final differential endpoint is not included; the evidence records
that limit rather than treating the scalar test as such a model.

## Reproduce and inspect

```sh
cd research/local-collar
lake exe cache get
python3 -m unittest -v test_verify
python3 verify.py
```

Lean is `v4.32.1`, compiler `f054605aea4b840552cca2e725580bffd1e1b704`,
Mathlib is `520045ab14e26149ee970e2e617ca04b09bde5d6`, and the Hatcher
reference is `bb91a091f0b968f8bbe8d861e025a88d82b161be`. All dependency
revisions and tracked-file states are checked before and after execution.
The 13 reused proof/model files remain byte-identical to the previous
`collar-separation` component. Earlier snapshots and their evidence are not
rewritten.

The verifier builds all default targets, prints the elaborated endpoint
types and definitions of the supplied conditions, and audits every new
named theorem. The default Lean audit also traverses all new and reused
proof namespaces. Extra axioms, placeholders, removal of compactness,
Hausdorffness, zero-section injectivity or local invertibility, and an
unproved coordinate derivative are all required to be rejected.

The complete `leanchecker --verbose --fresh LocalCollarAudit` replay is
performed before writing the [success record](evidence/verification.json).
This is Lean's own kernel, not independently implemented checker software
or designated expert review. Compiled dependency caches may be reused; a
clean rebuild of every dependency is not claimed. The known unchanged
Hatcher `unitCircleCov` style warning is recorded explicitly; unrelated
diagnostics fail verification.

## Attribution and complete-proof status

The arguments are classical compactness and inverse-function mathematics,
not a new discovery of the Poincare proof. The underlying Lean, Mathlib and
Hatcher code retains its authorship, including the proved van Kampen and
covering-space results inherited from the earlier components. See
[NOTICE](NOTICE).

The original full Poincare target and submission gate remain unchanged.
Producing the transverse geometric family, general Ricci surgery and its
curvature/continuation control, geometric width and finite extinction,
connected-sum reconstruction and the three-dimensional topological-to-smooth
bridge remain unproved by this component. No formalization priority,
official acceptance, prize eligibility, award tier or payment is asserted.
