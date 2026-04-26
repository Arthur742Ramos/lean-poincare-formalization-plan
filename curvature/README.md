# PoincareCurvature

This subproject now covers the first three geometry layers of the broader
Poincare Conjecture roadmap in the parent repository.

## Proof standard

For this subproject, a roadmap point counts as complete only when the target
mathematics has been fully formalized and proved in Lean. Reusing existing
proved theorems from mathlib is fine; interfaces, axioms, `sorry`, and
scaffolding do not count as completion.

## What is here

- a Lean 4 + mathlib package pinned to a working toolchain
- `CovariantDerivative.along`, packaging the section `∇_X σ`
- `CovariantDerivative.contMDiff_along`, a first regularity theorem for that
  operation
- `CovariantDerivative.curvatureAux`, the raw curvature commutator
- alternating identities for the raw curvature commutator
- `CovariantDerivative.curvatureTensor`, packaging curvature fibrewise as a
  multilinear map
- `CovariantDerivative.ricciCurvature` and `CovariantDerivative.scalarCurvature`
  on the tangent bundle
- `CovariantDerivative.IsMetricCompatible`, a reusable metric-compatibility
  interface for Riemannian vector bundles
- tangent-bundle predicates `CovariantDerivative.IsTorsionFree` and
  `CovariantDerivative.IsLeviCivita`
- existence theorems producing Levi-Civita connections on the tangent bundle
- existence theorems producing global `C^1` Levi-Civita connections on the
  tangent bundle and slicewise `C^1` Levi-Civita families for time-dependent
  metrics
- a Levi-Civita uniqueness theorem at the current mathlib boundary:
  if two affine connections are torsion-free and metric-compatible, then their
  difference one-form vanishes
- existence of global `C^1` affine connections on `C^2` bundle data, together
  with the tangent-bundle specialization of that theorem
- first section-level `C^1` regularity lemmas for the Levi-Civita correction
  ingredients: `toDual`, fiberwise composition, metric-defect sections, and
  torsion sections on `C^2` vector fields
- `CovariantDerivative.sectionalCurvature` together with its numerator and
  denominator package
- first-Bianchi theorems for `curvatureAux` and `curvatureTensor`
- a raw second-Bianchi identity package on smooth tangent vector fields
- `CovariantDerivative.TimeFamily`, `TimeDependentSection`, and
  `TimeDependentCovariantDerivative` for one-parameter families
- evaluation, constant-family, and `ContMDiffInSpace` interfaces for those
  time-dependent objects
- `TimeDependentRiemannianMetric` for one-parameter families of smooth tangent
  bundle metrics
- family-level metric compatibility and Levi-Civita predicates
- slicewise Levi-Civita correction and existence for time-dependent metrics
- pointwise-in-time lifts of `along`, `curvatureAux`, `curvatureTensor`,
  metric-dependent `ricciCurvature`, `scalarCurvature`, and sectional
  curvature on the tangent bundle

## Roadmap status

Roadmap points 1, 2, and 3 are landed in this package as actual Lean
formalization.

Point 4 is **not** closed under the package standard: the current
`RicciFlow.LocalExistence` draft material is only a theorem boundary and not a
Lean proof of local existence/uniqueness. It is kept as an internal scaffold,
not as part of the public proof-bearing package surface. The next active
milestone is therefore still point 4 itself. The package does now include a
proof-bearing section-smoothing layer: local-to-global gluing for smooth
vector-bundle sections valued in fiberwise convex sets, trivial-bundle and
open-set smoothing, local smoothing in a fixed trivialization, and a global
smoothing theorem for continuous bundle sections constrained to open fiberwise
convex subsets of the total space, together with an intrinsic fiberwise-`ε`
approximation theorem for continuous sections of smooth Riemannian vector
bundles. It also now has a proof-bearing `C^0` coordinate layer for continuous
sections: local-frame continuity criteria, compact coordinate-map packaging,
compact overlap coordinate-change identities in `C(K, F)`, and cover-level
compatible coordinate families that determine the section on the covered
region. For finite compact covers with complete fiber model, those compatible
families now sit in a closed complete compatibility kernel inside the ambient
finite product of compact `ContinuousMap` spaces, continuous sections are
reconstructed from them by a proved finite-cover equivalence, and that
equivalence now transfers the induced additive, module, normed, and complete
structure to a dedicated continuous-section wrapper. Continuous and smooth
Riemannian metrics are also now packaged as honest sections of the bilinear-form
hom bundle, with extensionality lemmas reducing metric equality to pointwise
equality of fiberwise bilinear forms. The same public layer now also proves
finite-dimensional coercivity and operator-norm openness lemmas for
positive-definite continuous bilinear forms, giving the first fiberwise
open-neighborhood result needed for a section-space model of Riemannian
metrics, and lifts that result to compact coordinate families in `C(K, ·)` and
`BoundedContinuousFunction`, and then to the preferred finite-cover
`ContinuousSectionSpace` model, where actual positive-definite bilinear-form
sections form an open subset, the symmetric locus is now closed, and bundled
continuous Riemannian metrics lie in the refined symmetric positive-definite
locus inside that model; equivalently, the metric locus is now packaged as an
open subset of the closed symmetric section subtype. Separately, the internal
`Geometry.Manifold.RicciFlow.LocalExistence` scaffold now proves a stationary
Ricci-flat special case: a Ricci-flat initial metric with a chosen smooth
Levi-Civita connection yields a constant local Ricci-flow solution, and any two
such stationary constructions have the same evolving metric tensor and the same
connection on their common interval. It also now packages the same existence
statement through the new chosen smooth Levi-Civita witness, so callers no
longer need to supply that auxiliary connection separately in the stationary
Ricci-flat corollary, and it now packages that same stationary hypothesis as an
intrinsic `InitialValueProblem.IsRicciFlat` predicate with a canonical
stationary local solution built from it. It also now proves that any zero-velocity
local solution stays equal to the initial metric tensor and initial
Levi-Civita connection across its full interval, yielding uniqueness on the
common interval for zero-velocity local solutions, and therefore that any local
solution whose Ricci tensor vanishes across its full interval is stationary in
the same metric-and-connection sense as well. The same scaffold now also proves
that the Ricci tensor, Ricci-flow right-hand side, and Ricci-flow equation are
independent of the chosen Levi-Civita family for a fixed metric family, and it
now packages the matching intrinsic boundary
`intrinsicRicciTensor` / `intrinsicRicciFlowRHS` /
 `SatisfiesIntrinsicEquationAt` using the chosen smooth Levi-Civita witness. It
  also packages intrinsic `IntrinsicSolution` / `IntrinsicLocalSolution` /
  `IntrinsicLocalExistenceUniqueness` wrappers with conversions to and from the
  older connection-parametrized boundary, together with metric-only versions of
  the zero-velocity / intrinsic-Ricci-zero interval-stationarity theorems and the
  common-time connection-equality theorem. A new internal
  `Geometry.Manifold.RicciFlow.DeTurck` layer now packages the intrinsic DeTurck
  one-form, vector field, correction term, and gauge-fixed Ricci-DeTurck
  right-hand side, together with reduction lemmas showing that this gauge-fixed
  boundary agrees with intrinsic Ricci flow whenever the chosen background
  family is Levi-Civita for the evolving metric. That same file now also
  packages background-explicit intrinsic Ricci-DeTurck solution /
  local-solution wrappers, conversions from intrinsic Ricci-flow solutions using
  the chosen Levi-Civita family, and chosen-background Ricci-flat stationary
  comparison lemmas against arbitrary zero-velocity or intrinsic-Ricci-zero
  DeTurck local solutions with Levi-Civita background. It now also mirrors the
  common-time connection-equality consequences on that Levi-Civita-background
  DeTurck side and packages a chosen-background DeTurck local-existence /
  uniqueness theorem package equivalent to the current intrinsic Ricci-flow
  package. A further internal `Geometry.Manifold.RicciFlow.GaugeTransport` file
  now packages time-dependent bundled `C^1` self-map families together with
  pullback of tangent-bundle bilinear tensor fields and evolving metric tensors,
  proving identity, composition, symmetry-preservation, and initial-time
  invariance lemmas for that transport, and it also defines time-dependent
  gauge-flow / anchored-map predicates tying those pullbacks to integral-curve
  data. It now also packages bundled `C^1` self-diffeomorphisms and
  time-dependent diffeomorphism families, together with tangent pushforward /
  pullback maps and inverse lemmas for tangent-vector-field transport. The
  diffeomorphism pullback is now also identified with mathlib's manifold
  `VectorField.mpullback`, and a further internal `C^2` diffeomorphism layer
  now packages time-dependent `C^2` gauge families, proves that both pullback
  and pushforward preserve `C^1` tangent-vector-field regularity, and records
  the corresponding pointwise differentiability corollaries needed before
  defining affine-connection transport. A first internal
  `Geometry.Manifold.RicciFlow.GaugeReduction` wrapper now specializes those
  objects to the intrinsic DeTurck vector field and proves that anchored gauge
  pullbacks preserve the prescribed initial metric tensor for intrinsic
  Ricci-DeTurck local solutions; it also now includes a diffeomorphism-valued
  anchored DeTurck gauge wrapper reducing to the map-valued one. The same
  internal `C^2` diffeomorphism layer now also defines a bundled pullback of
  tangent-bundle covariant derivatives, proves inverse identities for
  pullback/pushforward of vector fields, identifies transport of `∇_X Y` under
  that pullback, proves the corresponding torsion transport formula, shows
  torsion-free affine connections remain torsion-free after pullback (under the
  ambient Riemannian tangent-bundle hypotheses already used by the Levi-Civita
  layer), transports affine-connection difference tensors, proves metric
  compatibility transport once a chosen target smooth metric is identified with
  the pulled-back inner product, lifts that result slice by slice to
  time-dependent `C^2` diffeomorphism/connection families, now also lifts
  torsion-free transport slice by slice to those pulled-back connection
  families, packages the actual pulled-back `C^1` Riemannian metric as a bundled
  `ContMDiffRiemannianMetric I 1`, upgrades the metric-compatibility transport
  theorem to use that concrete pulled-back metric, specializes the family
  metric-compatibility theorem slicewise to the same concrete pulled-back metric
  object, and now transports the raw curvature commutator under both static and
  family pullback of the connection. It also now transports
  `ricciEndomorphism` after applying `pushforwardTangent` and identifies
  pulled-back `ricciCurvature` with the trace of the tangent-map-conjugated
  endomorphism, again both statically and slice by slice for connection
  families. This is still not the full compact-manifold local
  existence/uniqueness theorem, so point 4 remains open; the next geometric
  blocker is now the extension-independence bridge from these raw
  curvature/Ricci transport formulas to genuine bundled Levi-Civita/Ricci
  transport, whose most direct wrapper statements currently time out.
  The public connection
layer now also closes the Levi-Civita regularity step: the package proves
existence of global `C^1` affine connections on `C^2` bundle data, exports that
result to the tangent bundle, provides section-level `C^1` regularity lemmas
for `toDual`, fiberwise composition, `metricDefectAux`, and torsion on `C^2`
vector fields (the torsion lemma currently uses a `C^3` manifold hypothesis),
proves that `leviCivitaConnection` preserves
`ContMDiffCovariantDerivative 1`, and packages both static and time-dependent
`C^1` Levi-Civita existence. Point 4 still remains open because the missing
pieces are now the extension-independence upgrade from the current raw
curvature/Ricci transport formulas to genuine target Levi-Civita/Ricci data
along the gauge flow, and the quasilinear parabolic PDE layer, not bundle
regularity.

## Build

From this directory:

```powershell
lake +leanprover/lean4:v4.29.1 build PoincareCurvature
```
