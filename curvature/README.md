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

Point 4 is **not** closed in full generality under the package standard: the
current `RicciFlow.LocalExistence` material does not yet prove compact
Ricci-flow local existence/uniqueness in arbitrary dimension. It is kept as an
internal scaffold, not as part of the public proof-bearing package surface.
The next active milestone is therefore still the general point-4 theorem.
The scaffold now contains proof-bearing stationary theorem packages for
subsingleton tangent/model spaces and for rank-one tangent/model spaces
(`Module.finrank ℝ E ≤ 1`), plus a thin `LocalExistence.RankOne` extension
showing that every rank-one local solution has zero metric velocity, is
stationary in metric components, and has the same Levi-Civita connection on
overlaps. The package also includes a
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
sections form an open subset, the symmetric locus is now closed, and a
transported continuous-linear coordinatewise antisymmetric-defect map has
exactly that symmetric locus as its kernel. Bundled continuous Riemannian
metrics lie in the refined symmetric positive-definite locus inside that model;
equivalently, the metric locus is now packaged as an open subset of the closed
symmetric section subtype. Separately, the internal
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
   families. A thin
   `Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowDerivative`
   module now names the primitive `C^3` intrinsic gauge-flow derivative data,
   proves it equivalent to the geometric `SatisfiesGaugeFlowOn` formulation, and
   packages the corresponding chosen-DeTurck-solution family interface and a
   reusable gauge-flow family bundle with anchored-gauge projections and direct
   gauge-reducible/intrinsic/ordinary theorem-family projections from
   pulled-back metric time-derivative data, plus a fixed-initial-value-problem
   bundle with matching local theorem-package projections. Both bundle levels
   now also extract the scalar inner-product derivative data from the same
   gauge-pulled metric time-derivative proof. The
   gauge-reduction layer also now closes the identity `C^3`
   gauge-reducibility path for chosen Levi-Civita-background DeTurck theorem
   families, including the explicit scalar-derivative gauge-reducible interface
   and direct identity-`C^3` gauge-reduced wrappers with source/metric/velocity
   simplification lemmas; it also exposes a raw non-identity gauge-flow route
   from `C^3` diffeomorphism families, anchoring, the gauge-flow equation, and
   scalar inner-product derivative identities to the same scalar-derivative
     theorem-family package, with bundled global/interval endpoint data objects
     using that named gauge-flow derivative family and
    projecting to scalar-derivative, intrinsic, and ordinary theorem families. A
    separate `AnalyticPDE.GeometricGaugeFlow` module now also gives matching
    global/interval endpoint bundles for geometric `C^3` gauge-flow families plus
    pullback-time-derivative proofs, deriving the scalar endpoint internally and
    projecting through the derivative bundles to scalar, gauge-reducible,
    intrinsic, and ordinary theorem families; it also exposes a fixed-IVP
    endpoint bundle and a family-to-fixed-IVP projection. A new
    `GaugeReduction.Diffeomorph3FlowExistence` layer names the raw `C^3`
    diffeomorphism-flow existence witness expected from the manifold ODE theorem
    and converts it into the fixed-IVP and theorem-family geometric gauge-flow
    bundles, and geometric endpoint data can now replace its bundled gauge-flow
    component by such a raw existence witness at fixed-IVP, global, and
    interval scope. A thin `AnalyticPDE.SmoothRealization` module names the
    global/interval PDE closure data that turns a Banach chart solution into a
    smooth chosen-background DeTurck solution and its self-encoding candidate:
    metric realization, boundary time derivatives, chart-RHS/geometric-RHS
    identification, and chosen Levi-Civita background; it also packages the
    all-solutions smooth-realization plus reverse-candidate-encoding closure
    into direct global/interval chosen-background DeTurck theorem packages. The optional
   `PoincareCurvature.RicciFlowLocalExistence` aggregate now
   imports this gauge-reduction boundary plus the `AnalyticPDE` evolution layer proving the reusable
   Picard-Lindelof Banach-evolution local-solution core, open-state
   state-preserving uniqueness, a positive-definite finite-cover metric-locus
   bridge, an abstract continuous-linear symmetry/fixed-locus preservation
   theorem for later slot-swap symmetry, and a direct continuous-linear
   antisymmetric-defect criterion that keeps solutions in the symmetric
   positive-definite locus once the vector field's coordinatewise defect
   vanishes, plus a direct global-geometric-to-interval-defect chart adapter
   and a pointwise-symmetric-vector-field variant that supplies that defect
   vanishing automatically; the global metric-reification and chosen-background
   package constructors now take their witnesses through this terminal defect
   route, and globally Lipschitz charts expose terminal-bounded
   continuous-metric and metric-curve reification endpoints directly, plus a
   direct bounded candidate-encoding witness for the associated interval chart
   and global/local-family chosen-background routes that can consume those
   interval-bounded encodings without rebuilding global encodings; the direct
   global intrinsic Ricci-flow endpoint also accepts the same interval-bounded
   encodings, and the global gauge-reducible and scalar-inner-derivative gauge
   packages, including their theorem-family and direct intrinsic-family
   projections, can now be built from them; smooth Banach realizations can now
   reduce the closed-interval time-derivative boundary, including at the global
   and interval chosen-background theorem-package surfaces and the corresponding
   local/family non-identity gauge-time-derivative intrinsic Ricci-flow endpoints,
   to the two endpoint derivative statements; the global and interval charts also
   expose reusable single-solution and theorem-family endpoint-to-boundary
   derivative adapters, and the raw global/interval non-identity gauge-flow
   time-derivative theorem-family endpoints now consume only endpoint
   time-derivative data before the gauge-flow conversion; encoded candidates in
   the same global or interval chart now have a named metric-uniqueness theorem
   on their common interval.
   The same state-set mechanism now also has a
   non-autonomous Picard-Lindelof specialization: time-dependent Banach-chart
   vector fields satisfying the verified Picard/Lipschitz hypotheses shrink to
   positive-definite local metric evolutions and, when identified pointwise with
   the intrinsic Ricci-DeTurck RHS, remain symmetric by the proved geometric
   symmetry theorem. This time-dependent Ricci-DeTurck bridge is also bundled as
   `TimeDependentGeometricRicciDeTurckBanachChart`, whose fields are precisely
   the remaining Picard/Lipschitz/geometric-agreement obligations and whose
   extractor produces the symmetric positive-definite local Banach metric
   evolution. The reverse metric bridge is now proof-bearing as well: any
   finite-cover symmetric positive-definite section-state reifies to a bundled
   continuous Riemannian metric, and the packaged Banach solution now exposes one
   metric-valued curve whose local-interval inner products agree with the Banach
   section curve, whose initial value is the original initial metric, and whose
   common-interval uniqueness follows from Banach uniqueness. For autonomous
   charts, a new local `C^1` reduction also shrinks to an open neighborhood
   inside the positive-definite metric locus and derives the needed local
   Lipschitz bound there, so chart estimates can be proved locally around the
   initial metric instead of globally on the whole metric locus; for
   non-autonomous charts, the lower-level positive-definite and symmetric
   bridges, plus the reusable
   `TimeDependentGeometricRicciDeTurckBanachChartOnIcc` package, now accept
   Lipschitz estimates restricted to the verified Picard time interval and
   expose the constructed solution's `terminalTime ≤ T` bound. A
   smooth-realization adapter packages the exact remaining
   lift/time-derivative/DeTurck-equation obligations needed to turn such a
   Banach solution into an `IntrinsicDeTurckLocalSolution`; when supplied for a
   smooth-IVP-seeded chart solution it extracts that DeTurck local solution, and
   two such smooth realizations have equal metric tensors on common intervals.
   The interval chart also has a bounded candidate-encoding theorem: candidates
   whose Banach representatives satisfy `terminalTime ≤ T` promote all the way
   to `IntrinsicDeTurckLocalExistenceUniqueness`, the identity-gauge intrinsic
    Ricci-flow package, the non-identity gauge-reducible package, and the
    explicit scalar-inner-derivative gauge package using only `Icc`-restricted
    Lipschitz control; the chosen-background identity, arbitrary-background
    identity, gauge-reducible, and scalar-inner-derivative gauge routes now
    preserve the stronger arbitrary-background DeTurck, chosen-background
    DeTurck, and gauge theorem-family packages before exposing
     `IntrinsicLocalExistenceUniquenessFamily` extractors, and the finite-cover
     section-space completeness obligation is now inferred from the existing
     `ContinuousSectionSpace` complete-space instance instead of being carried as
     a chart field.
   With the explicit reverse-chart encoding for arbitrary or chosen-background
   candidates, the same package now promotes to
   `IntrinsicDeTurckLocalExistenceUniqueness`,
   `ChosenIntrinsicDeTurckLocalExistenceUniqueness`, and then to intrinsic
   Ricci-flow local existence/uniqueness either by the chosen-background identity
   route or by the non-identity gauge-reducibility package; the global-chart
   family theorem produces `IntrinsicLocalExistenceUniquenessFamily` once these
   chart, realization, encoding, and gauge-reducibility obligations are supplied
   for every initial value problem. It also specializes these criteria to genuine
   bundled continuous Riemannian initial metrics, so future Ricci-DeTurck
   Banach-chart work no longer has to manually prove finite-cover metric-locus
   membership for the initial datum. The interval chart now derives the
   genuine symmetric-carrier vector field from the ambient Ricci-DeTurck chart:
   geometric RHS symmetry proves tangency to symmetric bilinear forms, and the
   ambient interval Lipschitz estimate descends to the restricted metric-locus
   vector field. The ordinary, intrinsic,
   chosen-background, gauge-reduced, and scalar-derivative theorem families now
   expose package-level connection uniqueness on common intervals. This is still
   not the full compact-manifold local existence/uniqueness theorem, so point 4
   remains open; the remaining geometric/analytic blockers are the raw
   non-identity gauge-flow obligations and the quasilinear parabolic PDE layer,
   including the
   actual Ricci-DeTurck Banach chart and Picard estimates on the restricted
   symmetric carrier plus the identification of that Banach representative with
   the geometric Ricci-DeTurck right-hand side. Item 2 of those obligations (raw
   `C³` gauge-flow existence) is now closed in four special cases via dedicated
   `IntrinsicDeTurckGaugeFlowExistence(.Family)` constructors:
   `identityOfChosenBackground`, `identityOfSubsingletonTangent`,
   `identityOfSubsingletonModel`, and `identityOfIsEmpty`, each accompanied by a
   matching `_hpullDerivative` time-derivative lemma. Two new thin extension
   modules also fill API gaps: `LocalExistence/RankOneDeTurck.lean` provides
   `chosenIntrinsicDeTurckLocalExistenceUniqueness(.Family)_of_finrank_le_one`
   and the model-space synonym, while `LocalExistence/IsEmptyDeTurckFamily.lean`
   supplies the empty-manifold parallels of the existing
   `_of_subsingleton_tangent` family conversions between
   `IntrinsicLocalExistenceUniquenessFamily`,
   `ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily`, and
   `IntrinsicDeTurckLocalExistenceUniquenessFamily`. See
   `docs/point4-plan.md` for the systematic decomposition of the three
   remaining items.
   The curvature, time-dependent geometry, intrinsic Ricci-flow, and DeTurck
   layers now prove the geometric symmetry input outright: metric compatibility
   gives curvature-operator skew-adjointness, torsion-freeness gives first
   Bianchi, the Ricci contraction is symmetric for Levi-Civita families, the
   intrinsic Ricci-flow RHS is symmetric, and the full intrinsic Ricci-DeTurck RHS
   is symmetric because the DeTurck correction term itself is symmetric.
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

The heavier Ricci-flow local-existence scaffold is intentionally kept
out of the root target for faster routine iteration. Build it explicitly when
working on that layer:

```powershell
lake +leanprover/lean4:v4.29.1 build PoincareCurvature.RicciFlowLocalExistence
```
