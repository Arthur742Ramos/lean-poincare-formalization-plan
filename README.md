# Lean Formalization Roadmap for the Poincare Conjecture

This repository is a working plan for a serious Lean formalization effort around
the 3-dimensional Poincare Conjecture, with the proof route understood as
Perelman's Ricci-flow-with-surgery program.

The point of this repo is not to claim that the theorem is already formalized.
It is not. The goal here is to break the project into chunks that are large
enough to be independently meaningful, and in many cases paper-worthy in the
style of the Annals of Formalized Mathematics.

## Contents

- `docs/roadmap.md`: the main roadmap, with AFM-scale project slices
- `docs/dependencies.md`: dependency structure and a suggested execution order
- `curvature/`: Lean/mathlib subproject for the front-end connection and
  curvature layers of the roadmap

## Current framing

The roadmap assumes:

- public Lean/mathlib does not yet contain a completed formal proof of the
  Poincare Conjecture
- the real difficulty is not just the final theorem, but the missing geometric
  analysis infrastructure required to even state Perelman's arguments cleanly
- several intermediate deliverables would already be major formalization papers

## Completion standard

A roadmap point counts as complete only when the target mathematical statements
have been fully formalized and proved in Lean. Reusing existing theorems from
mathlib or other Lean libraries is completely acceptable; what matters is that
the final result is backed by actual Lean proofs.

The following do **not** count as completing a roadmap point on their own:

- interfaces or theorem boundaries without proofs
- added axioms or unchecked assumptions
- `sorry` or any other placeholder proof term
- documentation-only or API-only scaffolding

So throughout this repository, “done” means **proved**, not merely packaged or
anticipated.

## Scope

This is intentionally a research-program repository, not an implementation
repository.

The current exception is `curvature/`, which now contains a concrete Lean
package for covariant derivatives along vector fields, the raw curvature
commutator, a bundled curvature tensor, Ricci/scalar curvature, metric
compatibility, Levi-Civita existence and uniqueness, sectional curvature, the
first and second Bianchi identities, and a time-dependent geometry layer for
one-parameter families of sections, connections, smooth metrics, Levi-Civita
families, curvature quantities, and a proof-bearing section-smoothing layer:
local-to-global gluing for smooth vector-bundle sections valued in fiberwise
convex sets, trivial-bundle and open-set smoothing theorems, local smoothing in
bundle trivializations, and a global theorem smoothing continuous bundle
sections while staying inside open fiberwise convex subsets of the total space,
as well as an intrinsic fiberwise-`ε` approximation theorem for continuous
sections of smooth Riemannian vector bundles. There is also an internal
preparatory Ricci-flow local-existence scaffold module, but it is not part of
the public package boundary and does **not** count as completing point 4 under
this repository's proof-only standard, even though it now contains genuine
stationary Ricci-flat, zero-velocity, and Ricci-tensor-zero special-case
theorems at both the metric and Levi-Civita-connection levels, including
theorem-family packages under subsingleton tangent/model hypotheses and the
rank-one-or-less model hypothesis `Module.finrank ℝ E ≤ 1`; the thin
`LocalExistence.RankOne` extension further proves that every rank-one local
solution has zero metric velocity, stays equal to its initial metric, and has
the same Levi-Civita connection on overlaps. It also now proves that, once a
connection
family is known to be Levi-Civita for a metric family, the Ricci tensor,
Ricci-flow right-hand side, and Ricci-flow equation are independent of which
Levi-Civita family is used, and it packages intrinsic metric-only solution /
local-solution / compact theorem-package wrappers with conversions to and from
the older connection-parametrized boundary. The same intrinsic side now also
packages the canonical stationary local solution attached to
   `InitialValueProblem.IsRicciFlat`, together with metric-only comparison lemmas
   against arbitrary intrinsic zero-velocity or intrinsic-Ricci-zero local
   solutions. A new internal `Geometry.Manifold.RicciFlow.DeTurck` layer also
   packages the intrinsic DeTurck one-form, vector field, correction term, and
   gauge-fixed Ricci-DeTurck right-hand side, together with reduction lemmas
   showing that this gauge-fixed equation collapses back to intrinsic Ricci flow
   whenever the chosen background family is Levi-Civita for the evolving metric.
   That same DeTurck side now also packages background-explicit intrinsic
   Ricci-DeTurck solution / local-solution wrappers, conversions from intrinsic
   Ricci-flow solutions using the chosen Levi-Civita family, and chosen-background
   Ricci-flat stationary comparison lemmas against arbitrary zero-velocity or
   intrinsic-Ricci-zero DeTurck local solutions with Levi-Civita background. It
   now also mirrors the common-time connection-equality consequences on that
   Levi-Civita-background DeTurck side and packages a chosen-background DeTurck
   local-existence/uniqueness theorem package equivalent to the current intrinsic
   Ricci-flow package. A further internal
  `Geometry.Manifold.RicciFlow.GaugeTransport` layer now packages time-dependent
  bundled `C^1` self-map families together with pullback of tangent-bundle
  bilinear tensor fields and evolving metric tensors, proving identity,
  composition, symmetry-preservation, and initial-time invariance lemmas for
  that transport, and it also defines time-dependent gauge-flow / anchored-map
  predicates tying those pullbacks to integral-curve data. It now also packages
  bundled `C^1` self-diffeomorphisms and time-dependent diffeomorphism families,
  together with tangent pushforward / pullback maps and inverse lemmas for the
  induced transport of tangent-vector fields. The diffeomorphism pullback is now
  also identified with mathlib's manifold `VectorField.mpullback`, and a further
  internal `C^2` diffeomorphism layer now packages time-dependent `C^2` gauge
  families, proves that both pullback and pushforward preserve `C^1`
  tangent-vector-field regularity, and records the corresponding pointwise
  differentiability corollaries needed before defining affine-connection
  transport. A first internal
  `Geometry.Manifold.RicciFlow.GaugeReduction` wrapper now specializes those
  objects to the intrinsic DeTurck vector field and proves that anchored gauge
  pullbacks preserve the prescribed initial metric tensor for intrinsic
  Ricci-DeTurck local solutions; it also now has a diffeomorphism-valued DeTurck
  gauge wrapper reducing back to the map-valued one. The internal `C^2`
  diffeomorphism layer has now also crossed onto the connection side: it defines
  a bundled pullback of tangent-bundle covariant derivatives, proves inverse
  identities for pullback/pushforward of vector fields, identifies transport of
  `∇_X Y` under that pullback, proves the corresponding torsion transport
  formula, shows torsion-free affine connections stay torsion-free after
  pullback (under the ambient Riemannian tangent-bundle hypotheses already used
  by the Levi-Civita layer), transports affine-connection difference tensors,
  proves metric compatibility is preserved whenever a chosen target smooth
  metric realizes the pulled-back inner product, lifts that
  metric-compatibility statement slice by slice to time-dependent `C^2`
  diffeomorphism/connection families, now also lifts torsion-free transport
  slice by slice to those time-dependent connection families, specializes that
  family metric-compatibility statement to the actual slicewise pulled-back
  `C^1` metric object, and transports the raw curvature commutator under both
  static and family pullback of the connection, including pointwise formulas
  after applying `pullbackTangent`/`pushforwardTangent`. It now also pushes the
  pulled-back `ricciEndomorphism` forward to the corresponding target-side raw
  curvature operator and identifies the pulled-back `ricciCurvature` with the
  trace of the tangent-map-conjugated endomorphism, again both statically and
  slice by slice for connection families. That new metric is built as a bundled
  `ContMDiffRiemannianMetric I 1`, with coordinate-level `C^1` regularity for
  the pulled-back bilinear form and a wrapper that discharges the earlier
   metric-compatibility hypothesis automatically. Bundled Levi-Civita pullback
   transport now feeds the gauge-reduction layer, where identity diffeomorphism
   gauges convert smooth Levi-Civita-background Ricci-DeTurck local-solution
  packages back into intrinsic Ricci-flow local-existence/uniqueness packages;
  the identity `C^3` gauge path now also identifies the concrete
  gauge-corrected pullback velocity with the source DeTurck velocity and
  packages chosen-background DeTurck theorem families as gauge-reducible by the
  identity diffeomorphism gauge. A thin
  `Geometry.Manifold.RicciFlow.GaugeReduction.Diffeomorph3FlowDerivative`
  module now names the primitive `C^3` intrinsic gauge-flow derivative data and
  proves it equivalent to the geometric `SatisfiesGaugeFlowOn` formulation, with
  a reusable chosen-DeTurck-solution gauge-flow family bundle projecting to both
  derivative-family data and anchored gauges; the same bundle now feeds the
  gauge-reducible, intrinsic, and ordinary theorem-family routes from a proved
  pulled-back metric time derivative, and has a fixed-initial-value-problem
  counterpart with matching local theorem-package projections. Both bundle levels
  can now also extract the scalar inner-product derivative hypothesis from the
  same gauge-pulled metric time-derivative proof. It also now lowers the
  non-identity boundary
  from a prebuilt anchored `C^3` DeTurck gauge to raw `C^3` diffeomorphism
  families equipped with anchoring, the gauge-flow equation, and scalar
  inner-product derivative identities, and those direct and raw gauge-flow
  routes now expose ordinary theorem-family wrappers alongside the intrinsic
  ones.
  The conditional gauge-reduced package now records the exact non-identity
  gauge obligations whose discharge yields intrinsic and ordinary point-4 theorem
  packages, re-packages the transformed metric as a pulled-back Ricci-DeTurck
  local solution with Levi-Civita pulled-back background, converts that data to
  the generic Levi-Civita-background DeTurck package, compares pulled-back
  backgrounds on common intervals, exposes the gauge ODE and transformed
  Ricci-flow/DeTurck equations on the actual local interval, expands the source
  DeTurck equation into its background-Ricci plus DeTurck-correction form,
  exposes the pointwise gauge-flow derivative, and rewrites transformed velocity
  as `-2` times the trace of the pulled-back Ricci endomorphism in the
  trace-conjugation form supplied by connection transport. The same transport
  layer now also carries connection-difference trace endomorphisms through
  time-dependent pullback and identifies the corresponding pulled-back
  chosen-Levi-Civita/source-background trace with the source DeTurck one-form.
  It also includes a
  theorem-family reduction for all initial data, identifies the identity `C^3`
  gauge's fixed-vector scalar derivative, upgrades chosen-background packages
  through the explicit scalar-derivative gauge-reducible interface, exposes
   direct identity-`C^3` gauge-reduced wrappers with source/metric/velocity
   simplification lemmas. The non-identity right-slot/Ricci-transport obligation
   is now discharged by the `C^3` transport layer; the remaining primitive
   non-identity gauge input is the time-derivative/scalar-derivative formula for
   the gauge-pulled metric, with the local scalar inner-product derivative now
   extractable from a proved pullback-metric time derivative. Raw pointwise
   gauge-flow-derivative routes now feed the explicit scalar-derivative,
   gauge-reduced, intrinsic, and ordinary packages directly from both the
    theorem-package and global/interval analytic boundary-chart surfaces, and the
    endpoint chart routes now have bundled global/interval gauge-flow data objects
    whose gauge fields use the named derivative-family interface, plus a separate
    `AnalyticPDE.GeometricGaugeFlow` endpoint module whose global/interval bundles
    accept geometric `C^3` gauge-flow families plus pullback-time-derivative
    proofs, derive the scalar endpoint internally, and project through the
    derivative bundles to scalar-derivative, gauge-reducible, intrinsic, and
    ordinary theorem families; the same module now exposes a fixed-IVP endpoint
    bundle and a family-to-fixed-IVP projection. With
    those pullback-time-derivative proofs they also feed intrinsic and
    ordinary theorem packages directly. The constant `C^3` identity diffeomorphism family now also
    supplies primitive derivative-level gauge data when the DeTurck gauge field
    vanishes, and the identity gauge route has direct intrinsic/ordinary theorem-package
    projections matching the non-identity APIs. A new
    `GaugeReduction.Diffeomorph3FlowExistence` layer names the raw `C^3`
    diffeomorphism-flow existence witness needed from the manifold ODE theorem
    and converts it into the fixed-IVP and theorem-family geometric gauge-flow
    bundles, while the geometric endpoint data can now replace its bundled
    gauge-flow component by such a raw existence witness at fixed-IVP, global,
    and interval scope. A thin `AnalyticPDE.SmoothRealization` module names the
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
  positive-definite locus once the vector field's coordinatewise defect vanishes,
  plus interval-scoped fixed-locus, fixed-symmetry, and direct-defect variants
  lifted to time-dependent finite-cover evolutions, bundled-continuous-Riemannian
  initial data, a reusable interval coordinatewise-defect chart interface,
  a direct global-geometric-to-interval-defect chart adapter, and a
  pointwise-symmetric-vector-field variant that supplies that defect vanishing
  automatically; the global metric-reification and chosen-background package
  constructors now take their witnesses through this terminal defect route, and
  globally Lipschitz charts expose terminal-bounded continuous-metric and
  metric-curve reification endpoints directly, plus a direct bounded
  candidate-encoding witness for the associated interval chart and
  global/local-family chosen-background routes that can consume those
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
  the same global or interval chart now have a named metric-uniqueness theorem on
  their common interval. The
  same state-set mechanism now also has a
  non-autonomous Picard-Lindelof specialization: time-dependent Banach-chart
  vector fields satisfying the verified Picard/Lipschitz hypotheses shrink to
  positive-definite local metric evolutions and, when identified pointwise with
  the intrinsic Ricci-DeTurck RHS, remain symmetric by the proved geometric
  symmetry theorem. This time-dependent Ricci-DeTurck bridge is also bundled as
  `TimeDependentGeometricRicciDeTurckBanachChart`, whose fields are precisely the
  remaining Picard/Lipschitz/geometric-agreement obligations and whose extractor
  produces the symmetric positive-definite local Banach metric evolution. The
  reverse metric bridge is now proof-bearing as well: any finite-cover
  symmetric positive-definite section-state reifies to a bundled continuous
  Riemannian metric, and the packaged Banach solution now exposes one
  metric-valued curve whose local-interval inner products agree with the Banach
  section curve, whose initial value is the original initial metric, and whose
  common-interval uniqueness follows from Banach uniqueness. For autonomous
  charts, a new local `C^1` reduction also shrinks to an open neighborhood inside
  the positive-definite metric locus and derives the needed local Lipschitz bound
  there, so chart estimates can be proved locally around the initial metric
  instead of globally on the whole metric locus; for non-autonomous charts, the
  lower-level positive-definite and symmetric bridges, plus the reusable
  `TimeDependentGeometricRicciDeTurckBanachChartOnIcc` package, now accept
  Lipschitz estimates restricted to the verified Picard time interval and expose
  the constructed solution's `terminalTime ≤ T` bound, including when the Banach
  section solution is reified as continuous Riemannian metrics or a single
  metric-valued curve. A
  smooth-realization adapter packages the exact remaining
  lift/time-derivative/DeTurck-equation
  obligations needed to turn such a Banach solution into an
  `IntrinsicDeTurckLocalSolution`; when supplied for a smooth-IVP-seeded chart
  solution it extracts that DeTurck local solution, and two such smooth
  realizations have equal metric tensors on common intervals. The interval
  chart also has a bounded candidate-encoding theorem: candidates whose Banach
  representatives satisfy `terminalTime ≤ T` promote all the way to
  `IntrinsicDeTurckLocalExistenceUniqueness`, the identity-gauge intrinsic
  Ricci-flow package, the non-identity gauge-reducible package, and the explicit
  scalar-inner-derivative gauge package using only `Icc`-restricted Lipschitz
  control; the chosen-background identity, arbitrary-background identity,
  gauge-reducible, and scalar-inner-derivative gauge routes now preserve the
  stronger arbitrary-background DeTurck, chosen-background DeTurck, and gauge theorem-family packages before exposing
  `IntrinsicLocalExistenceUniquenessFamily` extractors, and the finite-cover
  section-space completeness obligation is now discharged by the existing
  `ContinuousSectionSpace` instance instead of being a chart field. With the
  explicit reverse-chart encoding for arbitrary or chosen-background candidates,
  the same package now promotes to `IntrinsicDeTurckLocalExistenceUniqueness`,
  `ChosenIntrinsicDeTurckLocalExistenceUniqueness`, and then to intrinsic
  Ricci-flow local existence/uniqueness either by the chosen-background identity
  route or by the non-identity gauge-reducibility package; the global-chart
  family theorem produces `IntrinsicLocalExistenceUniquenessFamily` once these
  chart, realization, encoding, and gauge-reducibility obligations are supplied
  for every initial value problem. The direct interval chosen-background route
  and the global/interval raw `C^3` gauge-flow routes, including the boundary-reduced
  derivative-level scalar-derivative and time-derivative boundaries, now also expose ordinary
  `LocalExistenceUniquenessFamily` endpoints. It also specializes these criteria to genuine
  bundled continuous Riemannian initial metrics, so future Ricci-DeTurck
  Banach-chart work no longer has to manually prove finite-cover metric-locus
  membership for the initial datum. The interval chart now also restricts its
  ambient Ricci-DeTurck vector field to the genuine symmetric Riemannian Banach
  carrier: geometric RHS symmetry proves tangency to symmetric bilinear forms,
  and the ambient interval Lipschitz estimate descends to the restricted
  metric-locus vector field.
  The ordinary, intrinsic,
  chosen-background, gauge-reduced, and scalar-derivative theorem families expose
  package-level connection uniqueness on common intervals. The remaining gap to
  full point 4 is therefore proving the raw non-identity gauge-flow and
  gauge-pullback time-regularity obligations
  and the quasilinear parabolic PDE existence/uniqueness step needed to produce
  Ricci-DeTurck solutions on the restricted symmetric carrier, including the
  actual Ricci-DeTurck Banach chart and Picard estimates plus the analytic proof
  of the now-named smooth-realization and Banach/geometric RHS-identification
  data, and the reverse-candidate encoding closure for arbitrary
  chosen-background candidates. The first parabolic Hölder primitives are now
  proof-bearing: `AnalyticPDE/ParabolicHolder.lean` defines the parabolic
  distance/cylinders and `C^{0,α}` control, proves the parabolic triangle
  inequality, product-topology local-base compatibility for parabolic balls and
  product cylinders, exact standard ball/cylinder identifications,
  closed-to-open shrink inclusions for balls/cylinders,
  open-to-closed closure containment, proper-space compactness for closed
  balls/cylinders, finite open/closed parabolic ball and cylinder covers of
  compact sets, finite center-dependent open ball/cylinder subcovers
  subordinate to any ambient open set containing a compact set, with matching
  closed balls/cylinders still contained in that open set, uniform positive
  closed ball/cylinder radii inside such open neighborhoods, continuity and
  uniform continuity from
  positive Hölder exponent, explicit closed-ball/cylinder oscillation bounds,
  estimate monotonicity in the controlling constants, constant-preserving
  localization of open-domain Hölder and `C^{0,α}` estimates to uniform closed
  parabolic patches around compact subsets, a bounded local-to-global Hölder
  estimate from parabolic ball covers and doubled closed patches, plus its
  compact uniform-local corollary, finite-cover Holder patching with automatic
  local-constant selection, matching local-to-global `C^{0,α}` patching
  theorems, and finite-cover `C^{0,α}` patching with automatic local-constant
  selection, variable-radius finite-cover Holder and `C^{0,α}` patching plus
  compact point-dependent- and existential-radius corollaries, finite-sum
  closure for explicit Holder, bounded, and `C^{0,α}` controls,
  finite-sum closure for existential Holder and `C^{0,α}` controls,
  finite-product closure for existential normed-comm-ring-valued `C^{0,α}`
  controls,
  and
  add/subtract/smul, integer-scalar, and product-valued pairing closure
  estimates plus the bounded product estimate for normed-ring-valued
  `C^{0,α}` functions and the corresponding bounded scalar-action estimate for
  normed-space-valued functions, reciprocal closure for normed-field-valued
  functions bounded away from zero and the corresponding division closure,
  along with closure
  under taking norms, Lipschitz composition on the controlled range, bounded
  `C^{0,α}` composition under range or explicit closed-sup-ball bounds, and
  exponent lowering on unit parabolic-diameter domains with closed-ball and
  closed-cylinder specializations across the Holder and `C^{0,α}` interfaces,
  backed by closed-ball diameter control, product ball/closed-ball
  compatibility in both directions for parabolic balls and product cylinders,
  plus
  basepoint-to-sup bounds and Holder-to-`C^{0,α}` packaging on compact domains,
  with direct proper-space closed-ball/cylinder corollaries. These primitives do
  not yet supply the
  Schauder estimates or the Ricci-DeTurck Banach chart. A separate
  `AnalyticPDE/Parabolic/MatrixC0Alpha.lean` module now builds on those
  primitives to prove parabolic `C^{0,α}` closure of finite matrix
  determinants, adjugate entries, and inverse entries under determinant lower
  bounds, plus matrix-product and matrix-vector-product entries, from entrywise
  control. The curvature, time-dependent geometry,
  intrinsic Ricci-flow, and DeTurck layers now prove the geometric
  symmetry input outright: metric compatibility gives curvature-operator
  skew-adjointness, torsion-freeness gives first Bianchi, the Ricci contraction is
  symmetric for Levi-Civita families, the intrinsic Ricci-flow RHS is symmetric,
  and the full intrinsic Ricci-DeTurck RHS is symmetric because the DeTurck
  correction term itself is symmetric.
 The public vector-bundle layer also now
 packages continuous and smooth Riemannian metrics as honest sections of the
bilinear-form hom bundle, with pointwise extensionality lemmas for metric
equality. It also proves finite-dimensional coercivity and operator-norm
open-ball lemmas for positive-definite continuous bilinear forms, lifts that
openness to compact continuous families in `C(K, ·)` and
`BoundedContinuousFunction`, and then transfers it through preferred bundle
trivialization coordinates to the finite-cover `ContinuousSectionSpace` model:
actual positive-definite bilinear-form sections form an open subset there, the
symmetric locus is closed there, and a transported continuous-linear
coordinatewise antisymmetric-defect map has exactly that symmetric locus as its
kernel. Continuous Riemannian metrics land in the refined symmetric
positive-definite locus inside that model. In particular, the metric locus is now
packaged as an open subset of the closed symmetric section subtype. The same public layer
now also proves existence of global `C^1` affine connections on `C^2` bundle
data and provides the first section-level `C^1` regularity lemmas for the
Levi-Civita correction ingredients (`toDual`, fiberwise composition,
`metricDefectAux`, and torsion on `C^2` vector fields, with the torsion lemma
currently stated on `C^3` manifolds). This still does not prove the actual
Ricci-flow local existence/uniqueness theorem, so point 4 remains open.
