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
  ones. The derivative-view layer also has fixed-IVP and theorem-family
  closed-Picard handoffs from model-vector-field chart ODE data to the ordinary
  chart and primitive derivative packages on the open `Ioo` solution interval,
  including relative-filter model-field identification on `Ioo` and same-time-set
  relative-filter adapters for primitive and preferred-chart derivative packages,
  plus matching raw-existence constructors and ordinary-to-within weakening for
  chart-ODE derivative data. The raw fixed-IVP and theorem-family time-derivative layers
  now also package endpoint within-field/component and operator-domain data
  directly as named scalar pullback-metric derivative data when solution time
  sets are explicit `Ioo` intervals.
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
    and interval scope, either from tensor pullback-time-derivative proofs or
    from named scalar or coordinate-level pullback-metric derivative data. That
    raw-flow layer now also rewrites within-time-set
    manifold and preferred-chart derivative readouts under vector-field
    agreement in the relative filter `𝓝[s] t`, matching closed-interval Picard
    endpoint data, and the fixed-IVP/theorem-family raw intrinsic existence
    packages mirror those readouts. A thin `AnalyticPDE.SmoothRealization`
    module names the
    global/interval PDE closure data that turns a Banach chart solution into a
    smooth chosen-background DeTurck solution and its self-encoding candidate:
    metric realization, boundary time derivatives, chart-RHS/geometric-RHS
    identification, and chosen Levi-Civita background; it also packages the
    all-solutions smooth-realization plus reverse-candidate-encoding closure
    into direct global/interval chosen-background DeTurck theorem packages. The optional
   `PoincareCurvature.RicciFlowLocalExistence` aggregate now
  imports this gauge-reduction boundary plus the `AnalyticPDE` evolution layer proving the reusable
  Picard-Lindelof Banach-evolution local-solution core, open-state
  state-preserving uniqueness, Banach/geometric shorter-terminal restriction constructors and
  interval equation/continuity/state-membership/uniqueness readouts, a
  positive-definite finite-cover metric-locus bridge, an abstract continuous-linear
  symmetry/fixed-locus preservation theorem for later slot-swap symmetry, and a direct continuous-linear
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
  time-derivative data before the gauge-flow conversion; the closed-Picard
  metric-coordinate gauge-pullback route now also consumes product
  Picard-Lindelof hypotheses directly, including ordinary/open product-state
  handoffs and open-domain/radius-specialized endpoint forms, and its
  time-difference component data
  now localizes monotonically under raw gauge-flow time-set restriction, with
  closed-Picard ordinary time-difference tensor wrappers that accept full-`Icc`
  data directly; product-domain vector-slot scalar readouts now have
  eventual-equality transfer lemmas for locally equal finite-cover scalar
  identities, matching the operator-domain readout route;
  model-flow overlap uniqueness now also
  covers common closed subintervals of different ambient Picard intervals for
  local, continuous space-time, full variational `(flow, tangent)`, and
  scalar-readout derivative-domain `(t, flow, A(t)u, A(t)v)` packages, with
  open-overlap readouts for base flows, full variational pairs, scalar states,
  and scalar time graphs, pointwise common-interval readouts, and common
  time-graph/scalar-state compatibility; tangent-map and vector-slot
  common-subinterval readouts now
  also handle the case where base curves have already been identified for
  chart gluing, and full-pair, time-graph, scalar-state, and scalar-time-graph
  readouts now reuse that same base-equality route, including closed scalar
  readouts obtained from an open-overlap base-flow equality by continuity;
  product Picard convex-state, state-preserving closed-ball, and componentwise
  closed-ball continuity estimates now feed the full- and common-`Ioo`
  time-slice neighborhood-map, local open-partial-homeomorphism, and open
  bijective-patch readouts directly, including chart-lifted open-bijective and
  continuity-carrying patches with prescribed source/target variants plus
  local inverse-identity/overlap-equality and `C^3` gluing readouts plus
  positive source-ball patches for
  radius-shrinking chart arguments, and
  the state-preserving product-Picard/component-continuity routes now also have
  localized constructors and proof-level `Nonempty` wrappers, including the
  operator/identity-ball specializations, with direct closed-state-ball readouts
  after Picard-interval shrinking and localized common-`Ioo` time-slice
  neighborhood/local-inverse readouts;
  encoded candidates in
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
  metric-locus vector field. `SmoothRealizationMetricCone.lean` now bundles the
  positive-radius metric-cone shrink handoff from ambient interval closure data
  to genuine symmetric-carrier closure data and the chosen-background,
  intrinsic, and ordinary theorem-package witnesses, while still requiring the
  reverse-encoding terminal-fit compatibility for the selected shrink; the
  local Ricci-flow, intrinsic Ricci-flow, intrinsic Ricci-DeTurck, and
  chosen-background DeTurck candidate types now also have proof-bearing
  shorter-terminal restriction constructors, which is the prefix layer needed
  before replacing terminal-fit assumptions by localized candidate encodings.
  The analytic smooth-realization and interval candidate-encoding layers now
  preserve these prefixes as well: a smooth Banach realization restricts to a
  shorter Banach interval, and an interval Ricci-DeTurck candidate encoding
  restricts to the corresponding shorter geometric candidate. The genuine
  symmetric-carrier candidate encoding has the same shorter-terminal readout,
  reusing the ambient smooth realization on the restricted symmetric Banach
  interval. A new localized symmetric-carrier uniqueness theorem proves metric
  equality on any shared shorter interval `[t₀, S]` from reverse encodings of
  the candidates restricted to that same `S ≤ T`, and shrunk ambient closure
  data now supplies this local uniqueness readout without requiring the full
  arbitrary candidate intervals to fit in the shrink. A packaged clipped
  interval version reads this as equality on the whole visible overlap
  `[t₀, min (min T₁ T₂) T']`, with a named full-common-interval metric and
  connection readout when `min T₁ T₂ ≤ T'`; `SmoothRealizationMetricCone.lean` now
  exposes the no-terminal-fit clipped uniqueness readout directly from
  the standard positive-radius metric-cone shrink, including a selected-shrink
  package that also returns the conditional full-common-interval readouts. The
  same clipped local route
  now also upgrades metric equality to equality of the canonical chosen-background
  connections, with a metric-cone readout that selects the shrink and returns
  the connection equality on the visible overlap, plus a bundled metric-cone
  readout that returns both metric and connection equality from the same selected
  shrink. A further single-shrink readout now carries the terminal-fit
  theorem-package route and both no-terminal-fit local uniqueness readouts
  together, and a companion readout adds the conditional full-common metric and
  connection readouts to that same package. Downstream closure code no longer
  has to coordinate separate metric-cone choices for existence packages and
  local uniqueness. The
  initial-metric smooth-approximation route now also exposes the selected
  Picard time-radius proof and pairs its chart-carrier Banach
  solution/uniqueness witness with closure-data metric and connection readouts
  on that same clipped shrink.
  Global, closed-interval, and genuine symmetric-carrier chart-closure data now
  also project directly to chosen-background DeTurck theorem families, with
  single-IVP `Nonempty` readouts for the global and closed-interval closure
  records, so downstream gauge routes can consume the chosen package without
  first passing through the intrinsic or ordinary point-4 projections.
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
  parabolic patches around compact subsets, bounded local-to-global Hölder
  estimates from parabolic ball covers and product-cylinder covers with doubled
  closed patches, plus compact uniform-local corollaries, finite-cover Holder
  patching with automatic local-constant selection for both cover shapes,
  matching local-to-global `C^{0,α}` patching theorems, and finite-cover
  `C^{0,α}` patching with automatic local-constant selection, variable-radius
  finite-cover Holder and `C^{0,α}` patching for both ball and product-cylinder
  covers, including fixed-constant variants that preserve the sup constant and
  compact point-dependent- and existential-radius Holder-constant readouts,
  finite-sum
  closure for explicit Holder, bounded, and `C^{0,α}` controls,
  finite-sum closure for existential Holder and `C^{0,α}` controls,
  finite sum-difference closure for fixed-constant and existential `C^{0,α}` controls,
  finite sum-of-products closure for fixed-constant and existential
  normed-ring-valued `C^{0,α}` controls,
  finite-product and finite-product-difference closure for existential
  normed-comm-ring-valued `C^{0,α}` controls plus an explicit bounded `C^{0,α}`
  finite-product estimate, finite `Pi`
  packaging across bounded, Holder, and `C^{0,α}` controls from componentwise
  estimates and same-constant projection back to components, and
  continuous-linear closure, standalone Holder-level curried-bilinear closure
  from separate bounded and Holder controls, standalone Holder-level
  operator-application closure from separate operator/vector bounded and Holder
  controls, curried-bilinear-map closure, bounded and Holder-level
  curried-bilinear difference primitives, operator-application closure, bounded
  and Holder-level operator-application difference primitives, and
  operator-application difference with operator-norm constants in both
  fixed-constant and existential forms,
  add/subtract/smul, integer-scalar, and product-valued pairing closure
  estimates plus bounded and Holder-level normed-ring product/product-difference
  primitives, the bounded product estimate for normed-ring-valued `C^{0,α}`
  functions, two-factor and finite-sum product-difference `C^{0,α}` estimates,
  bounded and Holder-level scalar-action primitives, and the corresponding
  bounded scalar-action estimate for normed-space-valued functions, reciprocal
  closure plus bounded and Holder-level reciprocal-difference primitives for
  normed-field-valued functions bounded away from zero and the corresponding
  division closure,
  along with closure
  under taking norms, Lipschitz composition on the controlled range, direct
  parabolic Hölder/`C^{0,α}` lifts of time-independent spatial
  Hölder/Lipschitz functions on the spatial projection, direct time-only
  lifts from ordinary time Hölder exponent `α / 2` to parabolic exponent `α`
  and from time Lipschitz control to parabolic exponent `2`, with direct
  unit-diameter lowering bridges, including fixed-constant
  `ParabolicC0AlphaWith` and existential `ParabolicC0AlphaOn` lifts from
  spatial Lipschitz data for every
  `0 ≤ α ≤ 1` and from time Lipschitz data for every `0 ≤ α ≤ 2`, together
  with closed-ball and closed-cylinder subset variants,
  bounded
  `C^{0,α}` composition under range or explicit closed-sup-ball bounds,
  global and closed-ball Lipschitz composition with automatic composed sup
  bounds, pointwise finite-product Lipschitz estimates and finite-sum
  Lipschitz estimates for two-factor products on factorwise bounded sets, and
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
  primitives to package entrywise quantitative vector/matrix controls, including
  spatial-only and time-only finite vector and matrix coefficient families from
  ordinary Holder/Lipschitz estimates, explicit unit-parabolic-diameter spatial
  Lipschitz lifts for every `0 ≤ α ≤ 1`, and explicit unit-parabolic-diameter
  time-Lipschitz lifts for every `0 ≤ α ≤ 2`, now with matching
  fixed-constant and existential closed-ball and closed-cylinder variants for
  those Lipschitz coefficient bridges, and to prove explicit bounded
  `C^{0,α}`
  determinant, adjugate-entry,
  inverse-entry, and whole inverse-matrix estimates, plus parabolic `C^{0,α}`
  closure of finite matrix determinants, adjugate entries, and inverse entries
  under determinant lower bounds, pointwise determinant Lipschitz control in the
  elementwise matrix norm, named adjugate-entry, inverse-entry, summed whole
  inverse-matrix, function-level determinant/inverse/matrix-product
  bounded-difference, existential determinant and reciprocal-determinant
  difference `C^{0,α}` readouts with a compact nonvanishing-det adapter,
  existential inverse-entry, whole inverse-matrix, inverse-principal contraction,
  inverse-Christoffel array, quadratic Christoffel-Ricci, and primitive
  schematic RHS difference readouts,
  inverse-difference `C^{0,α}` control,
  inverse-principal entry Lipschitz,
  bounded Holder entry/matrix estimates, inverse-principal contraction
  `C^{0,α}` difference control, and inverse-principal contraction
  bounded-difference control with a compact-domain determinant-lower-bound
  variant,
  inverse-Christoffel derivative/metric-side and array-level Lipschitz constants,
  inverse-Christoffel `C^{0,α}` difference control, inverse-Christoffel
  function-level bounded-difference control with a compact-domain
  determinant-lower-bound variant, inverse-Christoffel bounded Holder
  entry/array estimates, and
  quadratic-Christoffel matrix-norm Lipschitz and bounded Holder entry/matrix
  estimates, supplied-Christoffel schematic bounded Holder entry/matrix
  estimates, primitive-input schematic bounded Holder entry/matrix estimates,
  primitive-input schematic RHS `C^{0,α}` difference control, supplied-Christoffel
  and primitive-input schematic RHS entrywise-difference `C^{0,α}` refinements, plus
  supplied-Christoffel and primitive-input schematic RHS entry and whole-matrix
  Lipschitz constants and a named function-level bounded-difference package for
  the primitive schematic matrix RHS, with a compact-domain variant selecting a
  common determinant lower bound, on entrywise
  bounded finite matrices with a determinant lower bound where needed, with
  compact nonvanishing determinant data now supplying such lower bounds,
  including finite-index common determinant lower bounds for compact families,
  finite-family compact inverse, inverse-action, inverse-bilinear,
  inverse-principal, and inverse-Christoffel estimates with the same shared
  determinant constant and matching existential finite-family inverse,
  inverse-action, inverse-bilinear, inverse-principal, and inverse-Christoffel
  closures, and
  compact-domain inverse,
  inverse-action, inverse-bilinear, and matrix-valued RHS variants, including
  finite-family primitive schematic RHS estimates with the same shared
  determinant constant and matching existential finite-family schematic RHS
  closures, plus finite-family primitive schematic RHS difference closures,
  quantitative difference estimates, and function-level bounded-difference
  estimates with one lower bound shared by both
  metric families, quantitative compact inverse-action and inverse-bilinear
  estimates, plus
  entrywise and whole-valued finite matrix transpose, pointwise
  symmetrization, explicit bounded transpose/symmetrization estimates and
  corresponding difference estimates, finite matrix trace, explicit bounded
  trace and trace-difference estimates, existential entrywise-difference
  readouts for vector/matrix packaging, transpose, symmetrization, and trace,
  matrix-product, explicit bounded
  entrywise/whole-matrix
  product estimates, explicit entrywise/whole-matrix product-difference estimates,
  matrix-vector/vector-matrix closure,
  explicit bounded matrix-vector/vector-matrix estimates,
  matrix-vector/vector-matrix product-difference estimates, and
  inverse-matrix vector-product closure, explicit bounded inverse-matrix
  vector-product estimates on both sides, explicit bounded inverse-bilinear
  contraction estimates, whole finite vector/matrix and
  inverse-matrix packages, finite vector dot products, explicit bounded
  dot-product estimates, dot-product difference estimates, explicit bounded
  finite bilinear-contraction estimates, finite bilinear-contraction difference
  estimates, and bilinear contractions
  through matrices or inverse matrices, including explicit bounded Holder entry
  and whole-array estimates for Christoffel-symbol type inverse-metric
  contractions and their entrywise/whole-array closure, explicit bounded Holder
  entry/matrix estimates and whole matrix-valued closure for principal-part
  contractions `g^{ab} H_abij`, explicit bounded Holder entry/matrix estimates,
  product-difference bounded Holder estimates, and whole matrix-valued closure
  for Ricci-coordinate quadratic Christoffel contractions, plus supplied-Christoffel
  and primitive-input schematic local
  Ricci-DeTurck RHS entry/matrix bounded Holder estimates and whole
  matrix-valued closure from entrywise control, plus finite product-cylinder
  local primitive-estimate and primitive-difference bridges, and compact
  point-local product-cylinder variants for the same schematic RHS and RHS
  difference closures, including direct existential-radius APIs before
  extracting determinant lower bounds, plus
  product-cylinder metric-control bridges for
  the function-level bounded-difference estimate, including finite-cover,
  compact point-local, direct existential-radius, and finite-family variants
  with one shared lower bound, and quantitative finite-cover, compact
  point-local, and existential-radius `sub_with` bridges whose Holder constants
  are the finite-cover patching constants.  The companion
  `AnalyticPDE/Parabolic/LocalFrameGram.lean` module connects compact
  time-space local-frame Gram determinant nonvanishing to parabolic inverse
  Gram-matrix control, inverse-Gram vector/vector-inverse products,
  inverse-Gram bilinear contractions, and inverse-Gram Christoffel/schematic
  Ricci-DeTurck closure, including spatial-Hölder entry-control variants,
  unit-parabolic-diameter spatial-Lipschitz entry-control variants for inverse
  Gram, inverse-Gram vector/vector-inverse products, inverse-Gram bilinear
  contractions, inverse-principal contractions `g^{ab}H_abij`, inverse-Gram
  Christoffel contractions, and schematic RHS bridges at every `0 ≤ α ≤ 1`,
  fixed-constant and existential closed-ball and closed-cylinder
  spatial-Lipschitz inverse-Gram, inverse-Gram action/bilinear,
  inverse-principal, inverse-Gram Christoffel, and schematic RHS variants, and
  compact quantitative inverse Gram,
  inverse-Gram action/bilinear,
  inverse-principal contraction, inverse-Gram Christoffel, and schematic RHS
  bridges exposing the determinant lower-bound constant, plus geometric
  finite-family local-frame Gram determinant lower-bound, inverse-estimate, and
  schematic RHS handoffs with spatial-Hölder, unit-diameter spatial-Lipschitz,
  closed-ball spatial-Lipschitz, and closed-cylinder spatial-Lipschitz
  Gram-entry input forms, existential finite-family inverse-Gram,
  inverse-Gram action/bilinear, inverse-principal, inverse-Gram Christoffel, and
  schematic RHS handoffs from entrywise `ParabolicC0AlphaOn` controls sharing the same
  compact determinant lower bound, with the inverse-Gram, inverse-Gram
  vector/vector-inverse product, inverse-Gram bilinear, inverse-principal, and
  inverse-Gram Christoffel, and schematic RHS handoffs now also accepting those
  same Gram-entry input forms, direct single-frame and finite-family compact
  point-local product-cylinder primitive-estimate and primitive-difference
  schematic RHS bridges with both explicit-radius and existential-radius entry
  points, single-frame and finite-family finite-cover product-cylinder
  schematic RHS bridges, plus finite-cover, compact point-local, and
  existential-radius bounded-difference metric-control bridges consuming the
  matrix APIs before selecting the local-frame determinant lower bound, and
  finite-cover, compact point-local, and existential-radius quantitative
  `sub_with` bridges carrying patched Holder constants for single-frame and
  finite-family local-frame Gram inputs, quantitative
  finite-family inverse-Gram
  vector/vector-inverse product, bilinear, inverse-principal, and
  inverse-Christoffel handoffs sharing that same compact determinant lower
  bound, with the quantitative vector/vector-inverse product, bilinear,
  inverse-principal, and inverse-Christoffel handoffs now also accepting those
  same Gram-entry input forms, finite-family inverse-Gram difference bridges
  against comparison matrix families with spatial-Hölder, unit-diameter
  spatial-Lipschitz, and closed ball/cylinder spatial-Lipschitz Gram-entry input
  forms while keeping one determinant lower bound shared by both sides, and
  finite-family schematic RHS quantitative difference, quantitative
  entrywise-difference, existential difference, and bounded-difference control
  against comparison primitive inputs with one lower bound shared by the Gram and
  comparison metric families, including spatial-Hölder, unit-diameter
  spatial-Lipschitz, and closed ball/cylinder spatial-Lipschitz Gram-entry forms
  for the quantitative difference and quantitative entrywise-difference bridges,
  the existential entrywise `C^{0,α}` difference bridge, and the
  bounded-difference bridge, and compact
  local-frame inverse Gram, inverse-principal contraction, inverse-Gram
  Christoffel arrays, and schematic RHS outputs, including existential
  difference readouts for all four from entrywise controls, and schematic RHS
  `C^{0,α}` difference control,
  including entrywise-difference inverse Gram, inverse-principal, inverse-Gram
  Christoffel, and schematic RHS bridges, and inverse Gram, inverse-principal
  contraction, inverse-Gram Christoffel, and schematic RHS bounded-difference
  bridges against comparison primitive inputs, all with matching
  spatial-Hölder Gram-entry input forms where applicable; the inverse-Gram,
  inverse-principal, inverse-Gram Christoffel, and schematic RHS
  bounded-difference, comparison, and entrywise-difference bridges now also have
  unit-diameter, closed-ball, and closed-cylinder spatial-Lipschitz Gram-entry
  variants for `0 < α ≤ 1`, and the single-frame existential schematic RHS
  entrywise-difference bridge now has direct spatial-Hölder, unit-diameter,
  closed-ball, and closed-cylinder Gram-entry variants for local chart callers.
  The curvature,
  time-dependent geometry, intrinsic Ricci-flow, and
  DeTurck layers now prove the geometric
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
packaged as an open subset of the closed symmetric section subtype. The same
finite-cover section model now also turns coordinatewise compact-readout
Lipschitz estimates into `LipschitzOnWith` estimates for section-space maps and
has a preferred-bilinear specialization that multiplies a fibrewise Lipschitz
constant by the square of the preferred inverse-trivialization bound, including
variants for covers supplied as `et` plus `et i = trivializationAt ...`, matching
the Ricci-DeTurck Banach-chart records. The finite-cover inverse-trivialization
bound used by those estimates is now named separately as a compactness theorem,
and the smooth-approximation layer now combines it with the fibrewise estimate
handoff to produce an existential section-space Lipschitz constant for
time-family preferred-cover fields. The Ricci-DeTurck smooth-closure layer now
uses that to build an interval Banach-chart package while choosing `Kstate`
from fibrewise estimates. The reverse preferred-cover bridge now also turns
compact bilinear-coordinate RHS estimates into the required fibrewise estimate,
and `SmoothApproxClosure` packages the corresponding interval chart constructor
from coordinate readout bounds. On the parabolic-coordinate side, `MatrixC0Alpha`
now factors the schematic Ricci-DeTurck bounded-difference constants through a
shared comparison radius, including finite-family estimates with one compact
determinant lower bound, and `LocalFrameGram` exposes both single-frame and
finite-family compact local-frame versions for Gram-matrix coordinate RHS
differences. Those linear-radius estimates now also have local finite-cover,
point-dependent local-cylinder, and existential point-local cylinder variants
in both the raw matrix and local-frame Gram layers, so compact coordinate
Lipschitz checks can consume local parabolic-cylinder regularity data directly.
The raw matrix layer also turns primitive state-space Lipschitz bounds, with a
uniform determinant lower bound, into `LipschitzOnWith` statements for each
schematic RHS coordinate and for finite RHS families; `SmoothApproxClosure`
now has the matching real-constant coordinate-Lipschitz constructor for the
interval Ricci-DeTurck Banach-chart package. The same raw constants are now
monotone in primitive metric, derivative, and principal-coefficient radii, so
finite-cover chart arguments can pass from local constants to coarser shared
bounds without re-expanding the schematic RHS formula; the function-level
bounded-difference, shared-radius, and state-space `LipschitzOnWith` estimates
expose that coarsening directly, including finite-family coordinate forms and
compact-domain determinant-extraction variants, and the compact local-frame
Gram-coordinate bridges now lift the same coarser constants.
The same public layer
now also proves existence of global `C^1` affine connections on `C^2` bundle
data and provides the first section-level `C^1` regularity lemmas for the
Levi-Civita correction ingredients (`toDual`, fiberwise composition,
`metricDefectAux`, and torsion on `C^2` vector fields, with the torsion lemma
currently stated on `C^3` manifolds). The Levi-Civita layer also proves that
local-frame Gram determinants are uniformly bounded away from zero on compact
subsets of a trivialization base. This still does not prove the actual
Ricci-flow local existence/uniqueness theorem, so point 4 remains open.
