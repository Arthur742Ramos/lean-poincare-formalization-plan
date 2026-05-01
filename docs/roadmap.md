# AFM-Scale Roadmap

This document breaks the Lean formalization of the Poincare Conjecture into
granular deliverables where each item would plausibly stand on its own as a
substantial formalization paper.

The intended proof route is:

1. build enough Riemannian and geometric-analysis infrastructure in Lean
2. formalize Ricci flow and its core estimates
3. formalize Perelman's monotonic quantities and non-collapsing theory
4. formalize Ricci flow with surgery
5. derive finite-time extinction and the 3D Poincare statement

## Completion standard

A roadmap point counts as complete only when the intended mathematical content
has been fully formalized and proved in Lean. Using existing proved theorems
from mathlib or other Lean libraries is fine.

The following do **not** close a roadmap point:

- interfaces or theorem packages without proofs
- added axioms or unchecked assumptions
- `sorry` placeholders
- scaffolding that only prepares later work

## Candidate paper-scale projects

### 1. Riemannian curvature package

Formalize the first reusable static curvature layer needed for Ricci flow:

- covariant derivatives along vector fields
- the raw curvature commutator
- the bundled Riemann curvature tensor
- Ricci curvature
- scalar curvature
- metric compatibility interfaces for Riemannian vector bundles
- torsion-free and Levi-Civita predicates on the tangent bundle
- Levi-Civita uniqueness at the current manifold API boundary
- compatibility statements tying these constructions back to the manifold API

Why this is paper-worthy:
it turns the existing manifold API into an actual reusable curvature package:
enough geometry to talk about the static tensors and contractions that later
Ricci-flow arguments are built from.

Current repo status:
this point is now closed by the concrete Lean subproject at `curvature/`,
which packages `∇_X σ`, the raw curvature commutator, the bundled curvature
tensor, Ricci/scalar curvature, metric compatibility, and Levi-Civita
uniqueness into a compilable library boundary.

### 2. Curvature identities and existence package

Formalize the remaining static Riemannian-geometry layer needed before full
Ricci-flow work:

- Levi-Civita existence
- sectional curvature
- first and second Bianchi identities
- compatibility statements tying these refinements back to the manifold API

Why this is paper-worthy:
it closes the remaining gap between the first curvature package and the full
static Riemannian API that Ricci-flow arguments expect.

Current repo status:
this point is now closed by the `curvature/` Lean package, which includes
Levi-Civita existence, sectional curvature, the first and second Bianchi
identities, and the corresponding manifold-facing package theorems.

### 3. Time-dependent geometric structures

Formalize one-parameter families of metrics, connections, tensors, and
differential operators on a manifold.

Why this is paper-worthy:
Ricci flow is a PDE on evolving metrics, so this is the layer that lets Lean
talk coherently about geometry at time `t` and compare it across times.

Current repo status:
this point is now closed by `curvature/`: the package contains
one-parameter families of sections, covariant derivatives, and smooth
Riemannian metrics; evaluation-at-time and constant-family interfaces; a
slice-by-slice spatial smoothness predicate; the time-lifted `along`
construction; metric-dependent Ricci/scalar/sectional curvature at each time;
and slicewise Levi-Civita predicates, constructions, and existence theorems.
Time dependence is still modeled explicitly as an `ℝ`-indexed family rather
than through a separate time-differentiability theory, but the package boundary
needed for later Ricci-flow work is now in place as actual Lean code and proofs.

### 4. Ricci-flow local existence and uniqueness

Formalize a first existence theorem for Ricci flow on compact manifolds,
together with uniqueness in the appropriate setting.

Why this is paper-worthy:
this is the first theorem package that turns the geometric infrastructure into
genuine geometric analysis.

Current repo status:
`curvature/` currently contains only preparatory scaffolding for this point:
metric-tensor time-derivative predicates, Ricci-flow solution and initial-value
problem structures, local solutions on forward time intervals, and a bundled
`LocalExistenceUniqueness` interface for compact manifolds. Under this
repository's standard, that does **not** count as completing point 4, because
the local existence and uniqueness theorem itself is not yet proved in Lean.
Point 4 therefore remains open. Proof-bearing analytic prerequisites have
landed separately: local-to-global gluing for smooth vector-bundle sections
valued in fiberwise convex sets, trivial-bundle and open-set smoothing, local
smoothing inside bundle trivializations, and a global smoothing theorem for
continuous bundle sections constrained to open fiberwise convex subsets of the
total space, together with an intrinsic fiberwise-`ε` approximation theorem
for continuous sections of smooth Riemannian vector bundles. The section-space
side has also been strengthened: continuity can now be checked in local-frame
coordinates, compact trivialization coordinates can be packaged as
`ContinuousMap`s, compact overlap identities are proved as coordinate-change
equalities in `C(K, F)`, and continuous sections now induce cover-level compact
coordinate families whose overlap compatibility determines the section on the
covered union. On finite compact covers, those compatible coordinate families
form a closed complete compatibility kernel inside the ambient finite-product
`ContinuousMap` space, the gluing/reconstruction lemmas identify continuous
sections with compatible compact coordinate families on the cover (hence also
with the closed compatibility kernel itself), and that equivalence now
transports the induced additive, module, normed, and complete-space structure
to a dedicated continuous-section wrapper. The internal Ricci-flow scaffold has
also gained a first genuine theorem in this direction: for Ricci-flat initial
data equipped with a chosen `C^1` Levi-Civita connection, the constant metric
family gives a local stationary Ricci-flow solution
(`stationaryRicciFlatLocalSolution` / `localSolution_nonempty_of_stationary_ricciFlat`),
and any two such stationary constructions have the same evolving metric tensor
and Levi-Civita connection on their common interval. The same stationary
existence statement is now also packaged through a chosen smooth Levi-Civita
witness, so callers no longer need to provide that auxiliary connection
separately for the basic Ricci-flat corollary, and the initial-data side now
 also carries an intrinsic `InitialValueProblem.IsRicciFlat` predicate with a
 canonical stationary local solution attached to it. The scaffold now proves a
 first nonempty class of full local-existence/uniqueness theorem packages: when
 every tangent fiber is a subsingleton, Ricci/scalar curvature, the sectional
 curvature numerator and denominator, the Ricci-flow right-hand side, every
 metric tensor component, and every solution metric velocity vanish pointwise.
 Local and intrinsic local solutions in this case are stationary in metric
 tensor components, and their Levi-Civita connection values all agree, so
 `intrinsicLocalExistenceUniqueness_of_subsingleton_tangent` and
 `localExistenceUniqueness_of_subsingleton_tangent` provide stationary existence
 and metric uniqueness for every initial metric, with theorem-family variants.
 Since mathlib's tangent space is a type synonym of the model vector space, the
 same theorem packages are now also exposed under the more natural
 `[Subsingleton E]` model-space hypothesis. The first positive-dimensional
 theorem package has also landed: on tangent fibers of real dimension at most
 one, the alternating curvature tensor vanishes in its first two slots, hence
 Ricci curvature and the intrinsic Ricci-flow right-hand side vanish. This
 yields stationary local-existence/metric-uniqueness packages
 `intrinsicLocalExistenceUniqueness_of_finrank_le_one`,
 `localExistenceUniqueness_of_finrank_le_one`, and model-space theorem-family
 variants under `[Fact (Module.finrank ℝ E ≤ 1)]`. The thin
 `LocalExistence.RankOne` extension also proves that all ordinary and intrinsic
 rank-one local solutions have zero metric velocity, remain equal to the initial
 metric on their local interval, and have unique Levi-Civita connection values on
 common intervals. More generally, the
scaffold now proves that any local solution with zero metric velocity on its
whole interval stays equal to the initial metric tensor there and keeps the
same Levi-Civita connection as its initial slice, so zero-velocity local
 solutions are unique on their common interval at both the metric and connection
 levels. It also packages pointwise equivalences between zero metric velocity
 and Ricci-tensor vanishing (with the corresponding RHS-zero consequences) and
 the direct geometric corollary that if the Ricci tensor vanishes along the
 whole local-solution interval, then the solution is stationary in this same
 metric-and-connection sense. It now also proves that
the Ricci tensor, Ricci-flow right-hand side, and Ricci-flow equation are
independent of which Levi-Civita family is chosen for a fixed metric family, so
the current point-4 boundary no longer depends on an arbitrary connection
choice. On top of that invariance layer, the same scaffold now packages an
intrinsic Ricci/RHS boundary using the chosen smooth Levi-Civita family:
`intrinsicRicciTensor`, `intrinsicRicciFlowRHS`, and
`SatisfiesIntrinsicEquationAt`, together with comparison lemmas showing these
agree with the older connection-parametrized objects for any Levi-Civita
family. It also packages intrinsic solution / local-solution / compact
 theorem-package wrappers (`IntrinsicSolution`, `IntrinsicLocalSolution`,
 `IntrinsicLocalExistenceUniqueness`) and theorem-family wrappers
 (`LocalExistenceUniquenessFamily`, `IntrinsicLocalExistenceUniquenessFamily`)
 together with conversions back and forth to the older
 connection-parametrized boundary, so the current abstract point-4 interface can
 now be stated directly in terms of the evolving metric for either one initial
 value problem or all initial value problems at once. The same
intrinsic local-solution layer also carries metric-only versions of the
zero-velocity, intrinsic-Ricci-zero, and common-time connection-equality
theorems, so those interval-stationarity consequences no longer require dropping
back to an auxiliary connection family. It now also packages the canonical
intrinsic stationary local solution attached to `InitialValueProblem.IsRicciFlat`,
with intrinsic comparison lemmas against arbitrary zero-velocity or
 intrinsic-Ricci-zero local solutions. A new internal
 `Geometry.Manifold.RicciFlow.DeTurck` file now packages the intrinsic DeTurck
 one-form, vector field, correction term, and gauge-fixed Ricci-DeTurck
 right-hand side, together with reduction lemmas showing that this gauge-fixed
 boundary agrees with the intrinsic Ricci-flow equation whenever the chosen
 background family is Levi-Civita for the evolving metric. In the
  zero-dimensional tangent-fiber case, the DeTurck correction, Ricci-DeTurck
  right-hand side, and DeTurck solution metric velocity are also proved to vanish
  for any background family; the intrinsic DeTurck and intrinsic Ricci-flow
  equations are proved equivalent there for arbitrary backgrounds, yielding
  solution and local-solution conversions in both directions without a
   Levi-Civita-background hypothesis, and background-free metric stationarity for
   DeTurck local solutions. It now also packages an arbitrary-background
   intrinsic Ricci-DeTurck local-existence/uniqueness theorem wrapper in this
   zero-dimensional case, with conversions back to intrinsic/ordinary Ricci-flow
   theorem families, equivalences with the chosen-background DeTurck theorem
   family, and an empty-compact-manifold specialization. The lower
   Levi-Civita layer now proves that every affine/time-dependent connection is
   automatically Levi-Civita on zero-dimensional tangent fibers, so DeTurck
   local solutions there also expose background-free Levi-Civita witnesses and
   stored-background connection stationarity/uniqueness. DeTurck local
   solutions with Levi-Civita background inherit the corresponding
   canonical-connection uniqueness consequences. That same file now
 also packages background-explicit intrinsic Ricci-DeTurck solution /
 local-solution wrappers, conversions from intrinsic Ricci-flow solutions using
 the chosen Levi-Civita family, and chosen-background Ricci-flat stationary
 comparison lemmas against arbitrary zero-velocity or intrinsic-Ricci-zero
 DeTurck local solutions with Levi-Civita background. It now also mirrors the
   common-time connection-equality consequences on that Levi-Civita-background
    DeTurck side and packages a chosen-background DeTurck local-existence /
    uniqueness theorem package, plus typed conversions between its
    theorem-family wrapper and the intrinsic/ordinary Ricci-flow theorem-family
     wrappers, plus zero-dimensional tangent-fiber and empty-manifold
     theorem-family instances equivalent to the current intrinsic Ricci-flow
     package. A further internal
  `Geometry.Manifold.RicciFlow.GaugeTransport` file
  now packages time-dependent bundled `C^1` self-map families together with
  pullback of tangent-bundle bilinear tensor fields and evolving metric tensors,
  proving identity, composition, symmetry-preservation, initial-time invariance,
  and zero-dimensional pulled-back metric-tensor vanishing lemmas for that
  transport layer, and it also defines
  time-dependent gauge-flow / anchored-map predicates tying those pullbacks to
  integral-curve data. It now also packages bundled `C^1`
  self-diffeomorphisms and time-dependent diffeomorphism families, together
  with tangent pushforward / pullback maps and inverse lemmas for the induced
  transport of tangent-vector fields. The diffeomorphism pullback is now also
  identified with mathlib's manifold `VectorField.mpullback`, and a further
  internal `C^2` diffeomorphism layer now packages time-dependent `C^2` gauge
  families, proves that both pullback and pushforward preserve `C^1`
  tangent-vector-field regularity, and records the corresponding pointwise
  differentiability corollaries needed before defining affine-connection
  transport. A first internal
   `Geometry.Manifold.RicciFlow.GaugeReduction` wrapper now specializes those
   objects to the intrinsic DeTurck vector field and proves that anchored gauge
   pullbacks preserve the prescribed initial metric tensor for intrinsic
   Ricci-DeTurck local solutions; it also now includes a diffeomorphism-valued
   anchored DeTurck gauge wrapper reducing to the map-valued one. It now also
   constructs the identity diffeomorphism gauge whenever the DeTurck background
   is Levi-Civita for the evolving metric, and also in the zero-dimensional
   tangent-fiber case for arbitrary backgrounds. It proves the corresponding
    all-time pullback connection smoothness/equation bridge, directly turns any
    zero-dimensional DeTurck local solution into an intrinsic/gauge-reduced
    Ricci-flow local solution through the identity gauge, and packages the generic
   smooth Levi-Civita-background Ricci-DeTurck local-existence/uniqueness
   theorem package conversion back to intrinsic Ricci flow through that identity
   gauge. The identity `C^3` gauge path now also proves that the concrete
   gauge-corrected pullback velocity is exactly the source DeTurck velocity and
   packages chosen-background DeTurck theorem families as gauge-reducible by the
   identity diffeomorphism gauge. It now also records a conditional
   gauge-reduced DeTurck local-solution
   package for the non-identity case, bundling the transformed metric, velocity,
    pulled-back-background regularity, and transformed Ricci-flow equation
    hypotheses whose proof yields intrinsic and ordinary local-existence/uniqueness
    packages. This package now also re-packages the transformed metric as an
    actual pulled-back Ricci-DeTurck local solution with Levi-Civita pulled-back
    background, converts that data into the generic Levi-Civita-background
     DeTurck package, compares the pulled-back backgrounds on common intervals,
     exposes the gauge ODE and transformed Ricci-flow/DeTurck equations on the
     actual local interval, expands the source DeTurck equation into its
     background-Ricci plus DeTurck-correction form, records the pointwise
      connection-uniqueness consequences at the ordinary, intrinsic,
      chosen-background, gauge-reduced, and scalar-derivative theorem-family
      levels, proves that the identity `C^3` gauge supplies the explicit
      scalar-derivative gauge-reducible interface for chosen-background
       packages, exposes direct identity-`C^3` gauge-reduced wrappers with
       source/metric/velocity simplification lemmas, and now lowers the
       non-identity route to raw `C^3` diffeomorphism families with anchoring,
         the gauge-flow equation, and scalar inner-product derivative identities.
         A thin `GaugeReduction.Diffeomorph3FlowDerivative` module now names the
         primitive intrinsic gauge-flow derivative proposition, proves it
         equivalent to the geometric `SatisfiesGaugeFlowOn` statement for `C^3`
         diffeomorphism families, and packages the corresponding
         chosen-DeTurck-solution family interface plus a reusable geometric
         gauge-flow family bundle with anchored-gauge projections and direct
         gauge-reducible/intrinsic/ordinary theorem-family routes from
         pulled-back metric time-derivative data, together with a
          fixed-initial-value-problem bundle exposing matching local
          theorem-package projections. Both bundle levels now also build the
          gauge-pulled metric time-derivative proof from scalar inner-product
          derivative hypotheses, and extract those scalar hypotheses back from
          the same proof.
        The non-identity right-slot/Ricci-transport obligation is now discharged
        by the `C^3` transport layer; the remaining primitive non-identity gauge
        input is the scalar chain-rule proof for the gauge-pulled metric.
        The optional `PoincareCurvature.RicciFlowLocalExistence` aggregate imports the
        gauge-reduction boundary. It also records the pointwise
    gauge-flow derivative, and rewrites transformed velocity as `-2` times the
     trace-conjugated pulled-back Ricci endomorphism supplied by the connection
     transport layer. In the zero-dimensional tangent-fiber case it also proves
     that both the source DeTurck and transformed velocities vanish, the source
     DeTurck intrinsic Ricci/Ricci-DeTurck right-hand sides and transformed
     intrinsic Ricci/Ricci-flow right-hand sides vanish, source DeTurck metrics
     and canonical source connections are stationary/unique, the source stored
     background is stationary/unique in connection values, and transformed local
     solutions are stationary/unique at the metric and connection levels. The
      identity-gauge layer now also exposes a smooth Levi-Civita-background
      DeTurck stationary local solution and a gauge-reduced stationary local
       solution for Ricci-flat initial data, with source and transformed velocity
       zero, Levi-Civita-background/source/transformed initial-metric
       stationarity, Levi-Civita-background/source-background stationarity in
       connection values, Levi-Civita-background/source/transformed intrinsic
       Ricci/Ricci-flow right-hand-side vanishing (plus the corresponding
       Ricci-DeTurck right-hand-side vanishing on the DeTurck sides), pointwise
       Levi-Civita-background/source/transformed equivalences between zero
       velocity and intrinsic Ricci-zero, and
       Levi-Civita-background/source/transformed metric and connection
       comparison against arbitrary matching solutions whose corresponding
       velocity or intrinsic Ricci tensor vanishes on the common interval. It
       also includes
      metric-uniqueness consequences, typed
      ordinary/intrinsic theorem-family conversions through the identity gauge,
      a theorem-family reduction for all initial-value problems, and a
      zero-dimensional conversion from the arbitrary-background DeTurck theorem
      family through the identity gauge into the gauge-reduced theorem family.
   The same
   internal `C^2` diffeomorphism layer now also defines a bundled pullback of
   tangent-bundle covariant derivatives, proves inverse identities for
   pullback/pushforward of vector fields, identifies transport of `∇_X Y` under
   that pullback, proves the corresponding torsion transport formula, shows
  torsion-free affine connections remain torsion-free after pullback (under the
  ambient Riemannian tangent-bundle hypotheses already used by the Levi-Civita
  layer), transports affine-connection difference tensors, proves that metric
  compatibility transports once a chosen target smooth metric is identified
  with the pulled-back inner product, lifts the same statement slice by slice
  to time-dependent `C^2` diffeomorphism/connection families, and now also
  packages the pointwise pullback of tangent-space bilinear forms along the
   tangent equivalence, including symmetry, positive-definiteness, and unit-ball
   boundedness transport for that fiberwise pullback. One further regularity
   step has also landed on the connection side:
  adding a smooth bundle-valued one-form to a `C^n` covariant derivative now
  preserves `C^n` regularity. On the metric-space side, the public vector-bundle layer now also proves
  finite-dimensional coercivity and operator-norm openness lemmas for
  positive-definite continuous bilinear forms, which is the first honest
  fiberwise openness step toward treating Riemannian metrics as an open subset of
a section space, and it now lifts that result to compact continuous families in
`C(K, ·)` and `BoundedContinuousFunction`, and then through preferred bundle
trivialization coordinates to the finite-cover `ContinuousSectionSpace` model,
where actual positive-definite bilinear-form sections form an open subset, the
symmetric locus is now closed, and continuous Riemannian metrics are shown to
inhabit the refined symmetric positive-definite locus inside that model. The
same package now also constructs a transported continuous-linear coordinatewise
antisymmetric-defect map whose kernel is exactly that symmetric locus, and it
presents the metric locus as an open subset of the closed symmetric section
subtype. The connection side has
also gained a new `C^1` regularity layer on `C^2` bundle data: the package now
proves existence of global `C^1` affine connections, specializes that theorem
to the tangent bundle, and adds section-level `C^1` regularity lemmas for
`toDual`, fiberwise composition, `metricDefectAux`, and torsion on `C^2`
vector fields (the torsion theorem currently uses a `C^3` manifold
hypothesis). That regularity gap is now closed as well: the package proves the
  local-to-global `C^1` regularity of `leviCivitaConnection`, together with
  existence of global and slicewise `C^1` Levi-Civita connections. The
  obstruction to point 4 is therefore no longer Levi-Civita regularity, nor
  even the bare metric-side or affine-connection transport object: the
  gauge-transport layer now also packages the actual pulled-back `C^1`
  Riemannian metric as a bundled `ContMDiffRiemannianMetric I 1`, proves the
  coordinate-regularity theorem for the pulled-back bilinear form, and upgrades
  metric-compatibility and Levi-Civita transport to use that concrete metric
  instead of an ad hoc pulled-back-inner-product hypothesis. A stronger `C^3`
  diffeomorphism layer now proves that pulling back a `C^2` metric remains a
  bundled `C^2` Riemannian metric, lifts this to `MetricFamily` pullbacks, and
  provides time-dependent compatibility/Levi-Civita wrappers for the associated
  pulled-back connection family. On the time-dependent connection side,
  torsion-free transport now also lifts slice by slice to pulled-back connection
  families, the raw curvature commutator now transports under both static and
  family pullback of the connection, and the same gauge-transport layer now
  also pushes the pulled-back `ricciEndomorphism` forward to a target-side raw
  curvature operator while identifying pulled-back `ricciCurvature` with the
  trace of the corresponding tangent-map-conjugated endomorphism; the
  gauge-reduction layer now uses those trace identities to expose transformed
  Ricci-flow velocity in precisely that pulled-back Ricci-endomorphism form.
  The same connection-transport layer now also proves time-dependent pullback
  formulas for connection-difference trace endomorphisms and the induced source
   DeTurck one-form trace, and the gauge-reduction layer now includes a `C^3`
   diffeomorphism-gauge wrapper and constructor whose transformed metric is the
   actual `C^2` gauge pullback rather than an externally supplied
   `MetricFamily`; the identity-gauge bridge has a corresponding proof-bearing
   `C^3` variant. The non-identity `C^3` path now also has a concrete
   gauge-corrected pulled-back velocity, proves that its metric-dual DeTurck
   vector pushes forward to the source DeTurck vector field, identifies the
   pulled-back DeTurck correction with the source DeTurck correction at the
   gauge image, and proves the corrected velocity is `-2` times the source
   background Ricci curvature at the gauge image. The same proof is now
   factored into an explicit `SatisfiesEquationAt` theorem: assuming the
   source-Ricci-to-pullback-Ricci transport identity, the concrete corrected
   velocity satisfies the pulled-back Ricci-flow equation, and the stronger
   constructor uses that exact theorem. The `C^3` transport layer now also
   proves direct family-level curvature transport wrappers for the raw
   commutator, curvature tensor, pushed-forward Ricci endomorphism, and
   tangent-map-conjugated Ricci endomorphism. It also reduces Ricci-curvature
   transport first to the corresponding tangent-map-conjugated
   Ricci-endomorphism identity and then to the remaining right-slot curvature
   replacement for the pushed canonical smooth extension, with endomorphism- and
   Ricci-level packaged variants that discharge this right-slot step from
   eventual equality of the pushed and canonical right-slot extensions, plus a
   stricter section-equality variant for the case where the pushed right-slot
   extension is globally equal to the canonical extension. These right-slot
   variants are now wired back into the gauge-reduction package: they prove the
   exact source-Ricci transport obligation from direct right-slot curvature
   replacement, local eventual equality, or stricter section equality, expose the
   anchored-time case where the stricter equality follows from the identity
   slice, derive the pulled-back corrected-velocity equation directly from the
   pointwise right-slot curvature replacement and at the initial anchored time,
   and provide `C^3`
   corrected-velocity constructors whose final geometric hypotheses are
   right-slot replacement facts rather than the whole Ricci-transport identity.
    The curvature tensor layer now also weakens the
    right-slot scalar-multiplication commutator lemma from a global `C^2` scalar
    hypothesis to global differentiability plus the explicit first-derivative
    commutator obligations, and proves a finite `C^2` expansion criterion for
    replacing the raw-curvature right slot when two local finite expansions share
    the same smooth section generators and have coefficients agreeing at the
    evaluation point. This is the current proof-bearing local-frame reduction
    toward full right-slot tensoriality. It also exposes a bundled curvature
    tensor computation rule from arbitrary smooth left/middle representatives and
    a locally canonical right representative, plus the supporting fact that the
    canonical smooth extension is locally the raw trivialization `extend` section
    because its bump is eventually `1`; for the local frame at `trivializationAt`,
    those canonical extensions are also locally equal to the frame sections
    themselves. The canonical smooth extension's local-frame coefficient
    functions are now proved globally `C^2` automatically from the
    bump-supported extension construction. This yields a concrete local-frame
    right-slot replacement criterion: if the pushed/arbitrary representative's
    `trivializationAt` frame coefficient functions are globally `C^2` and
    agree at the point with the target vector's coefficients, then raw curvature
    sees the same right slot. The same coefficient criterion is also packaged as
    a bundled curvature-tensor computation rule for arbitrary smooth left/middle
    representatives and an arbitrary right-slot representative whose local-frame
    coefficients match the target vector at the point. The `C^3`
    gauge-transport layer now has curvature-tensor transport theorems that first
    discharge the right-slot step either from local-frame coefficient hypotheses,
    eventual equality, global equality, or source-bump support containment; it
    then removes those artificial right-slot hypotheses entirely by choosing a
    smaller auxiliary bump supported inside the intersection of the source frame
    domain and the gauge preimage of the target frame domain. The resulting
    hypothesis-free curvature tensor transport feeds through the
    tangent-map-conjugated Ricci endomorphism and Ricci-curvature transport
    identities. The gauge-reduction package now consumes these transport
    theorems directly: it still exposes the coefficient and support variants,
   including basis-free finite-dimensional support variants using
   `Module.finBasis`, but also provides a source-Ricci transport theorem,
   corrected-velocity equation theorem, and corrected-velocity gauge-reduction
   constructor with no right-slot smoothness, equality, or support-containment
   assumptions. The time-derivative boundary has also been loosened: the local
   existence layer now has congruence lemmas for transporting time derivatives
   across pointwise-equal metric/velocity tensors, and gauge reduction has a
   constructor that accepts any transformed velocity pointwise equal to the
   concrete corrected gauge velocity. The time-derivative boundary has been
   sharpened further: the `C^3` transport layer proves that time derivatives
   commute with pullback by a time-independent `C^3` diffeomorphism, and the
   same static transport theorem now proves Ricci-flow invariance under fixed
   `C^3` diffeomorphism pullback, deriving pulled-back connection regularity
   from the transported Levi-Civita hypothesis; this is also lifted to the
   intrinsic metric-only Ricci-flow boundary, including the pointwise intrinsic
   equation, and packaged at the `Solution`, `IntrinsicSolution`,
   `LocalSolution`, and `IntrinsicLocalSolution` levels. These packages now
   include preservation of zero metric velocity under fixed pullback,
    preservation of ordinary and intrinsic local-solution nonemptiness for the
    pulled-back initial data, full ordinary and intrinsic theorem-package
    transport to pulled-back initial data, transported metric and
    Levi-Civita-connection uniqueness for both fixed-pullback images and
    arbitrary target-side local solutions, chosen-background Ricci-DeTurck
    theorem-package transport through the intrinsic package, and a corollary
    transporting the current Ricci-flat stationary local-existence examples through fixed `C^3` pullbacks. The
   non-identity gauge constructor can now consume the exact scalar derivative
   formula for the pulled-back inner product instead of a prepackaged
   `HasTimeDerivativeOn` proof, and a chosen-background Ricci-DeTurck theorem
   package now converts to the gauge-reduced Ricci-flow theorem package from a
   gauge-reducible chosen DeTurck solution, or from per-solution `C^3` gauges,
   using either the packaged time-derivative theorem or that exact scalar
   derivative formula. This final conditional boundary is also bundled as
   local-solution, theorem-package, and theorem-family structures whose
   conversions produce ordinary `LocalExistenceUniqueness` packages and the new
   intrinsic/ordinary theorem-family wrappers, including the direct `C^3` gauge,
   raw gauge-flow scalar/time-derivative routes, the derivative-level gauge-flow
   plus scalar-derivative boundary, and the derivative-level gauge-flow plus
   pullback-time-derivative boundary; the zero-dimensional tangent-fiber
   case and empty-manifold case are also packaged at the ordinary, intrinsic,
   chosen-background DeTurck, Levi-Civita-background, and gauge-reduced
   theorem-family levels. The
   Levi-Civita regularity boundary is also
   closed at this layer: any slicewise Levi-Civita family for a `C^2` metric
   family is proved slicewise `C^1`, so the source and pulled-back background
   regularity obligations in the final `C^3` gauge-reduction constructors are
   now derived from the Levi-Civita hypotheses rather than assumed separately;
   the corresponding Levi-Civita-background DeTurck wrapper no longer stores
   slicewise background regularity as an independent field. The same layer proves
   that gauge pullback and pushforward preserve
   `C^2` tangent-vector-field regularity, both for individual diffeomorphisms
   and slice-by-slice for diffeomorphism families, including the pushed and
   pulled canonical smooth extensions that appear in curvature tensor
   contractions, exposes direct anchored `C^3` tangent and vector-field
   pushforward identities, extracts the scalar inner-product derivative
    obligation from a proved `C^3` gauge-pulled metric time derivative, routes raw
    pointwise gauge-flow derivatives plus scalar derivative data to the explicit
    scalar-derivative, gauge-reduced, intrinsic, and ordinary packages, exposes the
    same scalar-derivative route as global and interval analytic boundary-chart
     intrinsic/ordinary theorem-family endpoints, now packages those endpoint
     hypotheses into bundled global/interval data objects using the named
     gauge-flow derivative-family interface with direct scalar,
     intrinsic, and ordinary projections, and adds a separate
     `AnalyticPDE.GeometricGaugeFlow` endpoint layer whose global/interval bundles
     take geometric `C^3` gauge-flow families plus pullback-time-derivative
     proofs, derive the scalar endpoint internally, and project through the
     derivative bundles to the same scalar, gauge-reducible, intrinsic, and
     ordinary theorem-family endpoints, with a fixed-IVP endpoint bundle and a
     family-to-fixed-IVP projection for local theorem packages, and adds a
     `GaugeReduction.Diffeomorph3FlowExistence` layer naming the raw `C^3`
     diffeomorphism-flow existence witness expected from the manifold ODE
     theorem and converting it into the fixed-IVP and theorem-family geometric
    gauge-flow bundles, with fixed-IVP, global, and interval geometric endpoint
    data able to replace their bundled gauge-flow component by such a raw
    existence witness, and a thin `AnalyticPDE.SmoothRealization` module naming
    the global/interval PDE closure data that turns a Banach chart solution into
    a smooth chosen-background DeTurck solution and its self-encoding candidate,
    with all-solutions smooth-realization plus reverse-candidate-encoding
    closure packaged into direct global/interval chosen-background DeTurck
    theorem packages,
     and routes raw pointwise gauge-flow derivatives plus
    pullback-time-derivative input to scalar-derivative, intrinsic, and ordinary theorem packages.
     The optional `PoincareCurvature.RicciFlowLocalExistence` aggregate also imports the
      `AnalyticPDE` evolution layer proving the reusable
    Picard-Lindelof Banach-evolution local-solution core, open-state
    state-preserving uniqueness, a positive-definite finite-cover metric-locus
    bridge, an abstract continuous-linear symmetry/fixed-locus preservation
    theorem for later slot-swap symmetry, and a direct continuous-linear
    antisymmetric-defect criterion that keeps solutions in the symmetric
      positive-definite locus once the vector field's coordinatewise defect
       vanishes, plus interval-scoped fixed-locus, fixed-symmetry, and direct-defect
       variants lifted to time-dependent finite-cover evolutions, bundled
       continuous-Riemannian initial data, a reusable interval coordinatewise-defect
       chart interface, a direct global-geometric-to-interval-defect chart adapter,
       and a pointwise-symmetric-vector-field variant that supplies that defect
       vanishing automatically; the global metric-reification and
       chosen-background package constructors now take their witnesses through
       this terminal defect route, and globally Lipschitz charts expose
       terminal-bounded continuous-metric and metric-curve reification endpoints
       directly, plus a direct bounded candidate-encoding witness for the
       associated interval chart and global/local-family chosen-background routes
       that can consume those interval-bounded encodings without rebuilding
        global encodings; the direct global intrinsic Ricci-flow endpoint also
        accepts the same interval-bounded encodings, and the global
        gauge-reducible and scalar-inner-derivative gauge packages, including
        their theorem-family and direct intrinsic-family projections, can now be
        built from them; smooth Banach realizations can now reduce the
        closed-interval time-derivative boundary, including at the global and
        interval chosen-background theorem-package surfaces and the corresponding
        local/family non-identity gauge-time-derivative intrinsic Ricci-flow endpoints,
        to the two endpoint derivative statements; the global and interval charts
        also expose reusable single-solution and theorem-family
        endpoint-to-boundary derivative adapters, and the raw global/interval
        non-identity gauge-flow time-derivative theorem-family endpoints now
        consume only endpoint time-derivative data before the gauge-flow
        conversion; encoded candidates in the same global or interval chart now
        have a named metric-uniqueness theorem on their common interval. The same
        state-set mechanism now also has a
      non-autonomous Picard-Lindelof specialization: time-dependent Banach-chart
     vector fields satisfying the verified Picard/Lipschitz hypotheses shrink to
     positive-definite local metric evolutions and, when identified pointwise with
     the intrinsic Ricci-DeTurck RHS, remain symmetric by the proved geometric
     symmetry theorem. This time-dependent Ricci-DeTurck bridge is also bundled
     as `TimeDependentGeometricRicciDeTurckBanachChart`, whose fields are
     precisely the remaining Picard/Lipschitz/geometric-agreement obligations and
     whose extractor produces the symmetric positive-definite local Banach metric
     evolution. The reverse metric bridge is now proof-bearing as well: any
      finite-cover symmetric positive-definite section-state reifies to a bundled
      continuous Riemannian metric, and the packaged Banach solution now exposes
       one metric-valued curve whose local-interval inner products agree with the
       Banach section curve, whose initial value is the original initial metric,
       and whose common-interval uniqueness follows from Banach uniqueness. For
       autonomous charts, a new local `C^1` reduction also shrinks to an open
       neighborhood inside the positive-definite metric locus and derives the
       needed local Lipschitz bound there, so chart estimates can be proved
       locally around the initial metric instead of globally on the whole metric
        locus; for non-autonomous charts, the lower-level positive-definite and
        symmetric bridges, plus the reusable
         `TimeDependentGeometricRicciDeTurckBanachChartOnIcc` package, now also
         accept Lipschitz estimates restricted to the verified Picard time
         interval and expose the constructed solution's `terminalTime ≤ T`
         bound, including after reifying the Banach section solution as
         continuous Riemannian metrics or a single metric-valued curve. A
       smooth-realization adapter packages the exact remaining
      lift/time-derivative/DeTurck-equation obligations needed to turn such a
      Banach solution into an `IntrinsicDeTurckLocalSolution`; when supplied for
      a smooth-IVP-seeded chart solution it extracts that DeTurck local solution,
       and two such smooth realizations have equal metric tensors on common
       intervals. The interval chart also has a bounded candidate-encoding
       theorem: candidates whose Banach representatives satisfy
        `terminalTime ≤ T` promote all the way to
        `IntrinsicDeTurckLocalExistenceUniqueness`, the identity-gauge intrinsic
         Ricci-flow package, the non-identity gauge-reducible package, and the
         explicit scalar-inner-derivative gauge package using only
         `Icc`-restricted Lipschitz control; the chosen-background identity,
         arbitrary-background identity, gauge-reducible, and
         scalar-inner-derivative gauge routes now preserve the stronger
         arbitrary-background DeTurck, chosen-background DeTurck, and gauge
          theorem-family packages before exposing
          `IntrinsicLocalExistenceUniquenessFamily` extractors, and the chart
          packages no longer carry a separate finite-cover section-space
          completeness field because that obligation is discharged by the
          existing `ContinuousSectionSpace` complete-space instance. With the explicit
        reverse-chart
        encoding for arbitrary or
       chosen-background candidates, the same package now promotes to
      `IntrinsicDeTurckLocalExistenceUniqueness`,
      `ChosenIntrinsicDeTurckLocalExistenceUniqueness`, and then to intrinsic
      Ricci-flow local existence/uniqueness either by the chosen-background
      identity route or by the non-identity gauge-reducibility package; the
      global-chart family theorem produces `IntrinsicLocalExistenceUniquenessFamily`
      once these chart, realization, encoding, and gauge-reducibility obligations
      are supplied for every initial value problem. The direct interval
      chosen-background route and the global/interval raw `C^3` gauge-flow routes,
      including the boundary-reduced derivative-level scalar-derivative and
      time-derivative boundaries, now also expose intrinsic/ordinary theorem-family
      endpoints, and the constant `C^3` identity family supplies primitive
      derivative-level gauge data whenever the DeTurck gauge field vanishes, with direct
      identity-route intrinsic/ordinary projections matching the non-identity APIs. These criteria are also
      specialized to genuine bundled continuous Riemannian initial metrics, so
       future Ricci-DeTurck Banach-chart work no longer has to manually prove
       finite-cover metric-locus membership for the initial datum. The interval
       chart now also derives the genuine symmetric-carrier vector field from
       the ambient Ricci-DeTurck chart: geometric RHS symmetry proves tangency
       to symmetric bilinear forms, and the ambient interval Lipschitz estimate
       descends to the restricted metric-locus vector field. The curvature, time-dependent geometry,
    intrinsic Ricci-flow, and DeTurck layers now prove the geometric symmetry
    input outright: metric compatibility gives curvature-operator
    skew-adjointness, torsion-freeness gives first Bianchi, the Ricci contraction
    is symmetric for Levi-Civita families, the intrinsic Ricci-flow RHS is
    symmetric, and the full intrinsic Ricci-DeTurck RHS is symmetric because the
    DeTurck correction term itself is symmetric. The analytic side is therefore
    no longer purely documentary. The raw `C³` gauge-flow existence layer
    (`Diffeomorph3GaugeFlowOn`) now exposes identity-flow constructors for
    arbitrary vector fields in subsingleton tangent, subsingleton model, and
    empty-manifold cases; `IntrinsicDeTurckGaugeFlowExistence(.Family)` lifts
    those to intrinsic DeTurck identity-gauge constructors, in addition to the
    chosen-Levi-Civita-background case. Raw intrinsic gauge-flow existence
    witnesses now also feed directly into the gauge-reduced, intrinsic, and
    ordinary theorem-package routes using either pulled-back metric
    time-derivative proofs or scalar inner-product derivative proofs. The raw
    flow layer also has fixed-IVP and theorem-family constructors from both
     pointwise `HasMFDerivAt[s]` and unrestricted `HasMFDerivAt` data produced by
     ODE/integral-curve theorems, named-derivative-family adapters,
     geometric-to-raw adapters, direct derivative/local-at-time extractors, and
     time-set restriction for raw flows, so future manifold-flow existence results
     can plug in through either derivative data or existing geometric gauge-flow
     bundles without a separate
     `SatisfiesGaugeFlowOn` repackaging step. The Banach-model ODE component of
     the positive-dimensional raw-flow construction is now also proof-bearing:
     `GaugeReduction.ModelGaugeFlowODE` packages mathlib's time-dependent
     Picard-Lindelöf theorem as local model flows with initialization on a
     closed ball, closed-interval ODE derivative data, and Lipschitz dependence
      on the initial point; it also packages the continuous space-time
      partial-flow form needed for chart gluing, plus the autonomous `C¹`
      integral-curve specialization and Gronwall uniqueness bridges for packaged
      local model flows on open and closed Picard intervals, including direct
      uniqueness routes for the continuous space-time package. The same model
      ODE bridge now packages the tangent-map variational equation
      `A'(t) = Df(t, flow(t)) ∘ A(t)` in `VariationalLocalFlowSolution`, matching
      the remaining coordinate-model `A`-derivative hypothesis, and proves
      variational/tangent-map uniqueness on the interior interval when the base
      local flows agree and the linearized ODE is uniformly Lipschitz. Raw gauge flows now also expose the first
      chart-membership bridge needed for coordinate pullback formulas:
      neighborhood-time flow equations imply continuity of `τ ↦ Φ_τ(x)` and
      eventual membership in the tangent trivialization at `Φ_t(x)`, with the
      same facts available directly within the raw time set for restricted ODE
      intervals. Thus the
     full point-4 input chain has no gauge-flow gap in any of the
     currently-proved special cases. The
    non-identity gauge time-regularity
    interface now also has the proof-bearing scalar-to-tensor bridge, and the
    fixed non-identity gauge case exposes both tensor and scalar derivative
    adapters in the thin `Diffeomorph3FlowTimeDerivative` module. That module
    now names the remaining dynamic scalar chain-rule target as
    `PullbackMetricInnerDerivativeOn` and proves its equivalence with
    `HasTimeDerivativeOn` for the pulled-back metric, with fixed-IVP and
    theorem-family bundle adapters, raw-existence adapters, and direct
    gauge-reduced, intrinsic, and ordinary theorem-package projections, plus
    time-set restriction, identity-gauge specialization, and fixed-IVP/family
    equivalence lemmas with tensor time-derivative data for both geometric and
    raw gauge-flow bundles; chosen-background, subsingleton-tangent/model, and
    empty-manifold identity raw gauge-flow fixed-IVP and theorem-family
    witnesses now also provide the named scalar data directly, so the
    remaining primitive input is exactly that scalar identity. The first
     model-space chain-rule component of that scalar identity is now proved:
     differentiating `B(t)(u(t), v(t))`, and the gauge-coordinate specialization
     `B(t)(A(t)u, A(t)v)`, including the `D ∘ A(t)` tangent-map derivative
     contribution, plus eventual-equality transfer lemmas for chart-local
     coordinate identifications. A coordinate-level package
      `CoordinatePullbackMetricInnerDerivativeOn` now also promotes those
      chartwise `B/A/D` derivative hypotheses to the actual geometric
      `PullbackMetricInnerDerivativeOn` scalar target and directly to tensor
      `HasTimeDerivativeOn` for the gauge-pulled metric, while
      `pullbackMetricInnerCoordinateModel` names the preferred
      `B(τ)(A(τ)u)(A(τ)v)` scalar expression; eventual target-trivialization
       membership now proves equality between that coordinate model and the
       geometric pullback scalar, and raw `Diffeomorph3GaugeFlowOn` witnesses
       supply this equality near times where their time set is a neighborhood.
       The remaining positive-dimensional primitive is isolated as
       `CoordinatePullbackMetricModelDerivativeOn`, a derivative package for the
       named coordinate model that promotes directly to the geometric scalar
       target and tensor `HasTimeDerivativeOn`, including raw-gauge-flow wrappers.
       The model algebra now also proves the moving metric-component chain rule
       for `Bfield(τ, y(τ))` and its combined
       `Bfield(τ, y(τ))(A(τ)u)(A(τ)v)` form with the variational tangent-map
       equation, bundled as `CoordinatePullbackMetricFieldDerivativeOn` with
       scalar, tensor, and raw-gauge-flow promotion routes.
       The coordinate data also restricts to smaller time sets and lifts
       through the fixed-IVP, theorem-family, and raw-existence gauge-flow APIs,
       so chart computations can feed the point-4 theorem routes without an
       intermediate tensor repackaging step. In the subsingleton-tangent case this non-identity
    time-regularity obligation is already closed for arbitrary geometric `C³`
    DeTurck gauge-flow families by componentwise vanishing, with direct
    gauge-reduced projections and matching model-space/empty-manifold synonyms
    plus raw gauge-flow-existence theorem-package routes requiring no extra
    derivative input; the ordinary theorem-family endpoint is now also available
    through that full chosen-DeTurck → raw `C³` gauge-flow → gauge-reduced chain
    in the subsingleton-tangent, subsingleton-model, and empty-manifold cases.
    The fixed-IVP geometric and raw gauge-flow routes now also expose matching
    model-space and empty-manifold aliases, so the zero-dimensional gauge-flow
    API is symmetric across fixed-IVP and theorem-family packages.
    The rank-one compact special case also exposes intrinsic and ordinary
    theorem packages through the gauge-reduced rank-one package, including
    model-space theorem-family aliases. The smooth Ricci-DeTurck global and
    interval chart-closure data now also projects to intrinsic and ordinary
    compact point-4 theorem packages through the raw identity `C^3` gauge-flow
    witness plus named scalar derivative data, so the PDE-realization endpoint
    is wired through the same raw-gauge interface as the rest of the gauge-flow
    API.
    What still
    remains is the geometric-analysis specialization for positive-dimensional
    non-identity gauges: that scalar chain-rule proof, an actual existence
    theorem producing raw gauge flows with the required regularity in the
    general case, and the
    quasilinear parabolic PDE framework for genuine Ricci-flow local existence
    and uniqueness, including the actual Ricci-DeTurck Banach chart and
    estimates plus the identification of that Banach representative with the
    geometric Ricci-DeTurck right-hand side. See `docs/point4-plan.md` for the
    systematic decomposition of these three remaining items.

### 5. Evolution equations and parabolic maximum principles

Formalize the evolution formulas for scalar curvature, Ricci curvature, and
other natural quantities under Ricci flow, together with the maximum-principle
arguments used to control them.

Why this is paper-worthy:
this is the engine behind many later monotonicity and pinching arguments.

### 6. Distance distortion, comparison, and compactness toolkit

Build the reusable analytic toolkit around evolving metrics:

- control of lengths and distances under the flow
- injectivity-radius style interfaces where needed
- compactness principles for sequences of Ricci flows
- blow-up and rescaling machinery

Why this is paper-worthy:
this creates the language for passing to singularity models and ancient limits.

### 7. Perelman's `L`-geometry

Formalize Perelman's reduced length, reduced distance, and reduced volume.

Why this is paper-worthy:
these are not just definitions; they are central conceptual inventions in the
proof and would produce a distinct formalized theory with independent value.

### 8. Non-collapsing theorems

Formalize Perelman's no-local-collapsing theory and the estimates needed to use
it in the singularity analysis.

Why this is paper-worthy:
this is one of the signature results of the proof and a major benchmark for any
proof assistant formalization of geometric analysis.

### 9. Ancient-solution theory in dimension 3

Formalize the classification results for non-collapsed ancient solutions that
feed into the description of high-curvature regions in dimension 3.

Why this is paper-worthy:
the theory of ancient solutions is already a major theorem cluster even before
it is connected back to surgery.

### 10. Canonical-neighborhood and neck-detection machinery

Formalize the local geometric recognition results that identify necks, caps, and
other canonical neighborhoods in high-curvature regions.

Why this is paper-worthy:
this is the interface between the singularity analysis and the actual surgery
construction.

### 11. Ricci flow with surgery

Formalize the existence of Ricci flow with surgery for the relevant class of
compact 3-manifolds.

Why this is paper-worthy:
this is a landmark result even in isolation and is one of the clearest natural
paper boundaries in the whole program.

### 12. Topological control of surgery

Formalize the effect of surgery on the topology of the manifold and the precise
bookkeeping that lets the flow continue while preserving the classification
target.

Why this is paper-worthy:
the surgery theorem is not useful without a mathematically precise bridge back
to topology.

### 13. Finite-time extinction

Formalize the finite-time extinction theorem for the relevant compact
3-manifolds.

Why this is paper-worthy:
this is the main end-stage theorem in the Ricci-flow-with-surgery route and one
of the cleanest major milestones before the final corollary.

### 14. Topological Poincare corollary

Extract from the extinction theorem the statement that a closed simply connected
3-manifold is homeomorphic to the 3-sphere.

Why this is paper-worthy:
even if short on paper, in Lean this requires careful packaging of everything
above into a final topological theorem with a clean interface to existing
topology APIs.

### 15. Smooth Poincare corollary

Bridge from the topological 3-dimensional statement to the smooth statement that
a smooth closed simply connected 3-manifold is diffeomorphic to `S^3`.

Why this is paper-worthy:
this final bridge is mathematically distinct from the analytic part of the
program and would likely deserve its own paper-scale treatment in Lean.

## What seems most urgent

With points 1 through 3 closed and point 4 still open, the most leverage likely
comes from:

1. an actual Lean proof of Ricci-flow local existence and uniqueness
2. evolution equations and maximum principles
3. distance distortion, comparison, and compactness toolkit
4. Perelman-specific monotonicity and non-collapsing packages

Without those, later Perelman-specific projects have nowhere to land.
