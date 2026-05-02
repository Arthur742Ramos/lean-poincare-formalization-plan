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
overlaps; the same rank-one compact special case is also exposed through
gauge-reduced-to-intrinsic/ordinary theorem-package projections. The package also includes a
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
   proves it equivalent to the geometric `SatisfiesGaugeFlowOn` formulation,
   provides monotonicity lemmas for restricting within-time-set and
   ordinary-at-time derivative views to smaller time sets, upgrades
   within-time-set derivative views to ordinary-at-time views at
   neighborhood-times, and
   packages the corresponding chosen-DeTurck-solution family interface and a
   reusable gauge-flow family bundle with anchored-gauge projections and direct
   gauge-reducible/intrinsic/ordinary theorem-family projections from
    pulled-back metric time-derivative data, plus a fixed-initial-value-problem
    bundle with matching local theorem-package projections. Both bundle levels
    now also build the gauge-pulled metric time-derivative proof from scalar
    inner-product derivative data and extract the same scalar data back from
    that proof. The
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
     bundles, with reverse adapters from existing geometric gauge-flow bundles
     back to raw existence witnesses. The primitive derivative-view packages now
     also round-trip with the geometric `SatisfiesGaugeFlowOn` equation for both
     fixed-IVP and theorem-family data, promote model-vector-field derivative
     data to the intrinsic DeTurck derivative views once the model RHS is
     identified along the flow, mirror that bridge at the fixed-IVP and
     theorem-family chosen-solution package layers, and anchored primitive
     derivative data now constructs the corresponding geometric `C³` gauge-flow
     bundles directly.
    It also now has fixed-IVP and theorem-family
    constructors from pointwise `HasMFDerivAt[s]` or unrestricted `HasMFDerivAt`
    integral-curve data, named-derivative-family adapters, plus raw-flow time-set
     restriction with readout simp lemmas and direct derivative/local-at-time
     extractors, matching the
     shape of Mathlib ODE output, and geometric endpoint data can now replace its
     bundled
     gauge-flow component by such a raw existence witness at fixed-IVP, global,
     and interval scope. The theorem-family zero-gauge-field identity constructor
     now also produces the pulled-back metric time-derivative proof needed by the
     gauge-reduction API directly from pointwise gauge-field vanishing, provides
     the matching named scalar derivative data, plus direct fixed-IVP and
     theorem-family zero-field projections to the gauge-reduced, intrinsic, and
     ordinary APIs. A new
     `GaugeReduction.ModelGaugeFlowODE` module packages
     mathlib's time-dependent Picard-Lindelöf theorem as Banach-model local flows
      with closed-interval ODE derivative data, initialization on a closed ball of
       initial data, ordinary interior derivative extractors, named
       Picard-interval continuity, Lipschitz dependence on that initial data, and the continuous
       space-time partial-flow form needed for chart gluing, plus the
       time-slice continuity bridges for continuous/variational local-flow
        packages, including direct within-interval and interior pointwise
        continuity readouts and open-interior `ContinuousOn` readouts,
         autonomous `C¹` local-integral-curve specialization with
        open-interval continuity and packaged `LocalFlowSolution`,
        `LipschitzLocalFlowSolution`, and `ContinuousLocalFlowSolution`
        extraction,
       restriction constructors and direct localized Picard-Lindelöf
       constructors for local/Lipschitz/continuous model-flow packages with
       matching proof-level `Nonempty` wrappers,
       vector-slot variational uniqueness, center-trajectory scalar chain-rule
      wrappers with eventual-equality transfer forms, center-trajectory
       uniqueness wrappers, direct within-set `B(t)(A(t)u)(A(t)v)` chain-rule
       primitives, including a moving-base full-field companion for
       `Bfield(τ, y(τ))(A(τ)u)(A(τ)v)` under `A' = D ∘ A` with
       within-filter/ordinary eventual-equality transfer forms, closed-interval
        field-level coordinate derivative packages and variational local-flow
          constructors for full metric-coordinate Fréchet data, raw gauge-flow
          endpoint wrappers from that data to interior tensor time-regularity,
          concrete/readout wrappers where variational local-flow identifications
          are only closed-interval within-filter equal, including pushed-forward
          geometric-slot forms,
          same-set raw gauge-flow moving-base field constructors plus readout-field
         and pushed-forward geometric-slot tensor projections,
          fixed-IVP/theorem-family within-field data packages and projections,
          matching raw intrinsic gauge-flow existence wrappers,
          generic within-filter transfer for arbitrary `A'`,
      raw-gauge-flow time-set/open-interior continuity helpers plus
      fixed-IVP/theorem-family raw-existence derivative, continuity,
      chart-coordinate continuity, preferred-chart range eventuality, and
      tangent-trivialization readouts in both within-time-set and
      ordinary-neighborhood forms, and
      Gronwall uniqueness
      bridges for packaged and continuous space-time model flows needed as chart-level
      raw-flow building block. It also packages the tangent-map variational
       equation `A'(t) = Df(t, flow(t)) ∘ A(t)` as
       `VariationalLocalFlowSolution`, matching the coordinate-model
       `A`-derivative hypothesis, including vector-slot derivatives for
       `t ↦ A(t)v`, with interior and closed-interval uniqueness bridges for
       tangent maps once base local flows agree. It also defines the
      product variational vector field `(y, A)' = (f(t, y), Df(t, y) ∘ A)` and
      projection lemmas from product local-flow solutions to the base and tangent
       equations, including ordinary interior and vector-slot tangent derivative
       forms plus named component continuity, and extracts
        `VariationalLocalFlowSolution` from continuous
        product local flows or product Picard-Lindelöf hypotheses initialized on
        `(x, 1)`, with a radius-specialized Picard constructor and
        closed-interval localized variants and proof-level `Nonempty` wrappers
        for continuous-product/product-Picard inputs and localized variants for
        the one-step closed-ball estimate constructors, with matching
        proof-level `Nonempty` wrappers. It also proves
       the left-composition operator-space Lipschitz estimate, a product-state
       Lipschitz estimate for the full variational vector field, and
       interior/closed-interval uniqueness for the full `(flow, tangent)` pair
       from base-flow uniqueness plus a uniform `‖Df‖` bound. An endpoint readout
       bridge now transfers the closed-interval geometric-slot variational theorem
       from any locally equal finite-cover metric-coordinate bilinear-form readout,
       matching the Banach readout output shape before interior tensor
       time-regularity is derived; direct and readout-field model-coordinate
       endpoint companions compare the variational ODE velocity with the raw
       gauge velocity using within-time-set agreement, and the time-difference
       formulation now has within-set chain-rule primitives for closed-interval
       endpoints, including a readout-field version for finite-cover metric
       coordinate data. Its closed-ball
       specialization now assembles product `IsPicardLindelof` witnesses and a
       one-step variational local-flow constructor from base/linearized
       closed-ball estimates plus the standard Picard continuity, norm, and
       time-radius assumptions, with a stronger component-estimate constructor
       that derives the product norm bound automatically and a continuity
       variant that derives product-field time-continuity from separate
       time-continuity of `f` and `Df`; its operator-ball variant derives the
       tangent-operator norm bound from closed-ball membership, with an explicit
       `1 + a` identity-ball specialization. The dynamic pullback bridge now turns such a variational local
       flow into the interior coordinate-field derivative data and proves the
       exact scalar chain rule along the flow, leaving only the metric-component
       derivative and concrete chart identification as local inputs. A parallel
       time-only model route now combines a variational local flow with a direct
       `HasDerivAt B B' t` proof for the already-composed moving bilinear-form
       readout, avoiding a full space-time `Bfield` derivative hypothesis when
       the chart calculation has already reduced to `B(t)(A(t)u)(A(t)v)`. The
       analytic finite-cover layer now differentiates the whole coordinate
       bilinear-form readout as an `F →L[ℝ] F →L[ℝ] ℝ` value for Banach local
       solutions, reified continuous metric curves, and smooth realizations, so
       the Banach Picard metric curve feeds that weaker time-only interface
       before choosing tangent-vector slots; matching one-sided `Ici t`
       endpoint variants feed the boundary-reduced theorem routes.
       Closed-Picard
        raw gauge flows also feed the coordinate-model/field time-derivative
        bridges directly on the open interior interval, with a one-step theorem
        from raw gauge flow plus variational model-flow chart data to interior
       gauge-pulled time-regularity; the moving-base field bridge also has an
       arbitrary-time-set form at neighborhood-times, so endpoint/restricted
       chart arguments can reuse the same raw-flow coordinate derivative. The
       concrete moving `B(τ)` and `A(τ)` coordinate components are now identified
       respectively with the metric at `Φ_τ(x)` in the target tangent
       trivialization and with the gauge pushforward tangent map in source/target
       coordinates, and the named `metricBilinearCoordinateField` identifies
       concrete `B(τ)` with a two-variable metric-coordinate field along the raw
       coordinate curve; the raw-flow bridge now builds the field-level
       coordinate derivative package from the derivative of that field, the
       concrete tangent-coordinate derivative, and the scalar velocity identity,
       with base-time simplification lemmas reducing those components to the
       ordinary metric and pushforward tangent vector in centered coordinates
       and slot-specialized forms for actual tangent vectors, plus a named
       `tangentVectorOfCoordinate` inverse for switching back to geometric tangent
       vectors; a geometric-slot raw-flow bridge now states the remaining scalar
       velocity identity in actual pushed-forward tangent-vector terms and routes
       that data directly to tensor time-regularity, with a closed-Picard `Ioo`
       specialization for interior regularity and a variational-flow version
       that discharges the raw coordinate-curve and tangent-map ODE parts once
       the named metric-coordinate field derivative is supplied,
       with the centered time-direction part of that derivative now supplied by
       `HasTimeDerivativeAt` / `HasTimeDerivativeOn`, including coordinate
       curves that are eventually stationary at the chart center,
       and fixed-time spatial slices of the field now proved `C²` in the
       preferred extended chart and extracted as canonical within-chart
        `fderivWithin` data with a raw-gauge-flow coordinate-curve chain rule,
        plus an additive decomposition that isolates the only remaining
        time-difference derivative for the full moving field and feeds the
        concrete component-derivative package through tensor time-regularity
        endpoints, with the variational-flow route now discharging the
        tangent-coordinate-map derivative for that formulation via a reusable
        concrete `pullbackMetricTangentCoordinateMap` derivative lemma, and a
        converse bridge deriving the time-difference derivative from the full
        `metricBilinearCoordinateField` Fréchet derivative after subtracting the
        frozen spatial `fderivWithin` contribution, with raw-flow endpoints that
        package that subtraction automatically, including both the direct
        closed-Picard `Ioo` wrapper for interval flows and a closed-Picard
        variational-tangent endpoint that accepts the full field derivative,
        tangent-map identification, and scalar velocity identity directly, plus a
        geometric-slot companion phrasing that identity in actual pushed-forward
        tangent vectors, and variational-local-flow variants that identify the
        model base velocity with the raw gauge vector field by derivative
        uniqueness when the base coordinate curves agree, both in direct
        model-coordinate slots and in pushed-forward geometric slots, with the
        base-velocity readouts themselves now exposing ordinary-neighborhood and
        closed-interval within-filter direct forms that avoid the centered
        `tangentCoordChange`, and with within-domain Fréchet chain-rule and
        time-difference primitives that let chart-local product-domain
        derivatives feed the same endpoint calculus, now including a raw
        gauge-flow metric-coordinate time-difference bridge that subtracts the
        frozen spatial term from such domain-restricted data before the
        closed-Picard tensor time-regularity route consumes it directly and
        variational tangent-map variants derive the tangent-coordinate
         derivative from the model variational ODE, with finite-cover/readout
         variants supplying the product-domain metric derivative by local
         equality and a fully localized geometric-slot form in actual
         pushed-forward tangent vectors, plus a variational-local-flow form that
         transports product-domain convergence from the model Picard graph to the
         raw coordinate graph using closed-interval base-flow equality, with an
          open-domain variant deriving model graph convergence from variational
          local-flow continuity and a raw-coordinate open-domain bridge deriving
          raw graph convergence from preferred-chart gauge-flow continuity, plus
          lower time-difference component-data constructors with the same
          open-domain reduction for direct and readout fields and public
          closed-Picard tensor wrappers exposing that open-domain shape, with
          variational tangent-map direct/readout tensor routes mirroring the same
          interface, and now with generic open-domain moving-base bilinear-field
           chain rules and full-field time-difference lemmas that derive product
           graph convergence from base-curve within-derivative continuity before
           the raw gauge-flow scalar endpoint theorem consumes them, the
            variational local-flow full-field route now also accepting
            `HasFDerivWithinAt` on an open chart product domain at the model-flow
            endpoint directly through named metric-coordinate, readout-field, and
            geometric-slot tensor wrappers, with the same open-domain input now
            feeding the ordinary open-interior `Ioo` tensor route and its readout
           and pushed-forward geometric-slot wrappers, with the lower scalar
           calculus now also exposing a four-variable open-domain chain rule for
           readouts on `(t, y, u, v)` and variational local-flow specializations
           for `(t, flow(t), A(t)u, A(t)v)`, including ordinary open-interior
           `Ioo` variants and matching eventual-equality transfer forms, plus
           non-open-domain graph-convergence variants, matching eventual-equality
           transfer forms, and raw tensor wrappers
           that consume both open and closed-domain scalar readouts directly, and the
            model-coordinate time-difference route also accepting any locally equal
         two-variable bilinear-form readout for the full field derivative in both
        model-coordinate and pushed-forward geometric scalar forms, and the
        closed-Picard model-velocity time-difference route now deriving the
        remaining endpoint `Btime` term directly from full/readout
        metric-coordinate Fréchet data before rewriting the model velocity to
        the raw gauge velocity, with matching pushed-forward geometric-slot
        variants and ordinary-neighborhood tangent-map variants, and the same
        geometric-slot phrasing available
        for the direct variational chain-rule route, plus a readout-field
        companion that transfers the
         required Fréchet derivative from any locally equal two-variable
          bilinear-form readout through the named
          `metricBilinearCoordinateField_hasFDerivAt_of_eventuallyEq` bridge,
          exposing the chart algebra needed for Banach finite-cover metric
          readouts, and the primitive time-difference decomposition now has its
          own readout-field theorem before subtracting the frozen spatial
           derivative, lifted through component data to a raw
            `HasTimeDerivativeOn` endpoint for `C³` gauge flows and its
            open-interior specialization, with a matching readout-field endpoint
            at the variational tangent-map layer plus a geometric-slot companion
            that keeps the readout-field derivative input while phrasing the
            scalar identity in actual pushed-forward tangent vectors, with
            further variants keeping both the base-flow and tangent-map
            identifications in the closed-interval within filter, and now
            with a within-set time-difference component package that routes
            closed-interval endpoint derivative data through
            `CoordinatePullbackMetricComponentDerivativeWithinOn` to interior
            tensor time-regularity, including direct and readout-field wrappers
            from full metric-coordinate Fréchet data plus closed-interval
            tangent-map derivatives, and
            `SmoothRealizationGaugeRoutes` now exposes the Banach chart right-hand
            side as centered derivatives of the named
            `metricBilinearCoordinateField`, including the tangent-vector-slot
           scalar form used by geometric gauge-pullback calculations, and now
           packages the same chart RHS as raw identity-gauge scalar derivative
           data plus the corresponding identity-pullback tensor derivative on the
           open Banach interval, with closed-left endpoint/right-derivative
           forms for the centered metric-coordinate field; the geometric
           corrected-velocity layer also now turns
         vanishing pulled-back background Ricci curvature directly into vanishing
         concrete `C³` gauge-corrected pullback velocity through a named theorem,
         including an initial-time specialization,
          and the Ricci-flat initial transport API has matching `C³`
          anchored-gauge wrappers for the general Levi-Civita-background and
          chosen-background cases, together with source-level aliases from
          `IntrinsicDeTurckLocalSolution` that take the anchored `C³` gauge as an
          argument. The
          raw-flow API also extracts continuity of
      `τ ↦ Φ_τ(x)` and eventual tangent-trivialization membership from a
     neighborhood-time flow equation, preparing the chart-local pullback formulas.
     A thin `AnalyticPDE.SmoothRealization` module names the
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
   common-interval uniqueness follows from Banach uniqueness. The smooth-density
   side also now specializes the preferred finite-cover closure theorem directly
   to bundled continuous Riemannian metrics, placing each such metric in the
   closure of smooth symmetric positive-definite sections and exposing a
   quantitative smooth-SPD approximant inside any prescribed positive
   preferred-cover radius; the underlying generic theorem gives the same
   quantitative readout for arbitrary continuous SPD bilinear-form sections,
   and the metric-level readout reifies the approximant as a bundled `C²`
   Riemannian metric, with a closure theorem for the image of bundled smooth
   metrics. For autonomous
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
    `identityOfSubsingletonModel`, and `identityOfIsEmpty`; a zero-gauge-field
    adapter now turns any proof of vanishing `intrinsicDeTurckGaugeField` on
    solution time sets into identity raw `C^3` gauge-flow existence, and the
    identity cases include matching `_hpullDerivative` time-derivative lemmas,
    named scalar derivative data, and direct fixed-IVP/theorem-family
    projections. The underlying
   `Diffeomorph3GaugeFlowOn` raw-flow API also has arbitrary-vector-field
     identity constructors for subsingleton tangent, subsingleton model, and empty
    manifolds plus pointwise `HasMFDerivAt[s]`, ordinary-on-time-set
      `HasMFDerivAt`, unrestricted `HasMFDerivAt`, and preferred-chart
      ODE adapters from continuity plus centered chart derivatives, including
      source-neighborhood variants that derive manifold-curve continuity from
      eventual membership in the centered chart source and now include raw,
      fixed-IVP, and theorem-family source-membership readouts for both
      closed-interval within filters and ordinary neighborhood filters, plus
      unrestricted ordinary `HasDerivAt` forms, named
       fixed-IVP and theorem-family preferred-chart ODE constructors from the
       same chart-ODE data,
       derivative-family adapters, including an ordinary-on-time-set
         `ofDerivativeAtFamily` bridge and named source-neighborhood chart-ODE
         `ofChartDerivative` / `ofChartDerivativeAt` bridges with
         direct primitive derivative-data readouts, within-filter/ordinary
         eventual-equality transfers from local model-coordinate curves, and
         direct lower-level chart-to-manifold derivative bridges,
         neighborhood-time upgrades from within-time-set to ordinary-at-time
         primitive derivative and chart-ODE data, monotone restriction of
         within-time-set and ordinary-at-time derivative views including
         chart-ODE views, direct closed-Picard `Icc` to open-interior `Ioo`
         upgrades for primitive derivative and chart-ODE data, closed-Picard
         `Ioo` local-congruence readouts for ordinary manifold and
         preferred-chart derivatives after locally replacing the vector field
         along the raw flow, a raw
         open-interior existence constructor from closed-interval centered chart
        ODE data, including a named intrinsic DeTurck chart-package version, the
        parallel open-interior constructors from closed-interval manifold
        derivative data and named intrinsic primitive derivative data, fixed-IVP
        and theorem-family `ofPicardIccDerivative` /
        `ofPicardIccChartDerivative` wrappers for solution time sets explicitly
        identified with the open Picard interior, matching derivative-view
        handoffs to ordinary-at-time derivative and chart-ODE packages on the
        same explicit open solution time sets, and time-derivative wrappers that
        discharge the neighborhood-of-each-time hypothesis from those `Ioo`
        identifications for coordinate-model, component, field-level, and
        within-set endpoint data, and matching fixed-IVP `ofDerivative` /
        `ofDerivativeAt` bridges,
        centered preferred-chart derivative simplifications that expose the
        actual gauge velocity directly, vector-field agreement transport for
        raw flows and local-at-time derivative readouts when vector fields agree
        along the flow near the time, including centered preferred-chart
        derivative readouts, geometric-to-raw adapters, and direct
        proof-level `Nonempty` wrappers for the raw geometric/derivative,
       restriction, and identity-flow constructors, plus matching fixed-IVP
       and theorem-family intrinsic proof-level wrappers and derivative/local-at-time
      extractors; raw intrinsic gauge-flow existence witnesses now project
     directly to gauge-reduced, intrinsic, and ordinary theorem packages from
    either pulled-back metric time-derivative or scalar inner-product derivative
    data. The new `GaugeReduction.ModelGaugeFlowODE` module now isolates the
    Banach-model Picard-Lindelöf local-flow theorem needed before the remaining
     positive-dimensional manifold ODE lift: it packages time-dependent local
     flows, their closed-interval ODE derivative, initial-data Lipschitz
     dependence, continuous space-time partial flows, restriction maps to smaller
     Picard intervals and initial balls with matching `Nonempty` wrappers,
     readout simp lemmas for localized flow/tangent maps and forgetful projections,
      overlap uniqueness for local and
      continuous base-flow packages plus variational tangent maps and full
       `(flow, tangent)` pairs with different centers/radii, including direct
        pointwise equality readouts on both `Ioo` and `Icc`, and autonomous
         `C¹` integral curves with packaged and directly localized
         `LocalFlowSolution`, `LipschitzLocalFlowSolution`, and
         `ContinuousLocalFlowSolution` extraction, closed-interval within-filter and
        open-interior open-set eventual-membership readouts for
        local/continuous/variational model-flow curves and for variational
        tangent maps and fixed vector slots, plus `(flow, tangent)` product-graph
        readouts, `(t, flow, tangent)` time-graph readouts, and fixed two-vector-slot
        `(t, flow, A(t)u, A(t)v)` readouts,
        plus Gronwall uniqueness bridges for packaged and continuous
      space-time model flows; the
      raw-flow API also extracts continuity of `τ ↦ Φ_τ(x)` and eventual
      tangent-trivialization membership from neighborhood-time flow data, with
       matching within-time-set versions for restricted ODE intervals. The
       fixed-IVP/theorem-family wrappers mirror the neighborhood-time and
       within-time-set chart-coordinate continuity, derivative, continuity, and
       trivialization readouts directly. It also
      converts the raw manifold derivative into the preferred local-coordinate
      derivative of the base flow curve at interior closed-interval times via
      `Diffeomorph3GaugeFlowOn.hasDerivAt_extChartAt_eval_of_mem_Ioo`, with
      within-time-set and neighborhood-time variants for restricted and endpoint
      routes.
     A new
    `GaugeReduction.Diffeomorph3FlowSubsingleton` module closes the
   non-identity gauge-pulled metric time-derivative obligation for arbitrary
   geometric `C³` DeTurck gauge-flow families on subsingleton tangent fibers by
   proving the corrected velocity and pulled metric components vanish, and
    exposes direct gauge-reduced projections plus matching model-space,
    empty-manifold, and raw-existence theorem-package routes that need no extra
    derivative input; it also exposes ordinary point-4 theorem-family endpoints
    routed through the full raw `C³` gauge-flow chain in the subsingleton-tangent,
    subsingleton-model, and empty-manifold cases, with matching fixed-IVP
    model-space and empty-manifold aliases for the geometric and raw gauge-flow
    routes. The rank-one compact special case also has gauge-reduced projections
    to intrinsic and ordinary theorem packages, including model-space
    theorem-family aliases. A thin `AnalyticPDE.SmoothRealizationGaugeRoutes`
     companion now also routes global and interval smooth Ricci-DeTurck
     chart-closure data to intrinsic and ordinary compact point-4 theorem packages
     through the raw identity `C³` gauge-flow witness plus named scalar derivative
     data, and exposes the smooth Banach realization's open-interval identity
     raw-gauge scalar/tensor derivative data directly; the global and interval
     chart-closure records also now expose named `nonempty_realization`,
     `realizationCandidateEncoding`, and `nonempty_candidateEncoding` readouts
     for their stored realization and reverse-encoding fields. The thin
     raw-gauge route module mirrors its global and interval projections to
     intrinsic and ordinary compact point-4 theorem packages as proof-level
     `Nonempty` witnesses, and does the same for the genuine symmetric-carrier
     interval closure data across the chosen-background, intrinsic, and ordinary
     theorem packages, including intrinsic and ordinary theorem-family witnesses
     from a family of symmetric-carrier interval closure data. Families of global
     and closed-interval `RicciDeTurckChartClosureData` now have the same
     proof-level intrinsic and ordinary theorem-family wrappers. Ambient interval
     closure data also now has proof-level constructors for genuine
     symmetric-carrier closure, including the metric-cone shrink route. The
     density-based interval restricted symmetric carrier is now proved equal to
     the chart's built-in restricted carrier on the Picard interval and the
     Riemannian metric locus, with both subtype and ambient-coordinate coe
      readouts. The preferred-cover local-bounds smooth-approximation route now
      also extracts a state-preserving Banach solution and common-interval
      uniqueness witness for the density-based interval carrier, including a
      proof-level `Nonempty` readout, and the
      chart-derived symmetric carrier now has the matching extraction after the
       standard metric-cone shrink, including a proof-level `Nonempty` readout,
       plus a no-shrink extraction when the current
      Picard ball is already contained in the Riemannian metric cone, including
      a proof-level `Nonempty` readout. Genuine symmetric-carrier interval closure data
      now exposes the same Banach solution/uniqueness witness directly, including
      proof-level `Nonempty` readouts for existence, smooth realization,
      reverse candidate encoding, and a paired Banach solution plus smooth
      intrinsic DeTurck realization witness, now with a stronger paired witness
      that also includes the reverse symmetric-carrier encoding of the
      represented chosen-background candidate, and a single-choice strengthening
      that carries terminal-time control and common-interval uniqueness with the
      same realization/encoding data, plus an existential readout of the Banach
      solution with terminal/uniqueness proofs and a nonempty
      realization/encoding fiber. Density-based interval-carrier
      solutions now also transport back to the chart's built-in restricted carrier
      under the terminal-time bound, and the preferred-cover local-bounds route
      now returns that chart-carrier `BanachEvolutionLocalSolutionIn` witness
      directly from the smooth-density Picard shrink, with a proof-level
      `Nonempty` readout for callers that only need existence. The vector-bundle
      smooth-approximation layer now also discharges the local coordinate-map
      boundedness hypothesis for continuous Riemannian vector bundles, deriving
      preferred-bilinear smooth approximants and the finite-cover Banach-norm
      approximation theorem from mathlib's
      `eventually_norm_trivializationAt_lt`, and it now upgrades symmetric
      continuous bilinear sections to symmetric smooth finite-cover approximants
      by fiberwise symmetrization. The Ricci-DeTurck preferred-cover
      local-bounds closure theorem now uses this symmetric approximation seam
      before applying positive-definite openness. The same generic layer now
      packages continuous SPD bilinear-form sections as limits of smooth SPD
      sections in the preferred finite-cover norm. It also derives the
      finite-cover inverse bound from compactness of the cover pieces inside
      their fixed trivialization domains by factoring fixed-center inverses
      through centered inverse trivializations and continuous coordinate changes,
      leaving the heavy PDE realization module unchanged. The
   `GaugeReduction.Diffeomorph3FlowTimeDerivative` module exposes the fixed
   non-identity gauge scalar derivative form of the static pullback calculation
   plus its scalar-to-tensor repackaging lemma, and names the remaining dynamic
   scalar chain-rule target as `PullbackMetricInnerDerivativeOn`, equivalent to
   tensor `HasTimeDerivativeOn` for the pulled-back metric, with fixed-IVP and
   theorem-family bundle adapters, raw-existence adapters, and direct
   gauge-reduced, intrinsic, and ordinary theorem-package projections, plus
    time-set restriction / identity-gauge structural lemmas and fixed-IVP/family
    equivalences with tensor time-derivative data for both geometric and raw
    gauge-flow bundles; chosen-background, subsingleton-tangent/model, and
    empty-manifold identity raw gauge-flow fixed-IVP and theorem-family witnesses
     now provide the named scalar data directly. Its first model-space
      chain-rule component is also proved: differentiating `B(t)(u(t), v(t))` and
      the gauge-coordinate specialization `B(t)(A(t)u, A(t)v)`, including the
      `D ∘ A(t)` tangent-map derivative contribution, plus a moving-base
      direct-vector-slot version now used by the variational scalar theorem via
      applied tangent-map ODE data and closed-interval/right-derivative
       counterparts for endpoint work, with eventual-equality transfer lemmas for
       chart-local coordinate identifications and an endpoint derivative bridge
       for the concrete tangent-coordinate component, packaged at the component
       derivative-data layer, plus monotone restriction for ordinary component-level
       derivative data and for component-level and full-field within-set derivative
       data, with a raw within-set component route to scalar and tensor
       time-regularity on the same time set and fixed-IVP/theorem-family/raw-existence
       component-data package lifts, a generic within-set scalar transfer and raw
       endpoint scalar derivative package that upgrades directly to tensor
       time-regularity on the open interval and restricts to smaller time sets
       through a raw gauge-flow endpoint
       wrapper, including variational tangent-map endpoint data with
       geometric-slot scalar identities, variants where the tangent-map
       identification is only known in the closed-interval within filter, and an
       analogous direct `hasFDerivAtWithin` wrapper family that fills in the
       `HasDerivWithinAt` tangent-coordinate derivative from the variational ODE,
       plus direct-velocity `_self` raw-flow endpoint lemmas for the
       frozen-spatial, total-derivative, and time-difference metric-coordinate
       calculations, including locally equal readout-field variants and
       ordinary-neighborhood and within-set component-data constructors that
       accept direct gauge-velocity hypotheses, plus public tensor
       time-regularity wrappers for full metric-coordinate Fréchet data in that
       same form, including variational local-flow wrappers that supply the
       tangent-coordinate derivative from the model tangent ODE and
       open-interior `Ioo` specializations, plus ordinary-neighborhood
       and within-set geometric-slot wrappers whose scalar identities stay in
       actual pushed-forward tangent vectors, including the closed-Picard
       `Ioo` specializations, and field-level base-coordinate wrappers that
       store the actual coordinate-curve derivative as `X t (G.maps3 t x)`,
       plus full-field variational tangent-map coordinate/readout and
       geometric/readout direct-velocity endpoint wrappers, closed-Picard
       variational tangent-map Fréchet geometric/readout `_self` wrappers
       including within-filter tangent-map agreement, and same-set
       within-field direct-velocity base-coordinate, metric-coordinate,
       readout-field, and tensor wrappers, with matching lower
       bilinear-coordinate derivative and ordinary metric-coordinate field
       package `_self` companions, and direct-velocity ordinary/within-set
       abstract time-difference component data packages with projections to
       component derivatives and tensor time-regularity, plus direct-velocity
       ordinary and closed-interval variational tangent-map wrappers for that
       time-difference formulation, including pushed-forward geometric-slot
       variants,
       direct variational endpoint wrappers for `HasDerivWithinAt`
       time-difference data with geometric-slot scalar identities and
       model-velocity rewrites from within-set base-flow agreement, and an
      endpoint bridge from full metric-coordinate Fréchet data to the concrete
      `B(τ)` derivative and then to tensor time-regularity. The
      coordinate-level `CoordinatePullbackMetricInnerDerivativeOn` package now
      promotes chartwise `B/A/D` derivative hypotheses to the actual geometric
      scalar target and directly to tensor `HasTimeDerivativeOn`; the preferred
      coordinate scalar expression is now named as
      `pullbackMetricInnerCoordinateModel`, with proof-bearing eventual equality
      to the geometric pullback scalar from target-trivialization membership and
      a raw-flow corollary supplying that equality near neighborhood-times.
      `CoordinatePullbackMetricModelDerivativeOn` isolates derivative data for
      that named coordinate model and promotes it directly to scalar and tensor
      time-regularity, including raw-gauge-flow wrappers. Its concrete
       moving-coordinate components are now named as
       `pullbackMetricBilinearCoordinateMap` and
       `pullbackMetricTangentCoordinateMap`, with a component-derivative theorem
       reducing the model obligation to derivatives of those `B(τ)` and `A(τ)`
       maps plus the scalar velocity identity. That primitive is now packaged as
       `CoordinatePullbackMetricComponentDerivativeOn`, with direct scalar,
       tensor, and raw-gauge-flow promotion routes, including the closed-Picard
       open-interior wrapper. A variational-flow component bridge now derives
       this package from local identifications of the named `B(τ)` and `A(τ)`
       maps with a variational model flow, plus the bilinear-form field
       derivative and scalar velocity identity, and exposes a matching raw
       closed-Picard route to interior tensor time-regularity. A narrower
       time-only variant accepts a direct derivative of the concrete `B(τ)`
       component, matching the Banach finite-cover readout layer, and uses the
       variational flow only for the `A(τ)` tangent map. The module also proves
       the moving metric-component chain rule for `Bfield(τ, y(τ))` and the
       combined `Bfield(τ, y(τ))(A(τ)u)(A(τ)v)` form with the variational tangent
       equation, bundled as `CoordinatePullbackMetricFieldDerivativeOn` with
         scalar, tensor, raw-gauge-flow, and bundle-level promotion routes. A companion
       raw-flow bridge now uses the actual gauge-flow coordinate curve as the
       moving base point and discharges its `y'(t)` clause from the raw manifold
       flow derivative before promoting the field-level data to tensor
        time-regularity. A companion
        variational route discharges the tangent-map derivative in applied
        vector slots while accepting a
        direct `HasDerivAt B B' t` proof for the already-composed coordinate
       readout, and raw closed-Picard gauge flows expose that route directly on
       the open interior interval. The
       coordinate, coordinate-model, and field-level data now restrict to smaller
       time sets or lift through fixed-IVP, theorem-family, and raw-existence
       gauge-flow APIs, with explicit neighborhood-time hypotheses on the
       model/field bundle routes. This leaves one primitive
    positive-dimensional time-regularity input. Two thin extension
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
