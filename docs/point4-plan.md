# Systematic plan to close roadmap point 4

This file is the working plan for closing point 4 ("Ricci-flow local existence
and uniqueness"). It complements `docs/roadmap.md`, which describes the
overall program; this file documents the precise sequence of remaining
mathematical steps and how each maps to the existing Lean scaffolding.

This is a **research-program plan**, not a checklist that one agent run can
finish. The infrastructure already in `curvature/PoincareCurvature/` is
fully proof-bearing (no `sorry`, `axiom`, `opaque`, `admit`,
`native_decide`, or `decide!`), and the boundary between proved and unproved
geometric content is precisely captured by a small number of named
structures. The remaining work is to construct inhabitants of those
structures for arbitrary compact Riemannian manifolds.

## Already proved (in this repository)

`IntrinsicLocalExistenceUniquenessFamily` is currently constructible
unconditionally in three families of compact manifolds:

* **Empty** manifolds (`[IsEmpty M]`):
  `intrinsicLocalExistenceUniquenessFamily_of_isEmpty`
* **Subsingleton tangent fibers** (`[∀ x, Subsingleton (TM x)]`) and
  the model-space synonym (`[Subsingleton E]`):
  `intrinsicLocalExistenceUniquenessFamily_of_subsingleton_tangent` /
  `_of_subsingleton_model`
* **Rank-one tangent fibers**
  (`hfin : ∀ x, Module.finrank ℝ (TM x) ≤ 1`)
  and the model-space synonym (`[Fact (Module.finrank ℝ E ≤ 1)]`):
  `intrinsicLocalExistenceUniquenessFamily_of_finrank_le_one` /
  `_of_finrank_model_le_one`

All three are real Lean theorems with stationary local solutions and
metric uniqueness, not interface placeholders.

## Conditional bridge already proved

The chain

```
TimeDependentGeometricRicciDeTurckBanachChart ivp
   + RicciDeTurckChartClosureData ivp
        (bundling realization + reverse encoding for all candidates)
⟹ IntrinsicLocalExistenceUniqueness ivp
```

is a real Lean theorem (the family form is
`intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData[OnIcc]`
in `AnalyticPDE/SmoothRealization.lean`). So the gap between the current
state and a fully unconditional point-4 closure is exactly the
construction of `chart` and `D` for every initial-value problem.

## Three remaining items

### Item 1 — time-regularity of the non-identity `C³` gauge-pulled metric

**Mathematical content.** Given a `C³` time-dependent diffeomorphism
family `Φ` and a `C^2` time-dependent Riemannian metric `g`, prove

```
HasTimeDerivativeOn (Φ.pullbackMetricFamily g)
                    (gaugeCorrectedPullbackVelocity)  s
```

where `gaugeCorrectedPullbackVelocity` is the explicit Lie-derivative
formula already named in
`IntrinsicDeTurckLocalSolution.gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge`.

The classical formula being formalized is

```
d/dt [(Φ_t^* g_t)(u, v)]
  = (Φ_t^* (∂_t g_t))(u, v) + (Φ_t^* L_{X_t} g_t)(u, v)
```

where `X_t` generates `Φ_t`. The right-hand side is the
already-defined `gaugeCorrectedPullbackVelocity`.

**Reduction to scalars.** Already proved in `GaugeTransport.lean`:
`pullbackMetricFamily_hasTimeDerivativeOn_of_inner_hasDerivAt` reduces
this to the scalar derivative

```
HasDerivAt
  (fun τ ↦ (g τ).inner (Φ τ x)
      ((Φ τ).pushforwardTangent x u)
      ((Φ τ).pushforwardTangent x v))
  [predicted velocity]
  t
```

**What still has to be done.** This scalar derivative is a chain-rule
calculation that splits into three pieces (time derivative of `g`,
spatial derivative of `g.inner` along `X_t`, derivative of the
pushforward `Φ_t * u` and `Φ_t * v`). Each piece needs a carefully
named auxiliary lemma. The static (time-independent `Φ`) special case
is already proved as `const_pullbackMetricFamily_hasTimeDerivativeOn`, and the
thin `Diffeomorph3FlowTimeDerivative.lean` module now also exposes its scalar
inner-product form plus the scalar-to-tensor repackaging lemma for fixed
non-identity gauges. That module names the remaining dynamic scalar target as
`SmoothSelfDiffeomorph3Family.PullbackMetricInnerDerivativeOn` and proves it
equivalent to `HasTimeDerivativeOn` for the pulled-back metric. It also lifts
that named scalar target to fixed-IVP and theorem-family geometric `C³` DeTurck
gauge-flow bundles, lifts the same named target through raw `C³` gauge-flow
existence witnesses, and provides direct gauge-reduced, intrinsic, and ordinary
theorem-package projections from that named data. The named scalar target also
has time-set restriction, identity-gauge specialization, and fixed-IVP/family
equivalence lemmas that identify named scalar data with tensor time-derivative
data for both geometric and raw gauge-flow bundles. The bundled
chosen-background, subsingleton-tangent/model, and empty-manifold identity raw
gauge-flow fixed-IVP and theorem-family witnesses now also provide this named
scalar data directly, and a new zero-gauge-field adapter packages any proof that
`intrinsicDeTurckGaugeField` vanishes on each solution time set into the same
identity raw `C³` gauge-flow existence data, with direct fixed-IVP and
theorem-family projections to the gauge-reduced, intrinsic, and ordinary APIs;
the fixed-IVP and theorem-family zero-field identity raw-flow witnesses now also
provide the named scalar derivative data expected by those routes. The bundled
non-identity gauge-flow API now has proof-bearing scalar-to-tensor wrappers, so
solving this single dynamic scalar identity automatically supplies the
`HasTimeDerivativeOn` package required by the gauge-reduction theorem routes.
The first proof-bearing piece of the dynamic calculation is now in place:
`hasDerivAt_bilinearForm_apply_apply` differentiates
`B(t) (u(t)) (v(t))`, and
`hasDerivAt_bilinearForm_linear_apply_apply[_of_comp_deriv]` specializes this
to the local-coordinate form `B(t) (A(t) u) (A(t) v)` of a gauge-pulled metric
component, including the expected vector-slot/Lie-derivative contributions.
The moving-base version
`hasDerivAt_bilinearFormField_apply_apply_along_curve` now handles two
independently differentiated vector paths directly, and the variational-flow
scalar theorem uses the applied tangent-map ODE rather than only the
operator-valued derivative. Closed-interval/right-derivative versions of these
same bilinear-form and moving-base vector-slot chain rules are also available,
including `hasDerivWithinAt_bilinearFormField_tangent_apply_apply` for
variational model flows on `Icc tmin tmax`, with an eventual-equality transfer
form for chart-local endpoint scalar identities.
The concrete gauge tangent-coordinate component now also has a closed-interval
derivative theorem from eventual equality with a variational tangent map, giving
the endpoint analogue of the existing interior positive-dimensional component
bridge. This is packaged as
`CoordinatePullbackMetricComponentDerivativeWithinOn`, with a variational
tangent-map constructor over `Icc tmin tmax`.
There is also a generic within-set eventual-equality scalar chain rule for the
concrete component shape `B(τ)(A(τ)u)(A(τ)v)` with `A'(t) = D ∘ A(t)`, so these
endpoint component packages can be transferred to local scalar identities.
The raw geometric endpoint target is now named as
`PullbackMetricInnerDerivativeWithinOn`, and endpoint concrete component data
plus chart-local equality imply this raw scalar within-derivative package.
The basic moving-base within-set chain rule
`hasDerivWithinAt_bilinearFormField_linear_apply_apply_along_curve` now also
differentiates `Bfield(τ, y(τ))(A(τ)u)(A(τ)v)` directly under the variational
tangent-map equation `A' = D ∘ A`, so closed-Picard chart calculations can use a
full metric-coordinate Fréchet derivative without first freezing the base curve
or introducing an eventual-equality transfer. Its within-filter and ordinary
eventual-equality transfer forms are also named, matching the chart-local
geometric scalar identities used downstream.
Within-set field-level coordinate derivative data now also restricts
monotonically to smaller time sets, so the full-field endpoint route can be
localized after shrinking a Picard interval.
Closed-interval scalar derivative data now upgrades back to ordinary
`PullbackMetricInnerDerivativeOn` on the open interval, so endpoint component
work can feed the existing interior gauge-pulled metric time-regularity routes;
the endpoint scalar package now also restricts monotonically to smaller time
sets, matching localized Picard intervals.
Component-level within-set coordinate derivative data now also restricts
monotonically to smaller time sets, using explicit continuous-linear-map
instances to avoid expensive typeclass search in the bilinear codomain.
Ordinary component-level coordinate derivative data now has the same monotone
time-set restriction, so callers can localize either closed-interval or
open-interior component hypotheses after shrinking a Picard interval.
Raw gauge flows now also promote arbitrary within-time-set concrete component
data directly to within-set scalar derivative data and, when the time set is a
neighborhood at its points, to tensor time-regularity on that same set.
The fixed-IVP, theorem-family, and raw intrinsic gauge-flow existence packages
now also expose ordinary and within-set concrete component derivative data as
first-class inputs, with direct projections to coordinate-model, scalar, and
tensor time-regularity packages.
A direct theorem packages closed-interval concrete component derivatives as
`HasTimeDerivativeOn` for the gauge-pulled metric family over `Ioo tmin tmax`.
The raw `Diffeomorph3GaugeFlowOn` layer now exposes the same endpoint route
using within-time-set chart equality, so endpoints no longer need to be
neighborhood times just to supply the component data.
It also has a variational tangent-map endpoint theorem: closed-interval
time-only `B(τ)` derivatives plus local identification with a variational ODE
tangent map imply interior tensor time-regularity of the gauge-pulled metric.
The same theorem now has a geometric-slot wrapper, so scalar identities may be
stated using actual pushed-forward tangent vectors at the base time.
The concrete moving bilinear component `B(τ)` now has an endpoint derivative
bridge from a full metric-coordinate field Fréchet derivative plus the raw
gauge-flow within derivative.
Consequently, raw closed-interval gauge flows now have an endpoint theorem that
uses full metric-coordinate Fréchet data and variational tangent-map data to
prove interior tensor time-regularity with geometric-slot scalar identities.
That endpoint theorem now also has a finite-cover/readout-field companion:
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_hasFDerivAt_variationalTangentMapWithin_geometricValue`
transfers the required full Fréchet derivative from any locally equal
two-variable bilinear-form readout before invoking the geometric-slot
variational endpoint route. Direct and readout-field model-coordinate endpoint
companions,
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_metricCoordinateField_hasFDerivAt_variationalLocalFlowWithin_geometricValue`
and
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_hasFDerivAt_variationalLocalFlowWithin_geometricValue`,
add the closed-interval base-velocity comparison needed when the scalar
identity is stated with the variational ODE vector field `f(t, y(t))` rather
than the raw gauge vector field. The corresponding `..._tangentWithin...`
variants now keep both the base-flow and tangent-map identifications in the
closed-interval within filter, matching Picard endpoint output without first
upgrading the tangent equality to an ambient neighborhood equality. The direct
`hasFDerivAtWithin` endpoint wrappers now have the same variational tangent-map
and readout-field conveniences, so callers can supply only the
metric-coordinate Fréchet derivative plus tangent-map equality and let the API
fill in the `HasDerivWithinAt` tangent-coordinate derivative. The
time-difference formulation now also has direct variational endpoint wrappers
for `HasDerivWithinAt` time-difference data, including a variant where the
tangent-map equality is only assumed in the closed-interval within filter, plus
geometric-slot variants that state the scalar identity using actual
pushed-forward tangent vectors. The same endpoint time-difference route now also
has model-velocity wrappers that rewrite `f(t, y(t))` to the raw gauge velocity
from within-set base-flow agreement, and direct/readout-field companions that
derive the remaining `Btime` time-difference term from a full metric-coordinate
Fréchet derivative at the variational base point before performing that
velocity rewrite, with geometric-slot variants for pushed-forward tangent-vector
scalar identities and ordinary-neighborhood tangent-map variants for callers
with stronger local-flow output. The variational base-velocity comparison now
also has direct ordinary-neighborhood and closed-interval within-filter readouts,
identifying the model ODE velocity with `X t ((G.maps3 t) x)` without exposing
the centered `tangentCoordChange` term. The endpoint model calculus now also has
within-domain Fréchet chain rules for moving bilinear-form fields and their
time-difference subtraction, so local chart/Picard derivatives that are only
proved on a product domain can feed the gauge-pullback endpoint route directly.
The raw gauge-flow metric-coordinate time-difference bridge now consumes that
domain-restricted derivative shape while subtracting the canonical frozen
spatial contribution and exposing the raw gauge velocity. The same
domain-restricted shape now packages as
`MetricCoordinateFieldTimeDifferenceComponentDataWithinOnSelf` and feeds a
closed-Picard `Ioo` tensor time-regularity theorem directly, so chart-local
product-domain derivatives no longer need to be upgraded to global
`HasFDerivAt` before entering the non-identity gauge-pullback route. It now
also has variational tangent-map routes, including the closed-interval
within-filter equality form, that synthesize the tangent-coordinate derivative
from the model variational ODE. Finite-cover/readout fields now have the same
product-domain entry point: a locally equal two-variable bilinear readout can
supply the `HasFDerivWithinAt` metric derivative, including for the variational
ODE routes, and the fully localized route now has a geometric-slot form where
the scalar identity is stated in actual pushed-forward tangent vectors.
The fully localized product-domain route now also has a variational-local-flow
form that assumes product-domain convergence only for the model Picard graph;
closed-interval base-flow equality transports that convergence to the raw
coordinate graph and rewrites the model ODE velocity to the raw gauge vector
field before applying the domain-restricted gauge-pullback theorem. A further
open-product-domain form derives the model graph convergence from the
variational local-flow continuity package whenever the derivative domain is open
and contains the Picard graph endpoint.
The full-field coordinate derivative route now
also has a closed-interval package
`CoordinatePullbackMetricFieldDerivativeWithinOn`, a variational local-flow
constructor for it, and direct endpoint-to-interior scalar promotion theorems,
so Picard endpoint base-flow/tangent-map derivatives plus a full
metric-coordinate Fréchet derivative can feed the geometric scalar target
without repackaging through frozen-time component data. Raw
`Diffeomorph3GaugeFlowOn` witnesses now expose the same endpoint full-field
route directly, including a one-step variational local-flow wrapper to tensor
time-regularity on `Ioo tmin tmax`; the same route now also has concrete and
readout-field wrappers
`hasTimeDerivativeOn_Ioo_of_metricCoordinateField_variationalLocalFlowWithin`
and
`hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_variationalLocalFlowWithin`,
so closed-interval base-flow/tangent-map identifications can feed the named
metric-coordinate field or a locally equal Banach readout directly; matching
geometric-slot variants state the scalar identity in actual pushed-forward
tangent vectors. It now also has same-set
`hasTimeDerivativeOn_of_coordinateFieldWithin`,
`coordinatePullbackMetricFieldDerivativeWithinOn_of_baseCoordinate`,
`coordinatePullbackMetricFieldDerivativeWithinOn_of_metricCoordinateField`,
`hasTimeDerivativeOn_of_baseCoordinateFieldWithin`, and
`hasTimeDerivativeOn_of_metricCoordinateFieldWithin`, together with readout-field
companions
`coordinatePullbackMetricFieldDerivativeWithinOn_of_eventuallyEq_metricCoordinateField`
and `hasTimeDerivativeOn_of_eventuallyEq_metricCoordinateFieldWithin`, for time
sets that are already neighborhoods of their points. This same-set route now
also has geometric-slot wrappers
`coordinatePullbackMetricFieldDerivativeWithinOn_of_metricCoordinateField_geometricValue`,
`hasTimeDerivativeOn_of_metricCoordinateFieldWithin_geometricValue`, and
`hasTimeDerivativeOn_Ioo_of_metricCoordinateFieldWithin_geometricValue`, so the
full-field hypotheses can be stated directly in actual pushed-forward tangent
vectors before being promoted to tensor time-regularity. The fixed-IVP and
theorem-family geometric DeTurck gauge-flow bundles now also expose within-set
field-derivative data packages and direct tensor time-regularity projections
from them, matching the ordinary field-data routes at package level. Raw
fixed-IVP and theorem-family intrinsic gauge-flow existence witnesses now mirror
those within-field packages and projections, so endpoint full-field data can be
supplied directly at the raw existence layer before promoting to gauge-pulled
metric time-regularity. It also has within-set chain-rule primitives:
`hasDerivWithinAt_of_timeDifference_and_frozenSpatial`,
`hasDerivWithinAt_timeDifference_of_fullField`, and
`Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_of_hasFDerivAt`
differentiate `B(τ, c(τ)) - B(t, c(τ))` directly at closed-interval endpoints;
`Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_of_eventuallyEq`
is the matching finite-cover/readout-field form. This endpoint time-difference
layer now also subtracts the canonical frozen-spatial `fderivWithin` term, via
`Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_of_hasFDerivAt_and_frozenSpatial`
and its readout-field companion, so callers can use the same `Bfull - spatial`
shape at endpoints as on neighborhood-time interiors. The within-set package
`MetricCoordinateFieldTimeDifferenceComponentDataWithinOn` feeds those
endpoint time-difference and tangent-map derivatives into
`CoordinatePullbackMetricComponentDerivativeWithinOn`; the wrapper
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_metricCoordinateField_timeDifferenceWithin`
then routes that closed-interval component package directly to interior tensor
time-regularity.
The same chain rule now has eventual-equality transfer lemmas, so a geometric
scalar that agrees with the model-coordinate expression only near `t` can reuse
the derivative proof directly.  The named coordinate package
`CoordinatePullbackMetricInnerDerivativeOn` now promotes those chart-level
`B/A/D` derivative hypotheses to the actual geometric
`PullbackMetricInnerDerivativeOn` target, and directly to tensor
`HasTimeDerivativeOn` for the gauge-pulled metric family, so Item 1 is reduced
to proving the coordinate derivative hypotheses for the metric component and
tangent map.  The preferred coordinate scalar expression itself is now named as
`pullbackMetricInnerCoordinateModel`, isolating the concrete `B(τ)(A(τ)u)(A(τ)v)`
term used in chart calculations. The chart-identification step for this scalar
is now proof-bearing: eventual membership of `Φ_τ(x)` in the target tangent
trivialization gives eventual equality between the geometric pullback scalar and
`pullbackMetricInnerCoordinateModel`, and raw `Diffeomorph3GaugeFlowOn` witnesses
provide that eventual equality automatically at times where their time set is a
neighborhood. The remaining positive-dimensional primitive is now isolated as
`CoordinatePullbackMetricModelDerivativeOn`: derivative data for the named
coordinate model itself. This model-derivative package restricts to smaller time
sets and, together with the chart-equality theorem, promotes directly to the
geometric scalar derivative and tensor `HasTimeDerivativeOn`; raw gauge flows
also have direct model-derivative-to-time-derivative wrappers. Coordinate-level,
coordinate-model, and field-level derivative data now all lift through the
fixed-IVP, theorem-family, and raw-existence gauge-flow APIs, so a future chart
calculation can feed the point-4 theorem routes without first repackaging it as
a tensor derivative. The model/field bundle routes explicitly require the
solution time set to be a neighborhood of each time where they are used, making
the endpoint/interior distinction visible rather than hidden.
The moving-coordinate pieces inside `pullbackMetricInnerCoordinateModel` are now
also named explicitly as `pullbackMetricBilinearCoordinateMap` (`B(τ)`) and
`pullbackMetricTangentCoordinateMap` (`A(τ)`), with
`sourceTangentCoordinate` for fixed source vectors. The theorem
`coordinatePullbackMetricModelDerivativeOn_of_components` proves that
derivatives of these concrete `B` and `A` components, plus the expected scalar
velocity identity, are exactly enough to discharge
`CoordinatePullbackMetricModelDerivativeOn`. This primitive is now packaged
directly as `CoordinatePullbackMetricComponentDerivativeOn`, with one-step
component-to-scalar and component-to-tensor promotion theorems and raw
closed-Picard interior wrappers
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn[_Ioo]_of_coordinateComponents`.
A variational model flow now also supplies the concrete component derivatives
directly via `coordinatePullbackMetricComponentDerivativeOn_of_variationalLocalFlow`:
local identifications of the named `B(τ)` and `A(τ)` components with a
variational flow, plus the bilinear-form field derivative and scalar velocity
identity, produce the component package. The raw closed-Picard wrapper
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_variationalLocalFlowComponents`
routes that data straight to interior tensor time-regularity.
A second, narrower route,
`coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap`, matches
the finite-cover Banach readout theorems: it accepts a direct time derivative of
the already-composed concrete `B(τ)` coordinate component and uses only the
variational flow to differentiate the concrete `A(τ)` tangent-coordinate map,
with raw wrapper
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_variationalTangentMapComponents`.
The model algebra now also includes the metric-component half of this remaining
primitive: `hasDerivAt_bilinearFormField_along_curve` differentiates a bilinear
form field `Bfield(τ, y(τ))`, and
`hasDerivAt_bilinearFormField_linear_apply_apply_along_curve` combines that with
the variational tangent-map equation to differentiate
`Bfield(τ, y(τ)) (A(τ)u) (A(τ)v)`. This is also bundled as
`CoordinatePullbackMetricFieldDerivativeOn`, which promotes to
`CoordinatePullbackMetricModelDerivativeOn`, the geometric scalar derivative, and
tensor `HasTimeDerivativeOn`, including raw-gauge-flow and bundle-level
wrappers. The variational
ODE layer now also proves the operator-norm Lipschitz estimate for
left-composition, the product-state Lipschitz estimate for the full variational
vector field `(y, A)' = (f(t,y), Df(t,y) ∘ A)`, and interior/closed-interval
uniqueness for the full pair `(flow, tangent)` from the usual base-flow
Lipschitz hypothesis plus a uniform `‖Df‖` bound. This removes a manual tangent
Lipschitz obligation from the future chart-gluing step and isolates the
remaining product Picard hypotheses to base-field and linearized-coefficient
estimates. The same layer now has the closed-ball specialization matching
Mathlib's `IsPicardLindelof` state, assembles a product-system
`IsPicardLindelof` witness from those closed-ball estimates plus the standard
continuity/norm/time-radius assumptions, and exposes a one-step
`ofProductClosedBallEstimates` constructor for the variational local flow. The
product norm bound is also now derived from component estimates, yielding the
stronger `ofProductComponentClosedBallEstimates` route whose remaining analytic
inputs are exactly base/linearized closed-ball Lipschitz bounds, component norm
bounds, continuity of the product vector field in time, and the usual Picard
time-radius inequality. A further time-continuity adapter now derives product
field continuity from separate time-continuity of `f(·, y)` and `Df(·, y)`,
giving the `ofProductComponentClosedBallContinuityEstimates` constructor whose
inputs match the natural chartwise estimates. The tangent-operator bound itself
can now be derived from closed-ball membership via
`nnnorm_le_nnnorm_add_radius_of_mem_closedBall`, giving an
`ofProductComponentClosedBallContinuityEstimates_of_operatorBall` constructor
that no longer asks callers to supply a separate `A`-state norm bound. The
identity-centered case is simplified further to the explicit bound
`‖A‖₊ ≤ 1 + a` and the corresponding
`ofProductComponentClosedBallContinuityEstimates_of_identityBall` constructor.
The raw gauge-flow layer now also extracts the model-coordinate derivative of
the base flow curve itself: `Diffeomorph3GaugeFlowOn.hasDerivAt_extChartAt_eval_of_mem_Ioo`
turns the manifold derivative of `τ ↦ Φ_τ(x)` into a `HasDerivAt` statement for
the preferred chart around `Φ_t(x)`, with derivative given by the coordinate
form of the DeTurck gauge vector field. The same extraction is available on an
arbitrary raw time set as `hasDerivWithinAt_extChartAt_eval` and at any
neighborhood-time as `hasDerivAt_extChartAt_eval`, so endpoint/restricted-time
routes do not have to reprove the chart conversion. This is the base-curve
derivative needed by the moving metric-component readout.
The time-derivative module now consumes this directly:
`Diffeomorph3GaugeFlowOn.coordinatePullbackMetricFieldDerivativeOn_Ioo_of_baseCoordinate`
packages field-level coordinate data whose moving base point is the actual raw
gauge-flow coordinate curve, using the raw-flow derivative theorem for the
`y'(t)` clause. The companion
`hasTimeDerivativeOn_Ioo_of_baseCoordinateField` then routes that data to
interior tensor time-regularity. The same bridge is now available on arbitrary
raw time sets at neighborhood-times as
`coordinatePullbackMetricFieldDerivativeOn_of_baseCoordinate` and
`hasTimeDerivativeOn_of_baseCoordinateField`, so endpoint/restricted-time
arguments can consume the same base-coordinate readout data without re-entering
the closed-Picard `Ioo` wrapper.
The concrete coordinate algebra has also been exposed: `pullbackMetricBilinearCoordinateMap_apply_eq`
identifies the moving `B(τ)` component with the metric at `Φ_τ(x)` read through
the tangent trivialization centered at `Φ_t(x)`, and
`pullbackMetricTangentCoordinateMap_apply_eq` /
`pullbackMetricTangentCoordinateMap_sourceTangentCoordinate_eq` identify the
moving `A(τ)` component with the gauge pushforward tangent map in source and
target tangent coordinates. These are the chart-local identities needed before
feeding Banach finite-cover metric readouts into the remaining component
derivative hypothesis. The named `metricBilinearCoordinateField` now packages
the two-variable field `(τ, y)` behind the moving `B(τ)` component, and
`pullbackMetricBilinearCoordinateMap_eventuallyEq_metricBilinearCoordinateField`
shows that concrete `B(τ)` is eventually this field evaluated along the raw
coordinate curve `τ ↦ extChartAt (Φ_t x) (Φ_τ x)`.
The raw gauge-flow bridge
`Diffeomorph3GaugeFlowOn.coordinatePullbackMetricFieldDerivativeOn_of_metricCoordinateField`
now consumes this: it automatically constructs the field-level scalar model
equality from the concrete `B(τ)`/`A(τ)` formulas and the raw coordinate curve.
The remaining local inputs are therefore the Fréchet derivative of
`metricBilinearCoordinateField`, the derivative of the concrete tangent
coordinate map, and the scalar velocity identity. Base-time simplification
lemmas now identify `metricBilinearCoordinateField` at `(t, extChartAt p p)`
with the ordinary metric in the tangent trivialization at `p`, and identify the
base-time concrete tangent-coordinate component with the gauge pushforward
tangent vector in target coordinates. Slot-specialized versions remove the
centered-coordinate wrappers entirely when the model slots are
`sourceTangentCoordinate`s of actual tangent vectors. The inverse
`tangentVectorOfCoordinate` is now named as well, with two-sided simplification
lemmas against `sourceTangentCoordinate`, so remaining velocity identities can
switch between model-coordinate and geometric tangent-vector forms directly.
The raw-flow metric-coordinate bridge now has a geometric-slot variant,
`coordinatePullbackMetricFieldDerivativeOn_of_metricCoordinateField_geometricValue`,
whose scalar velocity hypothesis is stated using actual pushed-forward tangent
vectors and only uses centered coordinates for the derivative inputs. The
companion `hasTimeDerivativeOn_of_metricCoordinateField_geometricValue` routes
that data directly to tensor time-regularity, including a closed-Picard
`Ioo` specialization for interior regularity from interval-local raw gauge
flows. A variational-flow variant now identifies the raw coordinate curve and
tangent-coordinate map with a `VariationalLocalFlowSolution`, so the ODE part
of the non-identity gauge calculation is discharged once the named
`metricBilinearCoordinateField` has its Fréchet derivative. The centered
time-direction part of that derivative is now formalized directly from
`HasTimeDerivativeAt` / `HasTimeDerivativeOn`; the remaining positive-dimensional
field derivative is the moving spatial-coordinate part.
The same centered formula now applies to any coordinate curve that is eventually
stationary at the chart center, covering the no-spatial-motion case needed by
identity/static gauges.
For the moving spatial-coordinate side, fixed-time slices of
`metricBilinearCoordinateField` are now proved `C²` in the preferred extended
chart, using the existing hom-bundle coordinate smoothness of each smooth
Riemannian metric slice. The same result now yields the canonical
`HasFDerivWithinAt` / `fderivWithin` derivative on `Set.range I`, a chain-rule
adapter along any chart-centered coordinate curve that stays in the model
range, and a raw-gauge-flow specialization for the frozen-time spatial
contribution along `τ ↦ extChartAt I ((G.maps3 t) x) ((G.maps3 τ) x)`.
The frozen-spatial, additive total-derivative, and time-difference raw-flow
specializations now also have `_self` variants that simplify the centered
`tangentCoordChange` at the base chart to the actual gauge velocity
`X t ((G.maps3 t) x)` before these endpoint calculations are packaged. The
same direct-velocity shape is available for locally equal finite-cover/Banach
readout fields and for both ordinary-neighborhood and within-set component-data
constructors that feed endpoint and closed-Picard packages; the public
`HasTimeDerivativeOn` wrappers for full metric-coordinate Fréchet data now
mirror that direct-velocity interface as well. The variational local-flow
wrappers that fill the tangent-coordinate derivative from the model tangent ODE
now have the same direct-velocity and readout-field forms, including when the
tangent-map identification is only known in the closed-interval within filter;
the open-interior `Ioo` specializations now mirror that direct-velocity API too.
The geometric-slot route, where scalar identities are stated in actual
pushed-forward tangent vectors, now also has ordinary-neighborhood and
within-set direct-velocity field-derivative and tensor time-regularity wrappers.
The closed-Picard `Ioo` geometric-slot specializations now mirror that
direct-velocity interface, so endpoint and interior callers can both state the
`Bfield'` scalar identity using the raw velocity `X t (G.maps3 t x)` and the
actual pushed-forward tangent vectors.
The field-level base-coordinate route now also has ordinary-neighborhood and
closed-Picard `Ioo` direct-velocity wrappers, so callers can package the actual
coordinate-curve derivative as `X t (G.maps3 t x)` instead of the centered
`tangentCoordChange`.
The full-field variational tangent-map endpoint now has direct-velocity
coordinate-slot, readout-field, geometric-slot, and geometric readout-field
wrappers, eliminating another public `Bfield' (1, tangentCoordChange ...)`
obligation from the closed-Picard time-regularity route. The closed-Picard
variational tangent-map Fréchet endpoint now also has direct-velocity
geometric-slot and readout-field variants, including the case where tangent-map
agreement is only known in the closed-interval within filter.
The same-set within-field route now also has direct-velocity base-coordinate,
metric-coordinate, readout-field, and tensor time-regularity wrappers, so
neighborhood-time callers can keep the raw velocity in all full-field
coordinate data packages. The underlying concrete bilinear-coordinate
derivative and ordinary metric-coordinate field package now also have
direct-velocity `_self` companions, so this interface is supported by
proof-level scalar chain-rule data rather than only by later wrapper rewrites.
An additive time/spatial decomposition now upgrades this frozen spatial term to
the full moving `metricBilinearCoordinateField` derivative whenever the
remaining time-difference derivative along the same raw gauge-flow coordinate
curve is supplied. That decomposition is also wired into the concrete
`CoordinatePullbackMetricComponentDerivativeOn` package: raw gauge-flow
component data now only needs the time-difference derivative for the named
metric-coordinate field, the tangent-coordinate-map derivative, and the final
scalar velocity identity including the canonical spatial `fderivWithin` term.
This abstract time-difference component data now also has ordinary and
within-set direct-velocity package forms, plus direct projections to the
concrete component derivative packages and tensor time-regularity, so the raw
velocity can be preserved through the time/spatial decomposition seam itself.
The variational tangent-map endpoints for this time-difference formulation now
also have ordinary and closed-interval direct-velocity wrappers, so the
variational ODE still fills the tangent-map derivative while the scalar
identity keeps the raw gauge velocity. The pushed-forward geometric-slot
variants for the same time-difference endpoints now mirror that direct-velocity
shape, preserving scalar identities in actual tangent vectors without exposing
the centered chart change.
This package now routes all the way to tensor time-regularity, including a
closed-Picard `Ioo` specialization. A variational-flow endpoint now discharges
the tangent-coordinate-map derivative in this time-difference formulation, so
on closed Picard interiors the remaining hard input is the named
time-difference derivative plus the final scalar velocity identity. Conversely,
`hasDerivAt_timeDifference_of_fullField_and_frozenSpatial` and the raw-flow
specialization
`Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_hasFDerivAt`
now derive that named time-difference derivative from a full Fréchet derivative
of `metricBilinearCoordinateField` after subtracting the already-proved frozen
spatial `fderivWithin` term. Thus the time-difference route is aligned with the
Banach finite-cover readout shape: a full field derivative can now feed the
closed-Picard component package without a separate hand-written difference
calculation. This is also packaged as the raw-flow component-data constructor
`Diffeomorph3GaugeFlowOn.metricCoordinateFieldTimeDifferenceComponentDataOn_of_hasFDerivAt`
and tensor endpoint
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_of_metricCoordinateField_hasFDerivAt`,
plus the closed-Picard interior wrapper
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_metricCoordinateField_hasFDerivAt`,
which hide the `Btime = Bfull - spatial` subtraction from callers.
The tangent-map part has also been extracted as the reusable lemma
`SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_hasDerivAt_of_variationalTangentMap`:
eventual equality between the concrete `pullbackMetricTangentCoordinateMap` and
a `VariationalLocalFlowSolution` tangent map now directly gives the required
`HasDerivAt` statement for the concrete component. The existing component
bridges use this lemma, so future chart-local applications can cite the tangent
ODE bridge independently. The closed-Picard endpoint
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_metricCoordinateField_hasFDerivAt_variationalTangentMap`
now combines this full-field derivative route with the variational tangent-map
identification directly: on Picard interiors, callers provide the full
`metricBilinearCoordinateField` Fréchet derivative, an eventual equality between
the concrete tangent-coordinate map and the variational tangent flow, and the
final scalar velocity identity.
The companion geometric-slot endpoint
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_metricCoordinateField_hasFDerivAt_variationalTangentMap_geometricValue`
states the same closed-Picard result with the scalar velocity identity written
in actual pushed-forward tangent vectors rather than raw centered model slots,
removing one more coordinate rewrite from future geometric applications.
The variational base-flow identification is now also formalized:
`Diffeomorph3GaugeFlowOn.variationalBaseVelocity_eq_tangentCoordChange_of_eventuallyEq`
uses uniqueness of derivatives to identify `f(t, y(t))` with the chart-coordinate
raw gauge vector field whenever the variational model flow agrees locally with
the raw gauge coordinate curve. The model-coordinate endpoint
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_metricCoordinateField_hasFDerivAt_variationalLocalFlow`
uses that identification directly, so the scalar identity can be stated at the
variational base point using `f(t, y(t))` and the concrete tangent-coordinate
slots. The geometric endpoint
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_metricCoordinateField_hasFDerivAt_variationalLocalFlow_geometricValue`
then accepts the same full field derivative with the scalar identity written in
actual pushed-forward tangent vectors. The readout-field model-coordinate
variant
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_hasFDerivAt_variationalLocalFlow`
transfers the Fréchet derivative from any locally equal two-variable
bilinear-form readout through the named
`metricBilinearCoordinateField_hasFDerivAt_of_eventuallyEq` bridge before this
geometric rewrite; the corresponding
geometric readout endpoint
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_hasFDerivAt_variationalLocalFlow_geometricValue`
does the same after rewriting the scalar identity into actual pushed-forward
tangent vectors. The direct chain-rule route, which
bypasses the time-difference decomposition entirely, now has the matching
geometric-slot endpoint
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_metricCoordinateField_variationalLocalFlow_geometricValue`.
Its readout-field variant
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_variationalLocalFlow_geometricValue`
transfers a Fréchet derivative from any locally equal two-variable bilinear-form
readout to `metricBilinearCoordinateField` through the same named bridge,
matching the finite-cover Banach readout shape more closely.
At the primitive decomposition level, the theorem
`Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_eventuallyEq`
now lets a locally equal finite-cover/Banach readout supply the full field
derivative before subtracting the frozen spatial derivative, so later arguments
can enter the time-difference route without first rewriting to the higher-level
endpoint.
The corresponding package-level endpoint is now named as well:
`Diffeomorph3GaugeFlowOn.metricCoordinateFieldTimeDifferenceComponentDataOn_of_eventuallyEq_hasFDerivAt`
builds the reusable time-difference component data, and
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_of_eventuallyEq_metricCoordinateField_hasFDerivAt`
turns that same readout shape directly into `HasTimeDerivativeOn` for raw
`C³` gauge flows at neighborhood-times.
The closed-Picard interior specialization
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_hasFDerivAt`
then packages the same readout route on `Ioo tmin tmax`, matching the interval
shape used by the variational local-flow endpoints. The endpoint/right-derivative
analogue is now also packaged:
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_metricCoordinateField_hasFDerivAtWithin`
and
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_hasFDerivAtWithin`
accept full metric-coordinate Fréchet data together with closed-interval
`HasDerivWithinAt` tangent-coordinate-map data and produce the same interior
tensor time-regularity conclusion without requiring the endpoint time set to be
a neighborhood.
The variational tangent-map layer also has a direct readout-field entry point:
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_hasFDerivAt_variationalTangentMap`
accepts the finite-cover/Banach two-variable readout before the base-flow
eventual-equality hypotheses are introduced. Its geometric-slot companion
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_hasFDerivAt_variationalTangentMap_geometricValue`
keeps that readout-field entry point while stating the scalar velocity identity
in actual pushed-forward tangent vectors at the base time.
On the PDE side,
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_hasDerivAt_chartRHS_of_mem_Ioo`
and
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_base_sourceTangentCoordinate_hasDerivAt_chartRHS_of_mem_Ioo`
now expose the Banach chart right-hand side as a centered derivative of the
named `metricBilinearCoordinateField`, including the tangent-vector-slot scalar
form used by geometric gauge-pullback calculations. The same thin bridge now
packages the smooth Banach realization's chart RHS as the raw identity-gauge
scalar derivative obligation,
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.id_pullbackMetricInnerDerivativeOn_Ioo_chartRHS`,
and as the corresponding tensor time-derivative statement for the identity
pullback metric family,
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.id_pullbackMetricFamily_hasTimeDerivativeOn_Ioo_chartRHS`.
The centered metric-coordinate bridge also reaches the closed-left endpoint:
`metricBilinearCoordinateField_base_hasDerivWithinAt_Ici_chartRHS_of_mem_Ico`
and its `sourceTangentCoordinate` variant expose the Banach chart RHS as a
right derivative on `Ici t` throughout `Ico ivp.initialTime sol.terminalTime`.
The subsingleton-tangent case is already closed for arbitrary geometric `C³`
DeTurck gauge-flow families by componentwise vanishing, including direct
gauge-reduced, intrinsic, and ordinary theorem-package projections and
model-space/empty-manifold/raw-existence synonyms.
The same module now also exposes ordinary point-4 theorem-family endpoints
routed through the full chosen-DeTurck → raw `C³` gauge-flow → gauge-reduced
chain in the subsingleton-tangent, subsingleton-model, and empty-manifold cases.
The fixed-IVP geometric and raw gauge-flow routes now have the same
model-space and empty-manifold aliases as the theorem-family routes, so the
zero-dimensional API is symmetric across fixed and family theorem packages.
The rank-one special case now also exposes intrinsic and ordinary theorem
packages projected through the gauge-reduced rank-one package, including the
model-space theorem-family aliases.
The smooth Ricci-DeTurck chart-closure layer now also has thin companion routes
from global and interval `RicciDeTurckChartClosureData` to intrinsic and
ordinary compact point-4 theorem packages through the raw identity `C^3`
gauge-flow witness and its named scalar derivative data, rather than only
through the direct identity-gauge projection.
The geometric corrected-velocity side now also has the named zero-curvature
readout
`gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_zero_of_pullbackBackgroundRicciCurvature_eq_zero`:
once the pulled-back background Ricci curvature vanishes in a slot, the concrete
`C³` gauge-corrected pullback velocity vanishes in that slot.
The same zero-curvature-to-zero-velocity route has an initial-time specialization
named
`gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge_eq_zero_initial_of_pullbackBackgroundRicciCurvature_eq_zero`.
The initial Ricci-flat transport API now has matching `C³` anchored-gauge
wrappers:
`AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackBackgroundRicciCurvature_eq_zero_initial_of_isLeviCivita`
and
`AnchoredIntrinsicDeTurckDiffeomorph3GaugeOn.pullbackChosenBackgroundRicciCurvature_eq_zero_initial`.
The same `C³` transport facts are also available from the DeTurck local-solution
object by supplying the anchored `C³` gauge:
`IntrinsicDeTurckLocalSolution.pullbackBackgroundRicciCurvature_eq_zero_initial_of_diffeomorph3Gauge_of_isLeviCivita`
and
`IntrinsicDeTurckLocalSolution.pullbackChosenBackgroundRicciCurvature_eq_zero_initial_of_diffeomorph3Gauge`.

**Module location.** A new module
`Geometry/Manifold/RicciFlow/GaugeReduction/Diffeomorph3FlowTimeDerivative.lean`
sibling of the existing `Diffeomorph3FlowDerivative.lean` and
`Diffeomorph3FlowExistence.lean`. Should not require touching
`SmoothRealization.lean`.

### Item 2 — raw `C³` gauge-flow existence on a compact manifold

**Mathematical content.** For a `C^∞` time-dependent vector field `X` on
a compact `C^∞` manifold `M`, produce a `C³` time-dependent self-
diffeomorphism family `Φ` solving the gauge-flow ODE

```
∂_τ Φ_τ(x) = X_τ(Φ_τ(x)),   Φ_{t₀} = id
```

i.e. an inhabitant of `Diffeomorph3GaugeFlowOn X s t₀`.

**Specialization.** When `X` is the intrinsic DeTurck vector field of a
chosen DeTurck local solution, this gives an inhabitant of
`IntrinsicDeTurckGaugeFlowExistenceFamily`.

**What still has to be done.** Adapt Mathlib's existing
flow-by-vector-field theorems (`mathlib4` has integral curves and
local flows for `C^k` vector fields on smooth manifolds) to produce
the bundled `SmoothSelfDiffeomorph3Family` representation used here.
Compactness gives global-in-time existence on a small interval; `C³`
regularity follows from `C^∞` source regularity.
The raw-flow layer now includes fixed-IVP and theorem-family
`of_hasMFDerivWithinAt`, `of_hasMFDerivAtOn`, and `of_hasMFDerivAt`
constructors, named-derivative-family adapters, geometric-to-raw adapters,
raw-flow derivative/local-at-time extractors, and raw-flow time-set restriction,
with simp readouts showing restriction preserves the same `C³` diffeomorphism
family and anchoring data,
so an ODE construction that already returns pointwise manifold derivative data
or a named geometric gauge-flow bundle can be connected directly to
`Diffeomorph3GaugeFlowOn` and `IntrinsicDeTurckGaugeFlowExistenceFamily`.  The
`of_hasMFDerivAtOn` variants match the common Picard-interior shape where the
ODE construction has ordinary derivatives only for times in the selected open
time set, not for all real times. The derivative-view layer now mirrors this
with `Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn`,
`ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily`, and the theorem-family
`ofDerivativeAtFamily` raw-existence bridge, so named Picard-interior derivative
data no longer has to be manually weakened to within-set form before entering
the gauge-flow existence API. The same derivative-view layer now upgrades
within-time-set derivative data back to ordinary-at-time data whenever the time
set is a neighborhood at each of its times, with fixed-IVP and theorem-family
wrappers. Both within-time-set and ordinary-at-time intrinsic derivative views
now also restrict monotonically to smaller time sets, matching the localized
Picard intervals produced by chart ODE arguments. The
same named-derivative symmetry is now present
for a single fixed IVP via `ChosenIntrinsicDeTurckGaugeFlowDerivative`,
`ChosenIntrinsicDeTurckGaugeFlowDerivativeAt`,
`IntrinsicDeTurckGaugeFlowExistence.ofDerivative`, and
`IntrinsicDeTurckGaugeFlowExistence.ofDerivativeAt`.
The theorem-family zero-gauge-field constructor now also carries the required
pullback metric time-derivative proof, so any family whose intrinsic DeTurck
gauge field vanishes on each solution time set can enter the gauge-reduction
API without re-proving the identity-gauge velocity algebra; the chosen-DeTurck
fixed-IVP and theorem-family layers now expose direct zero-field projections to
the gauge-reduced, intrinsic, and ordinary theorem packages.
The first Banach-model ODE bridge for this item is now proof-bearing in
`GaugeReduction.ModelGaugeFlowODE`: mathlib's time-dependent Picard-Lindelöf
theorem is packaged as `LocalFlowSolution` and `LipschitzLocalFlowSolution`,
including the ODE derivative on the closed time interval, initialization on a
closed ball of initial data, ordinary interior derivative extractors, and
named continuity on the Picard interval, plus Lipschitz dependence on initial data.
It also packages the continuous space-time partial-flow form as
`ContinuousLocalFlowSolution`, so the chart-level output now includes the
continuity needed before gluing local solutions. Continuous and variational
local-flow packages now expose named base-flow, tangent-map, and vector-slot
time-slice continuity bridges on the Picard interval, including direct
within-interval, interior pointwise, and open-interior `ContinuousOn`
readouts, and the autonomous `C¹`
local-integral-curve specialization now also returns continuity on its open
existence interval. Variational local-flow uniqueness now also has direct
interior and closed-interval vector-slot `A(t) v` bridges derived from
operator-norm bounds, matching the scalar gauge-pullback chain-rule
hypotheses, and these base-flow, continuous-flow, tangent-map, vector-slot, and
full variational-pair overlap results now have direct pointwise equality
readouts on both `Ioo` and `Icc`. The autonomous `C¹` vector-field route now also extracts a
proof-level `Nonempty LocalFlowSolution` package on a smaller closed time
interval and smaller initial ball, giving the first direct bridge from
mathlib's autonomous integral-curve theorem to the packaged raw model-flow API.
It now also has a localized form that immediately restricts that autonomous
existence witness to any smaller closed time interval containing the base time
and any smaller initial ball.
The model-flow packages now also have restriction constructors for
`LocalFlowSolution`, `LipschitzLocalFlowSolution`, `ContinuousLocalFlowSolution`,
and `VariationalLocalFlowSolution`, preserving ODE, continuity, Lipschitz, and
tangent-equation data on smaller closed time intervals and smaller initial balls.
Their `Nonempty` wrappers now restrict directly as well, so Picard existence
witnesses can be localized without destructing and rebuilding the package.
Picard-Lindelöf packages now also have direct localized constructors for local,
Lipschitz, and continuous model-flow data, combining theorem extraction with
closed-interval/closed-ball restriction in one API call, together with matching
`Nonempty` wrappers so later existence arguments do not need to choose a flow
until necessary.
Restriction readout simp lemmas record that the localized packages retain the
same underlying flow, and in the variational case the same tangent map, making
overlap proofs easier to rewrite. The same compatibility is now exposed for
forgetful projections: restricting a continuous flow and then forgetting to
`LocalFlowSolution`, or restricting a variational flow and then forgetting to
continuous/local flow data, is definitionally the same as forgetting first and
then restricting.
These are the overlap/localization maps needed before chartwise solutions can be
glued into a manifold-level flow. Base-flow uniqueness now also has overlap
forms for `LocalFlowSolution` and `ContinuousLocalFlowSolution`: two packages
with different centers/radii agree on `Ioo` and `Icc` for any initial point in
both closed balls, assuming the usual common Lipschitz state-region hypotheses.
Variational tangent-map uniqueness has matching overlap forms on `Ioo` and
`Icc`, plus operator-norm and vector-slot specializations on both intervals, so
tangent compatibility can also be proved across chart-local packages with
different centers and radii once the base curves agree. Full variational-pair uniqueness
now has overlap forms on both `Ioo` and `Icc`, plus pointwise equality readouts
for the base, continuous, tangent, vector-slot, and full pair conclusions,
combining base-flow Lipschitz uniqueness and tangent operator-norm uniqueness
into a single compatibility statement for `(flow, tangent)`.
The time-derivative layer now also has center-trajectory closed-interval and
interior scalar chain-rule wrappers for
`Bfield(t, y(t))(A(t)u)(A(t)v)`, so basepoint gauge-pullback calculations can
consume variational model-flow data without manually threading
`x₀ ∈ closedBall x₀ r`; the same center wrappers now have within-filter and
ordinary-neighborhood eventual-equality transfer forms for chart-local scalar
identifications.
The generic closed-interval scalar calculus now also includes exact within-set
`B(t)(A(t)u)(A(t)v)` chain-rule primitives, including the `A' = D ∘ A` gauge
tangent-map specialization, so endpoint component packages can use the direct
model expression without first passing through an eventual-equality wrapper.
There is also a generic within-filter eventual-equality transfer form for the
same `B/A/A'` calculation before specializing to the `D ∘ A` gauge tangent-map
shape.
The raw `C³` gauge-flow existence layer now also exposes named continuity
consequences of the ODE derivative data: `continuousOn_eval` for every base
point on the time set and `continuousWithinAt_extChartAt_eval` in the preferred
chart coordinates centered at the current time. Closed-Picard raw flows now
also expose the corresponding open-interior continuity helpers:
`continuousOn_eval_Ioo` and `continuousAt_extChartAt_eval_of_mem_Ioo`.
The fixed-IVP and theorem-family raw intrinsic gauge-flow existence packages
now mirror those derivative, continuity, and tangent-trivialization readouts
directly, so downstream chart arguments no longer have to unwrap the raw flow.
They also expose the ordinary-neighborhood versions of the same readouts:
`hasMFDerivAt`, `hasDerivAt_extChartAt_eval`,
`continuousAt_extChartAt_eval`, `continuousAt_eval`, and
`eventually_mem_trivializationAt_eval`, plus the matching within-time-set
preferred-chart continuity readout. The same fixed-IVP/theorem-family layer now
also mirrors raw preferred-chart range eventuality, both at ordinary
neighborhood-times and relative to the solution time set.
The raw, fixed-IVP, and theorem-family preferred-chart derivative readouts now
also have centered-chart simplifications that rewrite the derivative value from
`tangentCoordChange I p p p (...)` to the actual gauge velocity. This removes a
recurrent normalization step from downstream scalar gauge-pullback calculations,
and raw `Diffeomorph3GaugeFlowOn` witnesses can now be transported across
time-dependent vector fields that agree on the active time set.
The same raw layer now also has proof-level `Nonempty` wrappers for the
geometric, within-derivative, ordinary-on-time-set derivative, unrestricted
derivative, restriction, and identity-flow constructors, letting downstream
existence arguments retain raw gauge-flow existence without choosing a concrete
flow until needed.
The fixed-IVP intrinsic DeTurck gauge-flow existence layer mirrors this
proof-level shape for its derivative-data, ordinary-at-time derivative,
zero-field identity, chosen-background identity, subsingleton, and empty
constructors.
The theorem-family intrinsic DeTurck gauge-flow existence layer now has the
same proof-level wrappers, including conversion back down to a fixed IVP and
the named derivative-family/ordinary-derivative-family constructors.
The model ODE uniqueness layer now also has center-trajectory wrappers for
packaged local flows, continuous space-time local flows, and the full
variational pair `(flow, tangent)` on both `Ioo` and `Icc`, so basepoint
uniqueness arguments no longer repeat the same closed-ball membership proof.
The same module now also
packages the model-space variational equation as
`VariationalLocalFlowSolution`, with tangent maps initialized by the identity
and satisfying `A'(t) = Df(t, flow(t)) ∘ A(t)` on the Picard interval; this is
the ODE-side source of the `A`-derivative hypothesis in
`CoordinatePullbackMetricModelDerivativeOn`. It also proves interior uniqueness
for the variational/tangent maps once the base local flows agree and the
linearized ODE is uniformly Lipschitz on a state region, which is the tangent
compatibility input needed for chart gluing; the same uniqueness conclusion is
also available on the closed Picard interval using the within-interval endpoint
continuity. The module now also defines the product variational vector field
`(y, A)' = (f(t, y), Df(t, y) ∘ A)` and proves projection lemmas extracting the
base, tangent, and vector-slot tangent ODEs from any packaged
`LocalFlowSolution` of that product system, together with named continuity for
the base and tangent components, providing the intended route from
Picard-Lindelöf on a product Banach
space to variational tangent data. A continuous local flow for this product
system, initialized on `(x, 1)` and restricted to a base ball contained in the
product Picard ball, now extracts directly to `VariationalLocalFlowSolution`.
Consequently, a Picard-Lindelöf hypothesis for the product variational system
also constructs `VariationalLocalFlowSolution` directly after the same base-ball
restriction, with a specialized constructor that discharges this restriction
automatically when the chosen base radius is no larger than the product Picard
radius; continuous-product and product Picard constructors now also have
closed-interval localized variants and proof-level `Nonempty` wrappers,
including the radius-specialized form needed when a chart calculation shrinks
the Picard time interval before extracting tangent-map data. The one-step
closed-ball estimate constructors have matching
localized variants, including the componentwise-continuity and identity/operator
ball specializations used by chart-local variational estimates, and now expose
matching proof-level `Nonempty` wrappers for each estimate route. The ODE package
now also supplies ordinary interior time
derivatives for both the base flow `y(t)` and tangent map `A(t)`, including
closed-interval and interior vector-slot derivatives for `t ↦ A(t)v` via
`tangent_apply_hasDerivWithinAt` and `tangent_apply_hasDerivAt_of_mem_Ioo`, and
`Diffeomorph3FlowTimeDerivative.lean` uses those facts to build
`CoordinatePullbackMetricFieldDerivativeOn` directly from a variational local
flow on the interior Picard interval. It also proves the exact scalar chain rule
for `B(t, y(t))(A(t)u)(A(t)v)` along such a variational flow, plus an
eventual-equality transfer form for chart-local scalar identities. This removes
the ODE part of the remaining dynamic pullback chain rule from the list of
manual hypotheses: the residual chart-local work is now the metric-component
field derivative and the concrete identification of the geometric coordinate
model with the selected variational flow/tangent data. Raw `C³` gauge flows
constructed on closed Picard intervals also now specialize directly to the open
interior interval: their ordinary manifold derivative, continuity, chart
membership, coordinate-model equality, and coordinate-model/field
time-derivative bridges are available on `Ioo tmin tmax`. There is also a
one-step theorem,
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_variationalLocalFlowModel`,
combining a closed-interval raw gauge flow with variational model-flow chart
data to produce interior time-regularity of the gauge-pulled metric family.
This route only needs the already-composed moving bilinear-form readout
`B : ℝ → E →L[ℝ] E →L[ℝ] ℝ` to have `HasDerivAt B B' t`; it no longer forces
the caller to package the metric component as a full space-time
`Bfield : ℝ × E → E →L[ℝ] E →L[ℝ] ℝ` with a `HasFDerivAt` proof when a direct
time derivative of the readout is available.  The finite-cover analytic layer
now supplies exactly this vector-valued readout derivative:
`BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_hasDerivAt_of_mem_Ioo`
and its continuous-metric / smooth-realization variants differentiate the whole
coordinate bilinear form as an element of `E →L[ℝ] E →L[ℝ] ℝ`, before applying
it to tangent vectors; matching one-sided `HasDerivWithinAt` variants on
`Ici t` are also available at the Picard interval endpoints.  This connects the
Banach Picard metric curve directly to the weaker time-only dynamic pullback
interface on both interior and boundary-reduced routes.
The same module also records the
autonomous `C¹` local-integral-curve specialization and Gronwall-based
uniqueness bridges on the open and closed Picard time intervals for two packaged
local model flows whose curves stay in a uniformly Lipschitz state region; the
continuous space-time package now forgets to `LocalFlowSolution` and inherits
the same uniqueness bridges directly.
What remains is the genuinely manifold-level lift: pass intrinsic DeTurck vector
fields to these chartwise Banach ODE hypotheses, prove compatibility/gluing and
invertibility of the local flow, and upgrade the result to the bundled `C³`
self-diffeomorphism family.
The raw-flow interface also now extracts the first chart-regularity consequence
needed for that lift: at any time where the time set is a neighborhood, a raw
`Diffeomorph3GaugeFlowOn` gives continuity of `τ ↦ Φ_τ(x)` and eventual
membership in the preferred tangent trivialization centered at `Φ_t(x)`. The
same continuity and chart-membership facts are also available directly within
the raw time set, matching the restricted intervals produced by local ODE
theorems before any neighborhood-of-time strengthening is known.

**Module location.** The Banach-model bridge lives in
`Geometry/Manifold/RicciFlow/GaugeReduction/ModelGaugeFlowODE.lean`.  The final
manifold constructor should extend
`Geometry/Manifold/RicciFlow/GaugeReduction/Diffeomorph3FlowExistence.lean`
with the general (non-Levi-Civita-background) case.

### Item 3 — the Ricci-DeTurck Banach chart and chart-closure data

**Mathematical content.** For every initial-value problem `ivp` with
continuous Riemannian initial metric `g₀`, construct

* a `TimeDependentGeometricRicciDeTurckBanachChart` whose Banach
  representative `A` agrees with the geometric intrinsic Ricci-DeTurck
  RHS on the positive-definite metric locus, satisfies the named
  Picard–Lindelöf hypotheses near `g₀`, and is locally Lipschitz on the
  metric locus;
* a `RicciDeTurckChartClosureData` providing the smooth realization of
  every Banach chart solution and the reverse encoding for every chosen
  DeTurck candidate.

**Status.** This is the Hamilton–DeTurck local existence theorem
(Hamilton 1982; DeTurck 1983), strict-quasilinear parabolic PDE on a
compact Riemannian manifold. It is by itself a paper-scale formalization
project. Mathlib v4.29.1 does not yet contain the parabolic
Hölder/Sobolev framework needed; that infrastructure has to be built
first. The abstract closure-data interface itself now has named readouts for
both the global and closed-interval packages:
`nonempty_realization`, `realizationCandidateEncoding`, and
`nonempty_candidateEncoding`. These wrappers expose the already-stored smooth
realization and reverse encoding fields without reproving or destructing the
closure data, but they do not supply the missing Schauder/parabolic estimates.
The thin raw-gauge route module also now has proof-level `Nonempty` wrappers
for the global and interval closure-data projections to intrinsic and ordinary
compact point-4 theorem packages through the raw identity gauge:
`nonempty_intrinsicLocalExistenceUniqueness_viaRawIdentityGauge` and
`nonempty_localExistenceUniqueness_viaRawIdentityGauge`.
It now also gives the genuine symmetric-carrier interval closure data the same
proof-level readout shape for chosen-background, intrinsic, and ordinary
compact theorem packages, plus proof-level intrinsic and ordinary theorem-family
witnesses from a family of symmetric-carrier interval closure data. The same
`Nonempty` theorem-family wrappers are available for families of global and
closed-interval `RicciDeTurckChartClosureData`. Ambient interval closure data
now also has proof-level constructors for genuine symmetric-carrier closure,
both from an explicit restricted-carrier Picard proof and after shrinking into a
closed ball contained in the Riemannian metric cone. The density-based
interval-scoped restricted symmetric carrier is now connected back to the
chart's built-in restricted carrier by both a subtype equality and an ambient
coordinate coe equality on the Picard interval and Riemannian metric locus,
which makes the smooth-density approximation route usable without confusing it
with the ungated chart carrier outside the interval. The preferred-cover
local-bounds smooth-approximation module now also turns that density-based
Picard shrink into an actual state-preserving
`BanachEvolutionLocalSolutionIn` witness with terminal-time control and
uniqueness on common closed intervals, plus a proof-level `Nonempty` readout
for the density carrier. The chart-derived symmetric carrier now
has the parallel Banach-solution extraction after the standard metric-cone
shrink, so both the built-in carrier and the density-based carrier expose
actual state-preserving ODE solution witnesses rather than only Picard
hypotheses, and the standard-shrink route now also has a proof-level `Nonempty`
readout; when the current Picard ball already lies in the Riemannian metric
cone, the same chart-carrier solution/uniqueness witness is now available
without shrinking first, including a proof-level `Nonempty` readout. Genuine
symmetric-carrier interval closure data now also exposes
that Banach solution and common-interval uniqueness witness directly before
projecting to chosen-background, intrinsic, or ordinary theorem packages, plus
a proof-level `Nonempty` readout for callers that only need existence, and it
now mirrors the ambient closure-data proof-level readouts for smooth realization
and reverse candidate encoding. The
density-based interval-carrier solution now transports back to the chart's
built-in restricted carrier whenever its terminal time stays within the Picard
interval, giving a solution-level bridge rather than only pointwise vector-field
equalities. The preferred-cover local-bounds route now also performs that
transport internally, returning a chart-carrier `BanachEvolutionLocalSolutionIn`
witness directly from the smooth-density Picard shrink, plus a proof-level
`Nonempty` readout for callers that only need existence. At the vector-bundle
smooth-approximation layer, the local coordinate-map boundedness hypothesis is
now discharged for continuous Riemannian vector bundles:
`RiemannianSectionSmoothApprox` derives
`eventually_norm_trivializationAt_lt` from mathlib's Riemannian bundle estimate
and uses it to produce preferred-bilinear smooth approximants, including the
finite-cover Banach-norm approximation theorem. The same module now also
derives that finite-cover inverse bound from compactness of the cover pieces
inside their fixed trivialization domains by factoring fixed-center inverses
through centered inverse trivializations and continuous coordinate changes.

**Suggested decomposition** (multi-session):

1. Choose a function-space realization of the metric locus. The
   existing `ContinuousSectionSpace` finite-cover model is only `C^0`
   on the spatial side; for parabolic estimates we need either a
   parabolic Hölder space `C^{2+α, 1+α/2}` or a Sobolev space `H^k` with
   `k > n/2 + 2`. The cleanest first pass is parabolic Hölder.
2. Prove a *local* Lipschitz estimate for the Ricci-DeTurck RHS in the
   chosen norm around any continuous Riemannian metric (Schauder-type
   estimate). The hardest of the three substeps.
3. Verify the four chart fields (`A`, `picard`, `lipschitz`,
   `geometric`) and the closure data fields (`realization`, `encode`).

**Module location.** A new subdirectory
`Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/` with files for
parabolic norm setup, the Lipschitz/Schauder estimate, and the actual
chart construction. Will be the largest single addition of this whole
program.

## Dependencies between items

```
Item 1 ───────┐
              ├── feeds into the smooth-realization derivative
Item 2 ───────┤   field of RicciDeTurckChartClosureData
              │
Item 3 ───┘  (independent of Items 1, 2; consumes them indirectly
              via the chart-closure-data → family theorem chain)
```

Items 1 and 2 are *intermediate analytic infrastructure*; Item 3 is the
genuine PDE existence theorem. None of the three depends on the other
two as a strict prerequisite — they can be developed in parallel — but
all three are required to construct the chart-closure data needed by
the existing family-theorem constructor.

## Recommended sequencing

1. **Item 2 first.** It is the most modular and mathematically tractable
   because compact-manifold flow-by-vector-field is already in Mathlib
   in essentially the form needed; the work is mostly bridging to the
   `SmoothSelfDiffeomorph3Family` wrapper.
2. **Item 1 next.** Pure tensor calculus. The reduction to scalar
   derivatives is already in place; what remains is a moderately long
   chain-rule proof with no PDE content.
3. **Item 3 last.** This is the analytic main theorem and should be
   approached as its own multi-session project after Items 1 and 2 are
   in place, so that the `RicciDeTurckChartClosureData` builder is
   ready to consume the resulting Banach chart.

## Build-cost note

A clean `lake build` of `RicciFlowLocalExistence` from a cold cache is
expensive (the `AnalyticPDE/SmoothRealization` module alone takes
~18 minutes on the development machine). Each of the items above
should therefore be developed in **new modules** that import only the
already-cached parts of the scaffolding, never modify
`SmoothRealization.lean` or `AnalyticPDE.lean` directly, and only
appear in `RicciFlowLocalExistence.lean` as additional imports.
`AnalyticPDE/SmoothRealizationGaugeRoutes.lean` follows this pattern: it leaves
the heavy PDE realization file unchanged and adds raw-gauge endpoint projections
plus Banach-to-centered-metric-coordinate readout bridges on top of the
already-proved global and interval chart-closure data.
