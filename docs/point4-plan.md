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
the scalar identity is stated in actual pushed-forward tangent vectors. The
metric-coordinate Fréchet transfer now also has a relative-filter form, so
readout equality inside the product derivative domain is enough for the
open-product-domain time-difference scalar bridge, its reusable component-data
package, and the corresponding closed-Picard tensor time-regularity route.
The fully localized product-domain route now also has a variational-local-flow
form that assumes product-domain convergence only for the model Picard graph;
closed-interval base-flow equality transports that convergence to the raw
coordinate graph and rewrites the model ODE velocity to the raw gauge vector
field before applying the domain-restricted gauge-pullback theorem. A further
open-product-domain form derives the model graph convergence from the
variational local-flow continuity package whenever the derivative domain is open
and contains the Picard graph endpoint. The raw-coordinate route now has the
parallel open-product-domain bridge: raw graph convergence is derived from the
gauge-flow preferred-chart derivative/continuity theorem whenever the domain is
open around the raw coordinate endpoint. The same open-domain reduction now
exists at the lower time-difference component-data layer, including for locally
equal finite-cover/readout fields, so downstream tensor routes can inherit the
derived graph convergence without restating it. Closed-Picard tensor
time-regularity now also exposes direct open-product-domain wrappers for both
raw metric-coordinate fields and locally equal readout fields. The variational
tangent-map tensor routes now mirror the same open-domain interface, including
ordinary-neighborhood and closed-interval tangent-map agreement and readout-field
forms, so the model tangent ODE can supply the tangent derivative without a
separate graph-convergence proof. This reduction now reaches the generic
calculus layer itself: open-domain variants of the moving-base bilinear-field
chain rules and the full-field time-difference lemmas derive the needed product
graph convergence from the within-derivative/continuity of the base curve. The
raw gauge-flow open-domain scalar time-difference theorem is now proved through
that generic calculus, so the open-domain component-data constructors no longer
rest on a compatibility wrapper around the older explicit-convergence theorem.
The variational local-flow full-field route now also has open-product-domain
scalar, named metric-coordinate-field, readout-field, and geometric-slot tensor
wrappers; these consume `HasFDerivWithinAt` on an open chart product domain at
the model-flow endpoint directly, without upgrading local Banach/readout data to
global `HasFDerivAt`. The same open-domain input shape now reaches the ordinary
open-interior `Ioo` tensor route as well, including readout-field and
geometric-slot forms, by deriving the scalar `HasDerivAt` calculation from the
closed-interval open-domain proof and the variational local-flow continuity
package. These variational routes now also have relative-filter readout-field
companions for the open product-domain input shape, so finite-cover readout
equality inside the derivative domain is enough for both tangent-map and
geometric-slot tangent-map handoffs, as well as the variational-local-flow
tensor handoffs.
The full-field coordinate derivative route now
also has a closed-interval package
`CoordinatePullbackMetricFieldDerivativeWithinOn`, a variational local-flow
constructor for it, and direct endpoint-to-interior scalar promotion theorems,
so Picard endpoint base-flow/tangent-map derivatives plus a full
metric-coordinate Fréchet derivative can feed the geometric scalar target
without repackaging through frozen-time component data.
The endpoint coordinate-model layer now also has the named package
`CoordinatePullbackMetricModelDerivativeWithinOn`, monotone time-set
restriction, component and field-level constructors, and a direct promotion
`pullbackMetricInnerDerivativeWithinOn_of_coordinateModelWithin`, matching the
ordinary coordinate-model layer before passing to the geometric scalar target.
Raw
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
field-derivative and operator-domain derivative data packages with direct tensor
time-regularity projections from them, matching the ordinary field/operator
routes at package level. Raw fixed-IVP and theorem-family intrinsic gauge-flow
existence witnesses now mirror those within-field and operator-domain packages
and projections, so endpoint full-field or product-state operator data can be
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
uniqueness for the full pair `(flow, tangent)` and the operator
derivative-domain tuple `(t, flow, tangent)` from the usual base-flow
Lipschitz hypothesis plus a uniform `‖Df‖` bound. Product-derived continuous
flows now also preserve joint space-time continuity/eventual membership for
that operator tuple on closed and open Picard cylinders, and product Lipschitz
dependence gives fixed-time Lipschitz/continuity/distance estimates for it as
the base initial point varies. The scalar calculus now also has operator-domain
chain rules for readouts `F(t, y, A)` over `(t, flow(t), tangent(t))`, including
within-domain/open-domain, closed-interval, ordinary-interior, and
    center-trajectory variational local-flow forms, plus eventual-equality transfer
    wrappers for locally identified geometric/readout scalars. The primitive
    base-curve operator chain rules now also have within-filter and ordinary
    eventual-equality transfer lemmas, so local scalar identifications can be
    applied before specializing to a variational-flow package. The raw closed-Picard
`HasTimeDerivativeOn` route now consumes those operator-domain scalar readouts
directly, both when the derivative domain is open and when explicit graph
convergence is supplied; continuous product-Picard wrappers now perform the
`(y, A)` to variational-flow conversion internally for the same operator-domain
routes. The named coordinate package layer now also has
`CoordinatePullbackMetricOperatorDerivativeWithinOn` and
`CoordinatePullbackMetricOperatorDerivativeWithinOnOpen`, plus scalar, tensor,
raw gauge-flow, and closed-Picard `Ioo` promotion wrappers, so the same
operator-domain readouts can be stored as endpoint coordinate derivative data
before selecting a final tensor route. The open-domain operator package now
lowers to the explicit within-domain package by deriving product-graph
convergence from openness, and the fixed-IVP derivative-data layer exposes the
same conversion for bundled gauge-flow data. Variational local-flow constructors now
fill those packages directly from the model base/tangent ODE derivatives,
continuous product-Picard wrappers now enter the same named operator-coordinate
routes, including readouts stated directly on the product state `(y,A)` through
the final tensor `HasTimeDerivativeOn` bridge. The four-variable scalar-readout
routes now also accept direct product-state `(t,y,Au,Av)` data in both
open-domain and explicit-domain forms and have eventual-equality transfer lemmas
for locally equal scalar identities, the full operator-domain scalar-readout
routes accept direct product-state `(t,y,A)` data in the same variants, and the
closed-Picard metric-coordinate-field routes now accept direct product-state
base/tangent agreement in ordinary, open-domain, geometric pushed-vector-slot,
and finite-cover/readout-field forms before raw closed-Picard wrappers expose
both named package bridges and `HasTimeDerivativeOn` promotions.
This removes a manual tangent Lipschitz obligation from the future
chart-gluing step and isolates the
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
The component-continuity layer now also has state-preserving selected-flow
constructors, including operator-ball and identity-ball forms, and direct
forward-time local-inverse wrappers from component closed-ball estimates plus
the explicit `HasFDerivWithinAt` hypothesis identifying `Df` as the spatial
derivative of `f`. The same state-preserving selection now exposes direct
closed-ball readouts in the `r ≤ R` radius-specialized form and at the
component-continuity estimate level, so chart applications can reuse the Picard
state containment without rebuilding the product witness. The strict
time-slice derivative theorem now also has an `r ≤ R` product-Picard form and a
direct component-continuity estimate wrapper, including operator-ball and
identity-ball specializations, separating differentiability of the selected
time slice from the finite-dimensional local-inverse packaging. The
neighborhood-map equality form now also has closed-ball `ℝ≥0` product-Picard and
component-continuity estimate wrappers, including the operator-ball and
identity-ball forms, so chart-gluing arguments can consume the same estimates
without passing through the `OpenPartialHomeomorph` package.
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
The ordinary and within-set time-difference component packages, including their
direct-velocity variants, now also restrict monotonically along raw gauge-flow
time-set shrinkage, so closed-Picard localizations can be applied before this
remaining scalar input is converted to component derivative data.
The closed-Picard ordinary time-difference tensor route now also has centered
and direct-velocity variants that accept this data on the full raw `Icc`
interval and perform the open-interior restriction internally.
The variational tangent-map endpoints for this time-difference formulation now
also have ordinary and closed-interval direct-velocity wrappers, so the
variational ODE still fills the tangent-map derivative while the scalar
identity keeps the raw gauge velocity. The pushed-forward geometric-slot
variants for the same time-difference endpoints now mirror that direct-velocity
shape, preserving scalar identities in actual tangent vectors without exposing
the centered chart change.
The closed-Picard variational-local-flow full-field/time-difference endpoints
now also have direct raw-velocity geometric-slot forms,
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_metricCoordinateField_timeDifferenceWithin_hasFDerivAt_variationalLocalFlowWithin_geometricValue_self`
and
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEq_metricCoordinateField_timeDifferenceWithin_hasFDerivAt_variationalLocalFlowWithin_geometricValue_self`,
so finite-cover readouts at the variational base point can keep
`X t (G.maps3 t x)` in the scalar identity while closed-interval base-flow
agreement is used only to move the derivative endpoint to the raw centered
chart.
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
`SmoothRealization.lean`. The scalar calculus in this module now also has a
four-variable open-domain chain rule for readouts stated directly on
`(t, y, u, v)`, with variational local-flow specializations for
`(t, flow(t), A(t)u, A(t)v)`, so local chart derivatives can depend on the base
point and both pushed vector slots in one product domain. The same four-variable
route now has ordinary open-interior `Ioo` variants, including center-trajectory
specializations, so interior endpoint routes can consume product-domain scalar
derivatives without first passing through a closed-interval within derivative.
Both the closed-interval and open-interior four-variable routes now also have
within-filter/ordinary eventual-equality transfer forms, so chart-local
geometric scalar identities can reuse those product-domain derivatives after
they are identified with the model-coordinate readout near the endpoint. The
raw closed-Picard tensor route now consumes those scalar readouts directly via
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_variationalLocalFlowScalarReadoutOpen`
and
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_variationalLocalFlowScalarReadoutWithinOpen`,
so local chart/Banach data on `(t, y, A(t)u, A(t)v)` no longer has to be
repackaged as a two-variable bilinear-form field before producing
`HasTimeDerivativeOn`. The same scalar calculus now also has non-open-domain
forms where callers supply product-graph convergence/eventual membership into
the derivative domain directly, matching closed state constraints that arise in
Picard and Banach chart arguments; those non-open-domain forms now also have
within-filter and ordinary eventual-equality transfer companions, so local
geometric scalar identities can reuse the closed-domain product derivative
without adding an artificial openness step. The raw tensor route mirrors that
generalization through
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_variationalLocalFlowScalarReadout`
and
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_variationalLocalFlowScalarReadoutWithin`,
so closed-domain scalar readouts can now reach `HasTimeDerivativeOn` without an
artificial openness hypothesis.
On the Banach chart-closure side, symmetric-carrier interval data now also
exposes the strongest Banach solution/terminal-bound/uniqueness witness as an
existential readout with a nonempty smooth-realization-and-reverse-encoding
fiber, so downstream arguments can access the chosen solution and uniqueness
proof directly without first destructing the larger `Nonempty` package.

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
`Diffeomorph3GaugeFlowOn` and `IntrinsicDeTurckGaugeFlowExistenceFamily`.
The generic raw-flow API now also has open-Picard readouts from an abstract
time-set equality `s = Ioo tmin tmax`, exposing the local-at-time equation,
ordinary manifold/preferred-chart derivatives, continuity, and chart/trivialization
membership without first specializing to fixed-IVP or theorem-family packages.
The fixed-IVP and theorem-family open-Picard layers now lift the same
fixed-chart derivative, neighborhood-equal vector-field derivative, continuity,
and source-neighborhood readouts, so finite-cover arguments can stay in a chosen
chart center after the solution time set is identified with an `Ioo` interval.
The derivative-view layer now also preserves fixed-chart packages under time-set
restriction and under the closed-Picard `Icc` to open-interior `Ioo` upgrade, so
closed-interval chart Picard outputs can be used as ordinary interior ODE data
without detouring through the centered-chart package.
The time-derivative layer has matching raw open-Picard bridges from the same
`s = Ioo tmin tmax` equality, upgrading coordinate model, field, operator, and
component scalar derivative data to the named pullback-metric derivative and
`HasTimeDerivativeOn` packages without an extra neighborhood hypothesis.
Proof-level `Nonempty` transport wrappers now move raw intrinsic gauge-flow
existence back to the anchored geometric gauge objects and the fixed-IVP/family
geometric gauge-flow bundles.
Autonomous Mathlib `IsMIntegralCurveOn` data now also has a direct bridge to the
repository's constant-in-time gauge-flow predicate and raw `C³` gauge-flow
packaging, with matching local-at-time and all-times-in-set adapters for
`IsMIntegralCurveAt` plus raw `C³` packaging from local integral-curve data at
every time in the raw time set, matching the shape of Mathlib integral-curve
outputs. The
`of_hasMFDerivAtOn` variants match the common Picard-interior shape where the
ODE construction has ordinary derivatives only for times in the selected open
time set, not for all real times. The derivative-view layer now mirrors this
with `Diffeomorph3IntrinsicGaugeFlowDerivativeAtOn`,
`ChosenIntrinsicDeTurckGaugeFlowDerivativeAtFamily`, and the theorem-family
`ofDerivativeAtFamily` raw-existence bridge, so named Picard-interior derivative
data no longer has to be manually weakened to within-set form before entering
the gauge-flow existence API. It now also has named preferred-chart ODE packages
for both within-time-set and ordinary-at-time chart data:
`Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn`,
`Diffeomorph3IntrinsicGaugeFlowChartDerivativeAtOn`,
`ChosenIntrinsicDeTurckGaugeFlowChartDerivativeFamily`, and
`ChosenIntrinsicDeTurckGaugeFlowChartDerivativeAtFamily`, with fixed-IVP and
theorem-family `ofChartDerivative` / `ofChartDerivativeAt` bridges, so
source-neighborhood chart ODE data can enter raw existence without unpacking
into ad hoc constructor arguments. Both chart-ODE packages now have
eventual-equality transfer lemmas:
local model-coordinate curves with the right derivative can be used after they
are identified eventually with the actual centered preferred-chart coordinate
readout, with the within-set version using the closed-interval within-filter.
The primitive and chart derivative views now also have model-vector-field
RHS-identification adapters, in both within-set and ordinary-at-time forms:
once the model vector field agrees with the intrinsic DeTurck gauge field along
the flow, its manifold or preferred-chart derivative package is promoted to the
intrinsic derivative package directly. The fixed-IVP and theorem-family chosen
solution packages now mirror the same adapters, so Picard model-vector-field
derivatives can enter the named derivative and chart-ODE packages without first
hand-specializing the RHS at each solution. The raw gauge-flow existence layer
now also has one-step model-vector-field chart ODE constructors that perform the
same along-flow RHS rewrite while building `Diffeomorph3GaugeFlowOn`, including
the closed-Picard `Icc` to open-interior `Ioo` handoff, and the fixed-IVP and
theorem-family intrinsic existence layers now carry that same closed-Picard
model-field handoff directly to `IntrinsicDeTurckGaugeFlowExistence(.Family)`.
The derivative-view layer now also performs this closed-Picard model-field
handoff directly: fixed-IVP and theorem-family wrappers convert closed-interval
model-field chart ODE data plus the along-flow intrinsic DeTurck identification
into ordinary chart and primitive derivative data on the chosen open `Ioo`
solution time set. Endpoint callers can therefore use the scalar gauge-pullback
route from the model-field Picard output without first rebuilding an intrinsic
chart-ODE package by hand.
The same handoff is now available with relative-filter vector-field equality on
the open `Ioo` interval: both the raw existence constructors and the derivative
packages can consume model-field data without requiring endpoint pointwise
equality on all of `Icc`. The primitive and preferred-chart derivative packages
now also have same-time-set relative-filter RHS-identification adapters at the
raw, fixed-IVP, and theorem-family levels, so closed/restricted Picard outputs do
not have to be converted to pointwise RHS equality before entering the named
derivative views. The raw fixed-IVP and theorem-family existence layers expose
matching same-time-set one-step constructors for both within-set and
ordinary-at-time chart ODE data.
The chart-ODE packages themselves now also prove the underlying manifold-curve
continuity and convert directly to primitive intrinsic manifold derivative data
in both within-time-set and ordinary-at-time forms, with fixed-IVP and
theorem-family lifts; the existence-layer derivative readouts now use that
direct chart-to-manifold bridge instead of passing through a raw gauge-flow
witness first. Ordinary-at-time chart-ODE data can now also be weakened back to
the within-time-set chart package, mirroring the existing primitive derivative
weakening and letting callers choose either endpoint package shape without
reproving source-neighborhood or derivative facts.
The primitive derivative views now also round-trip with the geometric
`SatisfiesGaugeFlowOn` equation, both for fixed-IVP packages and theorem
families, so either formulation can be recovered without rebuilding the
pointwise ODE proof. Anchoring plus primitive derivative data now also
constructs the fixed-IVP and theorem-family geometric `C³` gauge-flow bundles
directly.
The same derivative-view layer now upgrades both primitive derivative data and
preferred-chart ODE data from within-time-set form back to ordinary-at-time form
whenever the time set is a neighborhood at each of its times, with fixed-IVP and
theorem-family wrappers. Both within-time-set and ordinary-at-time intrinsic
derivative views, including the chart-ODE view, now also restrict monotonically
to smaller time sets, matching the localized Picard intervals produced by chart
ODE arguments. Closed-Picard `Icc` primitive and chart-ODE data now also have
direct ordinary open-interior `Ioo` upgrade lemmas to primitive derivative data,
with the chart-ODE route also retaining its direct chart-ODE upgrade, matching
the standard Picard endpoint-to-interior handoff, and the raw existence API now has a one-step
constructor producing `Diffeomorph3GaugeFlowOn` on `Ioo tmin tmax` directly from
centered preferred-chart ODE data proved within `Icc tmin tmax`, including a
named intrinsic DeTurck chart-package version. The same raw open-interior
constructor shape is now available from closed-interval pointwise manifold
derivative data and from the named intrinsic DeTurck primitive derivative
package. Fixed-IVP and theorem-family wrappers now lift those closed-Picard
primitive/chart packages directly whenever the chosen solution time set is
explicitly the open interval `Ioo tmin tmax`, via `ofPicardIccDerivative`,
`ofPicardIccChartDerivative`, and matching `Nonempty` wrappers. The
derivative-view layer now has matching fixed-IVP and theorem-family handoffs
from closed-Picard primitive and chart-ODE data directly to ordinary-at-time
derivative packages, plus chart-ODE packages, on those explicit open solution
time sets, so endpoint scalar routes can consume the Picard data without first
constructing raw gauge-flow witnesses. The chart-based raw and fixed-IVP
closed-Picard constructors now route through the same primitive derivative
handoff, keeping the existence path aligned with the derivative-view API. The
raw existence layer now turns those explicit open Picard time-set
identifications into the neighborhood-of-each-time hypothesis once, and exposes
fixed-IVP and theorem-family open-Picard readouts for pointwise manifold
derivatives, preferred-chart derivatives, continuity, and chart-source control.
The time-derivative layer consumes that raw fact and exposes fixed-IVP and
theorem-family `..._of_timeSet_eq_Ioo` wrappers for coordinate-model,
component, field-level, and within-set endpoint data. The same
named-derivative symmetry is now present
for a single fixed IVP via `ChosenIntrinsicDeTurckGaugeFlowDerivative`,
`ChosenIntrinsicDeTurckGaugeFlowDerivativeAt`,
`IntrinsicDeTurckGaugeFlowExistence.ofDerivative`, and
`IntrinsicDeTurckGaugeFlowExistence.ofDerivativeAt`, together with the
fixed-IVP chart-data bridges `IntrinsicDeTurckGaugeFlowExistence.ofChartDerivative`
and `IntrinsicDeTurckGaugeFlowExistence.ofChartDerivativeAt`.
The raw fixed-IVP and theorem-family time-derivative packages now also expose
the corresponding open-Picard named scalar derivative wrappers for endpoint
within-field and within-component data, so theorem-package routes that consume
`PullbackMetricInnerDerivativeData` do not have to detour through tensor
`HasTimeDerivativeOn` just to discharge the `Ioo` neighborhood proof.
The geometric endpoint data records now mirror this: fixed-IVP, global family,
and interval family data can replace their bundled gauge-flow component by raw
gauge-flow existence plus named scalar or coordinate-level pullback-metric
derivative data, not only by a preconverted tensor pullback-time-derivative
proof.
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
named continuity on the Picard interval, plus direct time-slice Lipschitz,
continuity, and distance-estimate readouts for dependence on initial data. The
Picard extraction now also has a state-preserving Lipschitz-flow selection,
`toStatePreservingLipschitzLocalFlowSolution`, with
`exists_lipschitzLocalFlowSolution_mem_closedBall` and product variational
readouts
`ofProductStatePreservingPicardLindelof_flow_mem_base_closedBall[_forward_Icc]`,
so the closed Picard state ball can feed convex state-tube hypotheses without
reconstructing the fixed-point proof. The Lipschitz package now also proves
joint space-time continuity on the local
Picard cylinder from the uniform initial-data Lipschitz estimate and the
ODE-derived time continuity of each trajectory, and promotes any Lipschitz local
flow package to the continuous space-time partial-flow form
`ContinuousLocalFlowSolution`, so the chart-level output now includes the
continuity needed before gluing local solutions. Both Lipschitz and continuous
local-flow packages now also expose within-filter space-time continuity and
eventual-membership readouts on the Picard cylinder, matching chart-domain
membership arguments where the initial point and time vary together; at points
inside the initial-data ball and open Picard interval, those readouts upgrade
to ordinary neighborhood continuity, eventual membership, and `ContinuousOn` on
the open Picard cylinder. Continuous and variational
local-flow packages now expose named base-flow, tangent-map, and vector-slot
time-slice continuity bridges on the Picard interval, including direct
within-interval, interior pointwise, and open-interior `ContinuousOn`
readouts. Local, continuous, and variational model-flow packages now also expose
closed-interval within-filter and interior open-set eventual-membership
readouts, turning continuity plus membership in a chart domain into the
source-neighborhood facts expected by the within-set and ordinary chart-ODE
gauge-flow constructors; the variational package now also exposes the same
eventual-membership readouts for tangent maps and fixed vector slots `A(t) v`,
so tangent-coordinate chart-domain facts can be transported directly from the
linearized ODE. It now also exposes closed-interval and open-interior product
readouts for `(flow(t), tangent(t))`, matching chart-local derivative domains
that depend on the base point and tangent map together, plus the corresponding
time-graph readouts for `(t, flow(t), tangent(t))` and for fixed two-vector
slots `(t, flow(t), A(t)u, A(t)v)`. The autonomous `C¹`
local-integral-curve specialization now also returns continuity on its open
existence interval. Variational local-flow uniqueness now also has direct
interior and closed-interval vector-slot `A(t) v` bridges derived from
operator-norm bounds, matching the scalar gauge-pullback chain-rule
hypotheses, and these base-flow, continuous-flow, tangent-map, vector-slot, and
full variational-pair overlap results now have direct pointwise equality
readouts on both `Ioo` and `Icc`. The autonomous `C¹` vector-field route now also extracts
proof-level `Nonempty LocalFlowSolution`, `Nonempty LipschitzLocalFlowSolution`,
and `Nonempty ContinuousLocalFlowSolution` packages on a smaller closed time
interval and smaller initial ball, giving direct bridges from mathlib's
autonomous Picard-Lindelöf theorem to the packaged raw model-flow APIs. These
autonomous existence witnesses now also have localized forms that immediately
restrict to any smaller closed time interval containing the base time and any
smaller initial ball.
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
Model-flow compatibility now also has common-subinterval forms:
`LocalFlowSolution.eqOn_common_Icc_of_lipschitzOnWith_of_mem` and
`ContinuousLocalFlowSolution.eqOn_common_Icc_of_lipschitzOnWith_of_mem` prove
closed-interval overlap equality after restricting two packages with different
ambient Picard intervals to a shared interval containing the same base time,
and
`VariationalLocalFlowSolution.flow_tangent_eqOn_common_Icc_of_lipschitzOnWith_opNorm_bound_of_mem`
does the same for the full `(flow, tangent)` pair. The scalar-readout derivative
domain now has the matching common-interval theorem
`VariationalLocalFlowSolution.time_flow_tangent_apply_pair_eqOn_common_Icc_of_lipschitzOnWith_opNorm_bound_of_mem`
for `(t, flow, A(t)u, A(t)v)`.
The common-subinterval layer now also exposes direct pointwise readouts for the
local, continuous, full variational-pair, and scalar-readout conclusions, plus
common-interval time-graph compatibility for `(t, flow, tangent)` and
common-interval scalar-state compatibility for `(flow, A(t)u, A(t)v)`.
The base-flow, full variational-pair, scalar-state, and scalar time-graph
common-subinterval readouts now also have open-interval `Ioo` forms, so
chart-gluing arguments can use the visible open overlap directly instead of
manually restricting closed-overlap equality.
Tangent-map and fixed-vector-slot uniqueness now also have direct
common-subinterval `Icc`/`Ioo` readouts once the base curves are already
identified on the shared open interval, matching the two-stage chart-gluing
route where base flows are glued before tangent data.
The same base-equality route now packages full `(flow, tangent)` and
`(t, flow, tangent)` closed-overlap readouts, plus scalar-state and scalar
time-graph readouts for `(flow, A(t)u, A(t)v)` and
`(t, flow, A(t)u, A(t)v)`, so scalar pullback gluing can reuse an existing
base-flow equality instead of re-entering the base Lipschitz uniqueness theorem.
It also upgrades open-overlap base-flow equality to closed-overlap scalar-state
and scalar time-graph readouts by continuity, via
`VariationalLocalFlowSolution.flow_eqOn_common_Icc_of_eqOn_Ioo_of_mem` and the
closed `_of_flow_eqOn_Ioo` scalar wrappers.
These are the overlap/localization maps needed before chartwise solutions can be
glued into a manifold-level flow. Base-flow uniqueness now also has overlap
forms for `LocalFlowSolution` and `ContinuousLocalFlowSolution`: two packages
with different centers/radii agree on `Ioo` and `Icc` for any initial point in
both closed balls, assuming the usual common Lipschitz state-region hypotheses.
The base-flow uniqueness layer now also has a meeting-time form: two packaged
curves with different base times, centers, and radii agree on the whole closed
Picard interval if they meet at an interior time and stay in the same Lipschitz
state region. The corresponding reanchoring lemmas identify a curve from one
package with a second package based at a later interior time and initialized at
the first curve's value there. These readouts are available for
`LocalFlowSolution`, `ContinuousLocalFlowSolution`, and the base component of
`VariationalLocalFlowSolution`, giving the model-side uniqueness input needed
to compare forward and reanchored chartwise flow segments. They also have
common-subinterval forms for packages with different ambient Picard intervals,
provided both package base times lie in the visible common interval.
The same uniqueness mechanism now also yields interior time-slice injectivity:
`LocalFlowSolution.flow_injOn_of_lipschitzOnWith_of_mem_Ioo` and
`ContinuousLocalFlowSolution.flow_injOn_of_lipschitzOnWith_of_mem_Ioo` show that
if two initial points in the Picard ball have the same image at an interior time
and their trajectories remain in a common Lipschitz state region, then the
initial points are equal. The corresponding
`flow_injOn_common_Ioo_of_lipschitzOnWith_of_mem` variants first restrict to a
shared visible closed interval, so chart-gluing arguments can use only the
state-region hypotheses available on the overlap. Variational local-flow
packages expose the same base-flow injectivity readouts directly through their
continuous-flow component. This is the first model-level invertibility input for
upgrading glued chartwise flows to diffeomorphism slices.
Variational tangent-map uniqueness has matching overlap forms on `Ioo` and
`Icc`, plus operator-norm and vector-slot specializations on both intervals, so
tangent compatibility can also be proved across chart-local packages with
different centers and radii once the base curves agree. The same variational
ODE uniqueness mechanism now also gives tangent-map injectivity at interior
times: an operator-norm bound for `Df` along the base curve implies
`Function.Injective (α.tangent x t)` and
`LinearMap.ker (α.tangent x t) = ⊥`, with center-trajectory and common visible
`Ioo` interval variants. In finite-dimensional model spaces, this has now been
upgraded to `LinearMap.range (α.tangent x t) = ⊤` and packaged as
`V ≃L[ℝ] V` through
`tangent_continuousLinearEquiv_of_opNorm_bound_of_mem_Ioo` and its common-`Ioo`
and center-trajectory variants. The model layer now also connects this to the
inverse-function theorem: once the still-missing strict spatial derivative of
the time-slice map is supplied and identified with the variational tangent map,
`flow_timeSlice_map_nhds_eq_of_hasStrictFDerivAt_Ioo` gives the neighborhood
mapping equality and
`exists_flow_timeSlice_openPartialHomeomorph_of_hasStrictFDerivAt_Ioo` packages
the corresponding local open partial homeomorphism, with common-`Ioo` variants.
The common-`Ioo` inverse-function readouts now also have the same C¹-style entry
point as the single-interval route:
`flow_timeSlice_map_nhds_eq_common_Ioo_of_eventually_hasFDerivAt` and
`exists_flow_timeSlice_openPartialHomeomorph_common_Ioo_of_eventually_hasFDerivAt`
derive the strict derivative input from ordinary nearby spatial derivatives
and continuity of `y ↦ α.tangent y t`. The same local-homeomorphism packages
can now be unpacked into concrete open source and target neighborhoods with
`MapsTo` and `InjOn` for the time-slice map:
`flow_timeSlice_exists_open_nhds_mapsTo_injOn_of_hasStrictFDerivAt_Ioo`,
`flow_timeSlice_exists_open_nhds_mapsTo_injOn_common_Ioo_of_hasStrictFDerivAt`,
and the corresponding C¹-style variants expose exactly the local injective
patch needed by chart-gluing arguments. The full-interval and common-`Ioo`
routes additionally expose genuine bijective open patches through
`flow_timeSlice_exists_open_nhds_bijOn_of_hasStrictFDerivAt_Ioo`,
`flow_timeSlice_exists_open_nhds_bijOn_of_eventually_hasFDerivAt_Ioo`,
`flow_timeSlice_exists_open_nhds_bijOn_common_Ioo_of_hasStrictFDerivAt` and
`flow_timeSlice_exists_open_nhds_bijOn_common_Ioo_of_eventually_hasFDerivAt`.
The full-interval and common-`Ioo` routes also have ball-source forms,
`flow_timeSlice_exists_ball_mapsTo_injOn_of_hasStrictFDerivAt_Ioo`,
`flow_timeSlice_exists_ball_mapsTo_injOn_of_eventually_hasFDerivAt_Ioo`,
`flow_timeSlice_exists_ball_mapsTo_injOn_common_Ioo_of_hasStrictFDerivAt`
and
`flow_timeSlice_exists_ball_mapsTo_injOn_common_Ioo_of_eventually_hasFDerivAt`,
which shrink the source to a positive metric ball inside the inverse patch.
Product Picard flows now lift that
C¹-style common-interval criterion directly from ordinary spatial
differentiability on the initial-data ball through
`ofProduct_flow_timeSlice_map_nhds_eq_common_Ioo_of_hasFDerivAt_on_initialBall`
and
`exists_ofProduct_flow_timeSlice_openPartialHomeomorph_common_Ioo_of_hasFDerivAt_on_initialBall`.
They also expose the explicit open-neighborhood `MapsTo`/`InjOn` form through
`ofProduct_flow_timeSlice_exists_open_nhds_mapsTo_injOn_of_hasFDerivAt_on_initialBall_Ioo`
and
`ofProduct_flow_timeSlice_exists_open_nhds_mapsTo_injOn_common_Ioo_of_hasFDerivAt_on_initialBall`.
The product full-interval and common-interval paths have matching bijective
open-patch readouts through
`ofProduct_flow_timeSlice_exists_open_nhds_bijOn_of_hasFDerivAt_on_initialBall_Ioo`
and
`ofProduct_flow_timeSlice_exists_open_nhds_bijOn_common_Ioo_of_hasFDerivAt_on_initialBall`.
The product full-interval and common-interval paths likewise have
`ofProduct_flow_timeSlice_exists_ball_mapsTo_injOn_of_hasFDerivAt_on_initialBall_Ioo`
and
`ofProduct_flow_timeSlice_exists_ball_mapsTo_injOn_common_Ioo_of_hasFDerivAt_on_initialBall`,
so radius-shrinking chart arguments can use a ball source immediately.
Product Picard convex-state hypotheses, the state-preserving closed-ball
estimate specialization, and the componentwise closed-ball continuity estimate
packages now feed those common-`Ioo` time-slice neighborhood-map and local
open-partial-homeomorphism readouts directly. The common-`Ioo` convex-state
product route now also unpacks the forward and backward open-partial-homeomorphism
packages into explicit open source and target neighborhoods with `MapsTo` and
`InjOn`, via
`ofProduct_flow_timeSlice_exists_open_nhds_mapsTo_injOn_common_Ioo_of_Df_lipschitzOnWith_on_convex_state_forward_Icc_of_mem_ball`
and its backward analogue. The same forward/backward convex-state common-`Ioo`
route now also has open `BijOn` patch readouts and positive source-ball
`MapsTo`/`InjOn` readouts.
The product-Picard convex-state route now also has the backward-time half of this
local-inverse bridge: a left-endpoint Grönwall estimate feeds
`flow_timeSlice_hasFDerivAt_of_Df_lipschitzOnWith_on_convex_state_backward_Icc_of_mem_ball`,
which lifts through the product package to
`ofProduct_flow_timeSlice_hasStrictFDerivAt_of_Df_lipschitzOnWith_on_convex_state_backward_Icc_of_mem_ball`
and the backward interior neighborhood/open-partial-homeomorphism readouts
`ofProduct_flow_timeSlice_map_nhds_eq_of_Df_lipschitzOnWith_on_convex_state_backward_Ioo_of_mem_ball`
and
`exists_ofProduct_flow_timeSlice_openPartialHomeomorph_of_Df_lipschitzOnWith_on_convex_state_backward_Ioo_of_mem_ball`.
The product-Picard convex-state route now also has whole-closed-interval
ordinary and strict differentiability bridges,
`ofProduct_flow_timeSlice_hasFDerivAt_of_Df_lipschitzOnWith_on_convex_state_Icc_of_mem_ball`
and
`ofProduct_flow_timeSlice_hasStrictFDerivAt_of_Df_lipschitzOnWith_on_convex_state_Icc_of_mem_ball`,
which internalize the forward/backward time split and let later gauge-flow
arguments state the convex state-tube hypotheses once on `Icc tmin tmax`. The
same whole-interval convex-state hypotheses now also feed the interior
neighborhood-map and open-partial-homeomorphism readouts
`ofProduct_flow_timeSlice_map_nhds_eq_of_Df_lipschitzOnWith_on_convex_state_Ioo_of_mem_ball`
and
`exists_ofProduct_flow_timeSlice_openPartialHomeomorph_of_Df_lipschitzOnWith_on_convex_state_Ioo_of_mem_ball`.
This backward local-inverse bridge now also lifts through the state-preserving
closed-ball Picard route: the closed-ball estimate forms
`ofProductStatePreservingPicardLindelof_flow_timeSlice_hasStrictFDerivAt_of_closedBall_estimates_backward_Icc_of_mem_ball`
and
`exists_ofProductStatePreservingPicardLindelof_flow_timeSlice_openPartialHomeomorph_of_closedBall_estimates_backward_Ioo_of_mem_ball`
discharge convex-state membership from the Picard state ball, while the
`..._closedBall_nnnorm_estimates_backward...` map/open-local-inverse variants
consume the usual global `‖Df‖₊ ≤ BD` estimate on `Icc tmin tmax`. The same
backward readouts are available in the radius-specialized and localized Picard
forms
`ofProductStatePreservingPicardLindelof_restrict_flow_timeSlice_map_nhds_eq_of_closedBall_nnnorm_estimates_backward_Ioo_of_le_radius`
and
`exists_ofProductStatePreservingPicardLindelof_restrict_flow_timeSlice_openPartialHomeomorph_of_closedBall_nnnorm_estimates_backward_Ioo_of_le_radius`.
Componentwise closed-ball continuity estimates now expose the corresponding
backward neighborhood-map and open-partial-homeomorphism APIs directly,
including the operator-ball and identity-ball specializations, via
`ofProductStatePreservingComponentClosedBallContinuityEstimates_flow_timeSlice_map_nhds_eq_of_hasFDerivWithinAt_backward_Ioo_of_le_radius`
and
`exists_ofProductStatePreservingComponentClosedBallContinuityEstimates_flow_timeSlice_openPartialHomeomorph_of_hasFDerivWithinAt_backward_Ioo_of_le_radius`.
The same backward bridge now has common-`Ioo` forms for overlap arguments:
`ofProduct_flow_timeSlice_map_nhds_eq_common_Ioo_of_Df_lipschitzOnWith_on_convex_state_backward_Icc_of_mem_ball`
and
`exists_ofProduct_flow_timeSlice_openPartialHomeomorph_common_Ioo_of_Df_lipschitzOnWith_on_convex_state_backward_Icc_of_mem_ball`
lift through the state-preserving Picard closed-ball estimates to
`ofProductStatePreservingPicardLindelof_flow_timeSlice_map_nhds_eq_common_Ioo_of_closedBall_nnnorm_estimates_backward_Icc_of_le_radius`
and
`exists_ofProductStatePreservingPicardLindelof_flow_timeSlice_openPartialHomeomorph_common_Ioo_of_closedBall_nnnorm_estimates_backward_Icc_of_le_radius`,
while the non-localized state-preserving closed-ball route now also exposes
forward and backward common-`Ioo` open `BijOn` patches and positive source-ball
`MapsTo`/`InjOn` patches directly from the same `ℝ≥0` estimates. The
componentwise closed-ball continuity layer exposes the matching
operator-ball and identity-ball common-backward readouts.  The generic
componentwise backward-common route now also unpacks that local inverse into the
same gluing-ready concrete patches as the forward route:
`ofProductStatePreservingComponentClosedBallContinuityEstimates_flow_timeSlice_exists_open_nhds_bijOn_common_Ioo_of_hasFDerivWithinAt_backward_Icc_of_le_radius`
and
`ofProductStatePreservingComponentClosedBallContinuityEstimates_flow_timeSlice_exists_ball_mapsTo_injOn_common_Ioo_of_hasFDerivWithinAt_backward_Icc_of_le_radius`.
The operator-ball and identity-ball backward-common componentwise routes now
expose the same two concrete inverse-patch readouts, so callers using the
specialized tangent-operator estimates do not have to unfold the common
`OpenPartialHomeomorph`.
The same componentwise estimates now also have localized backward-interior
readouts on a shrunk Picard interval, including the neighborhood-map equality,
open-partial-homeomorphism package, bijective open patch, and positive
source-ball patch, via the corresponding
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_*_of_hasFDerivWithinAt_backward_Ioo_of_le_radius`
family.
The localized backward bridge now also has the common-`Ioo` overlap forms
needed when the shrunk Picard interval is used inside a larger chart overlap:
the state-preserving Picard layer exposes the corresponding
`ofProductStatePreservingPicardLindelof_restrict_flow_timeSlice_*_common_Ioo_of_closedBall_nnnorm_estimates_backward_Icc_of_le_radius`
family, and the componentwise closed-ball continuity layer exposes the matching
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_*_common_Ioo_of_hasFDerivWithinAt_backward_Icc_of_le_radius`
family, including operator-ball and identity-ball concrete inverse-patch
specializations.
The localized operator-ball and identity-ball backward-common componentwise
routes now also expose the specialized neighborhood-map equalities and the
actual `OpenPartialHomeomorph` witnesses, matching the forward route and letting
glued inverse-slice arguments keep the same local inverse object without
unpacking through concrete open or ball patches first.
This strict derivative input has now been reduced one step further in the model
layer: `flow_timeSlice_hasStrictFDerivAt_of_eventually_hasFDerivAt` uses
Mathlib's real `C¹`-implies-strict-differentiability theorem, so ordinary
spatial derivatives of nearby time slices plus continuity of
`y ↦ α.tangent y t` imply the strict derivative required by the inverse
function theorem. `flow_timeSlice_hasFDerivAt_of_hasFDerivAt_spaceTime` and
`flow_timeSlice_hasStrictFDerivAt_of_eventually_hasFDerivAt_spaceTime` also
accept full space-time Fréchet derivatives of `(y, τ) ↦ flow (y, τ)`, extracting
the fixed-time spatial derivative by precomposing with the spatial inclusion
`v ↦ (v,0)`. The new endpoint criterion
`flow_timeSlice_hasFDerivAt_of_remainder_bound_nhds_zero` turns a first-order
remainder estimate
`‖flow(x+h,t)-flow(x,t)-tangent(x,t)h‖ ≤ η(h)‖h‖`, with `η(h) → 0`, directly
into the ordinary spatial derivative of the time slice; the remaining analytic
model task is therefore to obtain this estimate from the nonlinear variational
ODE by Gronwall. The supporting identity
`gronwallBound_zero_left_eq_mul_forcing` records the linear dependence of
Mathlib's zero-initial-error Gronwall bound on the forcing term, isolating the
last algebraic step needed to convert such a bound into `o(‖h‖)`. That
conversion is now formalized as
`gronwallBound_zero_left_forcing_mul_norm_isLittleO`, and
`flow_timeSlice_hasFDerivAt_of_gronwall_remainder_bound_nhds_zero` consumes the
result directly: a model-flow remainder bounded by the corresponding Gronwall
expression gives the ordinary spatial derivative of the time slice.
`spatialRemainder` now names this nonlinear first-order error, and
`flow_timeSlice_hasFDerivAt_of_remainder_deriv_bound_Icc` applies Mathlib's
Gronwall inequality in time: once the concrete remainder curve starts at zero
and has derivative bounded by `K‖remainder‖ + η(h)‖h‖`, the ordinary spatial
derivative follows. The concrete ODE data for this remainder is now exposed:
`spatialRemainder_initial_eq`, `spatialRemainder_continuousOn`,
`spatialRemainderDeriv`, and
`spatialRemainder_hasDerivWithinAt_Ici_of_mem_Ico` discharge the initial,
continuity, and right-derivative hypotheses. The forward-time wrappers
`flow_timeSlice_hasFDerivAt_of_spatialRemainderDeriv_bound_forward_Icc` and
`..._of_mem_ball` leave only the actual Taylor/Lipschitz bound on
`spatialRemainderDeriv`. This bound is now algebraically reduced to the
vector-field Taylor remainder itself:
`spatialRemainderDeriv_eq_fieldRemainder_add`,
`norm_spatialRemainderDeriv_le_of_fieldRemainder_bound`, and
`flow_timeSlice_hasFDerivAt_of_fieldRemainder_bound_forward_Icc_of_mem_ball`
show that a bound for
`f(τ, flow(x+h,τ)) - f(τ, flow(x,τ)) - Df(τ, flow(x,τ))(flow(x+h,τ)-flow(x,τ))`,
together with an operator-norm bound for `Df` along the base flow, gives the
ordinary time-slice derivative. The relative Taylor-remainder form is now also
available:
`flow_timeSlice_hasFDerivAt_of_relative_fieldRemainder_bound_forward_Icc_of_mem_ball`
turns a bound of the field remainder by `θ(h)` times the actual flow separation,
plus a Lipschitz bound of that separation by `L‖h‖` and `θ(h) → 0`, into the
same absolute forcing estimate. Product-Picard flows now expose the uniform
Lipschitz readout needed for this automatically:
`ofProduct_flow_exists_lipschitzOnWith_time_uniform`,
`ofProduct_eventually_flow_norm_sub_le_mul_forward_Icc_of_mem_ball`, and
`ofProduct_flow_timeSlice_hasFDerivAt_of_relative_fieldRemainder_bound_forward_Icc_of_mem_ball`
leave only the relative vector-field Taylor estimate and the base `Df` bound.
That Taylor input has now been reduced by the mean-value theorem to derivative
oscillation on the flow chord:
`norm_fieldRemainder_le_of_Df_sub_bound_on_segment`,
`eventually_fieldRemainder_bound_forward_Icc_of_Df_sub_bound_on_flow_segment`,
and
`ofProduct_flow_timeSlice_hasFDerivAt_of_Df_sub_bound_on_flow_segment_forward_Icc_of_mem_ball`
consume eventual bounds for `‖Df(τ,z)-Df(τ,flow(x,τ))‖` on each segment between
the base and perturbed flow points. A further state-tube form,
`eventually_Df_sub_bound_on_flow_segment_of_lipschitzOnWith` and
`ofProduct_flow_timeSlice_hasFDerivAt_of_Df_lipschitzOnWith_on_flow_segment_forward_Icc_of_mem_ball`,
derives this oscillation bound from a Lipschitz estimate for `Df` on any state
tube containing the flow chord. This has now been packaged in the more natural
convex-state form:
`eventually_flow_segment_subset_state_forward_Icc_of_convex_of_mem_ball`,
`eventually_hasFDerivWithinAt_on_flow_segment_of_state`, and
`ofProduct_flow_timeSlice_hasFDerivAt_of_Df_lipschitzOnWith_on_convex_state_forward_Icc_of_mem_ball`
derive chord membership, the base `Df` bound, and the within-segment derivative
from state preservation in a convex tube, a state-tube `Df` bound, a state-tube
`Df` Lipschitz estimate, and a state-tube derivative theorem for `f`. The
matching product wrappers
`ofProduct_flow_timeSlice_hasStrictFDerivAt_of_Df_lipschitzOnWith_on_convex_state_forward_Icc_of_mem_ball`,
`ofProduct_flow_timeSlice_map_nhds_eq_of_Df_lipschitzOnWith_on_convex_state_forward_Ioo_of_mem_ball`,
and
`exists_ofProduct_flow_timeSlice_openPartialHomeomorph_of_Df_lipschitzOnWith_on_convex_state_forward_Ioo_of_mem_ball`
feed this convex-state package directly into strict differentiability and the
local inverse-function readouts at interior forward times. For Picard product
flows selected with state preservation, the closed-ball specializations
`ofProductStatePreservingPicardLindelof_flow_timeSlice_hasStrictFDerivAt_of_closedBall_estimates_forward_Icc_of_mem_ball`
and
`exists_ofProductStatePreservingPicardLindelof_flow_timeSlice_openPartialHomeomorph_of_closedBall_estimates_forward_Ioo_of_mem_ball`
now discharge the convex-state membership hypothesis from the product Picard
state ball and leave only closed-ball estimates for `Df`, Lipschitz `Df`, and
the state-restricted derivative theorem for `f`. Matching `..._nnnorm_estimates...`
variants consume the usual `‖Df‖₊ ≤ BD` closed-ball estimate on `Icc` and derive
the real norm bounds and forward-interval restrictions internally; the
`..._of_le_radius` form matches the existing product Picard radius hypothesis
`r ≤ R`. The localized state-preserving Picard and component-continuity estimate
layers now also expose the strict time-slice derivative itself on restricted
forward intervals, including the operator-ball and identity-ball specializations,
so later common-interval neighborhood-map and local-inverse wrappers no longer
hide this differentiability bridge. The `r ≤ R` localized state-preserving
Picard route now also exposes the restricted forward-interior neighborhood-map
and open-partial-homeomorphism readouts directly, so callers using a shrunk time
interval do not have to unfold the ambient Picard solution to recover the local
inverse theorem. The same localized route now also unpacks that local inverse
package into a bijective open patch and into a positive source-ball
`MapsTo`/`InjOn` patch through
`ofProductStatePreservingPicardLindelof_restrict_flow_timeSlice_exists_open_nhds_bijOn_common_Ioo_of_closedBall_nnnorm_estimates_forward_Icc_of_le_radius`
and
`ofProductStatePreservingPicardLindelof_restrict_flow_timeSlice_exists_ball_mapsTo_injOn_common_Ioo_of_closedBall_nnnorm_estimates_forward_Icc_of_le_radius`.
The nonlocalized componentwise closed-ball route now also unpacks the forward
common-`Ioo` open partial homeomorphism into the same bijective open patch and
positive source-ball patch, matching the existing backward and localized forward
interfaces used by chart-gluing arguments:
`ofProductStatePreservingComponentClosedBallContinuityEstimates_flow_timeSlice_exists_open_nhds_bijOn_common_Ioo_of_hasFDerivWithinAt_forward_Icc_of_le_radius`
and
`ofProductStatePreservingComponentClosedBallContinuityEstimates_flow_timeSlice_exists_ball_mapsTo_injOn_common_Ioo_of_hasFDerivWithinAt_forward_Icc_of_le_radius`.
The forward operator-ball and identity-ball componentwise routes expose the
same concrete readouts directly.
The localized componentwise closed-ball continuity route now has the same
direct inverse-patch unpacking via
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_exists_open_nhds_bijOn_common_Ioo_of_hasFDerivWithinAt_forward_Icc_of_le_radius`
and
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_exists_ball_mapsTo_injOn_common_Ioo_of_hasFDerivWithinAt_forward_Icc_of_le_radius`,
including the operator-ball and identity-ball specializations, so chart-local
component estimates can feed the inverse patch without dropping back to the
generic Picard package.
The corresponding
`..._of_eventually_hasFDerivAt_Ioo` inverse-function wrappers consume that
`C¹` package directly. For product-Picard output, the new
`ofProduct_flow_timeSlice_hasStrictFDerivAt_of_hasFDerivAt_on_initialBall`
and its neighborhood/open-partial-homeomorphism variants obtain tangent-map
continuity from the existing product-flow Lipschitz dependence; the explicit
open-neighborhood `MapsTo`/`InjOn` readouts additionally provide a local
injective source patch and image neighborhood for each interior time-slice, and
the ball-source variants shrink that source patch to a positive metric ball
around the base point.  An ordinary spatial derivative proof on the initial-data
ball is therefore enough at every interior base point of that ball.
This is a model-level infinitesimal invertibility input.  The purely topological
chart-transport bridge is now present in `Diffeomorph3FlowExistence.lean`:
`exists_open_nhds_bijOn_subset_of_openPartialHomeomorph` first shrinks a model
open-partial-homeomorphism patch to prescribed open source and target
constraints while retaining an open `BijOn` patch for the prescribed time-slice
map.
`mapsTo_symm_image_of_openPartialHomeomorph_model_mapsTo`,
`injOn_symm_image_of_openPartialHomeomorph_model_injOn`, and
`bijOn_symm_image_of_openPartialHomeomorph_model_bijOn` transport model
`MapsTo`/`InjOn`/`BijOn` facts through source and target open partial
homeomorphism charts, while
`exists_open_nhds_mapsTo_injOn_of_openPartialHomeomorph_model_mapsTo_injOn`
and
`exists_open_nhds_bijOn_of_openPartialHomeomorph_model_bijOn` return open
manifold-side patches for an already-defined uncharted map.  The same section
also has the dual lifted-model route,
`mapsTo_symm_image_of_openPartialHomeomorph_lifted_model_mapsTo`,
`injOn_symm_image_of_openPartialHomeomorph_lifted_model_injOn`,
`bijOn_symm_image_of_openPartialHomeomorph_lifted_model_bijOn`, and the two
corresponding `exists_open_nhds_*_lifted_model_*` patch readouts, for maps
defined as `e₁.symm ∘ G ∘ e₀` from a chartwise Picard time-slice `G`.
`exists_open_nhds_bijOn_of_lifted_openPartialHomeomorph_model` composes the
domain-shrink and lifted-model steps: a model open partial homeomorphism for
`G`, source membership in the source chart target, and target membership in the
target chart target directly produce a manifold-side open `BijOn` patch.  The
same section now also transports continuity and overlap equalities:
`continuousOn_symm_image_of_openPartialHomeomorph_lifted_model` lifts
model-side continuity of `G` on a chart patch to continuity of
`e₁.symm ∘ G ∘ e₀` on the manifold-side source patch, and
`exists_open_nhds_continuousOn_bijOn_of_lifted_openPartialHomeomorph_model`
shrinks a model inverse patch inside prescribed source/target chart domains
and returns a single manifold-side patch carrying both continuity and `BijOn`.
`eqOn_of_openPartialHomeomorph_coord_eqOn` turns equality in a common target
chart into equality of the underlying manifold maps, while
`eqOn_lifted_models_same_target_of_model_eqOn`,
`eqOn_symm_image_of_openPartialHomeomorph_lifted_model_eqOn`, and
`eqOn_lifted_models_of_common_target_chart_eqOn` cover the chart-lifted model
forms expected from local-flow uniqueness on overlaps.  The model ODE layer now
also composes its full-interval and common-`Ioo` inverse-function theorems with
this chart lift:
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_bijOn_of_hasStrictFDerivAt_Ioo`,
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_bijOn_of_eventually_hasFDerivAt_Ioo`,
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_bijOn_common_Ioo_of_hasStrictFDerivAt`
and
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_bijOn_common_Ioo_of_eventually_hasFDerivAt`
turn the model time-slice local inverse theorem directly into a manifold-side
open `BijOn` patch for `z ↦ e₁.symm (α.flow (e₀ z, t))`.  The
continuous local-flow package now also exposes
`ContinuousLocalFlowSolution.flow_timeSlice_continuousOn_initial` and
`ContinuousLocalFlowSolution.flow_timeSlice_lifted_continuousOn`, extracting
fixed-time spatial continuity from the model space-time continuity field and
transporting it through charts.  The variational inverse-function layer now has
the matching one-step full-interval and common-`Ioo` forms
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_of_hasStrictFDerivAt_Ioo`,
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_of_eventually_hasFDerivAt_Ioo`,
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_common_Ioo_of_hasStrictFDerivAt`
and
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_common_Ioo_of_eventually_hasFDerivAt`,
which shrink the source inside the open initial-data ball and return one lifted
manifold patch carrying both `ContinuousOn` and `BijOn`.  The same lift now has
overlap-ready constrained forms:
`exists_open_nhds_continuousOn_bijOn_subset_of_lifted_openPartialHomeomorph_model`
records prescribed manifold-side source and target containments after the
model patch has been chosen inside suitable chart images, and
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_subset_of_hasStrictFDerivAt_Ioo`,
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_subset_of_eventually_hasFDerivAt_Ioo`,
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_subset_common_Ioo_of_hasStrictFDerivAt`
with its C¹-style
`..._of_eventually_hasFDerivAt` variant push those containments through the
variational time-slice inverse theorem.  The full-interval constrained lift also
has the matching local inverse-identity readouts
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_inverseOn_subset_of_hasStrictFDerivAt_Ioo`
and
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_inverseOn_subset_of_eventually_hasFDerivAt_Ioo`,
plus full-interval overlap-equality readouts
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_subset_eqOn_of_hasStrictFDerivAt_Ioo`
and
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_subset_eqOn_of_eventually_hasFDerivAt_Ioo`.
These are the local patch shapes
needed to shrink chartwise Picard slices into visible overlap domains before
applying equality transport.  The variational layer also has the corresponding
common-subinterval overlap-equality readouts,
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_continuousOn_bijOn_subset_eqOn_common_Ioo_of_hasStrictFDerivAt`
and its C¹-style `..._of_eventually_hasFDerivAt` variant: once the target patch
is constrained inside a common chart source and common-chart coordinates agree
on the visible source set, the returned local patch carries the resulting
manifold-side `EqOn` together with `ContinuousOn` and `BijOn`.  The
topological existence layer also has continuity-gluing bridges for the next
step after such compatible patches are chosen:
`eqOn_of_iUnion_eqOn` globalizes local equality across an indexed cover of the
visible domain,
`continuousOn_of_locally_eqOn_open_continuousOn` turns pointwise local equality
to continuous open readouts into continuity of the candidate map on the domain,
and `continuousOn_of_iUnion_open_eqOn_continuousOn` gives the corresponding
indexed open-cover form.  These let a finite or locally indexed chart cover
feed continuity of a glued time-slice without reopening the pointwise
neighborhood argument.  The same block now also includes pointwise temporal
continuity gluing:
`continuousWithinAt_eval_of_iUnion_eventuallyEqOn_continuousWithinAt` and
`continuousWithinAt_eval_of_iUnion_eqOn_continuousWithinAt` transfer
`ContinuousWithinAt (fun τ ↦ local τ x) s t` from a local readout covering the
base point to the glued map `F`, matching the continuity input of the
source-membership-free Picard endpoint.  The matching preferred-chart
derivative transfer is also available through
`hasDerivWithinAt_extChartAt_eval_of_eventuallyEq`,
`hasDerivWithinAt_extChartAt_eval_of_iUnion_eventuallyEqOn`, and
`hasDerivWithinAt_extChartAt_eval_of_iUnion_eqOn`, so local chart ODE
derivatives can be pushed to the glued forward slice after overlap equality has
identified the relevant readout.  The same topological gluing block now includes
`leftInvOn_of_iUnion_eqOn_leftInvOn` and
`rightInvOn_of_iUnion_eqOn_rightInvOn`, which turn local forward/backward
inverse identities plus equality of the global candidates with local readouts
on the relevant image sets into global left- and right-inverse identities over
covered domains.  For the later smooth slice upgrade, the manifold layer now
also has the corresponding `C^n` regularity-gluing forms
`contMDiffOn_of_locally_eqOn_open_contMDiffOn` and
`contMDiffOn_of_iUnion_open_eqOn_contMDiffOn`, so local chart readouts that are
identified with the glued self-map on an open cover can supply `ContMDiffOn`
regularity directly.  The time-slice wrapper
`contMDiffOn_univ_timeSlice_of_iUnion_open_eqOn_contMDiffOn` packages the
`Set.univ` form needed by the glued forward/backward maps in the raw Picard
endpoint.  The variational model-flow layer now also has full-interval `C^3`
local-gluing readouts
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_of_hasStrictFDerivAt_Ioo`,
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_of_hasStrictFDerivAt_Ioo_of_contDiffAt_spaceTime`,
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_eqOn_of_hasStrictFDerivAt_Ioo`,
and
`VariationalLocalFlowSolution.flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_eqOn_of_hasStrictFDerivAt_Ioo_of_contDiffAt_spaceTime`,
so an interior full-interval Picard slice can expose the same forward/backward
local inverse identities, `C^3` regularity, and overlap equality as the
common-subinterval handoff.  Product-Picard output now has matching
full-interval handoffs through
`ofProduct_flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_of_hasFDerivAt_on_initialBall_Ioo`
and
`ofProduct_flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_of_hasFDerivAt_on_initialBall_Ioo_of_contDiffAt_spaceTime`,
so product-flow callers no longer have to manually unfold the extracted
variational local flow to reach the `C^3` gluing patch.  The
state-preserving component closed-ball common-subinterval handoff now also has
backward space-time-regularity variants
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_common_Ioo_of_hasFDerivWithinAt_backward_Icc_of_le_radius_of_contDiffAt_spaceTime`
and
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_eqOn_common_Ioo_of_hasFDerivWithinAt_backward_Icc_of_le_radius_of_contDiffAt_spaceTime`,
so backward/inverse patches can consume full space-time `C^3` regularity
directly rather than a pre-sliced fixed-time proof.  The same backward
space-time handoff now has both operator-ball and identity-ball specializations,
including
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_of_operatorBall_flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_common_Ioo_of_hasFDerivWithinAt_backward_Icc_of_le_radius_of_contDiffAt_spaceTime`,
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_of_operatorBall_flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_eqOn_common_Ioo_of_hasFDerivWithinAt_backward_Icc_of_le_radius_of_contDiffAt_spaceTime`,
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_of_identityBall_flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_common_Ioo_of_hasFDerivWithinAt_backward_Icc_of_le_radius_of_contDiffAt_spaceTime`
and
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_of_identityBall_flow_timeSlice_exists_lifted_open_nhds_local_gluing_data_subset_eqOn_common_Ioo_of_hasFDerivWithinAt_backward_Icc_of_le_radius_of_contDiffAt_spaceTime`,
so product Picard data can use either the natural operator-radius tangent bound
or the identity-radius specialization to produce backward local gluing patches.
The common backward gluing patches now also have fixed-time `C^3` operator-ball
and identity-ball specializations, including the overlap-`EqOn` local-gluing
data, so callers that already have a time-slice `ContDiffAt` proof need not
route through full space-time regularity.
These ingredients now assemble into a local-cover raw-flow endpoint,
`Diffeomorph3GaugeFlowOn.of_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
with proof-level `nonempty_...`: global glued forward/backward slices plus
local open-cover readouts carrying inverse identities, slice regularity,
time-continuity, anchoredness, chart derivatives, and relative vector-field
identification produce the raw open-Picard gauge flow directly.  The fixed-IVP
intrinsic layer now exposes the same local-cover shape as
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_iUnion_gluedSlices_vectorField_eq_nhdsWithin`
and its proof-level `nonempty_...`, so per-solution cover data feeds the
intrinsic witness without manually deriving global inverse, smoothness,
continuity, and derivative hypotheses first.  The theorem-family layer mirrors
this as
`IntrinsicDeTurckGaugeFlowExistenceFamily.ofPicardIccChartDerivative_of_iUnion_gluedSlices_vectorField_eq_nhdsWithin`
with a matching proof-level `nonempty_...`, exposing the same gluing-ready
input uniformly across all IVPs.  The
raw layer now also has the time-dependent compatible-cover bridge
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
and proof-level `nonempty_...`: canonical glued forward/backward slices are
built from compatible local readouts on the time-slice cover, while a
closed-Picard source-persistence hypothesis supplies the relative-filter
equality with the base-time patch.  The global-field route also has the
pointwise-source variant
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`,
so continuity and chart-derivative gluing can use per-base-point persistence
instead of uniform inclusion of the whole selected patch.  The fixed-IVP
intrinsic package now exposes the same pointwise-source compatible-cover route
through
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_vectorField_eq_nhdsWithin`
and proof-level `nonempty_...`, so per-solution glued-cover data feeds the
intrinsic witness without separately unpacking raw-flow hypotheses.  The helper
`timeDependent_iUnion_pointwiseSource_of_open_preimage_continuousWithinAt`
derives the pointwise source-persistence input when the patches are open
preimages along pointwise time-continuous trajectories, and
`timeDependent_iUnion_pointwiseSource_of_indexed_open_preimage_continuousWithinAt`
does the same for patchwise local readouts.  The bridge
`gluedMapOf_iUnion_eventually_eq_of_pointwiseSource` now packages the
eventual equality between the canonical glued map and the selected local
readout.  The new
`continuousWithinAt_eval_of_timeDependent_iUnion_pointwiseSource_continuousWithinAt`
and
`hasDerivWithinAt_extChartAt_eval_of_timeDependent_iUnion_pointwiseSource`
lemmas expose the corresponding continuity and preferred-chart derivative
transfers, and the raw pointwise-source constructor now uses those generic
handoffs.  The global-field pointwise-source raw route now also has the
open-preimage source-persistence variant
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`,
so callers can derive source persistence from fixed open target patches when
the vector-field identification is already stated along the glued slice.  The
local-readout pointwise-source raw constructor
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
uses the same source-persistence route but states vector-field identification
on the actual time-slice patches `U τ i`, so this local-field route no longer
needs finite-cover promotion when the local equality is available at the
current time.  The raw local-readout route now also has the open-preimage
source-persistence variant
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`,
which derives the pointwise patch persistence from fixed open target patches
and local time-continuity before invoking the same glued-flow constructor.  The
fixed-IVP intrinsic layer now exposes the global-field open-preimage handoff
through
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_vectorField_eq_nhdsWithin`
with proof-level `nonempty_...`, and exposes the local-readout handoffs through
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_localReadouts_vectorField_eq_nhdsWithin`
and
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_of_localReadouts_vectorField_eq_nhdsWithin`.
The theorem-family raw existence layer now
also has the generic assembly bridge
`IntrinsicDeTurckGaugeFlowExistenceFamily.of_forInitialValueProblem`, with a
proof-level equivalence between family existence and fixed-IVP existence for
all initial-value problems, so fixed-IVP pointwise/local handoffs do not need
bespoke family mirrors before they can feed theorem-family routes.  The
geometric `C³` gauge-flow family layer now has the same fixed-IVP assembly and
proof-level equivalence, and the raw/geometric fixed-IVP and theorem-family
conversions have simp round trips and field readouts, so future compact ODE
output can enter either package boundary without manual repackaging.  Its finite-cover
local-readout companion
`Diffeomorph3GaugeFlowOn.of_finite_timeDependent_iUnion_compatibleGluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
uses `timeDependent_iUnion_hFEqWithinAll_of_finite` to turn per-index equality
into the uniform vector-field-identification handoff needed for all base
points.  The helper `timeDependent_iUnion_cover_eventually_of_finite_subset`
now gives the matching cover-level persistence statement: a finite base-time
cover remains a cover in the relative time filter once every selected patch is
eventually contained in its time-moved counterpart.  Its interval form
`timeDependent_iUnion_cover_exists_Ioo_of_finite_subset`, based on the generic
real-line extraction helper `exists_Ioo_inter_subset_of_mem_nhdsWithin`, turns
that relative-filter cover persistence into an explicit open time interval
around the base time.  The closed-interval companions
`exists_Icc_inter_subset_of_mem_nhdsWithin`,
`timeDependent_iUnion_cover_exists_Icc_of_finite_subset`, and
`timeDependent_iUnion₂_cover_exists_Icc_of_finite_subset` shrink that
neighborhood to an `Icc` interval and synchronize finite source and target
cover persistence, matching the interval-local raw gauge-flow constructors.
The ordinary-neighborhood form `exists_Icc_subset_of_mem_nhds` and the
time-set-subset cover package
`timeDependent_iUnion₂_cover_exists_Icc_subset_of_finite_subset` choose the
closed interval inside the ambient time set, removing the relative-time side
condition when feeding raw constructors whose Picard interval is already
contained in that ambient set.
The raw gauge-flow layer now has an interval-cover
fallback constructor
`Diffeomorph3GaugeFlowOn.of_Icc_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`:
it adds an identity `Option.none` patch outside the closed Picard interval and
empty fallback patches inside, so the existing all-time
`SmoothSelfDiffeomorph3Family.ofInverse` assembly can consume source and target
covers known only on `Icc tmin tmax`.  The matching
`..._localGluingData_pointwiseSource_...` and
`..._openPreimage_localGluingData_...` adapters preserve the named
local-inverse-function package and derive pointwise source persistence from
fixed open target-preimage patches.  The fixed-IVP intrinsic
layer now exposes the same finite-cover shape
as
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin`
with proof-level
`nonempty_ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin`,
so compact finite-cover local readouts can feed the intrinsic witness without
manually unpacking the raw glued flow for each local solution.  The
theorem-family layer now mirrors that finite time-dependent compatible-cover
shape as
`IntrinsicDeTurckGaugeFlowExistenceFamily.ofPicardIccChartDerivative_of_finite_timeDependent_iUnion_compatibleGluedSlices_of_localReadouts_vectorField_eq_nhdsWithin`
with matching proof-level `nonempty_...`, so a compact finite-cover
construction can be supplied uniformly over all initial-value problems.  The raw
finite-cover layer now also packages per-slice inverse-function output as
`LocalGluingData`, with
`Diffeomorph3GaugeFlowOn.of_finite_timeDependent_iUnion_localGluingData_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
projecting those named patches into the compatible glued-flow constructor.  The
non-finite raw open-preimage route has the matching
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_localGluingData_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
adapter, so source persistence from fixed open target patches can be combined
with named local inverse-function packages without manually projecting the
openness, maps-to, inverse, and `C³` fields.  The fixed-IVP intrinsic layer now
has the corresponding
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_timeDependent_iUnion_compatibleGluedSlices_openPreimage_localGluingData_of_localReadouts_vectorField_eq_nhdsWithin`
wrapper with proof-level `nonempty_...`, so per-solution local gluing packages
can cross the intrinsic boundary on the same open-preimage source-persistence
hypotheses.  The
package also recovers forward/backward `BijOn` facts from its maps-to and local
inverse fields, so older inverse-function outputs that need bijectivity can be
used without storing an additional independent field.  It also has a compactness
subcover lemma
`LocalGluingData.exists_finset_subtype_iUnion_of_iUnion`, which restricts any
source-and-target covering local-gluing family to a finite subtype while
preserving the packaged data; the companion
`LocalGluingData.exists_finset_subtype_iUnion_compatible_of_iUnion` carries
forward/backward overlap compatibility through the same finite restriction.  The
time-dependent companion
`LocalGluingData.exists_finset_subtype_timeDependent_iUnion_compatible_of_iUnion_at`
selects the finite subtype from one time-slice cover while preserving the
selected patches' `LocalGluingData` and overlap compatibility for every time,
so later compact patch selection does not lose its all-time local ODE data when
the finite indices are chosen at the base slice.  Its open-preimage companion
`LocalGluingData.exists_finset_subtype_timeDependent_iUnion_compatible_openPreimage_of_iUnion_at`
also includes a finite cover by the fixed open target-preimage patches `W` and
preserves the restricted `hUpreimage`/`hWopen` data, matching the source
persistence route used by the open-preimage local-gluing constructors.  The
strengthened
`LocalGluingData.exists_finset_subtype_timeDependent_iUnion_compatible_openPreimage_Icc_cover_of_iUnion_at`
combines that compact subcover selection with finite source/target persistence
to return one positive closed time interval on which the selected source and
target patches still cover, while preserving the same local gluing,
compatibility, and open-preimage data.  Its
`..._Icc_subset_timeSet_cover_...` companion also chooses the closed interval
inside the ambient time set, so later raw-constructor calls can use the covers
without carrying a separate `τ ∈ timeSet` premise.  The
fixed-IVP and theorem-family intrinsic layers now expose matching
`..._finite_timeDependent_iUnion_localGluingData_...` wrappers, so later compact
manifold arguments can pass named local inverse-function packages through every
finite-cover boundary without separately projecting openness, maps-to, inverse,
and `C³` fields.  The lifted chart helper now also has a selected-shrink
`exists_open_nhds_localGluingData_subset_of_lifted_openPartialHomeomorph_model`
form, keeping the cover-selection membership/subset facts while packaging the
per-slice inverse-function output directly.  The model-space Picard layer now
has corresponding
`exists_open_nhds_localGluingData_subset_of_contDiffAt_model` and
`flow_timeSlice_exists_lifted_open_nhds_localGluingData_...` adapters, so a
single chartwise ODE time-slice can be selected as a named local gluing package;
the corresponding `..._localGluingData_subset_eqOn_...` adapters retain the
shrunk source overlap equality against another chart readout for forward
compatibility.  The remaining lift must still supply the chart-domain
shrinking/source-membership hypotheses and combine these local patches with
manifold-level flow compatibility before producing `C³` diffeomorphism slices.
On the final bundling side, `SmoothSelfDiffeomorph3.ofInverse` now packages
mutually inverse `C³` self-maps into a bundled `SmoothSelfDiffeomorph3`, with
simp readouts for the forward and inverse maps.  Thus the eventual glued-flow
upgrade can target forward/backward inverse identities plus `ContMDiff I I 3`
regularity, rather than constructing the `Diffeomorph` record by hand.  The
family-level `SmoothSelfDiffeomorph3Family.ofInverse` performs the same
slice-wise packaging for time-dependent forward/backward maps, and
`SmoothSelfDiffeomorph3Family.ofInverse_anchoredAt` turns pointwise identity of
the forward map at the base time into the anchored-family condition.  The raw
existence layer now consumes this package directly through
`Diffeomorph3GaugeFlowOn.of_inverse_hasMFDerivWithinAt` and
`Diffeomorph3GaugeFlowOn.nonempty_of_inverse_hasMFDerivWithinAt`: mutually
inverse `C³` time-slice maps, anchoring, and the pointwise manifold derivative
equation produce a raw `Diffeomorph3GaugeFlowOn` without a separate manual
`SmoothSelfDiffeomorph3Family` construction.  The raw-flow endpoint now also
accepts the direct output of the gluing layer through
`Diffeomorph3GaugeFlowOn.of_inverseOn_univ_hasMFDerivWithinAt` and
`Diffeomorph3GaugeFlowOn.nonempty_of_inverseOn_univ_hasMFDerivWithinAt`: inverse
identities and `ContMDiffOn` regularity stated on `Set.univ` are converted to
the global inverse and `ContMDiff` hypotheses expected by the bundled
diffeomorphism-family constructor.  The same glued-slice endpoint is now
available for preferred-chart ODE data through
`Diffeomorph3GaugeFlowOn.of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self`
and its proof-level `nonempty_...` form, plus the eventual-chart-source variant
`..._of_eventually_mem_source`; these consume chart-coordinate derivatives of
the forward map `F` directly after the open-cover gluing layer has supplied
inverse identities and `C³` slice regularity on `Set.univ`.  A further
relative-filter readout-field variant,
`Diffeomorph3GaugeFlowOn.of_inverseOn_univ_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`,
combines the same glued-slice endpoint with locally equal finite-cover/Banach
vector-field identifications before producing the raw gauge flow.  For the
Picard shape where the chart ODE is proved on a closed interval and the raw
flow lives on its interior, the endpoint
`Diffeomorph3GaugeFlowOn.of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
now performs the same glued-slice handoff from `Icc` preferred-chart derivative
data to an `Ioo` raw gauge flow.  The fixed-IVP intrinsic existence layer now
consumes exactly that glued-slice shape through
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin`
and its proof-level
`nonempty_ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin`,
so a future finite-cover construction can pass the glued forward/backward
slices, inverse identities, `C³` regularity on `Set.univ`, closed-interval
chart derivatives, and relative intrinsic-field identification directly into
the fixed-IVP witness.
The centered chart-source membership needed by that raw endpoint can now also
be discharged from time-continuity of the glued trajectory:
`preimage_extChartAt_source_self_mem_nhdsWithin_of_continuousWithinAt` packages
the general source-neighborhood consequence, and
`Diffeomorph3GaugeFlowOn.of_inverseOn_univ_hasDerivWithinAt_Icc_extChartAt_eval_self_of_continuousWithinAt_vectorField_eq_nhdsWithin`
uses it to replace the manual source-membership input by
`ContinuousWithinAt (fun τ ↦ F τ x) (Icc tmin tmax) t`.  Fixed-IVP and
theorem-family intrinsic existence now expose the same continuity-based
handoff through their
`...of_inverseOn_univ_continuousWithinAt_vectorField_eq_nhdsWithin` constructors
and proof-level `nonempty_...` forms.
The theorem-family layer mirrors the same handoff through
`IntrinsicDeTurckGaugeFlowExistenceFamily.ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin`
and its proof-level
`nonempty_ofPicardIccChartDerivative_of_inverseOn_univ_vectorField_eq_nhdsWithin`,
so the eventual compact-manifold construction can provide the glued data
uniformly for every IVP without repackaging each fixed-IVP witness by hand.
Full variational-pair uniqueness
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
`continuousAt_extChartAt_eval`, `continuousAt_eval`,
`eventually_mem_trivializationAt_eval`, and
`eventually_mem_extChartAt_source_eval`, plus the matching within-time-set
preferred-chart continuity and source-membership readouts. The same
fixed-IVP/theorem-family layer now also mirrors raw preferred-chart range and
source eventuality, both at ordinary neighborhood-times and relative to the
solution time set.
The raw gauge-flow layer now also exposes ordinary fixed-chart derivatives,
continuity, and chart-source eventuality in any preferred chart whose source
contains the time-`t` image:
`hasDerivAt_extChartAt_eval_of_mem_source`,
`hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_source`,
`continuousAt_extChartAt_eval_of_mem_source`, and
`eventually_mem_extChartAt_source_eval_of_mem_source`. Consequently a raw
intrinsic DeTurck flow can be repackaged directly as
`Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn` or as the ordinary
`Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn` on any open-time
subdomain where the raw time set is a neighborhood, via
`Diffeomorph3GaugeFlowOn.toIntrinsicFixedChartDerivativeOn` and
`Diffeomorph3GaugeFlowOn.toIntrinsicFixedChartDerivativeAtOn`; the
`..._congr_vectorField_nhdsWithin` variants cover chart-model vector fields
identified with the intrinsic DeTurck field along the flow. The fixed-IVP raw
existence package mirrors these as `fixedChartDerivativeData` and
`fixedChartDerivativeAtData`, removing another manual unpacking step between
manifold raw flows and the finite-cover fixed-chart ODE records.
The open-Picard specialization now includes the same fixed-chart readouts:
`hasDerivAt_extChartAt_eval_of_mem_source_of_timeSet_eq_Ioo`,
`hasDerivAt_extChartAt_eval_congr_vectorField_of_mem_source_of_timeSet_eq_Ioo`,
`continuousAt_extChartAt_eval_of_mem_source_of_timeSet_eq_Ioo`, and
`eventually_mem_extChartAt_source_eval_of_mem_source_of_timeSet_eq_Ioo`.
Raw flows can also package ordinary fixed-chart intrinsic ODE data on any
`u ⊆ s` directly from `s = Ioo tmin tmax` via
`toIntrinsicFixedChartDerivativeAtOn_of_timeSet_eq_Ioo` and the
`..._congr_vectorField_nhdsWithin_of_timeSet_eq_Ioo` variant; fixed-IVP and
theorem-family existence witnesses mirror the bundled extractor as
`fixedChartDerivativeAtData_of_timeSet_eq_Ioo`.
The derivative package now has the underlying fixed-chart-preserving restriction
and `Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeAtOn.of_fixedChartDerivativeOn_Ioo`
upgrade, so finite-cover Picard data can remain in a chosen chart center before
being converted to centered-chart or primitive manifold derivative data.
The raw, fixed-IVP, and theorem-family preferred-chart derivative readouts now
also have centered-chart simplifications that rewrite the derivative value from
`tangentCoordChange I p p p (...)` to the actual gauge velocity. This removes a
recurrent normalization step from downstream scalar gauge-pullback calculations,
and raw `Diffeomorph3GaugeFlowOn` witnesses can now be transported across
time-dependent vector fields that agree on the active time set; the local
integral-curve and gauge-flow layers now also have near-time vector-field
congruence, and raw gauge-flow witnesses expose matching local-at-time
`SatisfiesGaugeFlowAt`, `HasMFDerivAt`, and centered preferred-chart derivative
readouts when vector fields agree along the flow near that time. Closed-Picard
raw flows now also expose the corresponding open-interior `Ioo` readouts, so
Picard interval output can replace the vector field locally before extracting
ordinary manifold or preferred-chart derivatives. The same vector-field
replacement is now available directly in the relative time-set filter `𝓝[s] t`,
with raw within-set manifold, preferred-chart, and centered preferred-chart
derivative readouts for closed-interval endpoint data. The fixed-IVP and
theorem-family raw intrinsic gauge-flow existence packages mirror these
relative-filter readouts, so endpoint callers do not have to unwrap their raw
flow witnesses. The raw
existence layer now also has preferred-chart ODE constructors:
`of_hasDerivWithinAt_extChartAt_eval_self` and
`of_hasDerivAtOn_extChartAt_eval_self` build `Diffeomorph3GaugeFlowOn`
witnesses from continuity of the manifold curves plus the centered chart
derivative, matching the local Picard/ODE output shape more directly than a
prepackaged manifold derivative.
The fixed-IVP intrinsic DeTurck gauge-flow existence layer mirrors those
centered preferred-chart ODE constructors, so a chosen local solution can now be
upgraded directly from Picard-style chart-continuity plus chart-derivative
output without first packaging a manifold `HasMFDerivWithinAt` proof. The same
raw, fixed-IVP, and theorem-family layers now also have source-neighborhood
variants of those centered chart-ODE constructors: eventual membership in the
current preferred chart source, together with the chart derivative, derives the
manifold-curve continuity input automatically. This is the closer fit for
chart-local Picard output, where the solution is constructed inside a chosen
coordinate neighborhood. Those source-neighborhood constructors now also have
unrestricted ordinary `HasDerivAt` forms, so global-in-time chart ODE output can
feed raw, fixed-IVP, and theorem-family gauge-flow existence without restating
the derivative relative to a time set.
The same
raw layer now also has proof-level `Nonempty` wrappers for the geometric,
within-derivative, ordinary-on-time-set derivative, unrestricted derivative,
centered/source-neighborhood chart ODE, restriction, and identity-flow
constructors, letting downstream existence arguments retain raw gauge-flow
existence without choosing a concrete flow until needed.
The fixed-IVP intrinsic DeTurck gauge-flow existence layer mirrors this
proof-level shape for its derivative-data, ordinary-at-time derivative,
centered/source-neighborhood preferred-chart ODE, zero-field identity,
chosen-background identity, subsingleton, and empty constructors.
The theorem-family intrinsic DeTurck gauge-flow existence layer now has the
same proof-level wrappers, including conversion back down to a fixed IVP and
the named derivative-family/ordinary-derivative-family constructors, and it now
also has theorem-family centered/source-neighborhood preferred-chart ODE
constructors and `Nonempty` readouts.
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
That extraction now also exposes joint space-time continuity and
eventual-membership readouts for the extracted `(flow, tangent)` pair, so the
continuous product Picard output is not discarded when entering the variational
API; the same readouts have ordinary open-cylinder versions on the initial-data
ball interior and open Picard interval. Product Lipschitz dependence now also
descends to Lipschitz, continuity, and distance estimates for the extracted
`(flow, tangent)` pair as a function of the base initial point at each Picard
time, together with direct tangent-map projection estimates.
The extracted base-flow projection and the extracted tangent maps applied to a
fixed model vector now have the same Lipschitz, continuity, and distance
readouts, and two fixed vector slots have paired readouts for scalar pullback
calculations depending on both `A(t)u` and `A(t)v`. The same layer now also
combines the base flow with those two vector slots, giving direct
Lipschitz/continuity/distance readouts for
`x ↦ (flow_x(t), A_x(t)u, A_x(t)v)`. The continuous product-flow extraction now
also preserves closed-cylinder and open-cylinder space-time continuity/eventual
membership for the same scalar-readout state and for the full derivative-domain
tuple `(t, flow(t), A(t)u, A(t)v)`. Product Lipschitz dependence now also gives
fixed-time Lipschitz/continuity/distance estimates for that full
derivative-domain tuple as the base initial point varies, and variational
overlap uniqueness now has direct `Ioo`/`Icc` readouts for both that combined
state and the full derivative-domain tuple. The tensor
time-derivative layer can also consume continuous product Picard flows directly
in the open-domain and explicit-domain scalar-readout routes, in the named
metric-coordinate field routes, and in the finite-cover/readout-field variants,
including closed-Picard within-filter and geometric pushed-vector-slot variants,
converting the product flow internally to the variational package.
The closed-Picard metric-coordinate field routes now also have direct
product-Picard-Lindelöf wrappers, including the open-product-domain
`HasFDerivWithinAt` endpoint, ordinary/open product-state handoffs, and the
common radius-specialized `r ≤ R` form, so chart-local product Picard
hypotheses no longer need a caller-side conversion to a continuous product flow
or separate variational package before proving the gauge-pulled metric time
derivative. The geometric pushed-vector-slot closed-Picard endpoints now also
have direct product-Picard-Lindelöf and `r ≤ R` wrappers, in both ordinary
metric-coordinate and open-product-domain forms, so final scalar identities
written in actual tangent vectors can start from the Picard package directly.
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
matching proof-level `Nonempty` wrappers for each estimate route. The
state-preserving product Picard and component-continuity routes now have the
same localized constructors and proof-level witnesses, including the
operator/identity-ball specializations, so shrinking the Picard interval no
longer loses the direct closed-state-ball readouts used by the inverse-function
criteria. Those localized state-preserving routes now also expose common-`Ioo`
time-slice neighborhood-map and open-partial-homeomorphism readouts directly,
so chart-local inverse arguments can stay on the shrunk Picard interval; the
same restricted closed-ball estimate route now exposes the corresponding
bijective open patch and positive source-ball `MapsTo`/`InjOn` patch without
unfolding the `OpenPartialHomeomorph`; the componentwise closed-ball continuity
route exposes the same two patch forms directly from the chart-local estimates,
including the operator/identity-ball specializations on common forward and
backward intervals. The same forward restricted componentwise estimates now
feed the lifted `C^3` local gluing patch: strict differentiability and
invertibility are discharged from the closed-ball Picard data, while the
fixed-time `C³` input can now be supplied either directly or by a full
space-time `C³` hypothesis on the selected model flow. Operator-ball and
identity-ball lifted forms expose the standard tangent-bound specializations,
now also with direct space-time `C³` variants.
The lifted local-gluing layer and the product/forward localized Picard handoffs
now expose direct space-time-regularity entry points for both the basic patch
and overlap-equality patch, reducing the fixed-time `C³` input by slicing a full
space-time `C³` model flow at the selected endpoint.
The ODE package
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
The reusable Banach evolution layer now also has shorter-terminal restriction
constructors for both unconstrained and state-preserving local solutions, plus
direct interval equation, continuity, state-membership, and uniqueness readouts
for state-preserving solutions, so localized Picard/chart arguments can shrink
solutions without rebuilding the ODE proof or restating uniqueness on the
ambient terminal interval.
The geometric local-solution layer now has the matching shorter-terminal
restriction constructors for ordinary local Ricci-flow solutions, intrinsic
local Ricci-flow solutions, intrinsic Ricci-DeTurck local solutions, and the
chosen-background DeTurck subtype, with simp readouts showing that the
underlying solution object is unchanged. This does not remove the current
reverse-encoding terminal-fit assumptions by itself, but it supplies the
candidate-prefix operation needed for a later localized reverse-encoding
argument.
The analytic realization layer now preserves those prefixes too:
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.restrictTerminal`
reuses the same smooth metric, velocity, and background on any shorter Banach
solution interval, and
`TimeDependentGeometricRicciDeTurckBanachChartOnIcc.CandidateEncoding.restrictTerminal`
turns an interval reverse encoding into an encoding of the corresponding
restricted geometric candidate. The same prefix operation is now available for
`SymmetricSubmoduleCandidateEncodingOnIcc`, so the genuine symmetric-carrier
reverse encoding can be shortened without changing the realized smooth metric,
velocity, or background.  The theorem
`chosenIntrinsicDeTurckLocalSolution_metric_eq_on_restricted_interval_of_symmetricSubmoduleCandidateEncodingOnIcc`
now packages the corresponding local uniqueness readout: two chosen-background
DeTurck candidates agree on `[t₀, S]` once both restricted candidates are encoded
in the symmetric carrier for the same `S ≤ T`.  The shrunk ambient closure-data
theorem
`RicciDeTurckChartClosureDataOnIcc.metric_eq_on_restricted_interval_of_shrunk_symmetricCarrier`
derives that readout directly from ambient encodings of the restricted
candidates, so local uniqueness no longer needs a hypothesis that the full
candidate intervals fit inside the selected shrink.  The wrapper
`RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier`
chooses the shorter terminal automatically and states the result on
`[t₀, min (min T₁ T₂) T']`.  The companion
`RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_interval_of_common_terminal_le_shrink_of_shrunk_symmetricCarrier`
removes the extra clipping when `min T₁ T₂ ≤ T'`.  The generic
`chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_Ico_of_restricted_interval`
bridge now converts prescribed shorter-terminal uniqueness into uniqueness on
the open common candidate overlap, and
`RicciDeTurckChartClosureDataOnIcc.metric_eq_on_common_Ico_of_common_terminal_le_shrink_of_shrunk_symmetricCarrier`
exposes that continuation step for shrunk ambient closure data when the same
selected shrink contains the common terminal.  `SmoothRealizationMetricCone.lean`
now exposes the same clipped uniqueness readout after selecting the standard
positive-radius metric-cone shrink, still without a full-candidate terminal-fit
hypothesis.
The DeTurck layer now also has the closed-common version of that generic
continuation bridge:
`chosenIntrinsicDeTurckLocalSolution_metric_eq_on_common_interval_of_restricted_interval`
derives equality on the whole common closed interval from prescribed
shorter-terminal metric readouts, and
`chosenIntrinsicDeTurckLocalSolution_connection_eq_on_common_interval_of_restricted_interval_metric`
upgrades the same metric input to closed-common canonical connection equality.
The constructor
`ChosenIntrinsicDeTurckLocalExistenceUniqueness.ofRestrictedMetricReadout`
then packages existence plus those restricted-terminal metric readouts as the
full chosen-background DeTurck theorem package; the family-level constructor
`ChosenIntrinsicDeTurckLocalExistenceUniquenessFamily.ofRestrictedMetricReadout`
does the same uniformly over all initial-value problems.
The corresponding connection-level wrappers
`RicciDeTurckChartClosureDataOnIcc.connection_eq_on_restricted_interval_of_shrunk_symmetricCarrier`,
`RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_Ico_of_common_terminal_le_shrink_of_shrunk_symmetricCarrier`,
`RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_clipped_shrink_of_shrunk_symmetricCarrier`,
`RicciDeTurckChartClosureDataOnIcc.connection_eq_on_common_interval_of_common_terminal_le_shrink_of_shrunk_symmetricCarrier`,
and
`RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_localConnectionReadout`
upgrade the same local metric readout to equality of the canonical
chosen-background connections on the visible overlap.  The bundled
`RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_localMetricConnectionReadout`
selects one metric-cone shrink and returns both the clipped metric equality and
the clipped connection equality on that same visible overlap, while
`RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_localRestrictedMetricConnectionReadout`
uses the same selected-shrink data to expose metric and connection uniqueness
on any prescribed shorter terminal contained in both candidate intervals and
the selected shrink.  The wrapper
`RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_localMetricConnectionReadout_with_fullCommon`
returns the same selected-shrink clipped readouts together with the conditional
full-common-interval metric and connection readouts.  The stronger
`RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_theoremPackages_localMetricConnectionReadout`
uses the same selected shrink for the terminal-fit theorem-package handoff and
for both no-terminal-fit local uniqueness readouts.  Its restricted-terminal
companion
`RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_theoremPackages_localRestrictedMetricConnectionReadout`
uses the same selected shrink for the terminal-fit theorem-package handoff and
for any prescribed shorter-terminal metric/connection readout needed by
continuation arguments, while
`RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_theoremPackages_localRestrictedMetricConnectionReadout_with_fullCommon`
adds the conditional full-common metric and connection readouts to that
restricted-terminal single-shrink package.  The companion
`RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_theoremPackages_localMetricConnectionReadout_with_fullCommon`
packages the clipped no-terminal-fit readouts with the same conditional
full-common conclusion.
The same module also records the
autonomous `C¹` local-integral-curve specialization and Gronwall-based
uniqueness bridges on the open and closed Picard time intervals for two packaged
local model flows whose curves stay in a uniformly Lipschitz state region; the
Banach ODE layer now also has an order-theoretic bridge from equality on every
prescribed shorter terminal to equality on the open common interval, plus the
state-set Lipschitz-on-`Icc` specialization needed when estimates are only known
on those restricted terminals. `AnalyticPDE/BanachEndpointClosure.lean` now
also closes any already-established open-common Banach equality to the common
closed interval using within-interval continuity of the Banach ODE curves, and
closes the restricted-terminal bridge the same way. It gives the corresponding
restricted-estimate Picard-Lindelof existence theorem with closed-common
uniqueness. The same leaf
module lifts this endpoint-closed restricted-estimate readout to the
finite-cover positive-definite locus and the symmetric Riemannian metric-locus
submodule, to the symmetric positive-definite defect-carrier routes, and to the
finite-cover symmetric time-dependent vector-field route, as well as the
continuous-Riemannian/geometric Ricci-DeTurck restricted Banach-chart bridge.
The concrete restricted coordinatewise-defect and geometric Ricci-DeTurck chart
records now expose `_closed` extractors with closed-common `Icc` uniqueness
directly. The continuous space-time package now forgets to
`LocalFlowSolution` and inherits the same uniqueness bridges directly.
The finite-cover metric-locus layer also has positive-definite and symmetric
Riemannian-metric-locus specializations of this restricted-estimate theorem, so
future parabolic estimates can be supplied terminal-by-terminal while still
returning terminal control and open-common uniqueness. That restricted route now
lifts through the symmetric positive-definite coordinatewise-defect layer,
continuous-Riemannian initial data, symmetric time-dependent vector fields, and
the geometric Ricci-DeTurck RHS package, with reusable restricted-terminal chart
structures for both coordinatewise-defect and geometric Ricci-DeTurck inputs.
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
theorems before any neighborhood-of-time strengthening is known. Raw,
fixed-IVP, and theorem-family gauge-flow witnesses now also expose fixed-chart
derivative, continuity, vector-field-congruence, and eventual source-membership
readouts for any preferred chart whose source contains the time-slice image,
which is the finite-cover shape needed for chartwise model-ODE and overlap
arguments.  The derivative layer now has the matching proof-bearing input
package: `Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn` and its
ordinary-time analogue accept closed-Picard ODE data in a chosen chart center
`chartCenter t x`, prove the chart-transition conversion to the centered
`Diffeomorph3IntrinsicGaugeFlowChartDerivativeOn` packages by composing with
the fixed-to-centered chart change and canceling `tangentCoordChange`, and then
feed the raw existence layer through
`Diffeomorph3GaugeFlowOn.of_intrinsicFixedChartDerivativeOn_Ioo`.
`IntrinsicDeTurckGaugeFlowExistence.ofPicardIccFixedChartDerivative` and
`IntrinsicDeTurckGaugeFlowExistenceFamily.ofPicardIccFixedChartDerivative`
expose the same finite-cover handoff for fixed-IVP and theorem-family theorem
packages. The fixed-chart bridge now also accepts auxiliary model-vector-field
ODE data once that field is identified with the intrinsic DeTurck gauge field
along the candidate flow: the derivative layer, raw open-Picard constructor,
fixed-IVP constructor, and theorem-family constructor all expose pointwise and
closed-interval relative-filter variants of this handoff. The derivative-family
endpoint layer now has the same closed-Picard fixed-chart adapters, so
finite-cover ODE data can also supply ordinary `ChosenIntrinsicDeTurck` gauge
derivative families without first restating centered preferred-chart data. For
explicit open Picard time sets, the fixed-IVP and theorem-family raw existence APIs now
combine the `Ioo` identification with those ordinary-time derivative,
continuity, and chart-source readouts directly, in both unsimplified
preferred-chart and centered chart forms; the same no-extra-neighborhood
open-Picard layer now includes neighborhood-equal vector-field rewrites and
tangent-trivialization membership. The raw autonomous interface now
also runs in both directions: `Diffeomorph3GaugeFlowOn.autonomousIntegralCurveOn`
extracts Mathlib integral-curve data from a constant-in-time raw gauge flow, and
`eqOn_eval_of_autonomous_Ioo_boundaryless` /
`eval_eq_of_autonomous_Ioo_boundaryless` apply Mathlib's boundaryless
autonomous integral-curve uniqueness theorem to show that two anchored raw
`C³` autonomous gauge flows for the same `C¹` vector field agree pointwise on
their common open Picard interval. The same bridge now extends this equality to
closed Picard intervals when the anchor is in the interior:
`eqOn_eval_of_autonomous_Icc_boundaryless` /
`eval_eq_of_autonomous_Icc_boundaryless` use raw-flow continuity and
`closure_Ioo` to identify the endpoint values as well. Both the open- and
closed-interval bridges now also expose `maps3`-level uniqueness readouts
(`eqOn_maps3_of_autonomous_*_boundaryless` and
`maps3_eq_of_autonomous_*_boundaryless`), so downstream pullback-family
arguments can rewrite bundled time-slice diffeomorphisms directly. The same
autonomous uniqueness is now available on common visible subintervals of two
possibly different ambient raw time sets via the
`..._of_subset` open- and closed-interval readouts, now including pointwise
`eval_eq` and `maps3_eq` forms, matching later chart-gluing overlap arguments
without first rebuilding restricted raw-flow witnesses. For the standard open
and closed Picard interval cases, the raw autonomous uniqueness layer now also
chooses the visible overlap automatically as
`Ioo (max tmin₁ tmin₂) (min tmax₁ tmax₂)` or
`Icc (max tmin₁ tmin₂) (min tmax₁ tmax₂)` through the new
`..._overlap` pointwise `eval` and bundled `maps3` readouts. The raw intrinsic
flow-existence packages now also expose constructor readouts for the induced
fixed-IVP and theorem-family geometric gauge-flow bundles, including the
underlying `maps3`, anchoring, gauge-flow equation, and anchored gauge object,
so downstream endpoint arguments can rewrite from raw ODE output to geometric
gauge data without unfolding the adapters. The theorem-family geometric and raw
existence bundles now also expose fixed-IVP restriction readouts, so family
theorems can specialize to one initial-value problem without leaving hidden
constructor redexes in later proofs.

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
first. The first proof-bearing parabolic Hölder primitives now live in
`AnalyticPDE/ParabolicHolder.lean`: the file defines the parabolic distance,
open/closed balls and product cylinders, proves the triangle inequality,
topological compatibility with the ordinary product metric including local
bases by parabolic balls and product cylinders, exact standard ball/cylinder
identifications, plus closed-to-open shrink inclusions and open-to-closed
closure containment for balls/cylinders, proper-space compactness for closed
balls/cylinders, finite open/closed parabolic ball and cylinder covers of
compact sets, finite center-dependent open ball/cylinder subcovers subordinate
to any ambient open set containing a compact set, with matching closed
balls/cylinders still contained in that open set, uniform positive closed
ball/cylinder radii inside such open neighborhoods, and packages
`C^{0,α}`-style bounded/Hölder control with slice,
explicit closed-ball/cylinder oscillation, continuity,
uniform-continuity, estimate monotonicity in the controlling constants, and
constant-preserving localization of open-domain Hölder and `C^{0,α}` estimates
to uniform closed parabolic patches around compact subsets, and
bounded local-to-global Hölder estimates from parabolic ball covers and
product-cylinder covers with doubled closed patches, plus compact uniform-local
corollaries, and finite-cover Holder patching with automatic local-constant
selection for both cover shapes, matching local-to-global `C^{0,α}` patching
theorems, and finite-cover `C^{0,α}` patching with automatic local-constant
selection, and variable-radius finite-cover Holder and `C^{0,α}` patching for
both ball and product-cylinder covers, including fixed-constant variants that
preserve the sup constant and compact point-dependent- and existential-radius
Holder-constant readouts, and finite-sum closure for
explicit Holder, bounded, and `C^{0,α}` controls, and finite-sum closure for
existential Holder and `C^{0,α}` controls, and finite sum-difference closure
for fixed-constant and existential `C^{0,α}` controls, and finite
sum-of-products closure for fixed-constant and existential
normed-ring-valued `C^{0,α}` controls, and finite-product and
finite-product-difference closure for existential normed-comm-ring-valued
`C^{0,α}` controls, and an explicit bounded finite-product `C^{0,α}` estimate,
and finite `Pi` packaging across bounded,
Holder, and `C^{0,α}` controls from componentwise estimates and
same-constant projection back to components, and product-valued pairing
closure, continuous-linear closure, standalone Holder-level curried-bilinear
closure from separate bounded and Holder controls, standalone Holder-level
operator-application closure from separate operator/vector bounded and Holder
controls, curried-bilinear-map closure, bounded and Holder-level
curried-bilinear difference primitives, operator-application closure, bounded
and Holder-level operator-application difference primitives, and
operator-application difference estimates with operator-norm constants, now in
both fixed-constant and existential forms, and
integer-scalar closure,
and additive/subtractive algebra estimates,
including bounded and Holder-level normed-ring product/product-difference
primitives, the standard bounded-product estimate for normed-ring-valued
`C^{0,α}` functions, two-factor and finite-sum product-difference `C^{0,α}`
estimates, bounded and Holder-level scalar-action primitives, and the
corresponding bounded scalar-action estimate on normed-space-valued functions,
plus reciprocal closure, bounded and Holder-level reciprocal-difference
primitives, and division closure for normed-field-valued functions bounded away
from zero.
This is still only the
norm/topology vocabulary, with the expected norm-estimate closure, not the
Schauder estimates or Ricci-DeTurck Banach chart; it also already includes the
basic Lipschitz-composition estimate needed to pass local nonlinear coordinate
maps through Hölder control, the corresponding bounded `C^{0,α}` composition
result under range or explicit closed-sup-ball bounds, global and closed-ball
Lipschitz composition variants that derive the composed sup bound from the
input sup bound, direct parabolic
Hölder/`C^{0,α}` lifts of time-independent spatial Hölder/Lipschitz functions
on the spatial projection, direct time-only lifts from ordinary time Hölder
exponent `α / 2` to parabolic exponent `α` and from time Lipschitz control to
parabolic exponent `2`, with direct unit-diameter lowering bridges, including
fixed-constant `ParabolicC0AlphaWith` and existential `ParabolicC0AlphaOn`
lifts from spatial Lipschitz data for every `0 ≤ α ≤ 1` and from time
Lipschitz data for every `0 ≤ α ≤ 2`,
together with closed-ball and closed-cylinder subset variants,
pointwise finite-product Lipschitz estimates and
finite-sum Lipschitz estimates for two-factor products on factorwise bounded
sets, and exponent-lowering
on unit parabolic-diameter domains, with closed-ball and closed-cylinder
specializations across the Holder and `C^{0,α}` interfaces supplying that
hypothesis after shrinking.
Closed parabolic balls now map to and from ordinary product closed balls under
the quadratic time-radius control, and product cylinders map into ordinary
product balls/closed balls under coordinate radius control, matching
compactness-style local arguments. A basepoint-to-sup estimate now turns
Hölder control on a closed parabolic ball into explicit bounded control from
one value, and the same estimate is available on closed product cylinders with
the corresponding time/space radius expression; both closed-domain shapes now
also package Holder plus one basepoint bound as full `C^{0,α}` control, and
positive-exponent Holder control on any compact domain now packages as
`C^{0,α}` by compact-continuous boundedness, with direct proper-space
closed-ball/cylinder corollaries. The new
`AnalyticPDE/Parabolic/MatrixC0Alpha.lean` module proves determinant closure,
adjugate-entry closure, and inverse-entry closure under a determinant lower
bound for finite matrix-valued parabolic `C^{0,α}` functions from entrywise
control, now also with quantitative entrywise vector/matrix packaging and
spatial-only and time-only finite vector/matrix coefficient bridges from
ordinary Holder/Lipschitz estimates, including explicit unit-parabolic-diameter
spatial Lipschitz lifts for every `0 ≤ α ≤ 1` and time-Lipschitz lifts for
every `0 ≤ α ≤ 2`, now with matching fixed-constant and existential
closed-ball and closed-cylinder variants for those Lipschitz coefficient
bridges, plus explicit bounded determinant,
adjugate-entry, and inverse-entry estimates plus a whole inverse-matrix
estimate, including a
pointwise determinant Lipschitz estimate in the elementwise matrix norm,
named adjugate-entry, inverse-entry, summed whole inverse-matrix,
function-level determinant/inverse/matrix-product bounded-difference,
inverse-difference `C^{0,α}` control, inverse-principal entry Lipschitz,
bounded Holder entry/matrix estimates, inverse-principal contraction
`C^{0,α}` difference control, and inverse-principal contraction
bounded-difference control with a compact-domain determinant-lower-bound
variant, inverse-Christoffel
derivative/metric-side and array-level Lipschitz constants,
inverse-Christoffel `C^{0,α}` difference control, inverse-Christoffel
function-level bounded-difference control with a compact-domain
determinant-lower-bound variant, inverse-Christoffel bounded Holder
entry/array estimates, and
quadratic-Christoffel matrix-norm Lipschitz and bounded Holder entry/matrix
estimates, supplied-Christoffel schematic bounded Holder entry/matrix estimates,
primitive-input schematic bounded Holder entry/matrix estimates,
primitive-input schematic RHS `C^{0,α}` difference control, supplied-Christoffel
and primitive-input schematic RHS entrywise-difference `C^{0,α}` refinements, plus
supplied-Christoffel and primitive-input schematic RHS entry and whole-matrix
Lipschitz constants and a named function-level bounded-difference package for
the primitive schematic matrix RHS, with a compact-domain variant selecting a
common determinant lower bound, on entrywise
bounded finite matrices, using a determinant lower bound for inverse
estimates, and a compactness bridge from
nonvanishing determinants to uniform determinant lower bounds, including
finite-index common determinant lower bounds for compact matrix families,
finite-family compact inverse, inverse-action, inverse-bilinear,
inverse-principal, and inverse-Christoffel estimates using that shared
determinant constant, matching existential finite-family inverse,
inverse-action, inverse-bilinear, inverse-principal, and inverse-Christoffel
closures, finite-family compact inverse-difference and entrywise
inverse-difference estimates with one lower bound shared by both matrix
families plus the matching existential entrywise inverse-difference closure, and
compact-domain inverse-entry, inverse-action, inverse-bilinear, and schematic
matrix-valued RHS variants,
including finite-family primitive schematic RHS estimates using the same shared
determinant constant and matching existential finite-family schematic RHS
closures, plus finite-family primitive schematic RHS difference closures,
quantitative difference estimates, and function-level bounded-difference
estimates with one lower bound shared by both
metric families, quantitative compact inverse-action and inverse-bilinear
estimates, existential determinant and reciprocal-determinant difference
readouts from entrywise difference controls with a compact nonvanishing-det
adapter for reciprocal determinant differences, existential inverse-entry,
whole inverse-matrix, inverse-principal contraction, inverse-Christoffel array,
quadratic Christoffel-Ricci, and primitive schematic RHS difference readouts from
entrywise difference controls, plus entrywise and whole-valued closure
for finite matrix transpose, pointwise symmetrization, matrix products,
explicit bounded transpose/symmetrization estimates and corresponding
difference estimates, finite matrix trace, explicit bounded trace and
trace-difference estimates, existential entrywise-difference readouts for
vector/matrix packaging, transpose, symmetrization, and trace,
explicit bounded entrywise/whole-matrix product estimates,
explicit entrywise/whole-matrix product-difference estimates,
matrix-vector and vector-matrix products, explicit bounded matrix-vector/vector-matrix estimates,
matrix-vector/vector-matrix product-difference
estimates, and inverse-matrix vector products on
both sides under the same determinant lower bound, including explicit bounded
estimates for both inverse-vector product orders and explicit bounded
inverse-bilinear contraction estimates, plus whole finite
vector/matrix and inverse-matrix packages, finite vector dot products,
explicit bounded dot-product estimates, dot-product difference estimates,
explicit bounded finite bilinear-contraction estimates,
finite bilinear-contraction difference estimates, and bilinear contractions
through matrices or inverse matrices, including explicit
bounded Holder entry and whole-array estimates for Christoffel-symbol type
inverse-metric contractions and their entrywise/whole-array closure, whole
matrix-valued principal-part contractions with explicit bounded Holder
entry/matrix estimates for `g^{ab} H_abij`, whole matrix-valued
Ricci-coordinate quadratic Christoffel contractions with explicit bounded
Holder entry/matrix estimates and product-difference bounded Holder estimates,
and supplied-Christoffel schematic local
Ricci-DeTurck RHS entry/matrix bounded Holder estimates, primitive-input
schematic RHS entry/matrix bounded Holder estimates, and whole matrix-valued
closure, plus finite product-cylinder local primitive-estimate and
primitive-difference bridges, and compact point-local product-cylinder variants
for the same schematic RHS and RHS difference closures, including direct
existential-radius APIs before extracting determinant lower bounds, plus
product-cylinder metric-control bridges for the function-level
bounded-difference estimate, including finite-cover, compact point-local,
direct existential-radius, and finite-family variants with one shared lower
bound, and quantitative finite-cover, compact point-local, and
existential-radius `sub_with` bridges whose Holder constants are the
finite-cover patching constants, using finite-product,
integer-scalar, reciprocal, and division closure. On the
geometric side, the Levi-Civita local-frame Gram
matrix layer now also turns pointwise Gram determinant nonvanishing into a
positive determinant lower bound on compact subsets of a trivialization base.
The parabolic companion `AnalyticPDE/Parabolic/LocalFrameGram.lean` bridges
those compact time-space Gram determinant facts to parabolic inverse
Gram-matrix control, inverse-Gram vector/vector-inverse products,
inverse-Gram bilinear contractions, and inverse-Gram Christoffel/schematic
Ricci-DeTurck closure, including spatial-Hölder entry-control variants,
unit-parabolic-diameter spatial-Lipschitz entry-control variants for inverse
Gram, inverse-Gram vector/vector-inverse products, inverse-Gram bilinear
contractions, inverse-principal contractions `g^{ab}H_abij`, inverse-Gram
Christoffel contractions, and schematic RHS bridges at every `0 ≤ α ≤ 1`,
fixed-constant and existential closed-ball and closed-cylinder spatial-Lipschitz
inverse-Gram, inverse-Gram action/bilinear, inverse-principal,
inverse-Gram Christoffel, and schematic RHS variants, and
compact quantitative inverse Gram, inverse-Gram action/bilinear,
inverse-principal contraction, inverse-Gram Christoffel, and schematic RHS
bridges exposing the determinant lower-bound constant, plus geometric
finite-family local-frame Gram determinant lower-bound, inverse-estimate, and
schematic RHS handoffs with spatial-Hölder, unit-diameter spatial-Lipschitz,
closed-ball spatial-Lipschitz, and closed-cylinder spatial-Lipschitz
Gram-entry input forms, existential finite-family inverse-Gram, inverse-Gram
action/bilinear, inverse-principal, inverse-Gram Christoffel, and schematic RHS
handoffs from entrywise `ParabolicC0AlphaOn` controls sharing the same compact
determinant lower bound, with the inverse-Gram, inverse-Gram vector/vector-inverse product,
inverse-Gram bilinear, inverse-principal, inverse-Gram Christoffel, and
schematic RHS handoffs now also
accepting those same Gram-entry input forms, quantitative finite-family inverse-Gram
vector/vector-inverse product, bilinear, inverse-principal, and
inverse-Christoffel handoffs sharing that same compact determinant lower bound,
with the quantitative vector/vector-inverse product, bilinear,
inverse-principal, and inverse-Christoffel handoffs now also accepting those
same Gram-entry input forms,
direct single-frame and finite-family compact point-local product-cylinder
primitive-estimate and primitive-difference schematic RHS bridges with both
explicit-radius and existential-radius entry points, single-frame and finite-family
finite-cover product-cylinder schematic RHS bridges, plus finite-cover, compact
point-local, and existential-radius bounded-difference metric-control bridges
now consume the matrix APIs before selecting the local-frame determinant lower
bound, and finite-cover, compact point-local, and existential-radius
quantitative `sub_with` bridges now carry the patched Holder constants through
single-frame and finite-family local-frame Gram inputs,
quantitative finite-family inverse-Gram handoffs now also keep the shared
compact determinant lower bound and explicit inverse-entry constants under
spatial-Hölder, unit-diameter spatial-Lipschitz, and closed ball/cylinder
spatial-Lipschitz Gram-entry hypotheses,
finite-family inverse-Gram difference bridges against comparison matrix families
now expose the same spatial-Hölder, unit-diameter spatial-Lipschitz, and closed
ball/cylinder spatial-Lipschitz Gram-entry input forms while keeping one
determinant lower bound shared by both sides,
finite-family schematic RHS
quantitative difference, quantitative entrywise-difference, existential
difference, and bounded-difference control against
comparison primitive inputs with one lower bound shared by the Gram and
comparison metric families, including spatial-Hölder, unit-diameter
spatial-Lipschitz, and closed ball/cylinder spatial-Lipschitz Gram-entry forms
for the quantitative difference and quantitative entrywise-difference bridges,
the existential entrywise `C^{0,α}` difference bridge, and the
bounded-difference bridge,
and compact
local-frame
inverse Gram, inverse-principal contraction, and inverse-Gram Christoffel
arrays, and schematic RHS outputs, including existential difference readouts for
all four from entrywise controls, and schematic RHS `C^{0,α}` difference control, including
entrywise-difference inverse Gram, inverse-principal, inverse-Gram Christoffel,
and schematic RHS bridges, and inverse Gram, inverse-principal contraction,
inverse-Gram
Christoffel, and schematic RHS bounded-difference bridges against comparison
primitive inputs, all with matching spatial-Hölder Gram-entry input forms where
applicable; the inverse-Gram, inverse-principal, inverse-Gram Christoffel, and
schematic RHS bounded-difference, comparison, and entrywise-difference bridges
now also have unit-diameter, closed-ball, and
closed-cylinder spatial-Lipschitz Gram-entry variants for `0 < α ≤ 1`, and the
single-frame existential schematic RHS entrywise-difference bridge now has
direct spatial-Hölder, unit-diameter, closed-ball, and closed-cylinder
Gram-entry variants instead of requiring callers to package a singleton
finite family, and the single-frame compact entrywise-difference bridge now
also produces a `ParabolicC0AlphaNormLe` norm-ball bound for the schematic RHS
difference after extracting one shared compact determinant lower bound.
The abstract
closure-data interface itself now has named readouts for
both the global and closed-interval packages:
`nonempty_realization`, `realizationCandidateEncoding`, and
`nonempty_candidateEncoding`. These wrappers expose the already-stored smooth
realization and reverse encoding fields without reproving or destructing the
closure data, but they do not supply the missing Schauder/parabolic estimates.
The global raw-gauge route now also exposes the ambient state-preserving Banach
solution with common-interval uniqueness and symmetric positive-definite
persistence, the represented continuous Riemannian-metric-valued curve, and a
paired smooth-realization/reverse-encoding fiber as a single selected witness.
The selected metric curve is unique on common Banach existence intervals.
The interval raw-gauge route similarly exposes the ambient state-preserving
Banach solution with terminal-time control and common-interval uniqueness, now
including the stronger symmetric positive-definite persistence readout and the
represented continuous Riemannian-metric-valued curve, plus a combined
proof-level fiber carrying that solution's smooth realization and reverse
encoding of the realized chosen-background candidate, all available as a single
selected witness; the represented metric curve is likewise unique on common
Banach intervals.
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
closed-interval `RicciDeTurckChartClosureData`. The global, closed-interval, and
genuine symmetric-carrier closure records now also project directly to
chosen-background DeTurck theorem families, and the ambient global/closed-interval
records expose single-IVP proof-level chosen-background package witnesses before
forgetting to intrinsic or ordinary compact theorem packages. Ambient interval closure data
now also has proof-level constructors for genuine symmetric-carrier closure,
both from an explicit restricted-carrier Picard proof and after shrinking into a
closed ball contained in the Riemannian metric cone. The metric-cone handoff is
now also bundled in `SmoothRealizationMetricCone`: a positive-radius ambient
interval closure package selects the standard shrink and, under the same
terminal-fit compatibility for reverse encodings, returns the genuine symmetric
closure datum together with chosen-background, intrinsic, and ordinary theorem
package witnesses. The companion
`RicciDeTurckChartClosureDataOnIcc.exists_metricCone_shrunk_theoremPackages_and_conditional_symmetricCarrier`
keeps the theorem-package witnesses unconditional from the ambient closure data;
the terminal-fit hypothesis is isolated only to constructing the shrunk genuine
symmetric-carrier closure datum. The local-solution prefix constructors now make
it possible to state future terminal-fit replacements against restricted
candidates rather than against the full arbitrary candidate interval, and the analytic
smooth-realization / interval-encoding prefixes now preserve the same
underlying metric data on the shorter interval, including after descending to
the genuine symmetric carrier, and local uniqueness can now be read on a chosen
common restricted terminal from shrunk ambient closure data. These local readouts
now include both metric equality and canonical chosen-background connection
equality, and the clipped readouts now have full-common-interval companions when
the chosen shrink covers the two candidate terminals. A single metric-cone
shrink can return both clipped readouts at once; the same selected shrink can
now also carry the terminal-fit theorem-package handoff alongside those local
readouts, the terminal-fit theorem-package handoff with arbitrary
shorter-terminal metric/connection readouts, and a further readout carries the
same theorem-package handoff, clipped readouts, and conditional full-common
metric/connection readouts together. The continuation from these local readouts
to full arbitrary-overlap uniqueness is still open, but the base Banach ODE
layer now supplies the missing order-theoretic bridge from restricted terminals
to the open common interval for both bare and state-preserving solutions, and
the Picard layer has the matching restricted-estimate existence/uniqueness
theorem with open-common uniqueness. The same restricted-estimate route is now
available directly for the finite-cover positive-definite locus and symmetric
Riemannian metric-locus submodule, and it now lifts through the finite-cover
symmetric positive-definite defect carriers and the geometric Ricci-DeTurck
Banach-chart constructors.
The density-based
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
and reverse candidate encoding. It now also has a paired proof-level witness that
chooses a state-preserving Banach solution together with its smooth intrinsic
DeTurck realization, so downstream callers do not have to coordinate two
separate `Nonempty` choices, and a stronger paired witness adds the reverse
symmetric-carrier encoding of the chosen-background candidate represented by
that realization. A single-choice strengthened witness now also carries the
Banach terminal-time bound and common-interval uniqueness proof together with
the same smooth realization and reverse encoding. The
density-based interval-carrier solution now transports back to the chart's
built-in restricted carrier whenever its terminal time stays within the Picard
interval, giving a solution-level bridge rather than only pointwise vector-field
equalities. The preferred-cover local-bounds and continuous-Riemannian-bundle
routes now also perform that transport internally, returning chart-carrier
`BanachEvolutionLocalSolutionIn` witnesses directly from the smooth-density
Picard shrink; together with the initial-metric specialization, these routes
all expose both proof-level existence readouts and stronger selected witnesses
retaining terminal-time control and common-interval uniqueness. The selected
chart-carrier witnesses now also expose the Picard time-radius proof used to
form the shrink, and the initial-metric route has a single-shrink readout that
pairs the chart-carrier Banach solution/uniqueness witness with ambient
closure-data metric and connection uniqueness on the same clipped interval,
plus a prescribed-shorter-terminal companion and a companion that adds
conditional full-common metric and connection readouts whenever that same
selected shrink contains the common candidate terminal. The prescribed-terminal
companion now also has a terminal-fit theorem-package handoff on that same
selected shrink, so continuation arguments can keep the Banach solution,
ambient metric/connection uniqueness, and conditional point-4 theorem packages
coordinated by one `T'`/`a'` choice. The same selected-shrink package now also
combines that terminal-fit theorem-package handoff with the prescribed
shorter-terminal readouts and the conditional full-common metric/connection
readouts, both at the raw metric-cone handoff and at the preferred-cover
initial-metric smooth-approximation route. The smooth-realization layer now
also records the order-theoretic open-overlap continuation bridge from
prescribed shorter-terminal readouts, with metric and connection closure-data
readouts on `Ico t₀ (min T₁ T₂)` under the existing selected-shrink containment
hypothesis. The DeTurck/smooth-realization stack now also closes any
chosen-background open-common metric readout to the closed common interval by
continuity from the stored time derivatives, turns prescribed shorter-terminal
metric readouts into closed-common metric equality and full chosen-background
theorem packages, and promotes those metric readouts to canonical connection
equality. At the vector-bundle
smooth-approximation layer, the local coordinate-map boundedness hypothesis is
now discharged for continuous Riemannian vector bundles:
`RiemannianSectionSmoothApprox` derives
`eventually_norm_trivializationAt_lt` from mathlib's Riemannian bundle estimate
and uses it to produce preferred-bilinear smooth approximants, including the
finite-cover Banach-norm approximation theorem. It now also upgrades symmetric
continuous bilinear-form sections to symmetric smooth finite-cover approximants
by fiberwise symmetrization without increasing distance, and the Ricci-DeTurck
preferred-cover local-bounds closure theorem now routes through that symmetric
finite-cover approximation seam before applying positive-definite openness. The
same module now also packages the generic closure theorem that every continuous
SPD bilinear-form section in a continuous Riemannian vector bundle lies in the
closure of smooth SPD sections for the preferred finite-cover norm, with the
core quantitative theorem now returning a smooth SPD approximant to any
continuous SPD bilinear-form section inside any prescribed positive
preferred-cover radius. The same layer has the direct specialization that any
bundled continuous Riemannian metric itself lies in that smooth-SPD closure when
viewed through the preferred finite-cover bilinear-form chart, plus the
corresponding metric-level quantitative readout. That readout now reifies the
approximant as an actual bundled `C²` Riemannian metric, not just as an SPD
section, and the same result is packaged as closure of the image of bundled
`C²` Riemannian metrics in the preferred finite-cover section norm.
`ContinuousSection` now also has generic finite-cover Lipschitz handoffs,
`ContinuousSectionSpace.lipschitzOnWith_of_forall_coord_dist_le` and its
time-family variant, which turn compact coordinate-readout estimates into
`LipschitzOnWith` hypotheses on section-space vector fields. The same layer now
also unpacks finite coordinate-family `LipschitzOnWith` readouts to the
pointwise compact-coordinate distance estimates required by local chart
constructors, again with a time-family variant. `RiemannianSection`
specializes this for preferred bilinear-form charts:
`preferredBilinear_lipschitzOnWith_of_forall_fiber_dist_le` and its time-family
form combine a fibrewise Lipschitz estimate with the squared preferred
inverse-trivialization bound. The corresponding `_of_eq_trivializationAt`
variants accept the existing chart-record shape with an arbitrary cover `et`
and proof `et i = trivializationAt ...`. The compactness lemma
`exists_uniform_norm_preferred_trivializationAt_symmL_le_of_finite_compact_cover`
now provides the shared finite-cover inverse-trivialization bound consumed by
both smooth-density and Lipschitz handoffs, and
`exists_preferredBilinear_lipschitzOnWith_family_of_forall_fiber_dist_le`
uses it to produce an existential `LipschitzOnWith` constant for time-family
preferred-cover fields from a fibrewise estimate alone.
`timeDependentGeometricRicciDeTurckBanachChartOnIccOfForallFiberDistLe`
then packages an interval-scoped geometric Ricci-DeTurck Banach chart while
choosing `Kstate` from Picard data, geometric identification, and that fibrewise
estimate. The reverse preferred-cover bridge now also converts compact
bilinear-coordinate RHS bounds into the required fibrewise estimate, and
`timeDependentGeometricRicciDeTurckBanachChartOnIccOfForallCoordDistLe`
packages the corresponding interval chart constructor directly from coordinate
readout bounds. These are still handoff theorems; they do not
prove the Ricci-DeTurck Schauder estimates or construct the missing Banach chart.
It also derives that finite-cover inverse
bound from compactness of the cover pieces
inside their fixed trivialization domains by factoring fixed-center inverses
through centered inverse trivializations and continuous coordinate changes.
`MatrixC0Alpha` now also names the linear-radius form of the schematic
Ricci-DeTurck matrix estimate: when the primitive metric, first-derivative, and
principal-coefficient inputs differ by fixed constants times one shared radius,
the schematic RHS differs by `ricciDeTurckSchematicDiffBoundConst * radius`.
The same linear-radius estimate now has a finite-family form sharing one compact
determinant lower bound across all matrix families. `LocalFrameGram` lifts both
the single-frame and finite-family estimates to compact local-frame Gram
coordinates. The raw matrix and local-frame layers now also expose the same
linear-radius handoff after finite product-cylinder covers, point-dependent
local cylinders, and existential point-local cylinder data. `MatrixC0Alpha`
also converts primitive state-space Lipschitz hypotheses and a uniform
determinant lower bound into pointwise `LipschitzOnWith` estimates for the
schematic RHS coordinate map, including finite-family form. It also proves
monotonicity of the inverse-Christoffel array and schematic RHS constants in
their primitive radii, so finite-cover arguments can replace local constants by
coarser shared bounds without reopening the formulas. The function-level
bounded-difference and shared-radius schematic RHS estimates now carry this
coarsening step directly, and the state-space `LipschitzOnWith` coordinate
bridges have matching single-family and finite-family coarser-constant forms.
The compact-domain determinant-extraction variants now expose the same coarser
bounded-difference and shared-radius RHS estimates, and the compact local-frame
Gram-coordinate bridges lift those coarser constants through the geometric Gram
readout. The raw finite product-cylinder cover bridge now also exposes the
coarser shared-radius schematic RHS estimate directly, with a matching
local-frame Gram-coordinate finite-cover form; the raw point-dependent and
existential local-cylinder variants now have the same coarser shared-radius
handoff, and the local-frame Gram-coordinate layer has matching point-dependent
and existential local-cylinder forms. The finite-family compact-domain,
finite product-cylinder cover, point-dependent local-cylinder, and existential
local-cylinder bounded-difference and shared-radius estimates now also have
coarser-primitive-constant forms in both the raw matrix and local-frame
Gram-coordinate layers, so a finite cover can keep sharper memberwise primitive
estimates while exporting one larger Picard/Lipschitz chart constant per member.
The finite-family quantitative `C^{0,α}` schematic RHS difference estimates
now also have the same coarser primitive-difference promotion for compact
sets, finite product-cylinder covers, point-dependent local cylinders, and
existential local cylinders while preserving their Holder constants, with
matching local-frame Gram-coordinate bridges. The interval
Banach-chart constructor now also has a real-constant coordinate-Lipschitz
entry point, so those matrix constants no longer need to be prepackaged as
`ℝ≥0` by callers. This is a
coordinate Lipschitz bridge toward the fibrewise RHS hypothesis above, not a
Schauder estimate or the actual Banach-chart construction.
The first function-space module for this item is now
`AnalyticPDE/Parabolic/FunctionSpace.lean`: it packages
single-radius `ParabolicC0AlphaNormLe` balls from bounded plus Holder
constants and proves the expected algebra, restriction, continuity, and uniform
continuity rules, including finite sums, finite Pi-valued packaging,
continuous-linear images, products, and Lipschitz nonlinear composition. It
also packages `ParabolicC0AlphaOn` as a real submodule of all time-space
functions, proves restriction to smaller domains as a linear map, and gives
positive-exponent linear readouts into `ContinuousMap`s on compact time-space
pieces and compact piece families, with determination on the covered set and
injectivity for global compact-piece covers. This is the finite-cover
`C^{0,α}` analogue of the existing continuous-section compact-readout layer;
compact readout sup-norm differences, including the finite product readout
norm, are now bounded by the same single-radius `C^{0,α}` difference control,
and by sup-bound-only difference estimates; pairwise norm-ball and sup-bound
difference estimates now promote directly to `LipschitzOnWith` estimates for
single compact-piece, finite compact-family, and linear finite-cover readouts,
with finite compact-family `LipschitzOnWith` estimates unpacking to pointwise
compact-coordinate distance bounds.
`AnalyticPDE/Parabolic/HigherFunctionSpace.lean` now begins the coordinate
`C^{2+α,1+α/2}` layer: it defines time and spatial slices, packages a genuine
parabolic second jet with time, spatial, and second-spatial derivative
witnesses on those slices, and defines a single-radius
`ParabolicC2AlphaNormLe` predicate whose radius dominates the value, spatial
derivative, spatial Hessian, and time-derivative `C^{0,α}` norm-ball controls;
this higher predicate already has constant and zero constructors and is closed
under addition, finite sums, negation, subtraction, scalar multiplication, and
continuous-linear value maps with explicit radius bounds. Chosen parabolic
second jets now also compose with continuous linear value maps, transforming
the time, spatial, and second-spatial derivative witnesses componentwise. Its
existential `ParabolicC2AlphaOn` class now forms a real submodule of all
coordinate time-space functions, is closed under continuous-linear value maps,
and reads back to `ParabolicC0AlphaOn` for the value component; the full
`C^{2+α,1+α/2}` radius also bounds the value-level `C^{0,α}` norm, and the
submodule has linear maps for both continuous-linear value composition and
forgetful inclusion into the existing `C^{0,α}` submodule. Higher norm balls
now also give value-level pointwise norm and distance readouts,
positive-exponent continuity and uniform-continuity readouts, and
continuous-linear-image `C^{0,α}` norm-ball controls, plus full
higher-coordinate projections for finite Pi-valued functions. Existential
higher membership and the higher
submodule now also expose actual time, spatial, and second-spatial derivative
witnesses with value-level `C^{0,α}` controls, without choosing a canonical
derivative map, and the norm-ball layer can coarsen one chosen second jet's
value and derivative components to the same `C^{0,α}` radius. The higher
submodule also has finite-Pi coordinate projection maps and inherits compact
value readouts from that forgetful map: single
compact pieces, finite compact families, and the linear finite-cover readout
all have sup-norm bounds from
`ParabolicC2AlphaNormLe` difference balls, plus matching
`LipschitzOnWith` estimates for pairwise higher-norm controls; equality of all
compact-family value readouts determines higher-parabolic functions on covered
domains and gives injectivity when the compact pieces cover all time-space, and
finite compact-family value `LipschitzOnWith` estimates unpack to pointwise
compact-coordinate distance bounds.
Second jets, `ParabolicC2AlphaNormLe`, `ParabolicC2AlphaOn`, and the higher
submodule now also restrict to smaller time-space domains.
`AnalyticPDE/Parabolic/HigherMatrix.lean` now supplies the first direct
higher-to-matrix handoff: entrywise `C^{2+α,1+α/2}` controls package
matrix-valued and finite-Pi-valued `C^{0,α}` controls, matrix-valued higher norm
balls project to entries both as full higher norm balls and as entry
`C^{0,α}` norm balls, and higher primitive entry controls feed the direct
schematic Ricci-DeTurck RHS `C^{0,α}` estimate and the existing single-radius
schematic Ricci-DeTurck RHS difference theorem. The direct schematic RHS
constant is named at the higher layer and has finite-family and Pi-valued
exact-sum norm-ball packaging. It now also converts entrywise higher
primitive difference controls with radii linear in a shared radius into the
linear-radius `ParabolicBoundedWith` schematic RHS estimate and the
compact-coordinate readout `LipschitzOnWith` bridge for any parabolic
`C^{0,α}` vector field agreeing with that RHS on the state set, including a
coarser exported-constant variant for sharper entrywise higher primitive
controls. The schematic RHS Lipschitz bridge now also has exact and coarser
linear finite-cover readout variants, so callers that use the finite-product
linear map do not have to unfold the compact-coordinate family manually. That
coarser compact readout now also unpacks to pointwise compact-coordinate
distance bounds with the same schematic RHS constant, including finite-family
forms with either memberwise constants or one shared finite-sum constant for
indexed frame/cover data. Radii linear in
`dist u v` give the matrix-norm/array primitive bounds needed by the existing
schematic RHS state-space `LipschitzOnWith` theorem, with a matching
finite-family wrapper, Pi-valued finite-product `C^{0,α}` and Lipschitz
packaging of all family coordinates, and matching coarser exported-constant
variants.
The matrix layer also has entrywise-to-matrix and matrix-to-entry bridges for
the same single-radius control, including matrix-valued higher difference
bounds and submodule-level matrix assembly/projection linear maps, plus
determinant and determinant-difference single-radius variants using the
existing quantitative determinant constants.
Inverse matrices and inverse-matrix differences now have matching
single-radius variants under a determinant lower bound. Finite matrix products,
matrix-vector products, and vector-matrix products, together with their
product-difference forms, now also have single-radius variants using the
existing quantitative product constants. Inverse-matrix-vector and
vector-inverse-matrix products, together with their difference forms, now have
the same single-radius packaging under a common determinant lower bound.
Finite vector dot products, bilinear contractions `v · M w`, and inverse
bilinear contractions `v · M⁻¹ w`, including the corresponding difference
forms, now also live in the same single-radius norm-ball API. The
inverse-Christoffel array and its entrywise-difference estimate now also have
single-radius norm-ball variants under a common determinant lower bound, and
the inverse-principal contractions `g^{ab}T_abij` now have matching
single-radius direct and entrywise-difference variants. The primitive-input
schematic Ricci-DeTurck matrix itself now has direct and entrywise-difference
single-radius variants assembled from those component estimates. The compact
local-frame Gram layer now also lifts the entrywise-difference primitive RHS
estimate into this norm-ball API for one geometric frame against arbitrary
comparison primitive inputs, extracting one shared determinant lower bound for
the Gram and comparison matrices from compactness first. It is still below the
actual `C^{2+α,1+α/2}` norm and Schauder estimate.

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
