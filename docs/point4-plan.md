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

## Definition of Done — Point 4 completion gate (authoritative)

**Do not declare point 4 closed, in a commit message, a status pulse, a
rollover note, or anywhere else, unless `curvature/scripts/point4_audit.sh`
prints `VERDICT: POINT 4 CLOSED` and exits `0` when run WITHOUT `--no-build`.**
That script is the single source of truth. Prose, `grep`, and "looks done"
do not count. (A naive `grep sorry` is specifically banned as evidence: the
word appears inside docstrings such as "proved sorry-free", which repeatedly
produced false "6 sorries" / "0 sorries" flip-flops. Use the audit's
comment-stripping scanner, `scripts/point4_scan.py cheats`, for the real
count.)

The audit enforces five hard gates, all of which must pass:

1. **G1 — sorry-free.** No `sorry`, `admit`, `sorryAx`, `native_decide`,
   `decide!`, `axiom`, or `opaque` in the `PoincareCurvature/` library source
   (measured after comments and string literals are stripped, so docstring
   prose cannot create false positives *or* hide a real cheat).
2. **G2 — build green.** `lake build` succeeds.
3. **G3 — unconditional construction.** A target theorem exists whose
   conclusion is `IntrinsicLocalExistenceUniquenessFamily` for a **general
   compact manifold**, carrying **no** restricting instance
   (`IsEmpty`, `Subsingleton`, `Fact (Module.finrank ℝ E ≤ 1)`, …) and **no**
   assumed `TimeDependentGeometricRicciDeTurckBanachChart` /
   `RicciDeTurckChartClosureData` hypothesis. In other words: the `chart` and
   `D` of the conditional bridge must be *constructed*, and Items 1, 2, and 3
   (below) discharged, not assumed.
4. **G4 — axiom-clean.** `#print axioms <target>` is a subset of
   `{propext, Classical.choice, Quot.sound}` and never mentions `sorryAx`.
5. **G5 — faithful type.** The *elaborated* type of the target (from
   `#check @<target>`) really is the point-4 package and carries none of the
   forbidden binders above — so vacuous or over-hypothesised instantiations are
   rejected even when the assumption is injected through a `variable`.

**Canonical target.** The audit looks for a declaration whose base name is in
`curvature/scripts/point4_target.txt` (default
`intrinsicLocalExistenceUniquenessFamily_pointFour`). When you assemble Items
1–3 into the unconditional closure, name it exactly that (or update the file),
and state it for a general compact manifold with only the ambient instances —
no `IsEmpty`/`Subsingleton`/`finrank` gate, no `chart`/`D` argument. The
existing bridge
`intrinsicLocalExistenceUniquenessFamily_of_ricciDeTurckChartClosureData`
passes G1/G4 but **fails G3/G5** precisely because it still takes `chart` and
`D` as hypotheses; that is the gap to close.

Partial closure is honest and welcome as *interim* progress (the empty /
subsingleton / rank-one / Einstein families already inhabit the package on
their sub-classes), but the audit only reports `CLOSED` for the fully general,
hypothesis-free, axiom-clean theorem. Report remaining work as fractions of
`{Item 1, Item 2, Item 3}` (equivalently `{chart, D}` construction), never as a
premature "done".

Run it yourself before any completion claim:

```bash
cd curvature && ./scripts/point4_audit.sh            # full check (runs lake build)
cd curvature && ./scripts/point4_audit.sh --no-build # fast gate check, no build
```

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

### Einstein homothetic *existence* (new, non-stationary)

A genuinely non-stationary positive-dimensional **existence** result is now
also proved in `LocalExistence/Einstein.lean`: for Einstein initial data
`Ric(cov₀) = λ • g₀` (with `cov₀` a Levi-Civita connection for `g₀`), the
homothetic family `g(t) = (1 - 2λ(t-t₀)) • g₀` is a genuine
`IntrinsicLocalSolution` on `[t₀, t₀ + δ]` with metric velocity `-2λ • g₀`
(`einsteinHomotheticIntrinsicLocalSolution` /
`intrinsicLocalSolution_nonempty_of_einstein`). Supporting reusable lemmas:

* `smulMetric` — positive scalar multiple of a `ContMDiffRiemannianMetric`;
* `isMetricCompatibleTangent_smulMetric` / `isLeviCivita_smulMetric` —
  scale-invariance of metric compatibility and the Levi-Civita property;
* `ricciCurvature_riemannianBundle_irrelevant` — the Ricci curvature value is
  independent of the Riemannian bundle instance (it is the trace of the
  connection-only curvature tensor);
* `intrinsicRicciTensor_homotheticMetricFamily` — intrinsic Ricci of the
  homothetic family is `λ • g₀`.

This is the first non-stationary positive-dimensional family with a proved
point-4 *intrinsic local solution*. It does **not** by itself close point 4
even on Einstein backgrounds, because the full
`IntrinsicLocalExistenceUniqueness` package additionally requires metric
*uniqueness over all* intrinsic local solutions; for `λ ≠ 0` the metric
velocity is nonzero, so the zero-velocity uniqueness machinery used in the
three families above does not apply, and uniqueness still needs the parabolic
DeTurck theorem (Item 3 below).

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

The same scalar/tensor conversion is now available at a single time via
`pullbackMetricFamily_hasTimeDerivativeAt_of_inner_hasDerivAt` and
`pullbackMetricFamily_inner_hasDerivAt_of_hasTimeDerivativeAt`, so endpoint
scalar derivative data can be moved into the tensor endpoint packages without
restating the pullback metric definition.
The DeTurck-specific gauge-reduction layer now exposes the same single-time
scalar/tensor conversion for the concrete gauge-corrected pullback velocity, so
endpoint arguments can stay at the intrinsic local-solution API when convenient.
It also has closed-interval gluing wrappers at that same API, accepting
interior `Ioo` tensor time-regularity plus either tensor endpoint derivatives
or scalar endpoint inner-product derivatives to produce time-regularity on the
intrinsic solution's `Icc` time set.
The same DeTurck-local API now accepts boundary-shaped endpoint data, matching
the Banach/PDE convention of supplying derivatives at closed-interval points
outside the open `Ioo` interior.

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
localized after shrinking a Picard interval. Ordinary scalar derivative data,
coordinate-model, field-level, and concrete component derivative packages now
also promote to their within-set endpoint versions on the same time set, so
stronger interior derivative data can enter the closed-Picard scalar route
without being repackaged by callers.
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
The concrete component consumer is named too:
`Diffeomorph3GaugeFlowOn.pullbackMetricBilinearCoordinateMap_hasDerivAt_of_metricCoordinateField_hasFDerivAt`
transfers the full field derivative to the actual moving `B(τ)` map at
neighborhood-times, with direct-velocity and finite-cover/readout companions.
The ordinary component package now consumes the same full/readout derivative
directly through
`Diffeomorph3GaugeFlowOn.coordinatePullbackMetricComponentDerivativeOn_of_metricCoordinateField_hasFDerivAt`
and its readout-field variant, rather than first routing through the field-level
package or the additive time-difference decomposition.
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
The fixed-time spatial derivative of `metricBilinearCoordinateField` now also
has model-slot forms using `tangentVectorOfCoordinate`, so Banach/readout
arguments carrying raw model coordinates can use the exterior-derivative and
Levi-Civita compatibility identities without first restating the slots as
`sourceTangentCoordinate`s.  The same model-slot interface now carries through
the spatial/tangent-map cancellation algebra via
`metricBilinearCoordinateField_spatial_tangentMapCorrection_modelSlots_eq`, so
Picard/readout linearization hypotheses stated directly on arbitrary centered
model slots can feed the DeTurck correction calculation before specializing to
geometric tangent vectors.  The raw variational correction route now consumes
that algebra through
`Diffeomorph3GaugeFlowOn.lieCorrection_modelSlots_of_tangentVectorOfCoordinate_Df_eq_cov_sub_extend`,
allowing the local `Df` identification to be stated on raw model coordinates
instead of only on `sourceTangentCoordinate` slots.  The signed DeTurck
correction endpoint now has the same entry point as
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_tangentVectorOfCoordinate_Df_eq_cov_sub_extend`,
so arbitrary model-slot `Df` identities can be carried directly to the
`-intrinsicDeTurckCorrection` scalar target.  The smooth-realization scalar
adapter now exposes this directly as
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_modelSlotCorrection`,
which feeds the model-slot signed correction into the finite-cover `hvalue`
route while specializing to source coordinates only at the final component
handoff.  Upstream, the Picard fixed-chart `Df` bridge now also has
model-slot variants
`Diffeomorph3GaugeFlowOn.tangentCoordChange_DfCoord_modelSlots_of_model_hasFDerivWithinAt_of_eventuallyEq`,
`Diffeomorph3GaugeFlowOn.tangentCoordChange_DfCoord_modelSlots_of_model_hasFDerivWithinAt_of_eventuallyEqWithin`,
and their closed-ball / fixed-center `EqOn` specializations, so closed-Picard
model derivative data can produce `Df` identities on arbitrary centered model
directions before entering the correction route.  The tangent-map Lie-bracket
and torsion-free covariant-difference bridges now mirror that model-slot shape
as well, via
`Diffeomorph3GaugeFlowOn.tangentVectorOfCoordinate_Df_eq_mlieBracket_of_tangentCoordChange_fderivWithin_modelSlots`
and
`Diffeomorph3GaugeFlowOn.tangentVectorOfCoordinate_Df_eq_cov_sub_extend_of_tangentCoordChange_fderivWithin_modelSlots`.
The signed correction endpoint now has matching fixed-chart and closed-ball
model-slot wrappers,
building on the raw model-slot Lie-correction bridges
`Diffeomorph3GaugeFlowOn.lieCorrection_modelSlots_of_tangentCoordChange_fderivWithin`
and
`Diffeomorph3GaugeFlowOn.lieCorrection_modelSlots_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_nhdsWithin`;
the signed endpoints are
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_tangentCoordChange_fderivWithin`
and
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_nhdsWithin`,
so fixed-center local `EqOn` Picard data can reach the signed correction while
keeping arbitrary centered model slots through the correction proof.  The
auxiliary-field wrapper
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_vectorField_of_eventuallyEq_along_maps3_nhdsWithin`
extends this one layer toward the compact finite-cover handoff by consuming the
patch-local auxiliary vector-field `EqOn` plus the along-flow intrinsic-field
certificate directly in model slots.  Its finite-cover/readout companion
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_iUnion_readout_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`
keeps the retained compact-witness readout equality in the same model-slot
shape, and
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_iUnion_readout_mpullbackWithin_of_eventuallyEq_along_maps3_nhdsWithin`
does the same when the patch-local field input is supplied in centered
`mpullbackWithin` form.  The local Picard/gluing wrapper
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_iUnion_readout_localGluingData_localFlowSolution_of_eventuallyEq_along_maps3_nhdsWithin`
now derives that pullback-field input from current-time anchored model flows
while preserving the arbitrary model-slot correction conclusion.  Its
continuous-readout companion
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_modelSlots_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`
matches the selected compact constructors that retain readout continuity rather
than an explicit source-persistence hypothesis.  The
smooth scalar endpoint also has
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_modelSlotSignedCorrection`,
which consumes a signed correction already stated in model slots and performs
the source-coordinate specialization only at the final `hvalue` handoff.  The
closed-ball smooth scalar routes now enter through this adapter, so their
Picard derivative data also stay in model slots until that final handoff.
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
In parallel, the finite-cover Banach-section route now proves the moving
time-difference directly in the section norm once the selected compact
coordinate readout is identified with the metric realization. That route avoids
reconstructing the time-difference from fixed-point scalar readouts, but it has
not yet been connected end-to-end to the raw gauge-flow
`metricBilinearCoordinateField` construction.
The same centered formula now applies to any coordinate curve that is eventually
stationary at the chart center, covering the no-spatial-motion case needed by
identity/static gauges, and it now has within-time-set variants for closed
Picard endpoint filters when the curve also agrees with the chart center at the
base time.
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
The localized open-product-domain local-flow route now also has the
relative-filter readout form
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_eventuallyEqWithin_metricCoordinateField_hasFDerivWithinAtOpenDomain_variationalLocalFlowWithin_geometricValue_self`.
This lets finite-cover readouts agree with the named metric-coordinate field
only inside the same open product domain used for the Fréchet derivative, while
the existing base-flow agreement still transports the model endpoint and raw
gauge velocity.
The direct full-field product-chain-rule primitive is now named as well:
`Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivAt_of_hasFDerivAt`
and
`Diffeomorph3GaugeFlowOn.metricBilinearCoordinateField_hasDerivAt_of_eventuallyEq`,
with direct-velocity `_self` versions and matching within-set companions. These
differentiate the raw gauge-flow coordinate curve through the named
`metricBilinearCoordinateField` once a full two-variable Fréchet/readout
derivative has already been supplied. They intentionally do not supply that
remaining positive-dimensional Fréchet/readout derivative.
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
The same one-sided endpoint now also accepts model-coordinate curves that are
stationary at the chart center along the right-time filter:
`metricBilinearCoordinateField_hasDerivWithinAt_Ici_chartRHS_of_eventuallyEq_center_of_mem_Ico`
and its `sourceTangentCoordinate` variant transfer the centered chart-RHS
derivative across `𝓝[Ici t] t` eventual equality plus the base-time equality.
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
once the model vector field agrees with the reverse intrinsic DeTurck gauge field along
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
chart-ODE package by hand. The raw gauge-flow theorem-package handoff now also
preserves scalar inner-derivative structure directly: fixed-IVP and theorem-family
chosen DeTurck packages can project to the scalar-derivative gauge-reducible
package from raw intrinsic gauge-flow existence plus scalar pullback-metric
derivative data, without detouring through the weaker gauge-reducible package.
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
proof. The global and interval geometric endpoint family records now also
project directly to the chosen-background Ricci-DeTurck theorem family before
gauge reduction, so callers can keep that package when they do not yet need the
intrinsic or ordinary Ricci-flow projections. The scalar endpoint derivative
family records now expose the same chosen-background theorem-family projection,
removing the remaining detour through intrinsic or ordinary projections for
callers that already have endpoint derivative gauge-flow data.
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
smaller initial ball. The autonomous `C¹` route now also exposes
state-preserving Lipschitz and continuous space-time local-flow witnesses,
together with localized forms, so after a Picard shrink callers keep the closed
state-ball estimate used by chart-domain and convex state-tube arguments.
At the underlying `IsPicardLindelof` layer, the same state-preserving route now
has direct continuous-flow and localized Lipschitz/continuous witnesses
`exists_lipschitzLocalFlowSolution_mem_closedBall_restrict` and
`exists_continuousLocalFlowSolution_mem_closedBall[_restrict]`, so non-autonomous
chart Picard output can be shrunk while retaining the closed Picard state-ball
readout without rebuilding the selected solution package.
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
The operator-ball and identity-ball state-preserving Picard specializations now
also expose the forward common-interior lifted chart patch as bundled
`LocalGluingData`, including the full space-time regularity variants. Their
overlap/`EqOn` variants, both from time-slice regularity and full space-time
regularity, likewise return the bundled local data together with the
same-source-patch readout equality, so compact raw-flow gluing constructors can
consume these Picard outputs directly without rebuilding the local inverse
package from the unbundled maps-to/inverse/smoothness fields.
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
The localized componentwise closed-ball continuity route now also has a
direction-free common-`Ioo` local-inverse wrapper,
`exists_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_openPartialHomeomorph_common_Ioo_of_hasFDerivWithinAt_Icc_of_le_radius`,
which dispatches internally to the forward or backward closed-interval theorem
according to the selected time.  Compact symmetric Picard intervals can
therefore request the model `OpenPartialHomeomorph` witness without exposing a
separate time-direction split at each call site.
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
Their common-patch and overlap-`EqOn` `localGluingData` counterparts now package
the same fixed-time and space-time backward inverse-function data as bundled
`LocalGluingData`, including the retained same-source-patch readout equality.
Thus callers that already have a time-slice `ContDiffAt` proof need not route
through full space-time regularity, and callers with space-time regularity still
avoid unpacking the inverse-function tuple.
The restricted state-preserving componentwise bundled common-patch handoff now
also has direction-free all-`Icc` wrappers,
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_exists_lifted_open_nhds_localGluingData_subset_common_Ioo_of_hasFDerivWithinAt_Icc_of_le_radius`
and
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_exists_lifted_open_nhds_localGluingData_subset_common_Ioo_of_hasFDerivWithinAt_Icc_of_le_radius_of_contDiffAt_spaceTime`.
These wrappers keep compact gluing callers on one selected closed interval
while consuming either fixed-time `C^3` regularity or the natural space-time
regularity proof and dispatching internally to the correct forward/backward
common-`Ioo` gluing package.
The retained same-source overlap-equality handoff now has the same
direction-free shape through
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_exists_lifted_open_nhds_localGluingData_subset_eqOn_common_Ioo_of_hasFDerivWithinAt_Icc_of_le_radius`
and
`ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_exists_lifted_open_nhds_localGluingData_subset_eqOn_common_Ioo_of_hasFDerivWithinAt_Icc_of_le_radius_of_contDiffAt_spaceTime`,
so compact Picard overlap readouts can carry their `EqOn` proof through the
same selected closed interval without exposing a time-direction split.
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
eventual pointwise equality between the canonical glued map and the selected
local readout, while
`gluedMapOf_iUnion_eventually_nhds_eqOn_of_pointwiseSource_open` and its
relative-time-set form
`gluedMapOf_iUnion_eventually_nhds_eqOn_of_pointwiseSource_openOn` upgrade that
to eventual equality on an actual open neighborhood of the base point.  The
raw local-readout constructor now also exposes
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_compatibleGluedSlices_pointwiseSource_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin_eventually_nhds_eqOn`,
which states the same local `EqOn` readout directly for the constructed
`G.maps3` witness.  The new
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
The generic moving-cover route now also has endpoint-retaining closed-interval
companions.  At the raw level,
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_gluedSlices_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin_on_Icc`
and
`Diffeomorph3GaugeFlowOn.of_timeDependent_iUnion_gluedSlices_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin_on_Icc`
produce `Icc` gauge-flow witnesses rather than immediately discarding the
endpoints, and
`timeDependent_iUnion_hFEqWithinAll_on_Icc_of_finite` supplies the finite-cover
uniform relative-filter handoff on the same closed interval.  The fixed-IVP
intrinsic layer exposes both the global glued-slice and local-readout closed
forms as
`IntrinsicDeTurckGaugeFlowExistence.ofClosedPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_vectorField_eq_nhdsWithin`
and
`IntrinsicDeTurckGaugeFlowExistence.ofClosedPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_of_localReadouts_vectorField_eq_nhdsWithin`;
the theorem-family layer has both corresponding closed constructors, including
`IntrinsicDeTurckGaugeFlowExistenceFamily.ofClosedPicardIccChartDerivative_of_timeDependent_iUnion_gluedSlices_of_localReadouts_vectorField_eq_nhdsWithin`,
assembled over the fixed-IVP closed local-readout route so compact Picard
callers can stay at the family boundary.
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
covers known only on `Icc tmin tmax`.  Its
`..._eventually_nhds_eqOn` readout theorem removes that fallback patch again
inside the closed interval, exposing eventual local `EqOn` between the
constructed `G.maps3` and the original selected local readout on `U τ i`.  The
interval-local `LocalGluingData` pointwise-source and open-preimage wrappers now
expose the same equality through
`Diffeomorph3GaugeFlowOn.of_Icc_timeDependent_iUnion_localGluingData_pointwiseSource_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin_eventually_nhds_eqOn`
and
`Diffeomorph3GaugeFlowOn.of_Icc_timeDependent_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin_eventually_nhds_eqOn`,
so Picard inverse-function outputs packaged as `LocalGluingData` no longer have
to unfold the raw compatible-slices constructor just to recover the local
readout agreement.  Their interior-time companions
`..._localGluingData_pointwiseSource_..._eventually_nhds_exists_eqOn_of_mem_Ioo`
and
`..._openPreimage_localGluingData_..._eventually_nhds_exists_eqOn_of_mem_Ioo`
upgrade the closed-Picard relative eventual to ordinary `𝓝 t` and package the
selected patch existentially, matching the readout input expected by the
readout-lifted tangent-map route.  The readout-lifted tangent-map layer now also
has the synchronization helper
`SmoothSelfDiffeomorph3Family.eventually_readout_lifted_eqOn_of_eventually_target_and_eqOn`,
its literal-lift specialization
`SmoothSelfDiffeomorph3Family.eventually_readout_lifted_eqOn_refl_of_eventually_target`,
and the ordinary-derivative adapters
`SmoothSelfDiffeomorph3Family.eventually_hasFDerivWithinAt_range_of_eventually_hasFDerivAt`,
`SmoothSelfDiffeomorph3Family.fixedChartModel_eventually_variational_source_exists_nhds_eqOn_hasFDerivAt_of_eventually_readout_lifted_eqOn`,
and
`SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_derivativesOn_of_variationalTangentMap_readout_lifted_eqOn_hasFDerivAt`;
these let Picard output prove target membership, lifted equality, and ordinary
time-slice spatial derivatives separately before feeding the existing
within-derivative readout route.  The target-membership input now has a
continuity bridge:
`SmoothSelfDiffeomorph3Family.eventually_extChartAt_model_mem_target_of_continuousAt`
turns space-time model continuity and an ordinary target-neighborhood condition
at the base point into the eventual local target membership needed by the
lifted readout route, with variational-flow, interior-Picard, and boundaryless
`..._of_mem_target` conveniences.  The same layer now also exposes
`SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_derivativesOn_of_variationalTangentMap_readout_target_lifted_eqOn_hasFDerivAt`,
`..._readout_continuousAt_lifted_eqOn_hasFDerivAt`, and
`..._readout_mem_ball_lifted_eqOn_hasFDerivAt`, so callers can supply target
membership, target-neighborhood continuity, or interior Picard ball data
separately from the lifted `EqOn` proof.  The same readout inputs now also have
eventual-equality forms
`SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_eventuallyEq_of_variationalTangentMap_readout_lifted_eqOn_hasFDerivAt`,
`..._readout_target_lifted_eqOn_hasFDerivAt`, and
`..._readout_mem_ball_lifted_eqOn_hasFDerivAt`; these preserve the concrete
identification with `α.tangent xE τ` for component routes whose value formula
still needs the explicit `Df t (α.flow (xE,t))` coefficient.  The component
layer now consumes those readout equalities directly through
`SmoothSelfDiffeomorph3Family.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_target_lifted_eqOn_hasFDerivAt`
and
`..._readout_mem_ball_lifted_eqOn_hasFDerivAt`, combining time-only bilinear
coordinate derivatives with the readout-local tangent-map identification while
leaving the explicit variational `Df` value formula intact.  The indexed-cover
companion
`SmoothSelfDiffeomorph3Family.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_lifted_eqOn_hasFDerivAt`
now chooses the patch containing each base point from an `iUnion` cover, so
finite-cover and compact local-gluing outputs can keep their local readout,
lifted model equality, and scalar value hypotheses indexed by patch until the
final component derivative package is assembled.  Its source-coordinate
companion
`SmoothSelfDiffeomorph3Family.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn`
uses the common Picard-estimate `HasFDerivAt` input directly, so indexed local
scalar data no longer needs to repeat the model-flow spatial derivative at each
patch.  The raw
`Diffeomorph3GaugeFlowOn` API now exposes the matching interior
time-regularity endpoints
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_variationalTangentMapComponents_readout_target_lifted_eqOn_hasFDerivAt`
and
`..._readout_mem_ball_lifted_eqOn_hasFDerivAt`, so a gauge-flow witness can
consume local readout equality, target membership or target-neighborhood
continuity, and time-only metric component derivatives without first packaging
the tangent-map equality manually.  The raw source-coordinate endpoint
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_variationalTangentMapComponents_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn`
adds the indexed-cover/Picard-derivative variant at this level too.  The same
closed-Picard readout/mem-ball
shape is now named at the fixed-IVP geometric layer as
`ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.VariationalTangentMapReadoutMemBallDerivativeDataOnIoo`,
with
`ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalTangentMapReadoutMemBallDerivativeDataOnIoo_of_iUnion`
choosing the patch containing each base point from an indexed cover before the
data are lifted through fixed-IVP, theorem-family, and raw intrinsic gauge-flow
existence wrappers.  Callers with `timeSet = Icc tmin tmax` can therefore keep
finite-cover or compact local-gluing outputs indexed until the package-level
API invokes the new raw endpoint and obtains the interior `Ioo` tensor time
derivative directly.  The companion
`ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalTangentMapReadoutMemBallDerivativeDataOnIoo_of_iUnion_source_hasFDerivAt`
factors the model-flow spatial derivative out of the indexed local scalar data:
Picard estimates can now supply one source-coordinate eventual `HasFDerivAt`
input, while each local patch only carries the metric-component time
derivative, source-ball membership, target-neighborhood fact, lifted readout
equality, and final scalar velocity identity.  On the model side,
`ModelGaugeFlowODE.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_flow_timeSlice_hasStrictFDerivAt_of_hasFDerivWithinAt_Icc_of_le_radius`
dispatches the selected restricted Picard time slice to the forward or backward
strict-derivative estimate, and
`ModelGaugeFlowODE.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_eventually_flow_timeSlice_hasFDerivAt_of_hasFDerivWithinAt_Ioo_of_le_radius`
turns this into the ordinary-neighborhood eventual `HasFDerivAt` input needed by
the new readout route, and
`ModelGaugeFlowODE.ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_source_eventually_flow_timeSlice_hasFDerivAt_of_hasFDerivWithinAt_Ioo_of_le_radius`
packages the same Picard estimate directly in the source-coordinate form
consumed by the fixed-IVP indexed readout-data bridge.  The
matching
`..._localGluingData_pointwiseSource_...` and
`..._openPreimage_localGluingData_...` adapters preserve the named
local-inverse-function package and derive pointwise source persistence from
fixed open target-preimage patches.  The closed-interval pointwise-source and
open-preimage readout lemmas
`Diffeomorph3GaugeFlowOn.of_Icc_timeDependent_iUnion_localGluingData_pointwiseSource_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin_on_Icc_eventually_nhds_exists_eqOn_of_mem_Ioo`
and
`Diffeomorph3GaugeFlowOn.of_Icc_timeDependent_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_Icc_extChartAt_eval_self_of_vectorField_eq_nhdsWithin_on_Icc_eventually_nhds_exists_eqOn_of_mem_Ioo`
now expose the same ordinary-neighborhood local readout equality for the `Icc`
raw flows consumed by the source-coordinate time-derivative endpoint.  The
ambient-time-set variant
`Diffeomorph3GaugeFlowOn.of_Icc_subset_timeSet_timeDependent_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
restricts local continuity and derivative data from a larger solution time set
to the chosen closed Picard interval using the interval-subset proof, and its
closed-interval readout companion
`Diffeomorph3GaugeFlowOn.of_Icc_subset_timeSet_timeDependent_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin_on_Icc_eventually_nhds_exists_eqOn_of_mem_Ioo`
preserves the local readout equality for the resulting `Icc` raw flow.  The
compact raw existence theorems
`Diffeomorph3GaugeFlowOn.exists_Ioo_gaugeFlow_of_compact_timeSet_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
and
`Diffeomorph3GaugeFlowOn.exists_Icc_gaugeFlow_of_compact_timeSet_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
now combine compact subcover selection, source/target cover persistence inside
the chosen Picard interval, and raw gauge-flow construction.  The finite-core
selected witness
`Diffeomorph3GaugeFlowOn.exists_Icc_gaugeFlow_with_readout_of_finite_timeSet_compactCore_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
keeps the chosen `Icc` raw flow and its indexed local readout equality together,
so downstream time-derivative routes do not have to recover readout evidence
from a bare `Nonempty` witness.  The same selected-readout shape now persists
through the finite compact-manifold wrapper
`Diffeomorph3GaugeFlowOn.exists_Icc_gaugeFlow_with_readout_of_finite_compact_timeSet_iUnion_openPreimage_localGluingData_of_spaceTime_continuous_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`,
the arbitrary compact finite-subcover wrapper
`Diffeomorph3GaugeFlowOn.exists_Icc_gaugeFlow_with_finiteSubcover_readout_of_compact_timeSet_iUnion_openPreimage_localGluingData_of_spaceTime_continuous_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`,
the ambient-time compact finite-subcover wrapper
`Diffeomorph3GaugeFlowOn.exists_Icc_gaugeFlow_with_finiteSubcover_readout_of_compact_timeSet_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`,
and the pointwise family wrapper
`Diffeomorph3GaugeFlowOn.exists_Icc_gaugeFlow_family_with_finiteSubcover_readout_of_compact_timeSet_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`.
For arbitrary index types these wrappers return the selected `Finset` and state
the readout over its subtype, matching the finite cover actually used by the
glued raw flow.  The ambient-time compact route now also has stronger
cover-preserving selected witnesses
`Diffeomorph3GaugeFlowOn.exists_Icc_gaugeFlow_with_finiteSubcover_Icc_subset_cover_readout_of_compact_timeSet_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
and
`Diffeomorph3GaugeFlowOn.exists_Icc_gaugeFlow_family_with_finiteSubcover_Icc_subset_cover_readout_of_compact_timeSet_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`,
which keep the selected finite source cover on the whole closed interval, the
ambient interval-subset certificate, the raw `Icc` gauge flow, and the local
readout equality in one package.  This matches the cover/readout hypotheses of
the raw source-coordinate time-derivative endpoint.  The time-derivative layer
now has matching closed-interval-cover entry points
`Diffeomorph3GaugeFlowOn.hasTimeDerivativeOn_Ioo_of_variationalTangentMapComponents_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn`
and
`ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow.variationalTangentMapReadoutMemBallDerivativeDataOnIoo_of_iUnion_Icc_cover_source_hasFDerivAt`,
which restrict that `Icc` source-cover certificate to the open interior before
invoking the existing readout-local source-coordinate derivative routes.  The
underlying tangent-map layer now has the same indexed-cover handoff through
`SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_derivativesOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn`
and its closed-interval-cover companion
`..._readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn`, so
selected compact finite covers can feed the tangent-coordinate derivative route
before metric-component scalar data is introduced.  The component-level route
now mirrors this closed-cover handoff via
`SmoothSelfDiffeomorph3Family.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn`,
so the same selected `Icc` source cover can feed the scalar pullback-metric
component package.  More broadly, the compact
raw existence
theorems combine
the ambient time set, ambient local regularity, and the open-preimage
local-gluing route to produce raw gauge-flow witnesses on small symmetric `Ioo`
and endpoint-retaining `Icc` intervals, deriving the base-time target cover and
the fixed target-preimage cover from the base-time source cover and anchored
local readouts. The finite compact-core, finite compact-manifold,
arbitrary-compact-subcover, and restricted-pair preimage routes now have matching
`exists_Icc_gaugeFlow_...` companions, so compact ODE output can keep endpoints
when constructing the raw flow.  Raw `Diffeomorph3GaugeFlowOn` witnesses now
also have `restrictTimeSet` and `restrictIooOfIcc`, so a closed-Picard witness
can be viewed on the open interior with the same `maps3` family before entering
open-time derivative routes.
through the raw open-preimage local-gluing boundary.  The ambient local-gluing
compact route now also has pointwise-family adapters,
`Diffeomorph3GaugeFlowOn.exists_Ioo_gaugeFlow_family_of_compact_timeSet_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
and
`Diffeomorph3GaugeFlowOn.exists_Icc_gaugeFlow_family_of_compact_timeSet_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`,
which choose a positive radius for each family member and expose the raw
small-interval witnesses before any fixed-IVP chosen-time-set repackaging.  The
matching `_with_Icc_subset_...` family adapters additionally return
`Icc (t₀ a - ε a) (t₀ a + ε a) ⊆ timeSet a`, so the compact shrink supplies
both the raw witness and the certificate needed to restrict the ambient DeTurck
solution to the same closed symmetric interval.  The intrinsic DeTurck local
solution records now have exact `restrictTimeSet` and `restrictSymmetricIcc`
constructors, with chosen-background wrappers and simp lemmas for the resulting
named `timeSet`.  The raw-flow bridge now also has
`IntrinsicDeTurckLocalSolution.nonempty_rawGaugeFlowOn_restrictTimeSet` and
`..._restrictSymmetricIcc`, so a compact raw witness on the selected interval
immediately repackages as a witness for the restricted local solution.  The
selected raw-flow layer now packages exactly that fixed-IVP and theorem-family
handoff as `SelectedIntrinsicDeTurckGaugeFlowExistence` and
`SelectedIntrinsicDeTurckGaugeFlowExistenceFamily`: callers provide one selected
restricted chosen DeTurck solution, identify its exact named time set with the
raw compact interval via `ofRawGaugeFlowOn`, and then project directly to
gauge-reducible, intrinsic, or ordinary theorem packages once the selected
gauge-pulled metric time derivative or scalar inner-derivative data is supplied.
The selected layer also records the scalar/tensor time-derivative equivalence,
so endpoint projections can consume or recover the selected scalar derivative
package without unfolding the gauge-pulled metric theorem.
Its time-derivative interface now accepts selected coordinate-level,
coordinate-model, concrete-component, and field-level scalar derivative data,
including explicit open-Picard `Ioo` neighborhood discharges, and converts those
inputs directly to the selected scalar package.
For compact Picard output, the selected interface also accepts within-set
component, field, and operator data on a closed `Icc` time set and returns
tensor time-regularity on the open interior `Ioo`, matching the endpoint shape
of closed-interval chart ODE constructions.
The same selected fixed-IVP and theorem-family closed-Picard interfaces now
also expose the readout-local variational tangent-map handoff, so Banach/Picard
tangent-map data can feed the selected gauge-pulled metric time derivative
without reintroducing the all-candidate solution parameter.
The selected fixed-IVP package has matching `iUnion` and closed-`Icc` source
cover constructors, including the source-coordinate `HasFDerivAt` variant used
by compact local variational-flow output.
It also has `ofRawGaugeFlowOn_restrictTimeSet` and
`ofRawGaugeFlowOn_restrictSymmetricIcc`, with proof-level `nonempty_...`
versions, so callers can start from an ambient chosen DeTurck solution plus the
raw flow on the restricted interval and obtain the selected package in one
step.
For open-Picard selected time sets, the selected raw-flow existence package now
also has direct single-solution constructors from closed-`Icc` primitive
derivative, centered-chart derivative, and fixed-chart ODE data, with matching
proof-level `Nonempty` forms, so compact Picard output no longer has to be
promoted to an all-candidates raw-flow family before selecting the solution to
gauge-reduce.
The same selected fixed-chart route now accepts model-vector-field ODE data with
either pointwise or closed-interval relative-filter identification with the
intrinsic DeTurck gauge field along the selected candidate flow.
It also has a finite time-dependent `LocalGluingData` local-readout constructor,
so compatible local inverse-function outputs can assemble a selected raw flow
on the selected open Picard time set directly.
The selected theorem-family layer now also has the compact restricted-symmetric
route-data wrapper
`SelectedIntrinsicDeTurckGaugeFlowExistenceFamily.exists_restrictSymmetricIcc_routeData_with_finiteSubcover_Icc_subset_cover_readout_localData_auxiliaryEqAlong_of_compact_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`,
which chooses the finite subcover, closed interval, selected restricted raw
flow, local readout equality, local `LocalGluingData`, continuity, chart-ODE
data, and auxiliary-field equality uniformly over all initial-value problems.
Thus theorem-family gauge-reduction routes no longer have to repeat the
fixed-IVP compact-selection destructuring before entering the selected
time-derivative interfaces.
The older all-candidates fixed-IVP and theorem-family intrinsic layers also
continue to expose `ofRawGaugeFlowOn` with proof-level
`nonempty_ofRawGaugeFlowOn`, packaging raw witnesses on named time sets once
those sets have been identified with every chosen local-solution time set.  The
fixed-IVP intrinsic
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
compatibility.  The common-subinterval variants now have the same
`LocalGluingData` and overlap-equality packages, so compact subinterval
selection no longer has to unpack the long inverse-function tuple before
feeding finite-cover gluing.  The product-Picard common-subinterval handoff and
the main forward/backward state-preserving component closed-ball routes now
expose the same package shape, including overlap-equality forms, so the compact
finite-cover route can request named local packages directly from the ODE
estimate layer.  The remaining lift must still supply the chart-domain
shrinking/source-membership hypotheses and combine these local patches with
manifold-level flow compatibility before producing `C³` diffeomorphism slices.
On the gauge-transport side, the reduced solution has now crossed from the
transported-background equation to genuine target Ricci data: the transformed
velocity is exposed directly as
`GaugeReducedIntrinsicDeTurckLocalSolution.transformed_velocity_eq_neg_two_intrinsicRicciTensor`
on the source time set and by a local-interval companion.
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
The same finite-cover layer now also has the section-norm moving-evaluation
bridge
`HasDerivAt.continuousMap_moving_eval_sub_const` /
`HasDerivWithinAt.continuousMap_moving_eval_sub_const`, plus the concrete
metric-section wrappers
`BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_timeDifference_hasDerivAt_of_mem_Ioo`
and
`BanachEvolutionLocalSolutionIn.coordBilinearFormReadoutMap_timeDifference_hasDerivWithinAt_Ici_of_mem_Ico`.
These lemmas differentiate the time-difference
`coord(sol.curve τ)(x τ) - coord(sol.curve t)(x τ)` at a moving compact
coordinate point directly from the Banach derivative in sup norm. They remove
the need to rebuild this time-difference from scalar fixed-point readouts.
The smooth-realization wrappers
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadoutMap_timeDifference_hasDerivAt_of_mem_Ioo`
and
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metric_coordBilinearFormReadoutMap_timeDifference_hasDerivWithinAt_Ici_of_mem_Ico`
now perform the intermediate transfer from `sol.curve` to the realized smooth
metric section using `metric_toContinuousSection_eq_curve`.
`SmoothRealizationGaugeRoutes` now also proves the geometric identification:
`metric_coordBilinearFormReadoutMap_eq_metricBilinearCoordinateField` rewrites a
preferred finite-cover bilinear coordinate readout as the raw
`metricBilinearCoordinateField`, and
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricBilinearCoordinateField_timeDifference_hasDerivAt_of_coord_mem_Ioo`
transfers the moving time-difference derivative to that raw coordinate field
when the finite-cover center is the raw gauge center. The stronger
target-centered bridge removes that center-equality requirement:
`targetBilinearCoordReadoutContinuousLinearMap` restricts a finite-cover
component to a smaller compact set and changes bilinear-form coordinates to the
trivialization centered at the time-`t` gauge image, while
`metric_targetBilinearCoordReadout_eq_metricBilinearCoordinateField` identifies
that changed readout with the raw coordinate field. The time-difference wrappers
`metricBilinearCoordinateField_timeDifference_hasDerivAt_of_target_coord_mem_Ioo`
and
`metricBilinearCoordinateField_timeDifference_hasDerivWithinAt_Ici_of_target_coord_mem_Ico`
then feed the Banach derivative through this target-centered compact readout.
The raw gauge-flow wrappers
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_target_coord_mem_Ioo`
and
`metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_target_coord_mem_timeSet_Ico`
combine that target-centered time-difference term with the existing
frozen-spatial raw-flow derivative. Their convenience forms
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_eventually_mem_target_K_Ioo`,
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_target_K_Ioo`,
`metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_eventually_mem_target_K_Ico`,
and
`metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_target_K_Ico`
build the selected compact curve from ordinary or relative eventual membership,
with interior membership making the eventual-membership witnesses automatic.
The compact-overlap selection step is now packaged one level higher:
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_mem_interior_Kc_target_overlap_Ioo`
and
`metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_mem_interior_Kc_target_overlap_Ico`
use local compactness of the finite-dimensional manifold to choose such a
compact `K` whenever the gauge point is already in `interior (Kc i)`. Thus the
target-domain overlap no longer has to be supplied by callers. At the
interior-cover level,
`metricBilinearCoordinateField_hasDerivAt_along_gauge_eval_of_interior_cover_target_overlap_Ioo`
and
`metricBilinearCoordinateField_hasDerivWithinAt_along_gauge_eval_of_interior_cover_target_overlap_Ico`
also select the cover index from
`(⋃ i, interior (Kc i : Set M)) = Set.univ`, so the scalar route consumes the
refined compact cover directly at both open-interior and right-sided endpoint
times. The open-interior selector now feeds the first downstream
non-identity-gauge component package:
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.coordinatePullbackMetricComponentDerivativeOn_of_interior_cover_target_overlap_Ioo`
turns the selected scalar derivative into
`SmoothSelfDiffeomorph3Family.CoordinatePullbackMetricComponentDerivativeOn`
once the tangent-coordinate-map derivative and final scalar velocity identity
are supplied, and
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_interior_cover_target_overlap_Ioo`
lifts that component package to tensor `HasTimeDerivativeOn` for the raw
gauge-pulled realized metric. Thus the finite-cover selector is now connected
to the named tensor time-regularity route. The tangent-map derivative datum
now has a generic variational bridge,
`SmoothSelfDiffeomorph3Family.pullbackMetricTangentCoordinateMap_derivativesOn_of_variationalTangentMap`:
an eventual identification with a `VariationalLocalFlowSolution` tangent map on
any `s ⊆ Ioo tmin tmax` gives the required quantified
`∃ D, HasDerivAt ... (D.comp A(t)) t` package. That eventual identification
can now itself be produced from fixed-chart spatial derivative data:
`pullbackMetricTangentCoordinateMap_eq_fderivWithin_fixedChart` identifies the
concrete tangent-coordinate map with the `fderivWithin` of
`extChartAt I ((Φ t) x) ∘ Φ τ ∘ (extChartAt I x).symm`, while
`pullbackMetricTangentCoordinateMap_eventuallyEq_of_hasFDerivWithinAt_fixedChart`
and
`pullbackMetricTangentCoordinateMap_derivativesOn_of_variationalTangentMap_fixedChart`
package the corresponding eventual and quantified variational selectors. The
next layer is now also present:
`pullbackMetricTangentCoordinateMap_eventuallyEq_of_eventuallyEq_variationalFlow_hasFDerivWithinAt_fixedChart`
and
`pullbackMetricTangentCoordinateMap_derivativesOn_of_variationalTangentMap_fixedChartModel`
consume local equality with the selected variational model flow plus the
model-flow spatial derivative, producing the same tangent-coordinate derivative
package. The local-equality input can now be supplied as manifold-side gluing
data:
`fixedChartModel_eventuallyEq_nhdsWithin_range_of_eqOn_source` converts a
neighborhood `EqOn` statement for a time slice into the required
`𝓝[range I]` model-coordinate eventual equality, and
`pullbackMetricTangentCoordinateMap_eventuallyEq_of_eventually_eqOn_variationalFlow_hasFDerivWithinAt_fixedChart`
packages that conversion with the variational model-flow spatial derivative.
For gluing outputs stated as equality of manifold-valued lifted maps,
`fixedChartModel_eqOn_of_lifted_eqOn_source` and
`fixedChartModel_eventuallyEq_nhdsWithin_range_of_lifted_eqOn_source` first push
the equality through the fixed target chart, assuming the model values stay in
that chart target.  The new
`fixedChartModel_eqOn_of_readout_lifted_eqOn_source`,
`fixedChartModel_exists_nhds_eqOn_of_readout_lifted_eqOn_source`, and
`fixedChartModel_eventually_exists_nhds_eqOn_of_eventually_readout_lifted_eqOn_source`
compose that lifted model equality with the constructed-flow/local-readout
equality exposed by the pointwise-source constructors, producing the exact
local fixed-chart `EqOn` existential expected by `hA_model`.  The filter helper
`eventually_nhds_of_eventually_nhdsWithin_Icc_of_mem_Ioo` also records the
standard upgrade from closed-Picard relative eventuals to ordinary eventuals at
interior times.  The companion
`fixedChartModel_eventually_source_exists_nhds_eqOn_hasFDerivWithinAt_of_eventually_readout_lifted_eqOn_source`
and its variational-flow specialization package that local `EqOn` together
with source membership and model spatial derivative data into the full eventual
triple used by the fixed-chart `hA_model` routes.  A lighter companion now
derives that source membership from the readout equality, lifted equality, and
target-chart membership itself:
`fixedChartModel_source_mem_of_readout_lifted_eqOn_source`,
`fixedChartModel_eventually_source_exists_nhds_eqOn_hasFDerivWithinAt_of_eventually_readout_lifted_eqOn`,
and
`fixedChartModel_eventually_variational_source_exists_nhds_eqOn_hasFDerivWithinAt_of_eventually_readout_lifted_eqOn`.
The quantified component-level route is also available as
`pullbackMetricTangentCoordinateMap_derivativesOn_of_variationalTangentMap_fixedChartModel_eqOn`,
and the readout-lifted companion
`pullbackMetricTangentCoordinateMap_derivativesOn_of_variationalTangentMap_readout_lifted_eqOn`
accepts the Picard/gluing eventuals before fixed-chart composition without a
separate fixed-target source-membership input.  At the smooth-realization
scalar-selector layer,
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue`
now offers the same readout-lifted input shape while preserving the existing
geometric-slot scalar identity. Its tensor-level companion
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue`
promotes that component package to `HasTimeDerivativeOn` using the raw
gauge-flow coordinate/geometric equality, so downstream scalar selectors can
consume manifold-side `EqOn` gluing data directly. The same smooth-realization
layer now has indexed source-cover companions
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue`
and
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue`,
which choose the finite-cover readout internally and derive the lifted
target-chart input from Picard ball membership, model-flow space-time
continuity, and the target-chart neighborhood condition.  The tensor route also
has the closed-cover companion
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue`,
so compact selected witnesses can keep their source cover on `Icc tmin tmax`
while the smooth-realization theorem runs on the open active time set. The
same layer now has a proof-bearing scalar-value adapter,
`targetBilinearCoordReadoutContinuousLinearMap_apply_self_eq` plus
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_correction`:
the first identifies the target-centered readout of an arbitrary Banach RHS
section at the target center, and the second turns the route's local `hvalue`
obligation into exactly two geometric identities, namely chart-RHS equals the
intrinsic Ricci-DeTurck RHS of the smooth realization and the spatial plus
tangent-map coordinate terms equal the negative intrinsic DeTurck correction at
the gauge image. The scalar adapter now uses the direct bridge
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.metricVelocity_eq_chartRHS_of_chartRHS_eq_intrinsic`,
internally, deriving the smooth metric-velocity/chart-RHS equality from the
realization equation and that pointwise chart-RHS/intrinsic-RHS identification.
The smooth-realization layer also has the narrower Lie-correction wrapper
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection`,
which derives the signed correction input from `MDiffAt` regularity of the
intrinsic DeTurck vector-field section and a coordinate identity with the
Levi-Civita derivative of `intrinsicDeTurckGaugeField`. The underlying
raw-gauge bridge is
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_lieCorrection`,
which isolates the remaining coordinate chain-rule calculation from the
DeTurck sign algebra. The raw bridge now also has the closed-ball Picard
specialization
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin`,
and the smooth-realization scalar selector exposes it via
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin`.
The route also now has fixed-center `EqOn` specializations:
`Diffeomorph3GaugeFlowOn.lieCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_nhdsWithin`,
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_nhdsWithin`,
and
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_nhdsWithin`.
Those routes replace the pre-sign Lie-correction hypothesis with the concrete
closed-ball Picard derivative, relative base-coordinate equality, strict active
ball membership, raw gauge-field equality, and a local fixed-chart `EqOn`
model-field identification. The same interface is available at the tensor route level through
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection`
and its closed-source-cover companion
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection`,
so callers can pass indexed readout/Picard derivative data, chart-RHS
identification, `MDiffAt` regularity, and the pre-sign Lie-correction identity
directly to obtain the gauge-corrected pullback time derivative.
The exact `MDiffAt` hypothesis in that interface is now supplied in the
Levi-Civita-background case by
`intrinsicDeTurckVectorField_mdiffAt_of_isLeviCivita`, with the global wrapper
`intrinsicDeTurckVectorField_mdiff_of_isLeviCivita`: the intrinsic DeTurck
vector field is identified with the zero section through
`intrinsicDeTurckVectorField_eq_zero_of_isLeviCivita`, and zero-section
regularity closes the differentiability input. This is the proof-bearing
regularity bridge needed by the Lie-correction sign route when the background
connection is already Levi-Civita for the evolving metric. The general
non-Levi-Civita/background regularity theorem for
`intrinsicDeTurckVectorField` remains open and is still required for the full
chosen-background gauge-flow construction.
At the reverse-gauge layer, the corresponding actual gauge-field API is now
also explicit:
`intrinsicDeTurckGaugeField_eq_zero_of_isLeviCivita`,
`intrinsicDeTurckGaugeField_mdiffAt_of_isLeviCivita`,
`intrinsicDeTurckGaugeField_mdiff_of_isLeviCivita`, and the
Levi-Civita-specialized Lie-correction theorem
`intrinsicDeTurckGaugeField_lieCorrection_eq_neg_intrinsicDeTurckCorrection_of_isLeviCivita`.
The raw spatial/tangent correction bridge now also has the corresponding
Levi-Civita-background route
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_lieCorrection_of_isLeviCivita`,
so callers no longer need to pass a separate DeTurck-vector `MDiffAt` package
in that case; the chart-level Lie-correction identity remains the real
coordinate calculation.
The same discharge is now exposed at the smooth-realization scalar-selector
level by
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_isLeviCivita`,
which keeps the chart-RHS and coordinate Lie-correction hypotheses explicit
while deriving the DeTurck-vector regularity input from the Levi-Civita
background hypothesis.
Independently of the Levi-Civita zero case, the DeTurck layer now has the
general conditional Riesz bridge
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiff_intrinsicDeTurckOneForm`
with the chart-local form
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiffOn_intrinsicDeTurckOneForm`
and the global wrapper
`intrinsicDeTurckVectorField_mdiff_of_contMDiff_intrinsicDeTurckOneForm`:
`C¹` regularity of the traced intrinsic DeTurck one-form at a fixed time
implies the required differentiability of the raised DeTurck vector-field
section. What remains for the full non-Levi-Civita/background case is to prove
that local one-form regularity from the connection-difference trace
construction and the available smoothness of the metric and background
connection.
That local one-form regularity now has a first componentwise packaging step:
`intrinsicDeTurckOneForm_contMDiffOn_of_localFrame_apply` reduces `C¹`
one-form-section regularity on a chart-local open set to scalar smoothness of
the local-frame evaluations `ω_x(e_i(x))`. The remaining hard input is therefore
the connection-difference trace calculation proving those scalar component
facts from the chosen Levi-Civita family and the background connection.
The trace calculation has now been exposed at the local-frame level:
`intrinsicDeTurckOneForm_apply_localFrame_eq_sum_localFrame_coeff` rewrites the
scalar evaluation as a finite sum of diagonal connection-difference
coefficients, and
`intrinsicDeTurckOneForm_contMDiffOn_of_connectionDifference_coeff` plus
`intrinsicDeTurckVectorField_mdiffAt_of_connectionDifference_coeff` package
`C¹` regularity of those diagonal coefficients into one-form and raised-vector
regularity. The next proof obligation is to derive those coefficient
smoothness hypotheses from the slicewise `ContMDiffCovariantDerivative`
packages for the chosen Levi-Civita and background connections.
That derivation is now also packaged locally:
`connectionDifference_localFrame_coeff_contMDiffOn` proves the smoothness of
local-frame coefficients of a difference of two tangent covariant derivatives
from `ContMDiffCovariantDerivativeOn` hypotheses, and the intrinsic wrappers
`intrinsicDeTurckOneForm_contMDiffOn_of_contMDiffCovariantDerivativeOn` and
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivativeOn` consume
the chosen-Levi-Civita/background slices directly. The residual gap is no
longer the trace algebra, but the local production of those
`ContMDiffCovariantDerivativeOn` packages for the relevant slices in the
chart-local gauge-flow setting.
The fixed-time route has also been globalized for smooth background slices:
`intrinsicDeTurckVectorField_mdiffAt_of_contMDiffCovariantDerivative_background`
and
`intrinsicDeTurckVectorField_mdiff_of_contMDiffCovariantDerivative_background`
derive the DeTurck vector-field differentiability directly from
`ContMDiffCovariantDerivative (background t) 1`; the chosen Levi-Civita slice is
localized automatically using the existing smooth-slice theorem.
The Lie-correction bridge now consumes this route via
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_lieCorrection_of_contMDiffCovariantDerivative_background`,
so the raw spatial/tangent correction theorem can discharge the DeTurck-vector
`MDiffAt` input from slicewise smoothness of the background connection, not only
from the Levi-Civita zero case.
The smooth-realization route now exposes the same smooth-background discharge at
the chart-RHS Lie-correction and tensor time-regularity layers:
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_contMDiffCovariantDerivative_background`,
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_contMDiffCovariantDerivative_background`,
and
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_contMDiffCovariantDerivative_background`.
These keep the chart-RHS, readout/Picard derivative, and coordinate
Lie-correction inputs explicit while removing the separate DeTurck-vector
`MDiffAt` hypothesis from callers with smooth background slices.
The gauge-flow sign convention has also been
aligned with this scalar target: `intrinsicDeTurckGaugeField` is now the
negative intrinsic DeTurck vector field, so differentiating the pullback gauge
subtracts exactly the intrinsic DeTurck correction appearing in
`gaugeCorrectedPullbackVelocityOfDiffeomorph3Gauge`. The
readout/mem-ball route now also
has closed-interval local-gluing readout lemmas, a source-coordinate Picard
derivative package, component and raw source-derivative endpoints, and the
fixed-IVP indexed data bridge.  The selected raw gauge-flow layer now also has
the compact-witness endpoint
`SelectedIntrinsicDeTurckGaugeFlowExistence.hasTimeDerivativeOn_Ioo_of_variationalTangentMapComponents_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_of_timeSet_eq_Icc`,
and the theorem-family analogue, which combine a closed-interval finite source
cover, selected local readout equality, model-flow spatial derivative data, and
the lifted-model/value hypotheses into the selected tensor time derivative.
The restricted-symmetric endpoint
`SelectedIntrinsicDeTurckGaugeFlowExistence.hasTimeDerivativeOn_Ioo_of_variationalTangentMapComponents_readout_mem_ball_lifted_eqOn_hasFDerivAt_of_solution_eq_restrictSymmetricIcc`
now derives the selected `timeSet = Icc` certificate internally, so compact
selected witnesses can feed the tensor route directly once the readout-local
derivative data package has been built.
Its compact finite-cover companion
`SelectedIntrinsicDeTurckGaugeFlowExistence.hasTimeDerivativeOn_Ioo_of_variationalTangentMapComponents_readout_mem_ball_iUnion_Icc_cover_source_hasFDerivAt_lifted_eqOn_of_solution_eq_restrictSymmetricIcc`
does the same for callers that already carry the source-cover derivative
package.
The theorem-family restricted companion exposes the same handoff after fixing
one `ivp` inside a selected existence family.
The Picard-estimate-specialized endpoints
`SelectedIntrinsicDeTurckGaugeFlowExistence.hasTimeDerivativeOn_Ioo_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_of_timeSet_eq_Icc`
and the theorem-family analogue now discharge that model-flow spatial
derivative input directly from the state-preserving component closed-ball
continuity estimates, leaving the compact source cover/readout and the
lifted-model/value hypotheses as the selected-route inputs. The fixed-IVP
restricted-symmetric companion ending in
`_of_solution_eq_restrictSymmetricIcc` now derives the selected closed interval
certificate internally for the same state-preserving Picard-estimate route.
The selected compact-constructor wrapper
`SelectedIntrinsicDeTurckGaugeFlowExistence.exists_restrictSymmetricIcc_hasTimeDerivativeOn_Ioo_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_of_compact_iUnion_openPreimage_localGluingData`
now goes one step further: it constructs the restricted selected raw gauge-flow
witness, consumes the finite source cover/readout certificates internally, and
leaves the remaining state-preserving Picard and lifted local tensor derivative
obligations in the `IccStatePreservingTensorDerivativeData` package.
The fixed-IVP compact endpoint now also has a same-witness combined form,
`SelectedIntrinsicDeTurckGaugeFlowExistence.exists_restrictSymmetricIcc_hasTimeDerivativeOn_Ioo_and_spatial_tangent_correction_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_of_compact_iUnion_openPreimage_localGluingData_of_contMDiffCovariantDerivative_background`,
which selects one restricted raw gauge-flow witness and returns both the
state-preserving tensor time-derivative continuation and the smooth-background
spatial-correction continuation for that same selected interval.
The open-interior result can now be promoted to the selected closed time set
when endpoint derivatives are available: `HasTimeDerivativeOn.of_Ioo_endpoints`
glues `Ioo` data with left/right endpoint `HasTimeDerivativeAt` facts, and the
selected fixed-IVP and theorem-family wrappers
`hasTimeDerivativeOn_of_timeSet_eq_Icc_of_Ioo_endpoints` and
`hasTimeDerivativeOn_of_solution_eq_restrictSymmetricIcc_of_Ioo_endpoints`
turn that into `HasTimeDerivativeOn` on the selected solution `timeSet`. The
same fixed-IVP and theorem-family endpoint-gluing routes now also project
directly to `PullbackMetricInnerDerivativeData`, so selected compact `Ioo`
tensor output plus endpoint tensor derivatives can feed the existing
scalar-derivative theorem-package projections without an extra manual
conversion step. The compact same-witness continuations now expose that
conversion directly as well: the fixed-IVP and theorem-family wrappers ending
in
`exists_restrictSymmetricIcc_pullbackMetricInnerDerivativeData_and_spatial_tangent_correction_of_statePreservingTensorSpatialCorrectionData_of_compact_iUnion_openPreimage_localGluingData_of_contMDiffCovariantDerivative_background`
return the selected scalar package and the spatial correction for the same
state-preserving Picard witness once the two endpoint tensor derivatives are
supplied. The selected endpoint-gluing layer also accepts endpoint
inner-product derivative facts directly, using the single-time pullback
scalar/tensor conversion to produce the tensor endpoint data internally before
returning either the full selected `HasTimeDerivativeOn` package or
`PullbackMetricInnerDerivativeData`.
The compact same-witness wrappers now have matching `endpointInner` variants,
so fixed-IVP and theorem-family compact callers can keep endpoint obligations
in scalar inner-product form all the way to the returned scalar package and
spatial correction.
They also have matching `boundary` and `boundaryInner` compact continuations,
so closed-Picard callers can provide derivative data uniformly at
closed-interval points outside the open interior rather than splitting it into
left and right endpoint hypotheses.
The selected fixed-IVP and theorem-family gluing layers now also accept
boundary-shaped endpoint data, both as tensor `HasTimeDerivativeAt` facts and
as scalar inner-product derivatives, and return either the full selected tensor
time-regularity package or `PullbackMetricInnerDerivativeData`.
The theorem-family analogue now performs the same same-witness assembly
uniformly over all initial-value problems, returning one selected gauge-flow
family with both per-IVP continuations.
The joint package
`SelectedIntrinsicDeTurckGaugeFlowExistence.IccStatePreservingTensorSpatialCorrectionData`
now ties those two local inputs to the same state-preserving Picard witness:
its spatial-correction field is indexed by the `α` already selected by the
tensor derivative package.  The fixed-IVP and theorem-family compact wrappers
ending in
`exists_restrictSymmetricIcc_hasTimeDerivativeOn_Ioo_and_spatial_tangent_correction_of_statePreservingTensorSpatialCorrectionData_of_compact_iUnion_openPreimage_localGluingData_of_contMDiffCovariantDerivative_background`
therefore return a single dependent continuation that produces both the tensor
time derivative and the spatial correction for that same Picard witness.
The theorem-family compact wrapper
`SelectedIntrinsicDeTurckGaugeFlowExistenceFamily.exists_restrictSymmetricIcc_hasTimeDerivativeOn_Ioo_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_of_compact_iUnion_openPreimage_localGluingData`
now performs the same selected compact construction uniformly over all initial
value problems, returning one selected existence family and per-IVP tensor
continuations with only the `IccStatePreservingTensorDerivativeData` obligation
left.
The theorem-family restricted-symmetric companion mirrors this after fixing one
selected `ivp`, so family-level compact Picard callers can avoid restating the
closed-interval certificate too.
The smooth-realization tensor route has the matching closed-interval finite-cover
wrapper
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_geometricValue`,
so Banach finite-cover readouts can also consume the selected Picard estimates
without restating the source-coordinate derivative hypothesis.
This specialization now reaches the gauge-corrected smooth-background endpoint
as well:
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_lieCorrection_of_contMDiffCovariantDerivative_background`
combines the Picard derivative discharge with the chart-RHS and Lie-correction
scalar adapter.
The compact local-gluing existence layer now retains those selected certificates
too:
`SelectedIntrinsicDeTurckGaugeFlowExistence.exists_restrictSymmetricIcc_with_finiteSubcover_Icc_subset_cover_readout_of_compact_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
constructs the restricted selected raw gauge-flow witness while preserving the
finite source subcover, the closed-interval subset proof, and the selected
local readout equality.
The remaining dynamic obligations are therefore narrowed to supplying those
compact-witness cover/readout certificates from the selected gauge-flow
construction, supplying the lifted manifold equality and target-membership facts
for the exact target charts selected by the time-derivative route, and proving
the spatial/tangent correction identity from the selected gauge-flow/PDE construction. For the
model-field part of that last item, the helper
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_tangentCoordChange_of_eventuallyEqWithin_base_of_eqOn_nhdsWithin`
now turns the natural local `EqOn` statement for `f t` around the fixed chart
center `(extChartAt I p) p` into the `hfCoord` eventual equality at the active
Picard point `α.flow (xE, t)`, using the relative base-coordinate equality to
transport the neighborhood. The closed-ball `Df`, Lie-correction, signed
correction, and smooth scalar routes now consume that fixed-center `EqOn`
form directly, so the remaining local-field obligation can be stated at the
fixed chart center selected by the compact witness. This boundary has also
been split through
`Diffeomorph3GaugeFlowOn.model_vectorField_eqOn_tangentCoordChange_of_eqOn_vectorField_of_eventuallyEq_along_maps3_nhdsWithin`:
if the Picard model field is locally equal to the fixed-chart expression of the
auxiliary readout vector field, and that auxiliary field agrees with the
intrinsic DeTurck gauge field along the diffeomorphism images in the relative
time filter, then the fixed-center intrinsic `EqOn` follows. Thus the remaining
model-field proof can target the actual local Picard/vector-field readout
rather than duplicating the intrinsic DeTurck expression at every downstream
correction route. The compact local-gluing constructor now preserves this
auxiliary-field handoff too:
`Diffeomorph3GaugeFlowOn.of_Icc_subset_timeSet_timeDependent_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin_on_Icc_eqOn_of_mem_Icc`
records pointwise equality of the constructed `maps3` slice with each selected
local readout on its actual source patch, and
`Diffeomorph3GaugeFlowOn.of_Icc_subset_timeSet_timeDependent_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin_on_Icc_eventuallyEq_along_maps3_nhdsWithin`
uses that source-patch equality to turn `hYLocal` into relative-filter equality
of the auxiliary field with the target field along `maps3`. The raw compact
witness endpoint
`Diffeomorph3GaugeFlowOn.exists_Icc_gaugeFlow_with_finiteSubcover_Icc_subset_cover_readout_auxiliaryEqAlong_of_compact_timeSet_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_timeSet_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
and the selected fixed-IVP endpoint
`SelectedIntrinsicDeTurckGaugeFlowExistence.exists_restrictSymmetricIcc_with_finiteSubcover_Icc_subset_cover_readout_auxiliaryEqAlong_of_compact_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
now return that auxiliary-along-flow equality alongside the selected finite
source cover and readout equality. The adapters
`SelectedIntrinsicDeTurckGaugeFlowExistence.timeSet_eq_Icc_of_solution_eq_restrictSymmetricIcc`
and
`SelectedIntrinsicDeTurckGaugeFlowExistence.auxiliaryEqAlong_of_solution_eq_restrictSymmetricIcc`
transport the selected construction's explicit `Icc` time-set and auxiliary
equality certificates to the selected solution time-set shape consumed by the
correction routes; the route-shaped constructor
`SelectedIntrinsicDeTurckGaugeFlowExistence.exists_restrictSymmetricIcc_routeData_with_finiteSubcover_Icc_subset_cover_readout_auxiliaryEqAlong_of_compact_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
returns those transported certificates directly. The companion adapters
`localGluingData_subtype`,
`continuousWithinAt_Icc_subtype_of_solution_eq_restrictSymmetricIcc`, and
`hasDerivWithinAt_Icc_subtype_of_solution_eq_restrictSymmetricIcc` restrict the
constructor's ambient local gluing, continuity, and chart-derivative inputs to
the selected finite subcover and closed interval, while
`mem_timeSet_of_solution_eq_restrictSymmetricIcc`,
`timeSet_subset_Icc_of_solution_eq_restrictSymmetricIcc`,
`x0Local_subtype_of_solution_eq_restrictSymmetricIcc`,
`rLocal_subtype_of_solution_eq_restrictSymmetricIcc`, and
`ballLocal_subtype_of_solution_eq_restrictSymmetricIcc` carry the ambient
closed-ball Picard centers, radii, and state certificates through the same
selected restriction. The model-ODE layer has the matching
`localFlowSolution_subtype_of_solution_eq_restrictSymmetricIcc`,
`modelLiftedEqOn_subtype_of_solution_eq_restrictSymmetricIcc`, and
`modelTarget_subtype_of_solution_eq_restrictSymmetricIcc` adapters, so selected
finite-subcover Picard output can keep its local flow, lifted equality, and
target-chart membership certificates without rebuilding them by hand. The
selected correction layer now uses those adapters in the interior compact
caller
`SelectedIntrinsicDeTurckGaugeFlowExistence.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_Icc_cover_readout_localGluingData_ambientLocalFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_Ioo_of_solution_eq_restrictSymmetricIcc`,
which accepts ambient selected-solution Picard model data and transports it to
the finite subcover before entering the local Picard correction route. Its
smooth-background companion ending in
`_of_contMDiffCovariantDerivative_background` also transports the ambient
background regularity before entering that route. The
`SelectedIntrinsicDeTurckGaugeFlowExistence.exists_restrictSymmetricIcc_routeData_with_finiteSubcover_Icc_subset_cover_readout_localData_auxiliaryEqAlong_of_compact_iUnion_openPreimage_localGluingData_of_local_hasDerivWithinAt_extChartAt_eval_self_of_vectorField_eq_nhdsWithin`
packages all of those route-shaped certificates together. The selected
time-derivative layer now has the compact smooth-background correction wrapper
`SelectedIntrinsicDeTurckGaugeFlowExistence.exists_restrictSymmetricIcc_spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_compact_iUnion_openPreimage_localGluingData_of_localFlowSolution_lifted_model_eqOn_of_contMDiffCovariantDerivative_background`:
it constructs the restricted selected raw gauge-flow witness, consumes the
finite cover/readout/local-gluing/continuity/derivative/auxiliary certificates
internally, and leaves callers with the selected-interval
`IccSpatialCorrectionLocalData` package for the remaining Picard ball,
lifted-model equality, and target-chart obligations.
The theorem-family analogue
`SelectedIntrinsicDeTurckGaugeFlowExistenceFamily.exists_restrictSymmetricIcc_spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_compact_iUnion_openPreimage_localGluingData_of_localFlowSolution_lifted_model_eqOn_of_contMDiffCovariantDerivative_background`
now packages that same smooth-background correction handoff uniformly over all
initial-value problems, using the family route-data constructor internally and
leaving only per-IVP `IccSpatialCorrectionLocalData` obligations.
The selected raw flow
now also exposes the
pointwise correction-route `hXeq` certificate as
`SelectedIntrinsicDeTurckGaugeFlowExistence.flow_vectorField_eq_intrinsicDeTurckGaugeField`,
since its driving vector field is definitionally the intrinsic DeTurck gauge
field. The selected correction layer now consumes that certificate directly via
`SelectedIntrinsicDeTurckGaugeFlowExistence.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`,
so selected local Picard/gluing correction routes no longer require callers to
thread the tautological `hXeq` hypothesis. The selected smooth-background
variant ending in `_of_contMDiffCovariantDerivative_background` now also
derives the DeTurck-vector `MDiffAt` input from slicewise
`ContMDiffCovariantDerivative (background t) 1`, via
`SelectedIntrinsicDeTurckGaugeFlowExistence.deTurckVector_mdiffAt_of_contMDiffCovariantDerivative_background`;
the restricted-symmetric transport
`SelectedIntrinsicDeTurckGaugeFlowExistence.deTurckVector_mdiffAt_of_solution_eq_restrictSymmetricIcc_of_contMDiffCovariantDerivative_background`
lets compact callers keep that smooth-background hypothesis on the ambient
chosen solution and move it to the selected closed interval when needed.
The selected correction layer also has an interior compact-readout route,
`SelectedIntrinsicDeTurckGaugeFlowExistence.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_Icc_cover_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_Ioo_of_timeSet_eq_Icc`,
and its smooth-background variant ending in
`_of_contMDiffCovariantDerivative_background`. These wrappers match the compact
constructor handoff more closely: the finite source cover is supplied on the
closed selected `Icc`, readout is needed only on the open `Ioo`, and the local
Picard/gluing data remain indexed by the selected closed time set while the
proof internally restricts the raw flow to the open interior.
The remaining local-field proof is
therefore the Picard-model-to-auxiliary fixed-chart input, not the flow equality
from the auxiliary field to the intrinsic field. This input can now be supplied
in the more geometric centered-chart pullback form: the derivative layer has
`Diffeomorph3GaugeFlowOn.model_vectorField_eqOn_tangentCoordChange_of_eventuallyEq_mpullbackWithin`
and
`Diffeomorph3GaugeFlowOn.model_vectorField_local_eqOn_tangentCoordChange_of_eventuallyEq_mpullbackWithin`,
which convert local eventual equality of `f t` with
`VectorField.mpullbackWithin ... (Y t)` through `(extChartAt I p).symm` into
the explicit `tangentCoordChange` `EqOn` shape used downstream. The derivative
layer now also exposes the derivative-uniqueness entry point
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_mpullbackWithin_of_common_derivatives`
and its `EqOn` package
`Diffeomorph3GaugeFlowOn.model_vectorField_eqOn_tangentCoordChange_of_common_derivatives`:
if a common local coordinate curve has within-time-set derivative `f t y` from
the Picard model and the auxiliary fixed-chart velocity from the manifold
readout, then the local Picard-model-to-auxiliary `mpullbackWithin` equality
follows directly. The derivative-view layer has the complementary chart
transition
`hasDerivWithinAt_extChartAt_eval_of_hasDerivWithinAt_extChartAt_eval_self`,
which transports centered readout derivatives to any fixed chart whose source
contains the endpoint. Combining that with a `LocalGluingData` inverse slice,
the derivative layer now has
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_mpullbackWithin_of_localGluingData_common_derivatives`,
which derives the same local `mpullbackWithin` equality from local inverse
readouts, centered auxiliary derivatives, and Picard/model derivatives in the
fixed chart. Its model-curve wrapper
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_mpullbackWithin_of_localGluingData_eventuallyEq_modelDerivative`
replaces the fixed-chart derivative input by eventual equality with any model
coordinate curve whose derivative is `f t y`, matching the natural Picard
handoff. The Picard-flow specialization
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_mpullbackWithin_of_localGluingData_localFlowSolution`
uses `ModelGaugeFlowODE.LocalFlowSolution.hasDerivWithinAt` and `initial_eq`
when the local Picard flow is anchored at the current time, so the remaining
model input is just fixed-chart eventual equality with `α.flow y`. This now has
the indexed finite-cover handoff
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_iUnion_readout_mpullbackWithin_of_localGluingData_localFlowSolution`,
which packages current-time anchored local Picard flows, local gluing data,
source persistence, model/readout equality, and centered auxiliary derivatives
into exactly the `hfLocal` pullback-field hypothesis consumed by the compact
correction theorem. The source-persistence input can now itself be discharged
from local readout time-continuity via
`Diffeomorph3GaugeFlowOn.localGluingData_source_extChartAt_mem_nhdsWithin_of_continuousWithinAt`
and the indexed package
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_iUnion_readout_mpullbackWithin_of_localGluingData_localFlowSolution_of_continuousWithinAt`,
matching compact local-gluing constructors that already retain
`ContinuousWithinAt` readouts. The patch-local Picard/model equality input can
now also be supplied as an `EqOn` statement on the Picard time set:
`Diffeomorph3GaugeFlowOn.iUnion_readout_model_eventuallyEq_nhdsWithin_of_eqOn`
converts that readout-local `EqOn` into the exact within-filter eventual
equality. The lifted-input bridge
`Diffeomorph3GaugeFlowOn.iUnion_readout_model_eqOn_of_lifted_model_eqOn`
pushes a manifold-side lifted Picard/readout equality through the selected
target chart, using target membership of the model values to produce that
readout-local chart `EqOn`; its filter-level companion
`Diffeomorph3GaugeFlowOn.iUnion_readout_model_eventuallyEq_nhdsWithin_of_lifted_model_eqOn`
provides the corresponding within-filter equality directly. The matching
model-vector-field wrappers
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_iUnion_readout_mpullbackWithin_of_localGluingData_localFlowSolution_of_lifted_model_eqOn`
and
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_iUnion_readout_mpullbackWithin_of_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn`
feed lifted equality plus target membership into the indexed local
Picard/local-gluing handoff. The chart-`EqOn` wrappers
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_iUnion_readout_mpullbackWithin_of_localGluingData_localFlowSolution_of_eqOn`
and
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_iUnion_readout_mpullbackWithin_of_localGluingData_localFlowSolution_of_continuousWithinAt_of_eqOn`
still combine chart `EqOn` with the indexed local Picard/local-gluing handoff,
optionally deriving source persistence from readout continuity. The compact correction
layer also has
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_eventuallyEq_along_maps3_nhdsWithin`,
which combines that indexed Picard/local-gluing discharge with the existing
finite-cover readout correction route. Its
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`
companion consumes the natural Picard output shape directly: source persistence
comes from local readout continuity and the model/readout identification is
only a patch-local `EqOn` on the Picard time set. Its lifted-input companion
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`
uses the same route after converting lifted equality plus target membership to
that patch-local chart `EqOn`. The derivative layer also has
`Diffeomorph3GaugeFlowOn.model_vectorField_eqOn_tangentCoordChange_of_iUnion_readout_eqOn`,
which transfers a patch-local Picard-model/auxiliary-field `EqOn` from the
selected local readout center `Fₗ i t x` to the actual glued-flow center
`(G.maps3 t) x` using the retained finite source cover and local readout
equality. Its composed intrinsic companion
`Diffeomorph3GaugeFlowOn.model_vectorField_eqOn_tangentCoordChange_intrinsic_of_iUnion_readout_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`
then combines that transferred patch-local model-field proof with the retained
auxiliary-along-flow equality. The active-Picard-point companion
`Diffeomorph3GaugeFlowOn.model_vectorField_eventuallyEq_tangentCoordChange_intrinsic_of_iUnion_readout_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`
additionally uses the base-coordinate equality to transport the resulting
neighborhood to `α.flow (xE, t)`, producing the `hfCoord` shape consumed by the
closed-ball `Df` route. The signed correction layer
also has the direct auxiliary-field adapter
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_vectorField_of_eventuallyEq_along_maps3_nhdsWithin`,
which composes the auxiliary fixed-chart `EqOn` and the auxiliary-along-flow
certificate into the intrinsic fixed-chart `EqOn` before entering the existing
closed-ball correction route. Its compact-witness companion
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`
first uses the retained finite source cover and selected local readout
equality to transport the patch-local Picard-model/auxiliary-field `EqOn` to
the glued-flow chart center, then applies that same auxiliary-field correction
adapter. Its centered-chart pullback companion
`Diffeomorph3GaugeFlowOn.spatial_tangent_correction_eq_neg_intrinsicDeTurckCorrection_of_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_mpullbackWithin_of_eventuallyEq_along_maps3_nhdsWithin`
first converts the patch-local `mpullbackWithin` equality into that `EqOn`
form, then follows the same compact finite-cover/readout route. The
smooth-realization scalar layer has the
matching auxiliary-field endpoint
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_eqOn_vectorField_of_eventuallyEq_along_maps3_nhdsWithin`,
which derives the intrinsic fixed-chart `EqOn` from the auxiliary model-field
`EqOn` plus the retained along-flow certificate before applying the existing
closed-ball scalar route. Its compact-witness companion
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`
first transports the patch-local Picard-model/auxiliary-field `EqOn` through
the selected finite source cover and local readout equality, then applies the
same scalar auxiliary-field route. Its local Picard/gluing counterpart
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_eventuallyEq_along_maps3_nhdsWithin`
first derives that patch-local `EqOn` from current-time anchored
`ModelGaugeFlowODE.LocalFlowSolution` data and `LocalGluingData`, so smooth
realization scalar routes no longer need callers to hand-convert local Picard
output to the finite-cover `EqOn` field hypothesis. Its
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`
companion consumes the same natural Picard output shape as the raw compact
correction route: local readout continuity supplies source persistence and a
patch-local `EqOn` on the Picard time set supplies the model/readout equality.
Its lifted-input companion
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.variational_hvalue_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_model_hasFDerivWithinAt_of_eventuallyEqWithin_of_iUnion_readout_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_eventuallyEq_along_maps3_nhdsWithin`
accepts the selected Picard output before chart cancellation, again requiring
target membership of the model values. The tensor-level companion
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn`
now feeds that lifted-input scalar correction identity into the indexed
readout-lifted `HasTimeDerivativeOn` route, so the smooth gauge-corrected
tensor endpoint can use local Picard/gluing correction data instead of an
explicit Lie-correction scalar hypothesis. Its state-preserving closed-ball
specialization
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn`
now derives the source-coordinate derivative from the selected Picard estimate
package while accepting the compact closed-interval source cover. Its
intrinsic-gauge specialization
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_of_variationalTangentMap_readout_mem_ball_iUnion_source_hasFDerivAt_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_intrinsicDeTurckGaugeField`
also removes the separate pointwise vector-field equality when the raw flow is
already driven by the smooth realization's intrinsic DeTurck gauge field, and
its state-preserving closed-ball variant
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_intrinsicDeTurckGaugeField`
combines both discharges. A smooth-background variant,
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_closedBall_localGluingData_localFlowSolution_of_continuousWithinAt_of_lifted_model_eqOn_of_intrinsicDeTurckGaugeField_of_contMDiffCovariantDerivative_background`
replaces the remaining DeTurck-vector `MDiffAt` input with slicewise
`ContMDiffCovariantDerivative (background t) 1`. The state-preserving smooth
route now also has the direct signed-correction entry point
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.hasTimeDerivativeOn_ofProductStatePreservingComponentClosedBallContinuityEstimates_restrict_readout_mem_ball_iUnion_Icc_cover_lifted_eqOn_interior_cover_target_overlap_Ioo_gaugeCorrectedPullbackVelocity_of_chartRHS_correction`,
so a previously proved `-intrinsicDeTurckCorrection` scalar identity can feed
the tensor derivative route without restating a pre-sign Lie-correction
hypothesis. The smooth-realization route also has the specialized bridge
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_interior_cover_target_overlap_Ioo_geometricValue`,
which combines the interior-cover scalar selector with that variational
tangent-map identification and states the remaining scalar identity in actual
pushed-forward tangent-vector slots using `Df t (α.flow (xE, t))`. Its
fixed-chart-gluing companion,
`BanachEvolutionLocalSolutionIn.SmoothIntrinsicDeTurckRealization.coordinatePullbackMetricComponentDerivativeOn_of_variationalTangentMap_fixedChartModel_eqOn_interior_cover_target_overlap_Ioo_geometricValue`,
derives the tangent-map identification from local manifold `EqOn` gluing data
and the variational model-flow spatial derivative before entering the same
component package. At the cover-construction level,
`exists_compact_subset_interior_cover_inter_open` chooses an index and compact
overlap from an interior-covering compact family and an open target patch, while
`exists_compacts_interior_cover_of_finite_open_cover` and its compact-space
`univ` variant record the standard shrinking step: a finite open cover of a
compact set can be replaced by compact subordinate pieces whose interiors still
cover. The compatibility bridges
`iUnion_compacts_eq_univ_of_iUnion_interior_eq_univ` and
`compactSpace_of_finite_compact_cover` let that stronger cover data feed the
existing ordinary `hcover` finite-cover APIs and expose compactness carried by a
finite compact cover of `univ`. The refinement bridge
`exists_interior_compact_cover_with_intersections_of_compact_cover` now turns an
ordinary finite compact chart cover subordinate to finite open patches into an
interior-covering compact cover subordinate to the same patches, with canonical
pairwise compact overlaps supplied by `compactCoverIntersections`. Its
trivialization-base specialization
`exists_interior_compact_trivialization_cover_with_intersections_of_compact_cover`
packages the same refinement directly for finite families of
`Bundle.Trivialization.baseSet`s. The
remaining non-identity gauge work is to prove and supply those tangent-map and
velocity identities from the selected gauge-flow/PDE construction, use the
refined chart data end to end inside the selected Banach chart/gauge-flow
constructions, and then integrate these route theorems with the full
local-existence and PDE estimate layers; the selected/raw intrinsic
vector-field equality itself is now an internal route input rather than a
remaining caller obligation.
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
These endpoint-closed metric-locus bridges now rely on the finite-cover
`ContinuousSectionSpace` completeness instance directly, so downstream chart
constructors no longer have to thread an explicit ambient `hcomplete`
argument through this leaf module.
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
arguments. Raw intrinsic DeTurck gauge-flow witnesses now also expose the
centered preferred-chart and primitive intrinsic derivative packages directly via
`Diffeomorph3GaugeFlowOn.toIntrinsicChartDerivativeOn`,
`Diffeomorph3GaugeFlowOn.toIntrinsicDerivativeOn`,
`Diffeomorph3GaugeFlowOn.toIntrinsicChartDerivativeAtOn`, and
`Diffeomorph3GaugeFlowOn.toIntrinsicDerivativeAtOn`, so downstream arguments can
consume the named centered derivative interfaces without first choosing an
auxiliary fixed chart. The fixed-IVP, theorem-family, and selected-solution raw
existence bundles now lift those same centered packages, including the
ordinary-at-time variants under the open-time-set neighborhood hypothesis and
the explicit `Ioo` open-Picard specialization; the geometric fixed-IVP and
theorem-family `ChosenIntrinsicDeTurckDiffeomorph3GaugeFlow` bundles expose the
same centered readouts through the raw-adapter route, so endpoint arguments can
stay at the geometric gauge-flow interface. The derivative layer now has the
matching proof-bearing
input package: `Diffeomorph3IntrinsicGaugeFlowFixedChartDerivativeOn` and its
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
ODE data once that field is identified with the reverse intrinsic DeTurck gauge field
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
control, now also with matrix-valued `C^{0,α}` submodule entry projection and
entrywise assembly maps, quantitative entrywise vector/matrix packaging and
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
It also exposes the same paired smooth-realization/reverse-encoding fiber for
any already-chosen global Banach solution, matching the existing interval
fixed-solution readout.
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
`ℝ≥0` by callers. It now also accepts time-dependent finite coordinate-family
`LipschitzOnWith` readouts directly, using the continuous-section
finite-cover theorem to produce the pointwise coordinate-distance hypothesis
for the preferred-cover chart constructor. This is a
coordinate Lipschitz bridge toward the fibrewise RHS hypothesis above, not a
Schauder estimate or the actual Banach-chart construction.
The first function-space module for this item is now
`AnalyticPDE/Parabolic/FunctionSpace.lean`: it packages
single-radius `ParabolicC0AlphaNormLe` balls from bounded plus Holder
constants and proves the expected algebra, restriction, continuity, and uniform
continuity rules, including finite sums, finite Pi-valued packaging,
continuous-linear images, products, reciprocal/division closure under pointwise
lower bounds, product and reciprocal differences, scalar-function actions,
curried bilinear maps, operator-valued application and their difference forms,
and Lipschitz nonlinear composition, including closed norm-ball forms. It
also packages `ParabolicC0AlphaOn` as a real submodule of all time-space
functions, proves restriction to smaller domains, continuous-linear value
composition, product-valued pairing, and finite Pi projection/assembly as
linear maps, and gives positive-exponent linear readouts into `ContinuousMap`s
on compact time-space pieces and compact piece families, with determination on
the covered set and injectivity for global compact-piece covers. This is the
finite-cover
`C^{0,α}` analogue of the existing continuous-section compact-readout layer;
compact readout sup-norm differences, including the finite product readout
norm, are now bounded by the same single-radius `C^{0,α}` difference control,
and by sup-bound-only difference estimates; finite Pi-valued `C^{0,α}` functions
now also have componentwise summed-radius pointwise norm/distance readouts and
compact-piece, finite compact-family, and linear finite-cover readout estimates,
with matching `LipschitzOnWith` forms. Pairwise norm-ball and sup-bound
difference estimates now promote directly to `LipschitzOnWith` estimates for
single compact-piece, finite compact-family, and linear finite-cover readouts,
with finite compact-family `LipschitzOnWith` estimates unpacking to pointwise
compact-coordinate distance bounds. Those time-space compact-coordinate bounds
now also restrict to fixed-time spatial compact readouts whenever the chosen
time-space compact pieces cover each requested time slice, giving the direct
bridge from parabolic readouts to spatial Banach-chart coordinate estimates.
Single-radius `C^{0,α}` norm balls now also project directly to exact-radius
parabolic Holder control, including fixed-space time-slice estimates with
exponent `α / 2` and fixed-time spatial Holder estimates with exponent `α`;
the same readouts have product-domain subset forms for `timeSet × spaceSet`
subdomains.
The compact-piece layer now also constructs the canonical product pieces
`Kt × Kxᵢ`, with an `Icc t₀ T` specialization, and proves both their domain
containment criterion and the fixed-time spatial slice cover property. It also
identifies the union of those product pieces with `Kt × ⋃ᵢ Kxᵢ`, including the
closed-interval and spatial-cover specializations needed for readout
determination on interval product domains. Compact-family readout equality now
also has a subset form, with direct `Kt × U` and `Icc t₀ T × U` product-domain
determination lemmas from a spatial compact-family cover of `U`. The lower
submodule now also has a finite-cover value seminormed additive-group and real
normed-space structure induced by the compact-family readout, plus a separated
normed additive-group structure when the compact pieces cover all time-space;
the norm and distance are definitionally the compact-family readout norm and
distance, the induced readout is now named as an isometry (and hence directly
nonexpansive and `1`-Lipschitz) in both the seminormed and separated all-cover
structures, and the finite-cover
value seminorm now has direct fixed-time spatial readout estimates and
direct/symmetric closed-ball readouts from `C^{0,α}` difference balls,
including finite-coordinate finite-Pi variants with radii `Kᵢ * R` and the
matching `LipschitzOnWith` forms with the summed `ℝ≥0` component constant, plus
the separated all-cover form. The lower readout layer now also factors the
global time-space finite-cover to fixed-time spatial-slice cover conversion as
a reusable bridge, with generic all-cover fixed-time spatial readout handoffs
for compact-coordinate estimates and `LipschitzOnWith` readouts.
`AnalyticPDE/Parabolic/HigherFunctionSpace.lean` now begins the coordinate
`C^{2+α,1+α/2}` layer: it defines time and spatial slices, packages a genuine
parabolic second jet with time, spatial, and second-spatial derivative
witnesses on those slices, and defines a single-radius
`ParabolicC2AlphaNormLe` predicate whose radius dominates the value, spatial
derivative, spatial Hessian, and time-derivative `C^{0,α}` norm-ball controls;
this higher predicate already has constant and zero constructors and is closed
under addition, finite sums, negation, subtraction, scalar multiplication, and
product-valued pairing and continuous-linear value maps with explicit radius
bounds, with a matching product-state difference estimate from component
difference controls. Chosen parabolic
second jets now also compose with continuous linear value maps, transforming
the time, spatial, and second-spatial derivative witnesses componentwise; they
also support componentwise subtraction and product pairing. Its
existential `ParabolicC2AlphaOn` class now forms a real submodule of all
coordinate time-space functions, is closed under product-valued pairing and
product-state differences, and continuous-linear value maps, and reads back to
`ParabolicC0AlphaOn` for the value component; the full
`C^{2+α,1+α/2}` radius also bounds the value-level `C^{0,α}` norm, and the
submodule has linear maps for continuous-linear value composition,
product-valued pairing on product submodules, and forgetful inclusion into the
existing `C^{0,α}` submodule. Higher norm balls
now also give value-level pointwise norm, distance, and exact-radius time- and
space-slice Holder readouts, including product-domain subset forms,
chosen-second-jet pointwise bounds for the value, spatial derivative, second
spatial derivative, and time derivative under one common higher radius,
positive-exponent continuity and uniform-continuity readouts, and
continuous-linear-image `C^{0,α}` norm-ball controls, plus full
higher-coordinate projections for finite Pi-valued functions and finite
Pi-valued higher norm-ball assembly from component controls, including
difference controls, with pointwise finite-Pi norm and distance bounds from
componentwise higher difference controls whose radii are linear in a shared
scalar, and corresponding compact-piece and finite compact-family readout
sup-norm bounds for finite Pi-valued higher functions; the same componentwise
finite-Pi hypotheses now also promote directly to `LipschitzOnWith` estimates
for single compact-piece, finite compact-family, and linear finite-cover
readouts with the summed NNReal component constant. The product and
continuous-linear higher radius multipliers now have explicit nonnegativity
lemmas, and finite-Pi difference controls with component radii `Kᵢ * R`
assemble into one linear-radius higher difference bound. Existential
higher membership and the higher
submodule now also expose actual time, spatial, and second-spatial derivative
witnesses with value-level `C^{0,α}` controls, without choosing a canonical
derivative map, and the norm-ball layer can coarsen one chosen second jet's
value and derivative components to the same `C^{0,α}` radius. Chosen second
jets now also identify their stored time and spatial derivatives with the
canonical `derivWithin`/`fderivWithin` on unique-differentiability slices, and
any two chosen jets have the same time, spatial, and second-spatial derivative
fields there. Consequently, the derivative-component `C^{0,α}` controls
supplied by a higher norm ball can now be transported from the existentially
selected jet to any caller-supplied second jet on such slices; the corresponding
difference theorem controls the value, spatial-derivative, second-spatial
derivative, and time-derivative differences of any two supplied jets from one
higher norm-ball bound on the value difference. The higher
submodule also has finite-Pi coordinate projection and component-assembly maps,
and inherits compact value readouts from that forgetful map: single
compact pieces, finite compact families, and the linear finite-cover readout
all have sup-norm bounds from
`ParabolicC2AlphaNormLe` difference balls, plus matching
`LipschitzOnWith` estimates for pairwise higher-norm controls; equality of all
compact-family value readouts determines higher-parabolic functions on covered
domains and gives injectivity when the compact pieces cover all time-space, and
finite compact-family value `LipschitzOnWith` estimates unpack to pointwise
compact-coordinate distance bounds. Those higher compact-coordinate distance
and finite-family `LipschitzOnWith` readouts now also restrict to fixed-time
spatial compact readouts whenever the chosen time-space compact pieces cover
each requested time slice. The higher compact-family readout determination layer
now also has subset, `Kt × U`, and `Icc t₀ T × U` product-domain forms matching
the lower `C^{0,α}` readout API. The higher submodule now mirrors the same
finite-cover value seminormed/normed carrier induced by compact-family value
readouts, including definitional norm/distance readback, a separated normed
additive-group structure for global compact-piece covers, and direct/symmetric
closed-ball readouts from higher difference balls, including finite-coordinate
finite-Pi value variants with radii `Kᵢ * R` and matching `LipschitzOnWith`
forms with the summed `ℝ≥0` component constant. This is only the value-readout
carrier, not the full `C^{2+α,1+α/2}` Banach norm or a completeness theorem.
The underlying finite-cover value readout product target is now recorded as
complete when the value model is complete; this is target-space completeness
only and not a completeness claim for the induced carrier. It also exposes
noncanonical chosen-second-jet readouts as lower
`C^{0,α}` submodule elements for the spatial derivative, second spatial
derivative, and time derivative. These wrappers only make the existential jet
choice reusable by downstream compact-readout APIs, and the same chosen
components now have compact-piece and compact-family readouts with simp
projections. Under unique-differentiability hypotheses on the time and spatial
slices, higher norm-ball controls also transport to these chosen components,
including pointwise compact-coordinate difference bounds for their readouts.
Those chosen spatial-derivative, second-spatial-derivative, and time-derivative
compact-family bounds now also lift to `LipschitzOnWith` estimates from
pairwise higher-norm controls, with pointwise compact-coordinate unpacking from
the resulting Lipschitz hypotheses. Under the same unique-slice hypotheses, the
chosen derivative compact-family readouts are now also packaged as genuine
linear maps on compact pieces contained in the domain, and each of the chosen
spatial-derivative, second-spatial-derivative, and time-derivative readouts now
induces its own finite-cover seminormed additive-group and real normed-space
structure with definitional norm and distance readback to the compact-family
readout, and each chosen-derivative finite-cover product target is recorded as
complete when the value model is complete. The value and chosen-derivative readouts are also bundled into one
combined finite-cover chosen-second-jet compact readout linear map, inducing a
single seminormed additive-group and real normed-space structure with
definitional norm and distance readback to that product readout. The combined
chosen-second-jet product readout target is now also recorded as complete when
the fiber model is complete; this is target-space completeness only and does
not assert that the induced readout image is closed. If the compact
pieces cover all time-space, the value projection makes that combined readout
injective and upgrades the induced structure to a separated normed additive
group with a paired real normed-space structure and definitional norm/distance
readback to the same product readout; the combined readout is now named as an
isometry for both the induced seminormed structure and the separated all-cover
normed structure, and for that separated norm the combined readout and each
component readout are also packaged as `1`-Lipschitz on
arbitrary state sets. Equality of the combined readout identifies the
underlying functions on any subset covered by the compact pieces. The same
combined readout has component norm and distance projection bounds for the
value, chosen spatial derivative, chosen second spatial derivative, and chosen
time derivative compact-family readouts; the combined readout and each
component readout are also packaged as `1`-Lipschitz on arbitrary state sets
for the induced seminormed structure without the all-cover separation
hypothesis, and the separated all-cover normed structure has matching component
norm and distance projection bounds. The same chosen derivative Lipschitz
readouts now also restrict to fixed-time spatial compact readouts whenever the
chosen time-space compact family covers the requested spatial slices, and the
combined seminorm now has direct fixed-time spatial value and chosen-derivative
distance estimates under the same cover hypothesis; the separated all-cover
normed structure has the matching fixed-time spatial estimates directly against
its distance for the value, chosen spatial derivative, chosen second spatial
derivative, and chosen time derivative readouts. The combined chosen-second-jet
seminorm is now connected back to the higher norm-ball API: a
`ParabolicC2AlphaNormLe` bound on `u - v` directly bounds the combined
finite-cover readout norm and hence the induced finite-cover chosen-second-jet
distance, with the same bridge available for the separated all-cover normed
carrier; pairwise higher difference bounds give `LipschitzOnWith` estimates
for maps into both structures. These bridges let current higher norm-ball
estimates feed the best available compact-family jet carrier without asserting
a full parabolic Banach norm. The value-level `ParabolicC0AlphaNormLe` and
higher `ParabolicC2AlphaNormLe` difference APIs now also expose pointwise and
product-domain distance bounds and direct/symmetric closed-ball membership
readouts, including finite-coordinate variants from linear-in-a-shared-radius
component bounds, so later positivity and chart-neighborhood arguments can
consume norm-ball difference estimates in the same metric-neighborhood shape
used by the geometric chart layer. The lower and higher finite-cover value
seminorms and the combined finite-cover chosen-second-jet seminorm now also
have direct and symmetric closed-ball readouts from those norm-ball difference
estimates, including finite-coordinate value variants, combined chosen-jet
variants with coordinate-insertion radii, and the separated all-cover normed
variants. The finite-coordinate value estimates also have `LipschitzOnWith`
forms with the summed `ℝ≥0` component constant, while the combined chosen-jet
estimates have `LipschitzOnWith` forms once an aggregate `ℝ≥0` constant bounds
the coordinate-insertion radius sum. They do not make the derivative choice
canonical or upgrade this compact-family jet seminorm into the full
`C^{2+α,1+α/2}` Banach
norm, Schauder estimate, or completeness content.
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
exact-sum norm-ball packaging. For finite coordinate models it now also reads
the first- and second-spatial derivative primitive arrays directly from chosen
metric-entry second jets, using coordinate-direction continuous-linear
readouts, and feeds those derived arrays into the direct schematic
Ricci-DeTurck `C^{0,α}` estimate, including a Pi-valued finite-family package
for finite cover products; the same bridge is available from qualitative
`ParabolicC2AlphaOn` membership when explicit radii are not needed. The
matrix submodule layer now also has a deterministic noncanonical
chosen-entry-jet version of this qualitative schematic RHS handoff, so callers
with a matrix-valued higher submodule element and a determinant lower bound no
longer have to manage the existential entry-jet family manually; the same shape
is available quantitatively under unique-differentiability of the slices, and
now also has quantitative Pi-valued finite-family forms for shared directions,
member-dependent directions, and coordinate-radius readouts, while the
qualitative finite-family forms remain available with either one shared
direction family or member-dependent direction families. The
state-space Lipschitz bridge can now be invoked directly with those
deterministic matrix-entry chosen jets, including the finite-coordinate
specialization with coordinate-radius constants and finite-family/Pi-valued
forms for family-dependent direction readouts. The same deterministic bridge
now also feeds the compact-coordinate and linear finite-cover readout maps, so
chart estimates that use higher matrix submodule elements do not need a
separate caller-supplied jet family. The
second-jet readout bridge now also accepts an arbitrary finite family of
spatial directions in any normed model, with quantitative and qualitative
finite-family packaging, so tangent-frame or chart-basis directions no longer
have to be encoded as coordinate unit vectors. Under unique-differentiability
of the time and spatial slices, caller-supplied metric-entry second jets and
entrywise higher difference balls now also give a state-space
`LipschitzOnWith` estimate for the schematic RHS read through any such finite
direction family. `HigherLocalFrameGram.lean`
specializes that finite-direction bridge to compact local-frame Gram matrices
on a normed-vector chart model: entrywise higher Gram controls choose second
jets, read first and second primitive arrays along the local-frame basis, and
extract the compact Gram determinant lower bound before applying the schematic
Ricci-DeTurck RHS estimate; the same specialization is available for finite
families of frames with one shared compact determinant lower bound. It also has
a deterministic chosen-entry-jet bridge for single and finite-family compact
local frames with the quantitative single-radius RHS estimate under
unique-differentiability of the slices, plus qualitative compact-frame forms,
assembling each Gram matrix into the higher matrix submodule before reading
the chosen entry jets along the relevant frame basis.
It now also
converts entrywise higher
primitive difference controls with radii linear in a shared radius into the
linear-radius `ParabolicBoundedWith` schematic RHS estimate and the
compact-coordinate readout `LipschitzOnWith` bridge for any parabolic
`C^{0,α}` vector field agreeing with that RHS on the state set, including a
coarser exported-constant variant for sharper entrywise higher primitive
controls. The schematic RHS Lipschitz bridge now also has exact and coarser
linear finite-cover readout variants, so callers that use the finite-product
linear map do not have to unfold the compact-coordinate family manually. The
chosen metric-entry second-jet/direction-family state-space Lipschitz theorem
now also has compact-family, linear finite-cover, and pointwise
compact-coordinate readout wrappers, carrying the unique-differentiability
transport all the way to the finite chart handoff; it also restricts to
fixed-time spatial compact readouts when the chosen time-space compact family
covers those slices, with all-cover entry points for the single-family and
Pi-valued fixed-time spatial forms. Coordinate-unit direction readouts now
reduce by named simp lemmas to the coordinate-radius API, including
nonnegativity readouts for those coordinate radii, and the chosen-jet
state-space Lipschitz theorem has a coordinate-space specialization stated
directly with those radii. The same
chosen-jet state-space bridge now has memberwise finite-family and Pi-valued
finite-product forms, using the finite sum of the member schematic constants,
and those Pi-valued finite products now also feed compact-family and linear
finite-cover readout `LipschitzOnWith` wrappers, plus pointwise compact
coordinate and fixed-time spatial readouts under the same time-space cover
hypotheses.
The exact and coarser compact readouts now also unpack to pointwise
compact-coordinate distance bounds with the same schematic RHS constant,
including finite-family forms with either memberwise constants or one shared
finite-sum constant for indexed frame/cover data. These exact and coarser
pointwise RHS readouts now also restrict directly to fixed-time spatial compact
readouts under a time-slice cover hypothesis, again with single-family,
memberwise finite-family, and shared finite-sum variants. Radii linear in
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

The affine parabolic chart layer now also has a complete topological-boundary
transport layer built on `affineChartHomeomorph`: for `r ≠ 0` the chart commutes
with `closure`, `interior`, and `frontier` of all four parabolic shapes
(open/closed balls and cylinders) in both the image (`affineChartHomeomorph_image_{closure,interior,frontier}_*`)
and preimage (`affineChartHomeomorph_preimage_{closure,interior,frontier}_*`)
directions, and restricts to a `Set.BijOn` between those boundary sets
(`affineChartHomeomorph_bijOn_{closure,interior,frontier}_*`).  Intrinsic
(chart-free) shape topology was filled in: each open parabolic shape lies in the
interior of the corresponding closed shape
(`parabolic{Ball,Cylinder}.subset_interior_closed*`), so each closed parabolic
shape of positive radius is a neighborhood of its center
(`parabolicClosed{Ball,Cylinder}.mem_nhds`).  Feeding the boundary `Set.BijOn`
into the generic `MapsTo`-parametrized change of variables
`ParabolicC0Alpha{With,On}.comp_affineChart` now gives the affine Schauder
`C^{0,α}` normalization directly on the closure of an open parabolic
ball/cylinder and on the interior of a closed parabolic ball/cylinder
(`ParabolicC0Alpha{With,On}.comp_affineChart_{closure_parabolicBall,closure_parabolicCylinder,interior_parabolicClosedBall,interior_parabolicClosedCylinder}`),
i.e. the affine change of variables is now available on the exact boundary-domain
shapes on which an interior parabolic regularity estimate is taken.
The parabolic Hölder vocabulary now also has the *reverse assembly* direction,
converse to the `space_slice` / `time_slice_half_exponent` readouts: on a
corner-closed time-space set (one containing the mixed corner `(τ, x)` of any two
of its points `(t, x)` and `(τ, y)` — proved automatic for open/closed parabolic
balls and cylinders via `parabolic{Ball,ClosedBall,Cylinder,ClosedCylinder}.corner_mem`,
each being a product of a time interval and a spatial ball), spatial `α`-Hölder
control uniform in time together with temporal `α/2`-Hölder control uniform in
space reassemble into parabolic `α`-Hölder control with the summed constant.
This is packaged as `ParabolicHolderWith.of_space_time_holder` and its
`ParabolicHolderOn` / `ParabolicC0AlphaWith` / `ParabolicC0AlphaOn` companions,
with closed cylinder/ball Schauder-domain specializations, plus the textbook
characterization `ParabolicHolderOn.iff_space_time_holder` (parabolic Hölder ⟺
separate spatial and temporal Hölder on a corner-closed set). This is the standard
route to parabolic Schauder estimates — control the space and time regularity of a
solution separately and then combine them into the parabolic norm.
The space/time characterization is now also available at the *full norm level* and on
the *open* Schauder domains: `ParabolicC0AlphaOn.iff_space_time_holder` records the sup
bound alongside the separate spatial/temporal Hölder control (the exact `C^0` +
space/time data of the parabolic `C^{0,α}` norm), with closed and open
cylinder/ball specializations, and `ParabolicHolderOn.iff_space_time_holder_parabolic{Cylinder,Ball}`
give the open-interior-domain analogues of the closed-shape characterization (both
proved from the general corner-closed `iff` via the open `corner_mem` lemmas).
The parabolic classes are now also proved *closed under limits*, the inheritance step
behind completeness of the parabolic Hölder space:
`ParabolicHolderWith`/`ParabolicBoundedWith`/`ParabolicC0AlphaWith.of_tendsto` pass a
fixed Hölder constant, uniform sup bound, and combined `C^{0,α}` control to pointwise
limits over any `NeBot` filter, and the `...of_tendstoUniformlyOn` companions state the
same closedness in the topology of uniform convergence (the fixed-constant `C^{0,α}`
ball is closed in `C^0`). The `C^{0,α}` seminorm is now packaged as an honest `ℝ`-valued
functional: `parabolicHolderSeminorm α u s = sInf {C ≥ 0 | ParabolicHolderWith C α u s}`
(the least admissible Hölder constant), its `C^0` companion `parabolicSupNorm u s`, and the
full norm `parabolicC0AlphaNorm α u s = parabolicSupNorm u s + parabolicHolderSeminorm α u s`.
Each is proved nonnegative, a lower bound for every admissible constant, and *attained* on the
corresponding class (`parabolicHolderWith_parabolicHolderSeminorm`,
`parabolicBoundedWith_parabolicSupNorm`,
`parabolicC0AlphaWith_parabolicSupNorm_parabolicHolderSeminorm`), with the class-membership
iff-characterizations (`parabolicHolderOn_iff_parabolicHolderWith_seminorm`,
`parabolicC0AlphaOn_iff_parabolicC0AlphaWith_norms`). The seminorm axioms are in place —
subadditivity (`parabolic{HolderSeminorm,SupNorm,C0AlphaNorm}_add_le` and the difference
forms `..._sub_le`), vanishing on zero (`parabolic{HolderSeminorm,SupNorm,C0AlphaNorm}_zero`),
integer homogeneity (`parabolic{HolderSeminorm,SupNorm}_zsmul_le`), and unconditional
negation invariance (`parabolic{HolderSeminorm,SupNorm,C0AlphaNorm}_neg`) — together with
domain monotonicity (`parabolic{HolderSeminorm,SupNorm}_mono_domain`), pointwise readouts
(`norm_sub_le_parabolicHolderSeminorm`, `norm_le_parabolicSupNorm`), `Set.EqOn`-congruence
(`parabolic{HolderSeminorm,SupNorm,C0AlphaNorm}_congr`, so the functional descends to the
restriction to `s`), and the completeness-facing bound `parabolicC0AlphaNorm_le_of_tendsto`
(the norm stays `≤ B + H` under any pointwise limit of a fixed `C^{0,α}` ball). What remains
for decomposition step 1 is to assemble the Banach-space (completeness) instance — a bundled
parabolic `C^{0,α}` function type with a `NormedAddCommGroup`/`CompleteSpace` structure whose
Cauchy sequences converge via the closedness lemmas above — then lift to `C^{2+α,1+α/2}`.
The completeness *property* itself is now proved at the function level: the norm functional
dominates its parts (`parabolic{SupNorm,HolderSeminorm}_le_parabolicC0AlphaNorm`) with pointwise
readouts (`norm_le_parabolicC0AlphaNorm`, `norm_sub_le_parabolicC0AlphaNorm_mul`) and the
uniform-metric difference bound `norm_sub_le_parabolicC0AlphaNorm_sub`; a norm bound converts to an
explicit ball via `parabolicC0AlphaWith_of_le_parabolicC0AlphaNorm`; and
`exists_parabolicC0AlphaOn_tendsto_of_cauchy` proves that, for complete `E`, a sequence of parabolic
`C^{0,α}` functions on `s` that is Cauchy in the parabolic `C^{0,α}` norm converges in that norm to
a parabolic `C^{0,α}` limit (pointwise limit via completeness of `E`, limit-in-class via
`ParabolicC0AlphaWith.of_tendsto`, norm convergence via `parabolicC0AlphaNorm_le_of_tendsto`).
The norm functional is also `1`-Lipschitz
(`abs_parabolicC0AlphaNorm_sub_le_parabolicC0AlphaNorm_sub`), so the norms of a Cauchy sequence
converge to the norm of the limit. The remaining gap is now only the bundling: a quotient/subtype
carrier for functions modulo agreement on `s` (so `‖·‖ = 0 ↔ · = 0`) with the packaged
`NormedAddCommGroup`/`CompleteSpace` instances, then the lift to `C^{2+α,1+α/2}`.
The seminormed-level bundling is now in place: `parabolicC0AlphaSubmodule.seminormedAddCommGroup`
(from the bundled `AddGroupSeminorm`/`Seminorm ℝ`) has readouts `seminormedAddCommGroup_norm`,
`seminormedAddCommGroup_dist` (`dist u v = parabolicC0AlphaNorm α (u−v) s`), and — the completeness
half of the parabolic Hölder Banach space — `parabolicC0AlphaSubmodule.completeSpace`, a
`@CompleteSpace` fact for the parabolic `C^{0,α}` submodule under the *pinned* `C^{0,α}` uniformity
(assembled from `Metric.complete_of_cauchySeq_tendsto` + `exists_parabolicC0AlphaOn_tendsto_of_cauchy`;
the uniformity is pinned because the ambient function subtype already carries the pointwise product
`instUniformSpaceSubtype`, which the honest separated Banach carrier on a type synonym/quotient will
displace). Scalar compatibility is packaged as `parabolicC0AlphaSubmodule.normedSpace`
(`NormedSpace ℝ` over the seminormed structure), so the parabolic Hölder space is exhibited as a
*complete seminormed `ℝ`-vector space* (semi-Banach); only point separation remains for the genuine
Banach instance. Toward decomposition step 2 (the Schauder/Lipschitz estimate), the parabolic
`C^{0,α}` norm functional is now shown to be a *normed algebra* norm: submultiplicativity
`parabolicC0AlphaNorm_mul_le` (`‖u·v‖ ≤ ‖u‖·‖v‖` in a normed ring, from `parabolicSupNorm_mul_le`
and the Leibniz `parabolicHolderSeminorm_mul_le`) and the bilinear Lipschitz product-difference bound
`parabolicC0AlphaNorm_mul_sub_mul_le` (`‖u·v − u'·v'‖ ≤ ‖u‖·‖v−v'‖ + ‖u−u'‖·‖v'‖`), the local
Lipschitz control of multiplication behind the nonlinear Ricci–DeTurck contraction/uniqueness
arguments.

Update — **the genuine (separated) parabolic `C^{0,α}` Banach space is now built**, closing the
"only point separation remains for the genuine Banach instance" gap flagged above (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`).  New module
`AnalyticPDE/Parabolic/BanachSpace.lean` (imports only `Parabolic/FunctionSpace` + Mathlib's
`SeparationQuotient` normed machinery; does not touch the heavy files):

* `ParabolicC0AlphaSpace X E α s` — a **type-synonym carrier** for `parabolicC0AlphaSubmodule` whose
  *canonical* `SeminormedAddCommGroup`/`NormedSpace ℝ`/`CompleteSpace` instances are the parabolic
  Hölder ones (displacing the ambient pointwise-product topology the bare submodule subtype carries).
  This is the complete seminormed space (`parabolicC0AlphaSubmodule.seminormedAddCommGroup` /
  `completeSpace` / `normedSpace`) exhibited as a first-class type, with `norm_def` / `dist_def`.
* `ParabolicC0AlphaBanach X E α s := SeparationQuotient (ParabolicC0AlphaSpace X E α s)` — the honest
  **Banach space**: Mathlib's `SeparationQuotient` upgrades the complete *seminormed* structure to a
  genuine `NormedAddCommGroup` (point separation) + `CompleteSpace` + `NormedSpace ℝ`.  With the
  projection `mk`, `mk_surjective`, `norm_mk` (`‖mk u‖ = parabolicC0AlphaNorm α u s` — the projection
  is norm-preserving on representatives), `norm_mk_ofSubmodule`, and `mk_eq_mk_iff` (`mk u = mk v ↔`
  the parabolic `C^{0,α}` norm of the difference is `0` — the point-separation characterisation).
* **Projection/section bounded-operator API**: `mkL` (the projection as `→L[ℝ]`, `‖mkL‖ ≤ 1`), a
  continuous linear **section** `outL` (`SeparationQuotient.outCLM`) with `mk_outL`
  (`mk (outL x) = x`), `mkL_comp_outL`, `outL_injective`, and `norm_outL` (`‖outL x‖ = ‖x‖` — the
  section is an **isometric** linear embedding of the Banach space into the semi-Banach carrier).
* **Domain-restriction operator** (a core chart-closure operation — restricting to sub-cylinders):
  the reusable norm estimate `parabolicC0AlphaNorm_mono_domain` (`t ⊆ s ⟹ parabolicC0AlphaNorm α u t
  ≤ parabolicC0AlphaNorm α u s`, from the sup- and Hölder-seminorm domain monotonicities — a genuine
  gap that was missing); the carrier restriction `ParabolicC0AlphaSpace.restrictL` (op-norm `≤ 1`,
  `LinearMap.mkContinuous` fed the monotonicity); and its **descent to the Banach spaces**
  `ParabolicC0AlphaBanach.restrictL` (well-defined on classes because norm-nonincreasing, via
  `SeparationQuotient.liftCLM`), with `restrictL_mk` (`restrictL (mk u) = mk (restrict u)`) and
  `norm_restrictL_le` (op-norm `≤ 1`).

This realises decomposition step 1 (the parabolic Hölder function-space carrier) at the `C^{0,α}`
level as a genuine Banach space with its basic operator API — the `C^0`-level function-space
realisation the Ricci–DeTurck Banach chart consumes.  Remaining (future sessions): the lift to the
higher-regularity parabolic Hölder space `C^{2+α,1+α/2}`, then decomposition steps 2 (the
Schauder/Lipschitz estimate for the Ricci–DeTurck RHS) and 3 (the chart / chart-closure fields).

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

Update — **the well-posedness / local-existence layer of the quasilinear Ricci–DeTurck fixed point
is now built** on the parabolic `C^{0,α}` Banach chart (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`), extending `AnalyticPDE/Parabolic/BanachSpace.lean`.  The
previous milestone gave the *unique solvability* of the quasilinear equation `A u + N u + f = u`
(bounded-linear principal part `A`, `k`-Lipschitz nonlinearity `N`, frozen data `f`, contraction
constant `‖A‖ + k < 1`, `exists_unique_affinePlusLipschitzFixedPoint`); this session supplies the
**continuous-dependence / a-priori / localisation data** the Ricci–DeTurck chart-closure consumes,
turning the bare solvability into a genuine well-posed solution operator:

* `norm_affinePlusLipschitzFixedPoint_sub_le` — **continuous (Lipschitz) dependence on the data**:
  two solutions for data `f₁`, `f₂` obey `‖u₁ − u₂‖ ≤ ‖f₁ − f₂‖ / (1 − (‖A‖ + k))` (via
  `norm_fixedPoint_sub_fixedPoint_le` with `gᵢ = A · + N · + fᵢ`, gap `g₁ − g₂ = f₁ − f₂`); generalises
  the affine `norm_affineSolveL_apply_sub_le` (`N = 0`).
* `norm_affinePlusLipschitzFixedPoint_le` — the **a-priori Schauder bound**
  `‖u‖ ≤ (‖N 0‖ + ‖f‖) / (1 − (‖A‖ + k))` (from `‖u‖ ≤ (‖A‖ + k)‖u‖ + (‖N 0‖ + ‖f‖)`, the nonlinearity
  contributing `‖N u‖ ≤ k‖u‖ + ‖N 0‖`, solved by `le_div_iff₀`).
* `norm_affinePlusLipschitzFixedPoint_sub_le_nonlinearity` — **stability under a uniform perturbation
  of the nonlinearity** (`‖N₁ z − N₂ z‖ ≤ C`): `‖u₁ − u₂‖ ≤ C / (1 − (‖A‖ + k))`; and
  `norm_affinePlusLipschitzFixedPoint_sub_le_of_data_nonlinearity` — the **combined** continuous
  dependence on `(N, f)`, `‖u₁ − u₂‖ ≤ (C + ‖f₁ − f₂‖) / (1 − (‖A‖ + k))` (gap
  `(N₁ − N₂) + (f₁ − f₂)`), of which the two above are the `N₁ = N₂` / `f₁ = f₂` faces.
* `affinePlusLipschitzSolve` (+ `_isSolution`, `_eq`, `norm_affinePlusLipschitzSolve_le`,
  `lipschitzWith_affinePlusLipschitzSolve`, `continuous_affinePlusLipschitzSolve`) — the **bundled
  quasilinear solution operator** `f ↦ u(f)` as a genuinely bounded (`≤ (‖N 0‖ + ‖f‖)/(1−(‖A‖+k))`),
  `((1 − (‖A‖ + k))⁻¹).toNNReal`-Lipschitz, continuous nonlinear solution realisation (the nonlinear
  analogue of the bounded *linear* `affineSolveL`).
* `fixedPoint_mem_of_mapsTo_isClosed` — **closed-set localisation** of a nonlinear fixed point: a
  `k`-contraction `g` (`k < 1`) with `Set.MapsTo g K K`, `c ∈ K`, `K` closed has its fixed point in `K`
  (the Picard iterates `g^[n] c` stay in `K` and converge to `u`, `IsClosed.mem_of_tendsto`); and
  `affinePlusLipschitzFixedPoint_mem_closedBall` — its **invariant-ball** specialisation, the honest
  short-time / small-ball chart existence (if the RHS maps `closedBall c r` into itself, the solution
  exists *and stays in the ball*, `dist u c ≤ r`).

Remaining (future sessions): the lift to the higher-regularity parabolic Hölder space
`C^{2+α,1+α/2}`, then the Schauder/Lipschitz estimate for the Ricci–DeTurck RHS (which supplies the
concrete `A`, `N`, `f` and the invariant ball these consume) and the chart / chart-closure fields.

Update — **the quadratic Ricci–DeTurck nonlinearity and its short-time small-ball well-posedness are
now built** on the parabolic `C^{0,α}` Banach chart (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`), extending `AnalyticPDE/Parabolic/BanachSpace.lean`.  The
frozen-coefficient operators (`mulL`/`mulCoeffL`) take their coefficient in the *seminormed carrier*
(the *linearised* operator); the genuine Ricci–DeTurck nonlinearity is *quadratic*, with the
coefficient itself a chart solution (a Banach class).  This session supplies exactly that quadratic
algebra and the honest local existence for it (the globally-Lipschitz `affinePlusLipschitz` solver
cannot reach a merely-locally-Lipschitz nonlinearity):

* `mulBilinL` — the **fully-Banach bilinear multiplication** `ParabolicC0AlphaBanach … E … →L[ℝ]
  (ParabolicC0AlphaBanach … F … →L[ℝ] ParabolicC0AlphaBanach … G …)` of norm `≤ ‖L‖`, descending
  `mulL L` through the separation quotient in the coefficient slot too (well defined because `mulL L` is
  `‖L‖`-Lipschitz); `mulBilinL_mk`/`mulBilinL_mk_mk`/`norm_mulBilinL_le`/`evalCLM_mulBilinL_apply` give
  its representative/pointwise-product/norm/point-evaluation coherence.  Both factors are Banach classes
  — the algebra of the *quadratic* nonlinear term, whose diagonal `u ↦ mulBilinL L u u` is the quadratic
  map.
* `norm_mulBilinL_diag_le` (`‖L(u,u)‖ ≤ ‖L‖‖u‖²`), `mulBilinL_diag_sub` (the bilinear polarisation
  `L(u,u) − L(v,v) = L(u, u−v) + L(u−v, v)`), `norm_mulBilinL_diag_sub_le`
  (`‖L(u,u) − L(v,v)‖ ≤ ‖L‖(‖u‖+‖v‖)‖u−v‖`), and `lipschitzOnWith_mulBilinL_diag` (the diagonal is
  `LipschitzWith (2‖L‖R)` on `closedBall 0 R`) — the **local Lipschitz control** of the quadratic
  nonlinearity, the `k`-Lipschitz-nonlinearity datum a fixed-point solver consumes.
* `exists_fixedPoint_of_lipschitzOnWith_closedBall` (+ `eq_of_fixedPoint_of_lipschitzOnWith_closedBall`)
  — the **Banach fixed point on a closed ball**: a self-map of `closedBall c r` that is
  `LipschitzOnWith K` (`K < 1`) has a (unique-in-ball) fixed point there, via
  `ContractingWith.exists_fixedPoint'` on the complete closed-ball subspace
  (`Metric.isClosed_closedBall.isComplete`).  The abstract short-time small-ball existence.
* `lipschitzOnWith_quadraticRHS_closedBall` — the **named contraction property** of the Ricci–DeTurck
  right-hand side `u ↦ A u + L(u,u) + f`: `LipschitzOnWith (‖A‖ + 2‖L‖(‖c‖+r))` on `closedBall c r`
  (linear part `‖A‖` + quadratic diagonal `2‖L‖(‖c‖+r)`).
* `mapsTo_quadraticRHS_closedBall_zero` — the **invariant-ball (self-mapping) datum** from the explicit
  scalar smallness `‖A‖·r + ‖L‖·r² + ‖f‖ ≤ r`.
* `exists_fixedPoint_quadraticRHS_closedBall` (general center, `MapsTo` hypothesis),
  `exists_fixedPoint_quadraticRHS_closedBall_zero` (center `0`, from the two scalar conditions
  `‖A‖+2‖L‖r < 1` and `‖A‖·r+‖L‖·r²+‖f‖ ≤ r` alone), `eq_of_fixedPoint_quadraticRHS_closedBall`
  (in-ball uniqueness), and the bundled `existsUnique_fixedPoint_quadraticRHS_closedBall_zero`
  (**`∃!`**) — the honest **short-time chart existence + uniqueness** for the quadratic Ricci–DeTurck
  equation `A u + L(u,u) + f = u`, stated purely from the operator/data norms.  The well-posed
  short-time chart datum the Ricci–DeTurck chart closure consumes for the genuinely quadratic (only
  locally Lipschitz) nonlinearity.

Remaining (future sessions): unchanged in scope — the lift to the higher-regularity parabolic Hölder
space `C^{2+α,1+α/2}`, then the Schauder/Lipschitz estimate for the Ricci–DeTurck RHS (which supplies
the concrete `A`, the bilinear `L` and data `f`, and the short-time invariant ball these consume via
the now-available quadratic well-posedness) and the chart / chart-closure fields.

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

## ODE dependence-on-initial-data infrastructure (new upstream module, Items 1/2)

The recurring blocker for Items 1 and 2 is that Mathlib v4.29.1 supplies smooth
ODE-flow dependence only at the Banach level (Grönwall trajectory estimates,
integral-curve existence), not the `C^k`/manifold flow-on-initial-data needed
here.  A dedicated new module builds that missing theory from the Banach-level
Mathlib results up, isolated so it never touches the heavy files:

`PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/SmoothDependenceCk.lean`
(imports only `Mathlib.Analysis.ODE.Basic` and `Mathlib.Analysis.ODE.Gronwall`).

The `C^0` / Lipschitz (`C^{0,1}`) base layer of the dependence tower is complete
and fully proved (axioms `propext`/`Classical.choice`/`Quot.sound` only):

* `isIntegralCurve_comp_neg` — the time-reversed curve `s ↦ f (-s)` is an integral
  curve of the time-reversed field `(s, x) ↦ -(v (-s) x)`.
* `dist_le_of_isIntegralCurve_of_le` — forward exponential dependence bound
  (`IsIntegralCurve` packaging of Mathlib's `dist_le_of_trajectories_ODE`).
* `dist_le_of_isIntegralCurve` — the **two-sided** bound
  `dist (f t) (g t) ≤ dist (f t₀) (g t₀) · exp (K · |t - t₀|)` for all `t`
  (Mathlib only gives the forward half; the backward half comes from applying the
  forward bound to the time-reversed curves).
* `dist_le_of_isIntegralCurve_of_abs_le` — uniform bound on a symmetric compact
  time interval.
* `eq_of_isIntegralCurve_of_eq`, `eq_of_isIntegralCurve_of_eq_at` — global
  uniqueness of an integral curve from agreement at the anchor / at any one time.
* `dist_le_of_isIntegralCurve_perturb_of_le` — forward Grönwall stability under a
  uniform perturbation of the vector field (continuous dependence on the field).
* Flow-family packaging for `Φ : E → ℝ → E` with `Φ x t₀ = x`:
  `dist_flow_apply_le`, `lipschitzWith_flow_apply`,
  `lipschitzWith_flow_apply_of_abs_le` (the time-`t` flow map is exponentially
  Lipschitz in the initial value), `continuous_flow_apply`,
  `injective_flow_apply` (injectivity — the diffeomorphism-onto-image half needed
  by Item 2), and `continuous_flow` (**joint** continuity of `(t, x) ↦ Φ x t`).

The `C^0` layer has since been rounded out with the quantitative
**bi-Lipschitz / embedding** and **stability** refinements (all axioms
`propext`/`Classical.choice`/`Quot.sound` only):

* `dist_ge_of_isIntegralCurve` — the **lower** two-sided exponential bound
  `dist (f t₀) (g t₀) · exp (-K · |t - t₀|) ≤ dist (f t) (g t)` (the flow run
  backward from `t` to `t₀` expands separation by at most `exp (K · |t - t₀|)`).
* `dist_flow_apply_ge`, `antilipschitzWith_flow_apply`,
  `antilipschitzWith_flow_apply_of_abs_le` — the time-`t` flow map is
  **antilipschitz** with constant `exp (K · |t - t₀|)` (uniform `exp (K · T)` on a
  symmetric compact interval): the quantitative injectivity.
* `isUniformEmbedding_flow_apply`, `isEmbedding_flow_apply` — being both Lipschitz
  and antilipschitz, `x ↦ Φ x t` is a **bi-Lipschitz uniform (topological)
  embedding onto its image**: the `C^0` "diffeomorphism onto its image" shadow
  consumed by the compact-manifold gauge flow of Item 2.
* `dist_le_of_isIntegralCurve_perturb` — the **two-sided** Grönwall stability under
  a uniform field perturbation, `dist (f t) (g t) ≤ gronwallBound (dist (f t₀)
  (g t₀)) K ε |t - t₀|` for all `t` (the backward half via the time-reversed
  curves), and its flow-family form `dist_flow_perturb_le` (two flows of
  `ε`-close fields, same anchor, stay `gronwallBound 0 K ε |t - t₀|`-close) — the
  DeTurck-flow continuous-dependence-on-the-field transfer.
* `flow_eq_of_isIntegralCurve` — uniqueness of the flow family (`ε = 0` degenerate
  case of the perturbation bound).
* `lipschitzWith_of_isIntegralCurve_of_norm_le`, `lipschitzWith_flow_of_norm_le`,
  `dist_flow_le_of_norm_le` — the **time-direction** modulus missing from
  `continuous_flow`: under a uniform velocity bound `‖v t (Φ x t)‖ ≤ M` each curve
  is `M`-Lipschitz in time, giving a joint Lipschitz modulus
  `dist (Φ x t) (Φ y s) ≤ M · |t - s| + exp (K · T) · dist x y` on a compact time
  interval.

Remaining in this tower (future sessions): the `C^1` (differentiable) dependence
layer — the flow derivative `D_x Φ_t` solving the linearised/variational ODE —
and its bootstrap to `C^k` (`C^3`), which is what the compact-manifold gauge flow
of Item 2 and the tensor time-derivative chain rule of Item 1 ultimately consume.

The **first brick of the `C^1` layer** is now in place (axioms
`propext`/`Classical.choice`/`Quot.sound` only): the linearised/variational ODE is
formalised as an object and shown well-posed.

* `variationalField A t W = (A t).comp W` — the operator-valued variational field on
  the operator Banach space `E →L[ℝ] E`, whose integral curves solve the
  fundamental-solution equation `W'(t) = A(t) ∘ W(t)` satisfied by `D_x Φ_t`;
  `lipschitzWith_variationalField` proves it is `K`-Lipschitz under `‖A t‖ ≤ K`
  (operator-norm submultiplicativity), and the `C^0` lemmas instantiated on
  `E →L[ℝ] E` give `variational_eq_of_isIntegralCurve` (uniqueness) and
  `dist_variational_le` (exponential a-priori bound).
* `variationalFieldVec A t u = A t u` — the **vector** variational field on `E`,
  whose integral curves solve `u'(t) = A(t) (u(t))`, the equation obeyed by the
  directional derivative `∂_{u₀} Φ_t = D_x Φ_t · u₀`; `lipschitzWith_variationalFieldVec`,
  `variationalVec_eq_of_isIntegralCurve`, `dist_variationalVec_le` are its Lipschitz /
  uniqueness / a-priori-bound analogues.
* `isIntegralCurve_variational_apply` — the connective lemma: evaluating a solution `W`
  of the operator equation on a fixed direction `u₀` yields a solution `t ↦ W t u₀` of
  the vector equation (via the derivative chain rule `HasDerivAt.clm_apply`), tying the
  fundamental solution to the directional derivatives it generates.
* `isIntegralCurve_variationalFieldVec_add`, `isIntegralCurve_variationalFieldVec_smul` —
  the **superposition principle**: solutions of the (linear) vector variational equation
  are closed under addition and scalar multiplication, so the directional derivative
  `u₀ ↦ D_x Φ_t · u₀` is linear in `u₀` and assembles into the bounded operator
  `D_x Φ_t ∈ E →L[ℝ] E`.

The superposition principle has now been **cashed out**: the directional-derivative map is
assembled into the honest bounded operator `D_x Φ_t ∈ E →L[ℝ] E` (the fundamental solution /
resolvent), with a full operator-level API (all axioms
`propext`/`Classical.choice`/`Quot.sound` only).  For a flow family `Φ` of
`variationalFieldVec A` (`‖A t‖ ≤ K`) anchored at `Φ x t₀ = x`:

* `flow_variationalFieldVec_add`, `flow_variationalFieldVec_smul`,
  `flow_variationalFieldVec_zero` — the time-`t` flow map `x ↦ Φ x t` of the *linear* field
  is additive, homogeneous, and fixes the origin (superposition + vector uniqueness).
* `norm_flow_variationalFieldVec_le` — the operator upper bound
  `‖Φ x t‖ ≤ exp (K · |t - t₀|) · ‖x‖` (from `dist_flow_apply_le` and `Φ 0 t = 0`).
* `fundamentalSolution` — the resulting **bounded operator** `D_x Φ_t ∈ E →L[ℝ] E`, packaged
  via `LinearMap.mkContinuous`, with `fundamentalSolution_apply` (`D_x Φ_t · x = Φ x t`),
  `norm_fundamentalSolution_le` (`‖D_x Φ_t‖ ≤ exp (K · |t - t₀|)`), and
  `fundamentalSolution_anchor` (`D_x Φ_{t₀} = 1`).
* `norm_flow_variationalFieldVec_ge`, `norm_fundamentalSolution_apply_ge`,
  `fundamentalSolution_injective` — the **lower** operator bound
  `exp (-K · |t - t₀|) · ‖x‖ ≤ ‖D_x Φ_t · x‖` (from the `C^0` lower bound
  `dist_flow_apply_ge`), whence the resolvent is bounded below and **injective** (the
  operator shadow of the bi-Lipschitz embedding `injective_flow_apply`): a non-degenerate
  resolvent.
* `fundamentalSolution_eq_of_operator_isIntegralCurve` — the **operator-ODE bridge**: any
  solution `W` of the operator variational equation `W'(t) = A(t) ∘ W(t)` with `W t₀ = 1`
  (the fundamental matrix) satisfies `fundamentalSolution … t = W t`, tying the operator- and
  vector-valued variational equations together.
* `continuous_fundamentalSolution_apply`, `continuous_fundamentalSolution` — strong (in time)
  and joint continuity of the resolvent action `(t, u₀) ↦ D_x Φ_t · u₀` (from
  `IsIntegralCurve.continuous` / `continuous_flow`).
* `isIntegralCurve_fundamentalSolution_apply`, `fundamentalSolution_apply_anchor` — the
  resolvent **columns are the variational-ODE solutions**: `t ↦ D_x Φ_t · u₀` is the integral
  curve of `variationalFieldVec A` through `u₀` at `t₀` (the characterisation a subsequent
  `C^1`-differentiability proof consumes).
* `fundamentalSolution_congr` — the resolvent is **canonical**: independent of the flow-family
  representative, depending only on the field `A` (and `t₀`, `t`).

Remaining in this tower (future sessions): *existence* of the variational flow family (global
integral curves of the uniformly-Lipschitz linear field, making the above non-vacuous), then
the actual `C^1` differentiability of the base flow `x ↦ Φ x t` with derivative `D_x Φ_t`
(the remainder Grönwall estimate), and its bootstrap to `C^k` (`C^3`).

The **`C^1` differentiability layer has now been opened** (all axioms
`propext`/`Classical.choice`/`Quot.sound` only): the *linearisation-remainder Grönwall bound* —
the analytic core of differentiable dependence — is proved, and assembled into the actual
Fréchet-differentiability of the flow (conditional on a defect modulus).  For integral curves
`f`, `g` of a field `v`, a solution `w` of the vector variational ODE `w' = A(s) w`
(`‖A s‖ ≤ K`) predicting the initial separation `w t₀ = g t₀ - f t₀`, and a bound `δ` on the
linearisation defect `‖v s (g s) - v s (f s) - A s (g s - f s)‖`:

* `norm_flow_sub_variational_le` — the **global** remainder bound
  `‖(g t - f t) - w t‖ ≤ gronwallBound 0 K δ |t - t₀|` (defect uniform in all time), proved by
  recognising `r := g - f - w` as an integral curve of `variationalFieldVec A` perturbed by the
  `δ`-bounded defect and comparing it to the zero solution via the two-sided perturbation
  Grönwall bound `dist_le_of_isIntegralCurve_perturb`.
* `norm_flow_sub_variational_le_Icc` — the **interval-restricted** refinement, needing the defect
  only on the forward interval `Ico t₀ b` (as the flow separation grows exponentially, a
  globally-uniform `δ` is unavailable; on a compact time tube the `C^1` modulus supplies one),
  via Mathlib's interval Grönwall estimate `dist_le_of_approx_trajectories_ODE`.
* `gronwallBound_zero_left_mul` — the **homogeneity** `gronwallBound 0 K ε x = ε · gronwallBound
  0 K 1 x`, turning the remainder bound into an estimate proportional to the defect `δ`.
* `norm_flow_sub_fundamentalSolution_le_Icc` — the **operator form** of the interval bound, with
  the honest resolvent `fundamentalSolution … t = D_x Φ_t` as the linear prediction:
  `‖(Φ y t - Φ x t) - D_x Φ_t · (y - x)‖ ≤ gronwallBound 0 K δ (t - t₀)` — the numerator of the
  Fréchet difference quotient for `x ↦ Φ x t`.
* `hasFDerivAt_flow_of_defect_isLittleO` — the **`C^1` differentiability** itself: if the defect
  is `o(‖z - x₀‖)` as `z → x₀` (a `D : E → ℝ`, `0 ≤ D`, bounding the defect on `Ico t₀ t` with
  `D =o[𝓝 x₀] (· - x₀)`), then `HasFDerivAt (fun z => Φ z t) (fundamentalSolution … t) x₀` — the
  flow map is Fréchet differentiable at `x₀` with derivative the resolvent.  Proof: the operator
  interval bound gives `numerator = O(D)` (via `gronwallBound_zero_left_mul`), which composed
  with `D = o(z - x₀)` gives `numerator = o(z - x₀)`.
* `differentiableAt_flow_of_defect_isLittleO`, `fderiv_flow_of_defect_isLittleO` — the
  consumer-facing corollaries: `DifferentiableAt ℝ (fun z => Φ z t) x₀`, and
  `fderiv ℝ (fun z => Φ z t) x₀ = fundamentalSolution … t` (the flow's spatial derivative **is**
  the fundamental solution operator).

Remaining in this tower (future sessions): **discharging the defect modulus** — proving that a
`C^1` field `v` (with `A s = D_x v(s, Φ x₀ s)`) *supplies* the hypothesis `D =o(‖z - x₀‖)`, via
the mean-value remainder `‖v s b - v s a - D_x v(s,a)(b-a)‖ ≤ (sup over the segment of
‖D_x v(s,·) - D_x v(s,a)‖)·‖b - a‖` (Mathlib `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le`)
uniformised over `s ∈ [t₀, t]` by Heine–Cantor on the compact trajectory tube together with the
exponential flow-separation bound `dist_flow_apply_le` — which upgrades
`hasFDerivAt_flow_of_defect_isLittleO` to an *unconditional* `C^1` dependence theorem; then the
*existence* of the variational flow family, and the bootstrap to `C^k` (`C^3`).

Update — the defect-modulus discharge is now built as a full reduction chain in
`SmoothDependenceCk`, bottoming out at a directly-usable hypothesis for smooth fields:

* `isLittleO_of_norm_le_mul_of_tendsto_nhds_zero` — the asymptotic glue: if `‖f x‖ ≤ g x · ‖u x‖`
  eventually and `g → 0`, then `f =o[l] u`.  Turns "`defect ≤ (modulus→0)·separation`" into the
  `o(‖z - x₀‖)` hypothesis of `hasFDerivAt_flow_of_defect_isLittleO`.
* `hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero` (+ `differentiableAt`/`fderiv`) — from a
  single time-uniform oscillation modulus `C : E → ℝ` with `C z → 0` bounding the defect on
  `Ico t₀ t` by `C z · (exp (K |s - t₀|) · ‖z - x₀‖)`, delivers `HasFDerivAt (fun z => Φ z t) =
  D_x Φ_t`.  (Sets `D z = C z · exp (K (t - t₀)) · ‖z - x₀‖`, `= o(‖z - x₀‖)` via the glue.)
* `hasFDerivAt_flow_of_segment_oscillation_tendsto_zero` (+ corollaries) — composes the mean-value
  bound `norm_flow_defect_le_of_segment_oscillation` with the previous, reducing the `C^1`
  dependence to a *pure `C^1`-regularity* hypothesis: the derivative chord-oscillation
  `‖Dv s ξ - A s‖` (over `ξ ∈ [Φ x₀ s, Φ z s]`, `s ∈ Ico t₀ t`) is `≤ C z → 0`.
* `tendsto_modulus_comp_norm_sub` — the "`C(z) → 0`" engine: for `0 ≤ c` and `ω → 0` along
  `𝓝[≥] 0`, `z ↦ ω (c · ‖z - x₀‖) → 0` as `z → x₀`.
* `hasFDerivAt_flow_of_uniform_deriv_modulus` (+ corollaries) — from a nonnegative monotone modulus
  `ω` vanishing at `0⁺` with `‖Dv s ξ - A s‖ ≤ ω (‖ξ - Φ x₀ s‖)`.  The chord points lie within
  `exp (K |s - t₀|) · ‖z - x₀‖` of the anchor (`dist_flow_apply_le` + the segment decomposition), so
  the monotone `ω` caps the oscillation by `C z = ω (exp (K (t - t₀)) · ‖z - x₀‖) → 0`.
* `hasFDerivAt_flow_of_lipschitz_deriv` (+ corollaries) — the `C^{1,1}` specialisation and the
  practical entry point: `‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖` (`0 ≤ L`, uniform in `s`) gives the
  `C^1` dependence via the linear modulus `ω r = L · max r 0`.  This covers every smooth field —
  in particular the intended Ricci-flow right-hand sides — so the smooth-case `C^1` dependence of
  the flow on initial data is now unconditional.

Remaining in this tower (future sessions): the *general* (merely-continuous, non-Lipschitz `Dv`)
modulus, i.e. extracting a monotone `ω → 0` for `hasFDerivAt_flow_of_uniform_deriv_modulus` from
joint continuity of `Dv` via Heine–Cantor uniform continuity on the compact trajectory tube; then
the *existence* of the variational flow family, and the bootstrap to `C^k` (`C^3`).

Update — the whole `C¹` dependence tower has been **localised**: since Fréchet differentiability of
`x ↦ Φ x t` at the base point `x₀` is a *local* property, every defect / oscillation /
derivative-existence hypothesis was weakened from the global `∀ z` to `∀ᶠ z in 𝓝 x₀` (the modulus
nonnegativity and the structural flow-family hypotheses stay global).  This matters because a
genuine smooth field has a spatial derivative that is only *locally* Lipschitz, so the global
Lipschitz-derivative bound of `hasFDerivAt_flow_of_lipschitz_deriv` generally fails for it — whereas
its local counterpart holds on the neighbourhood of `x₀` where the local estimate is available.  All
`_eventually` variants are fully proved (axioms `propext`/`Classical.choice`/`Quot.sound` only):

* `hasFDerivAt_flow_of_defect_isLittleO_eventually` (+ `differentiableAt`/`fderiv`) — the localised
  core: the linearisation-defect bound `‖v s (Φ z s) - v s (Φ x₀ s) - A s (Φ z s - Φ x₀ s)‖ ≤ D z`
  is needed only `∀ᶠ z in 𝓝 x₀` (the big-O numerator estimate is itself an eventual statement).
* `hasFDerivAt_flow_of_uniform_oscillation_tendsto_zero_eventually`,
  `hasFDerivAt_flow_of_segment_oscillation_tendsto_zero_eventually` (+ corollaries) — the localised
  oscillation layer.
* `hasFDerivAt_flow_of_uniform_deriv_modulus_eventually` (+ corollaries) — the localised modulus
  form.
* `hasFDerivAt_flow_of_lipschitz_deriv_eventually` (+ `_of_hasFDerivAt`, `differentiableAt`,
  `fderiv`) — **the local `C^{1,1}` payoff entry point**: `C¹` dependence from a *locally* Lipschitz
  spatial derivative `‖Dv s ξ - A s‖ ≤ L · ‖ξ - Φ x₀ s‖` holding only for `z` near `x₀` — the honest
  form the Ricci-DeTurck right-hand side supplies.
* `hasFDerivAt_flow_of_lipschitz_deriv_on_ball` (+ `differentiableAt`/`fderiv`) — **the chart-level
  entry point**: takes a *global* spatial derivative `HasFDerivAt (v s) (Dv s ξ) ξ` plus the
  Lipschitz-derivative bound holding only on a fixed radius-`r` ball around each anchor point
  `Φ x₀ s`; for `‖z - x₀‖ < r / exp (K (t - t₀))` the trajectory chord `[Φ x₀ s, Φ z s]` stays inside
  that ball (flow separation), discharging the eventual hypothesis.  This is exactly what a smooth
  (`C^∞`) field on a chart supplies — its derivative is locally Lipschitz on balls.

Update — **continuous dependence of the resolvent on the coefficient field** is now proved (axioms
`propext`/`Classical.choice`/`Quot.sound` only), the operator-level input to the `C²` regularity of
the flow in initial data (where the coefficient `A(x₀) s = D_x v(s, Φ x₀ s)` varies with the base
point) and to the continuous dependence of the DeTurck flow on the metric:

* `norm_fundamentalSolution_sub_apply_le_of_forall_le` — the directional form: for coefficients `A`,
  `A'` (both `‖·‖ ≤ K`) with variational flow families `Φ₁`, `Φ₂` and `‖A s - A' s‖ ≤ ε`, on the
  forward compact interval `[t₀, T]`,
  `‖D_x Φ_t^A u₀ - D_x Φ_t^{A'} u₀‖ ≤ ε · exp (K (T - t₀)) · ‖u₀‖ · gronwallBound 0 K 1 (t - t₀)`.
  The `A'`-column `s ↦ Φ₂ u₀ s` is an *approximate solution* of the `A`-field; the linearised
  perturbation `‖(A' s - A s)(Φ₂ u₀ s)‖ ≤ ε ‖Φ₂ u₀ s‖` is not uniform in the direction, so the
  a-priori trajectory bound `‖Φ₂ u₀ s‖ ≤ exp (K (T - t₀)) ‖u₀‖` (`norm_flow_variationalFieldVec_le`)
  is used to make it uniform on `[t₀, T]`, then Mathlib's `dist_le_of_approx_trajectories_ODE`.
* `norm_fundamentalSolution_sub_le_of_forall_le` — the operator-norm assembly over unit directions:
  `‖D_x Φ_t^A - D_x Φ_t^{A'}‖ ≤ ε · exp (K (T - t₀)) · gronwallBound 0 K 1 (t - t₀)`.  The resolvent
  is thus a locally Lipschitz function of its coefficient field.
* `gronwallBound_zero_one_nonneg` — the supporting `0 ≤ gronwallBound 0 K 1 x` (`0 ≤ K`, `0 ≤ x`).

Remaining in this tower (future sessions): the *general* (merely-continuous, non-Lipschitz `Dv`)
modulus; the *existence* of the variational flow family (global integral curves of the linear
field); and the bootstrap to `C^k` (`C^3`) — the resolvent-continuity brick is a first ingredient of
the latter (continuity of `x₀ ↦ D_x Φ_t` in the base point, once `x₀ ↦ A(x₀)` is set up).

Update — the resolvent's **regularity in time** is now proved at the *operator-norm* level (all
axioms `propext`/`Classical.choice`/`Quot.sound` only), culminating in the operator-valued
fundamental-solution equation itself — a central ingredient of the `C^k` bootstrap:

* `norm_fundamentalSolution_sub_le_time` — **operator-norm local Lipschitz continuity in time**:
  `‖D_x Φ_{t₂} - D_x Φ_{t₁}‖ ≤ K · exp (K · max |t₁ - t₀| |t₂ - t₀|) · |t₂ - t₁|`.  This is a genuine
  *operator*-norm (not merely strong / fixed-direction) bound: each resolvent column `s ↦ Φ u s`
  solves the vector variational ODE, so the one-dimensional mean-value inequality bounds its
  increment by the supremum over the time window of `‖A s (Φ u s)‖ ≤ K · exp (K |s - t₀|) · ‖u‖`; the
  exponential is maximised at an endpoint (`abs_le_max_abs_abs`), and the operator-norm supremum
  over unit directions (`opNorm_le_bound`) gives the bound.
* `continuous_fundamentalSolution_time` — the topological packaging: `t ↦ D_x Φ_t` is a **continuous
  curve in the operator Banach space** `E →L[ℝ] E`, obtained by squeezing the distance between `0`
  and the vanishing local-Lipschitz bound.  This upgrades the resolvent path from strongly
  continuous (`continuous_fundamentalSolution_apply`) to norm-continuous.
* `hasDerivAt_fundamentalSolution` / `isIntegralCurve_fundamentalSolution` — **the operator-valued
  variational ODE** `W' = A W`: for a *norm-continuous* coefficient `A` (`‖A t‖ ≤ K`), the resolvent
  is differentiable in the operator norm with `d/dt (D_x Φ_t) = A t ∘ (D_x Φ_t)`.  This is *operator*
  differentiability (uniform over unit directions), not just the strong/columnwise statement: the
  linearisation remainder applied to `u` is bounded, via the mean-value Taylor inequality, by
  `‖s - t‖ · (‖A σ ∘ D_x Φ_σ - A t ∘ D_x Φ_t‖ near t) · ‖u‖`, and the norm-continuity of
  `σ ↦ A σ ∘ D_x Φ_σ` (`continuous_fundamentalSolution_time` composed with `Continuous A` via
  `Continuous.clm_comp`) drives it to `o(‖s - t‖)`.  Combined with `fundamentalSolution_anchor`
  (`D_x Φ_{t₀} = 1`) this fully characterises the resolvent as *the* solution of `W' = A W`,
  `W t₀ = 1`, discharging the operator integral-curve hypothesis previously assumed by
  `fundamentalSolution_eq_of_operator_isIntegralCurve`.
* `norm_comp_fundamentalSolution_le` — the a priori **velocity bound** on the resolvent path:
  `‖A t ∘ D_x Φ_t‖ ≤ K · exp (K · |t - t₀|)` (the operator ODE's right-hand side), so the resolvent
  curve moves through operator space at speed controlled by the same exponential.

Remaining in this tower (future sessions): the *general* (merely-continuous, non-Lipschitz `Dv`)
modulus; the *existence* of the variational flow family (global integral curves of the linear
field); differentiable dependence of the resolvent on its coefficient field (the second-order
variational equation), toward the base-point `C^2`/`C^k` bootstrap.

Update — the resolvent's **Volterra / Duhamel integral equation** is now proved (axioms
`propext`/`Classical.choice`/`Quot.sound` only), converting the operator differential equation
`hasDerivAt_fundamentalSolution` into its Picard fixed-point form — the operator-Duhamel identity
that differentiable dependence on the coefficient field will be built on:

* `fundamentalSolution_eq_one_add_integral` — for a *norm-continuous* coefficient `A` (`‖A t‖ ≤ K`,
  `CompleteSpace E`), the resolvent satisfies `D_x Φ_t = 1 + ∫_{t₀}^{t} A σ ∘ D_x Φ_σ dσ`.  Proof:
  the operator ODE `W' = A W` (`hasDerivAt_fundamentalSolution`) holds at every time, its
  right-hand side `σ ↦ A σ ∘ D_x Φ_σ` is norm-continuous
  (`hAcont.clm_comp continuous_fundamentalSolution_time`) hence interval-integrable, so the
  fundamental theorem of calculus (`intervalIntegral.integral_eq_sub_of_hasDerivAt`) gives
  `∫_{t₀}^{t} A σ ∘ D_x Φ_σ dσ = D_x Φ_t - D_x Φ_{t₀}`, and folding in
  `fundamentalSolution_anchor` (`D_x Φ_{t₀} = 1`) yields the Volterra equation.  (This is the first
  use of Bochner interval integration in the module, adding the single core-Mathlib import
  `Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus`.)
* `norm_fundamentalSolution_sub_one_le` — the **short-time closeness of the resolvent to the
  identity**: `‖D_x Φ_t - 1‖ ≤ K · exp (K · |t - t₀|) · |t - t₀|` (`→ 0` as `t → t₀`).  Immediate
  from the Volterra identity (`D_x Φ_t - 1 = ∫_{t₀}^{t} A σ ∘ D_x Φ_σ dσ`) and the a-priori velocity
  bound `norm_comp_fundamentalSolution_le` (`‖A σ ∘ D_x Φ_σ‖ ≤ K · exp (K · |σ - t₀|)`), whose
  integrand is `≤ K · exp (K · |t - t₀|)` on the window `Ι t₀ t`, integrated by
  `intervalIntegral.norm_integral_le_of_norm_le_const`.  This is the operator-Duhamel short-time
  estimate underlying the contraction / invertibility of the resolvent for small `|t - t₀|`.
* `isUnit_fundamentalSolution_of_norm_sub_one_lt` / `isUnit_fundamentalSolution_of_time_lt` — the
  **invertibility of the resolvent** as an operator: if `‖D_x Φ_t - 1‖ < 1` then `D_x Φ_t` is a unit
  of `E →L[ℝ] E` (Neumann-series openness of the units around `1`, `Units.oneSub`); combined with the
  short-time bound above, `K · exp (K · |t - t₀|) · |t - t₀| < 1` suffices.  This is the
  operator/inverse-function-theorem shadow of the bi-Lipschitz embedding — on top of
  `fundamentalSolution_injective` (injectivity) it gives a genuine two-sided operator inverse, so the
  flow map `x ↦ Φ x t` is a linear isomorphism for `t` near `t₀` (the local-diffeomorphism input for
  Item 2's compact-manifold gauge flow).
* `fundamentalSolution_sub_eq_integral` — the **Duhamel difference formula** (variation of
  parameters) for two coefficient fields `A₁`, `A₂` with resolvents `W₁`, `W₂`:
  `W₁ t - W₂ t = ∫_{t₀}^{t} A₁ σ ∘ (W₁ σ - W₂ σ) dσ + ∫_{t₀}^{t} (A₁ σ - A₂ σ) ∘ W₂ σ dσ`.  Subtract
  the two Volterra equations (the identities cancel), then split the single integrand via bilinearity
  of composition `A₁ ∘ W₁ - A₂ ∘ W₂ = A₁ ∘ (W₁ - W₂) + (A₁ - A₂) ∘ W₂` (`comp_sub`/`sub_comp`) using
  `integral_sub`/`integral_add`/`integral_congr` (all four integrands norm-continuous hence
  interval-integrable).  This is the "homogeneous propagation of the resolvent gap" plus the "source
  term from the coefficient gap"; as `A₂ → A₁` the first term is `O(‖W₁ - W₂‖)` and the second is the
  leading `(A₁ - A₂)` contribution, so this is the exact ancestor of the *differentiable* dependence
  of the resolvent on its coefficient (the second-order variational equation).

Remaining in this tower (future sessions): the *general* (merely-continuous, non-Lipschitz `Dv`)
modulus; the *existence* of the variational flow family (global integral curves of the linear
field); the *differentiable* dependence of the resolvent on its coefficient field — now reduced to a
fixed-point / Neumann analysis of the Duhamel difference formula `fundamentalSolution_sub_eq_integral`
above — toward the base-point `C^2`/`C^k` bootstrap.

Update — the resolvent path's **`C¹`-in-time regularity** is now packaged (axioms
`propext`/`Classical.choice`/`Quot.sound` only):

* `deriv_fundamentalSolution` — the explicit `deriv` readout of the operator ODE:
  `deriv (t ↦ D_x Φ_t) = A t ∘ D_x Φ_t` (from `hasDerivAt_fundamentalSolution`).
* `contDiff_one_fundamentalSolution` — the curve `t ↦ D_x Φ_t ∈ E →L[ℝ] E` is `ContDiff ℝ 1`:
  differentiable everywhere with the norm-continuous derivative `t ↦ A t ∘ D_x Φ_t`
  (`contDiff_one_iff_deriv`).  This is the packaged regularity (vs. the raw `HasDerivAt` + continuity
  pieces) that higher-order `C^k` consumers compose against.
* `norm_integral_comp_fundamentalSolution_le` — the **a priori bound on the Duhamel source term**:
  for any operator path `B` with `‖B σ‖ ≤ ε` (`0 ≤ ε`),
  `‖∫_{t₀}^{t} B σ ∘ D_x Φ_σ dσ‖ ≤ ε · exp (K · |t - t₀|) · |t - t₀|` (pointwise
  `‖B σ ∘ D_x Φ_σ‖ ≤ ε · exp (K · |σ - t₀|) ≤ ε · exp (K · |t - t₀|)` via submultiplicativity +
  `norm_fundamentalSolution_le` + the endpoint-maximised exponential, integrated by
  `intervalIntegral.norm_integral_le_of_norm_le_const`).  Applied with `B = A₁ - A₂` this is the size
  of the inhomogeneous forcing in `fundamentalSolution_sub_eq_integral` — the leading-order resolvent
  response to a coefficient perturbation of size `ε`.

Remaining in this tower (future sessions): the *general* (merely-continuous, non-Lipschitz `Dv`)
modulus; the *existence* of the variational flow family (global integral curves of the linear
field); differentiable dependence of the resolvent on its coefficient field (the second-order
variational equation), built on the Volterra identity above, toward the base-point `C^2`/`C^k`
bootstrap.

Update — the resolvent's **`C^k` regularity in time** is now proved (all axioms
`propext`/`Classical.choice`/`Quot.sound` only), promoting the `C¹`-in-time result to arbitrary
order and adding a general integral-curve regularity lemma that also covers the base (nonlinear)
flow.  These are the time-direction half of the `C^k` regularity the DeTurck / Ricci-flow bootstrap
consumes:

* `contDiff_fundamentalSolution_time` — the **operator bootstrap**: if the coefficient path `A` is
  `C^n` in time (`ContDiff ℝ n A`) then the resolvent `t ↦ D_x Φ_t ∈ E →L[ℝ] E` is `C^{n+1}`.
  Induction on `n`: base `n = 0` is `contDiff_one_fundamentalSolution` (continuous `A` ⟹ `C¹`
  resolvent); the step reads `deriv (t ↦ D_x Φ_t) = A t ∘ D_x Φ_t` off the operator ODE
  (`deriv_fundamentalSolution`), a `ContDiff.clm_comp` of the `C^{n+1}` field with the
  inductively-`C^{n+1}` resolvent, so `deriv W ∈ C^{n+1}` and `W ∈ C^{n+2}`
  (`contDiff_succ_iff_deriv`).  `contDiff_infty_fundamentalSolution_time` is the `C^∞` corollary
  (order-by-order via `contDiff_infty`).
* `contDiff_fundamentalSolution_apply_time` / `contDiff_infty_…` — the resolvent **action**
  `t ↦ D_x Φ_t · u₀` (pushforward of a fixed vector) is `C^{n+1}` / `C^∞`, via evaluation-at-`u₀`
  (`ContDiff.clm_apply`); `contDiff_fundamentalSolution_apply_joint` / `contDiff_infty_…` upgrade
  this to the **joint** `(t, u₀) ↦ D_x Φ_t · u₀` on `ℝ × E` (pull back along `Prod.fst`, evaluate
  against `Prod.snd`).  These are the pushforward-leg forms Item 1's tensor time-derivative chain
  rule consumes.
* `hasDerivAt_deriv_fundamentalSolution` / `deriv_deriv_fundamentalSolution` — the **explicit
  second-order time equation** of the resolvent (the `k = 2` instance made concrete): for a `C¹`
  coefficient (`A' = deriv A`), `d/dt (A t ∘ D_x Φ_t) = A' t ∘ D_x Φ_t + A t ∘ (A t ∘ D_x Φ_t)`,
  the operator product rule `HasDerivAt.clm_comp` applied to the resolvent velocity field with the
  first-order operator ODE as the second factor.
* `contDiff_of_isIntegralCurve` — the **general** integral-curve regularity (not tied to the linear
  variational field): an integral curve `γ` of a jointly-`C^n` field
  (`ContDiff ℝ n (Function.uncurry v)`) is `C^{n+1}` in time — `γ'(t) = v t (γ t) = (↿v)(t, γ t)` is
  a `ContDiff.comp` of `↿v` with `t ↦ (t, γ t)`.  `contDiff_infty_of_isIntegralCurve` is the `C^∞`
  form, and `contDiff_flow_time` / `contDiff_infty_flow_time` specialise to a flow family (each
  trajectory `t ↦ Ψ x t` is `C^{n+1}` / `C^∞`) — the time-regularity of the **base** gauge flow that
  Item 2's compact-manifold flow consumes.

Remaining in this tower (future sessions): the *general* (merely-continuous, non-Lipschitz `Dv`)
spatial modulus (Heine–Cantor uniform continuity on the compact trajectory tube); the *existence* of
the variational flow family (global integral curves of the linear field — Mathlib supplies only
local Picard–Lindelöf, so this needs a continuation / Bielecki-norm argument); and the *spatial*
`C^k`/`C^2` bootstrap (differentiable dependence of `x₀ ↦ D_x Φ_t` on the base point, via
differentiable dependence of the resolvent on its coefficient).

Update — the **second-order variational equation** (differentiable dependence of the resolvent on its
coefficient field) is now proved (all axioms `propext`/`Classical.choice`/`Quot.sound` only),
promoting the Duhamel *difference* formula `fundamentalSolution_sub_eq_integral` and the coefficient
*Lipschitz* bound `norm_fundamentalSolution_sub_le_of_forall_le` to a genuine second-order (Gateaux)
derivative.  For coefficients `A₁`, `A₂` (`‖·‖ ≤ K`, norm-continuous) with `ε`-small gap
(`‖A₁ s - A₂ s‖ ≤ ε`) and resolvents `W₁ = D_x Φ₁`, `W₂ = D_x Φ₂`:

* `hasDerivAt_fundamentalSolution_sub` — the **differential form of the Duhamel gap equation**: the
  resolvent gap `t ↦ W₁ t - W₂ t` solves the inhomogeneous operator ODE
  `d/dt (W₁ - W₂) = A₁ ∘ (W₁ - W₂) + (A₁ - A₂) ∘ W₂` (subtract the two operator ODEs `W₁' = A₁ ∘ W₁`,
  `W₂' = A₂ ∘ W₂` of `hasDerivAt_fundamentalSolution` and regroup via bilinearity of composition
  `comp_sub`/`sub_comp`).  Homogeneous part propagates the gap; source `(A₁ - A₂) ∘ W₂` is the leading
  coefficient-perturbation forcing.  This is the differential ancestor of the integral identity
  `fundamentalSolution_sub_eq_integral`.
* `norm_fundamentalSolution_sub_sub_variation_le` — the **second-order remainder bound**: given the
  *first variation* `V` (a solution of the inhomogeneous operator ODE `V' = A₂ ∘ V + (A₁ - A₂) ∘ W₂`,
  `V t₀ = 0`, the leading linear response of the resolvent to the coefficient perturbation), the gap
  agrees with its linear prediction `V` to second order,
  `‖(W₁ t - W₂ t) - V t‖ ≤ ε² · exp (K (T - t₀)) · (gronwallBound 0 K 1 (T - t₀))²` on `[t₀, T]`.
  Proof: the remainder `R := (W₁ - W₂) - V` solves the *homogeneous* variational ODE
  `R' = A₂ ∘ R + (A₁ - A₂) ∘ (W₁ - W₂)` (subtract the first-variation ODE from the gap ODE — the two
  `(A₁ - A₂) ∘ W₂` sources cancel), `R t₀ = 0`, with an `O(ε²)` forcing (since the gap is `O(ε)` by
  `norm_fundamentalSolution_sub_le_of_forall_le`); operator Grönwall
  (`norm_le_gronwallBound_of_norm_deriv_right_le`) closes it.  This is the exact second-order
  variational equation the base-point `C²` bootstrap consumes.
* `norm_fundamentalSolution_variation_le` — the **`O(ε)` a-priori bound on the first variation**:
  `‖V t‖ ≤ ε · exp (K (T - t₀)) · gronwallBound 0 K 1 (t - t₀)` on `[t₀, T]` (Grönwall on the
  inhomogeneous ODE for `V`, its forcing `(A₁ - A₂) ∘ W₂` bounded by `ε · exp (K (T - t₀))`).
  Together with the second-order remainder this exhibits `W₁ - W₂ = V + O(ε²)` with linear leading
  term `V = O(ε)` — so `V` is genuinely the (Gateaux) derivative of the resolvent in the coefficient
  direction `A₁ - A₂`.

Remaining after this (future sessions): the *existence* / linearity-in-perturbation of the first
variation `V` (so the Gateaux derivative assembles into a bounded linear map of the coefficient
perturbation, upgrading the estimate to honest Fréchet differentiability of `A ↦ D_x Φ_t`); the
*general* merely-continuous spatial modulus; the *existence* of the variational flow family; and the
resulting *spatial* `C^k`/`C^2` bootstrap (`x₀ ↦ D_x Φ_t` differentiable in the base point, its
coefficient `A(x₀) s = D_x v(s, Φ x₀ s)` feeding the above).

Update — the **linearity-in-perturbation of the first variation** is now proved (all axioms
`propext`/`Classical.choice`/`Quot.sound` only), closing the *algebraic* half of the
existence/linearity target above.  The first variation `V` (solution of the inhomogeneous operator
ODE `V' = A ∘ V + F` anchored at `V t₀ = 0`, with the coefficient-perturbation forcing
`F = (A₁ - A₂) ∘ W₂` *linear* in the perturbation `A₁ - A₂`) is exhibited as a genuinely **bounded
linear** and **single-valued** function of the perturbation:

* `hasDerivAt_inhomogVariation_add` / `hasDerivAt_inhomogVariation_smul` /
  `hasDerivAt_inhomogVariation_sub` — **superposition** for the inhomogeneous variational ODE: the
  solution set is closed under addition, scalar multiplication and subtraction of the forcing
  (`(V₁ ± V₂)' = A ∘ (V₁ ± V₂) + (F₁ ± F₂)`, `(c • V)' = A ∘ (c • V) + c • F`), from `HasDerivAt.add`
  /`.const_smul`/`.sub` and bilinearity of composition (`comp_add`/`comp_smul`/`comp_sub`).
* `inhomogVariation_unique` — **uniqueness**: two anchored solutions of the *same* forcing agree
  everywhere (the difference solves the homogeneous variational ODE with zero anchor, killed by
  Grönwall uniqueness `variational_eq_of_isIntegralCurve`).  Makes the first variation single-valued.
* `hasDerivAt_firstVariation_perturbation_add` / `_smul` / `_sub` — the **coefficient-perturbation**
  specialisations (generic background resolvent `W`): the first variation for `B₁ ± B₂` / `c • B` is
  `V₁ ± V₂` / `c • V`, via linearity of `B ↦ B ∘ W` (`add_comp`/`smul_comp`/`sub_comp`).
* `norm_inhomogVariation_le` — the **general (forcing-agnostic) a-priori size bound**:
  `‖V t‖ ≤ M · gronwallBound 0 K 1 (t - t₀)` on `[t₀, T]` for any `V' = A ∘ V + F` (`‖A‖ ≤ K`,
  `‖F‖ ≤ M`), of which `norm_fundamentalSolution_variation_le` (forcing `(A₁ - A₂) ∘ W₂`,
  `M = ε · exp (K (T - t₀))`) is the leading instance.  Grönwall
  (`norm_le_gronwallBound_of_norm_deriv_right_le`).
* `norm_firstVariation_perturbation_sub_le` — **Lipschitz dependence on the perturbation**:
  `‖V₁ t - V₂ t‖ ≤ (ε · C) · gronwallBound 0 K 1 (t - t₀)` when `‖B₁ - B₂‖ ≤ ε`, `‖W‖ ≤ C` on
  `[t₀, T]` (`V₁ - V₂` is the first variation for `B₁ - B₂`, size-bounded by `norm_inhomogVariation_le`).
  Continuity/boundedness of the Gateaux-derivative map `perturbation ↦ V`.
* `inhomogVariation_eq_zero_of_forcing_zero` — the **origin value**: zero perturbation gives the zero
  first variation (uniqueness against the zero solution) — a linear map sends `0` to `0`.
* `firstVariation_perturbation_add_eq` / `firstVariation_perturbation_smul_eq` — the **map-level**
  linearity: the unique anchored first variation for `B₁ + B₂` (resp. `c • B`) *equals* `V₁ + V₂`
  (resp. `c • V`) as a pointwise identity (superposition + uniqueness).  With the origin value this
  makes `perturbation ↦ V` a genuine **linear map**.
* `inhomogVariation_eq_integral` — the **Volterra/Picard fixed-point equation**:
  `V t = ∫_{t₀}^{t} (A σ ∘ V σ + F σ) dσ` (FTC + anchor), companion to
  `fundamentalSolution_eq_one_add_integral`; the integral-equation entry point for the *existence*
  half.

Remaining after this (future sessions): the **existence** of the first variation `V` (the
continuation-flavoured half — Mathlib supplies only local Picard–Lindelöf; construct the global
anchored solution of the linear inhomogeneous ODE, e.g. by continuation/Bielecki iteration of the
Volterra equation `inhomogVariation_eq_integral`, or by reduction to a homogeneous flow on the
augmented state `L(E) × ℝ`); the *general* merely-continuous spatial modulus; the *existence* of the
variational flow family; and the resulting *spatial* `C^k`/`C^2` bootstrap (`x₀ ↦ D_x Φ_t`
differentiable in the base point).

Update — the **existence half is now CLOSED** (all axioms `propext`/`Classical.choice`/`Quot.sound`
only): the complete ODE existence tower from Mathlib's local Picard–Lindelöf up to a *global* integral
curve of a globally (in state, uniformly in time) Lipschitz field is proved in `SmoothDependenceCk`,
and applied to construct the first variation `V` and the resolvent `W = D_x Φ`.  This discharges the
flow-existence hypothesis (`∀ s, HasDerivAt z …` / `IsIntegralCurve`) that every downstream
first-variation and `fundamentalSolution` lemma in the file previously assumed.  New
`public import Mathlib.Analysis.ODE.PicardLindelof`.

* `lipschitzFlowStep K = min 1 (1/(2(K+1)))` (`_pos`, `_le_one`, `_mul_le`: `K·step ≤ 1/2`) — the
  **uniform, anchor-independent** local-existence half-step.
* `exists_isIntegralCurveOn_Icc_of_lipschitzWith` — **uniform-step local existence**: for a uniformly
  `K`-Lipschitz (`∀ t, LipschitzWith K (v t)`), time-continuous (`∀ x, Continuous (v · x)`) field on a
  complete Banach space, an integral curve through any `(t₀, x₀)` on `Icc (t₀-step) (t₀+step)`.  Built
  by assembling `IsPicardLindelof` (ball radius `a = 2·step·(C₀+1)+1`, bound `L = K·a+C₀+1`,
  `C₀ = sup_{Icc} ‖v · x₀‖`, giving `L·step ≤ a-½ ≤ a`) and
  `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`.  The *uniform* step (from choosing a
  large ball) is what allows chaining across arbitrarily long intervals.
* `exists_isIntegralCurveAt_of_lipschitzWith` — the `IsIntegralCurveAt` (local-at-a-point) form.
* `exists_isIntegralCurveOn_Icc_forward_of_lipschitzWith` — **forward** existence on *every* `Icc t₀ T`
  by induction on the number of uniform steps (base = local existence; step = extend by one local
  solution at the right endpoint, `isIntegralCurveOn_glue_Icc`); Archimedean choice of step count.
* `exists_isIntegralCurveOn_Icc_backward_of_lipschitzWith` — **backward** existence on `Icc T t₀` via
  the time-reversed field `w t x = -(v(-t)x)` (uniformly `K`-Lipschitz by `LipschitzWith.neg`) and
  `isIntegralCurveOn_comp_neg`.
* `exists_isIntegralCurveOn_Icc_of_lipschitzWith_containing` — **two-sided**: a *single* integral curve
  on any `Icc a b` with `a ≤ t₀ ≤ b` (glue backward on `Icc a t₀` and forward on `Icc t₀ b` at `t₀`).
* `eqOn_of_isIntegralCurveOn_Icc` — **interval uniqueness** (Mathlib `ODE_solution_unique_of_mem_Icc`,
  trivial state constraint; interior `HasDerivAt` + `IsIntegralCurveOn.continuousOn`).
* `exists_isIntegralCurve_of_lipschitzWith` — **GLOBAL existence**: choose a solution `Γ n` on each
  window `Icc (t₀-(n+1)) (t₀+(n+1))`, reconcile overlaps by interval uniqueness so the selection
  `γ t = Γ ⌊|t-t₀|⌋₊ t` is unambiguous and equals `Γ m` on `Icc (t₀-m) (t₀+m)`, then exhaust via
  `isIntegralCurve_of_forall_mem_Icc`.
* `exists_hasDerivAt_inhomogVariation` — **existence of the first variation**: for norm-bounded
  continuous `A, F`, a global `V` with `V t₀ = 0`, `V' = A∘V + F` (feed `augmentedVariationalField A F`
  — uniformly `(K+M)`-Lipschitz, time-continuous — into global existence; operator coordinate via
  `hasDerivAt_inhomogVariation_of_augmented`).  Closes the existence half of the first-variation target.
* `exists_hasDerivAt_resolvent` — **existence of the resolvent** `W' = A∘W`, `W t₀ = 1` (homogeneous
  field `W ↦ (A s)∘W`, `K`-Lipschitz + time-continuous, on the complete space `E →L[ℝ] E`).

Remaining after this (future sessions): the *general* merely-continuous spatial modulus (Heine–Cantor
on the compact trajectory tube); the **spatial `C^k`/`C^2` bootstrap** (`x₀ ↦ D_x Φ_t` differentiable
in the base point — now feedable, since the resolvent whose coefficient is `A(x₀) s = D_x v(s, Φ x₀ s)`
is a constructed object); and packaging the first variation as a bounded *linear map* of the
perturbation (Fréchet, via the existing linearity/uniqueness/bound lemmas + this existence).

Update — the **spatial `C¹` bootstrap is now CLOSED at the Banach level** for a `C^{1,1}` field (all
axioms `propext`/`Classical.choice`/`Quot.sound` only): the flow families are constructed from the
existence tower, and the base-point differentiable dependence — `x₀ ↦ Φ x₀ t` Fréchet differentiable
with derivative the resolvent — is assembled unconditionally from *field-level* data (no flow family,
coefficient path, or resolvent supplied by the caller).  This turns the whole conditional
`C¹`-dependence tower (`hasFDerivAt_flow_of_lipschitz_deriv`, …) into a self-contained theorem.

* `exists_flow_family` — **existence of the flow family**: for a uniformly `K`-Lipschitz,
  time-continuous field `v` on a complete Banach space, a family `Φ : E → ℝ → E` with `Φ z t₀ = z` and
  `IsIntegralCurve (Φ z) v` for every `z` (`choose` an integral curve through each `(t₀, z)` out of the
  global existence theorem `exists_isIntegralCurve_of_lipschitzWith`).  The `(hΦ, h0)` datum.
* `exists_variationalFlowFamily` — **existence of the variational flow family**: for a norm-bounded
  (`‖A s‖₊ ≤ K`), continuous coefficient `A`, the `variationalFieldVec A` specialisation of
  `exists_flow_family` (field `K`-Lipschitz via `lipschitzWith_variationalFieldVec`, time-continuous
  via `Continuous.clm_apply`).  The `(hΦ', h0')` datum, hence the resolvent `fundamentalSolution`.
* `exists_hasFDerivAt_flow_of_lipschitz_deriv` — **unconditional base-point differentiable
  dependence**: given `v` uniformly `K`-Lipschitz + time-continuous with an everywhere-defined,
  jointly continuous (`hDvc`), spatially `L`-Lipschitz (`hDvlip`) Fréchet derivative `Dv`, there exist a
  flow family `Φ` of `v` and a bounded operator `D` (the resolvent `D_x Φ_t`) with `HasFDerivAt
  (fun z => Φ z t) D x₀` at any `x₀`, `t ≥ t₀`.  Proof: `exists_flow_family` builds `Φ`; the coefficient
  `A s = Dv s (Φ x₀ s)` is norm-`≤ K` (`HasFDerivAt.le_of_lipschitz`) and continuous, so
  `exists_variationalFlowFamily` builds `Φ'`/`D`; `hasFDerivAt_flow_of_lipschitz_deriv` closes it
  (segment derivative via `HasFDerivAt.hasFDerivWithinAt`, Lipschitz defect via `hDvlip`).
* `exists_flow_differentiable_of_lipschitz_deriv` — **`C¹` in initial data everywhere**: a *single*
  flow family `Φ` of `v` whose time-`t` slice `z ↦ Φ z t` is `Differentiable ℝ` (Fréchet differentiable
  at every initial value) — the clean regularity statement (build `Φ` once, differentiate at each `x₀`).

Remaining after this (future sessions): the *general* merely-continuous spatial modulus (Heine–Cantor
on the compact trajectory tube — upgrades `C^{1,1}` to a general `C¹` field); the **spatial `C^2`/`C^k`
bootstrap** (differentiate `x₀ ↦ D_x Φ_t` once more, via the now-constructed resolvent and the
second-order variational equation `norm_fundamentalSolution_sub_sub_variation_le`); and packaging the
first variation as a bounded *linear map* of the perturbation (Fréchet).

Update — the **coefficient-side second-order (`C²`) estimate layer is now built** in
`SmoothDependenceCk` (all axioms `propext`/`Classical.choice`/`Quot.sound` only), supplying every
coefficient-side input the base-point `C²` bootstrap feeds to the second-order variational estimate
`norm_fundamentalSolution_sub_sub_variation_le`.  The coefficient is `A(x₀) s = Dv s (Φ x₀ s)`, the
linearisation of the field along the reference trajectory, with resolvent `R s = D_x Φ_s =
fundamentalSolution … s`.

* `hasFDerivAt_derivField_apply_flow` / `differentiableAt_derivField_apply_flow` — **the coefficient
  chain rule `∂A/∂x₀`**: from the flow derivative `HasFDerivAt (fun z => Φ z s) R x₀` (the `C¹`
  resolvent) and the field's *second* spatial derivative `HasFDerivAt (Dv s) D2 (Φ x₀ s)`, the
  coefficient `z ↦ Dv s (Φ z s)` is Fréchet differentiable at `x₀` with derivative
  `D2.comp R = D²v s (Φ x₀ s) ∘ D_x Φ_s` (pure `HasFDerivAt.comp`).
* `lipschitzWith_derivField_apply_flow`, `..._of_abs_le`, `norm_derivField_apply_flow_sub_le` — **the
  `ε = O(‖z − w‖)` size datum** (`hAA'`/`hε` of the second-order variational estimates): `Dv s`
  `L`-Lipschitz composed with the flow's exponential Lipschitz bound gives
  `‖Dv s (Φ z s) − Dv s (Φ w s)‖ ≤ L · exp (K T) · ‖z − w‖` uniformly on `|s − t₀| ≤ T`.
* `norm_flow_sub_fundamentalSolution_le_uniform` — **the uniform-in-time first-order flow remainder**:
  `norm_flow_sub_fundamentalSolution_le_Icc` with the `t`-dependent Grönwall factor replaced by its
  endpoint value (`gronwallBound_mono`), so `‖(Φ y t − Φ x t) − D_x Φ_t (y − x)‖ ≤
  δ · gronwallBound 0 K 1 (T − t₀)` for *all* `t ∈ [t₀, T]`.
* `norm_sub_fderiv_le_mul_sq_of_lipschitz` — **the pure quadratic `C^{1,1}` Taylor bound**:
  `‖g b − g a − g' a (b − a)‖ ≤ M ‖b − a‖²` for a map `g` with `M`-Lipschitz derivative `g'` (linearised
  MVT `Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'` + the segment bound `‖ξ − a‖ ≤ ‖b − a‖`);
  `norm_derivField_sub_sub_secondDeriv_le` is its `g = Dv s`, `g' = D²v s` specialisation.
* `norm_flow_sub_sq_le` — **flow-separation square bound** `‖Φ z s − Φ x s‖² ≤ exp (2 K T) ‖z − x‖²`
  (the square of `dist_flow_apply_le`).
* `norm_field_linearizationDefect_flow_le` + `norm_flow_sub_fundamentalSolution_le_sq` — **quantitative
  `C^{1,1}` dependence of the flow on initial data**: the field's trajectory-linearisation defect is
  `O(‖z − x₀‖²)` uniformly in `s`, which fed as `δ` to `norm_flow_sub_fundamentalSolution_le_uniform`
  upgrades the *qualitative* `C¹` (`HasFDerivAt`, remainder `o(‖z − x₀‖)`) to an *explicit* second-order
  rate `‖Φ z t − Φ x₀ t − D_x Φ_t (z − x₀)‖ ≤ L · exp (2K(T−t₀)) · gronwallBound 0 K 1 (T−t₀) · ‖z − x₀‖²`
  on `[t₀, T]`.
* `norm_derivField_sub_sub_comp_fundamentalSolution_le_sq` — **the central `C²` coefficient Taylor
  bound**: for a `C^{2,1}` field, `‖Dv s (Φ z s) − Dv s (Φ x₀ s) − (D²v s (Φ x₀ s) ∘ D_x Φ_s)(z − x₀)‖ ≤
  (M · e + C' · L · e · g) · ‖z − x₀‖²` (`e = exp (2K(T−t₀))`, `g = gronwallBound 0 K 1 (T−t₀)`)
  uniformly for `s ∈ [t₀, T]` — i.e. the coefficient is `C^{1,1}` in the base point with `O(‖z − x₀‖²)`
  remainder and derivative `∂A/∂x₀` above.  Split into the pure `Dv`-Taylor remainder
  (`norm_derivField_sub_sub_secondDeriv_le` + `norm_flow_sub_sq_le`) plus `D²v` applied to the flow's own
  quadratic remainder (`norm_flow_sub_fundamentalSolution_le_sq`).

Remaining for the base-point `C²` bootstrap (future sessions): assemble the above coefficient Taylor
bound (`= O(‖z − x₀‖²)` coefficient perturbation with linear leading term the chain-rule derivative)
with the second-order variational estimate `norm_fundamentalSolution_sub_sub_variation_le` and the
a-priori first-variation bound `norm_fundamentalSolution_variation_le` to conclude
`x₀ ↦ fundamentalSolution(A(x₀)) t = D_x Φ_t` is Fréchet differentiable (the first variation as a
bounded *linear* map of the base-point increment), giving the spatial `C²` regularity of the flow —
then iterate for `C³`.

Update — the **base-point `C²` numerator (second-order Taylor remainder of the resolvent in the base
point) is now CLOSED at the estimate level** (all axioms `propext`/`Classical.choice`/`Quot.sound`
only), assembling the coefficient Taylor bound with the second-order variational estimate to identify
the spatial `C²` derivative of the flow's resolvent up to an `O(‖z − x₀‖²)` remainder.  The
second-order variational machinery, previously stated with a *globally*-uniform coefficient gap, is
first re-cut in the interval-restricted form the base-point coefficients actually satisfy (their gap
`Dv s (Φ z s) − Dv s (Φ x₀ s)` is `≤ L exp(K(T−t₀)) ‖z−x₀‖` only on compact tubes, never globally):

* `norm_fundamentalSolution_sub_apply_le_of_forall_le_Icc`,
  `norm_fundamentalSolution_sub_le_of_forall_le_Icc` — the **interval-restricted resolvent-coefficient
  bounds**: the variants of `norm_fundamentalSolution_sub_apply/sub_le_of_forall_le` whose
  coefficient-gap hypothesis `‖A s − A′ s‖ ≤ ε` is required only on `[t₀, T]` (the proof evaluates the
  gap only there, through `dist_le_of_approx_trajectories_ODE`).
  `‖D_x Φ_t^A − D_x Φ_t^{A′}‖ ≤ ε · exp(K(T−t₀)) · gronwallBound 0 K 1 (t−t₀)`.
* `norm_fundamentalSolution_sub_sub_variation_le_Icc` — the **interval-restricted second-order
  variational estimate**: the variant of `norm_fundamentalSolution_sub_sub_variation_le` with the
  coefficient gap required only on `[t₀, T]` (via the interval sub-bound in `hgap` and directly on
  `Ico t₀ t` in `hbound`).  Given the first variation `V` (`V′ = A₂ ∘ V + (A₁ − A₂) ∘ W₂`, `V t₀ = 0`),
  `‖(W₁ t − W₂ t) − V t‖ ≤ ε² · exp(K(T−t₀)) · gronwallBound 0 K 1 (T−t₀)²` on `[t₀, T]`.
* `norm_firstVariation_sub_linearVariation_le_sq` — **second-order agreement of the true and the
  linearised first variation**: for the *true* first variation `Vz` (forcing `(A_z − A₀) ∘ W₀`) and the
  *linearised* first variation `Vlin` (chain-rule forcing `(D²v(Φ x₀ s) ∘ W₀ · (z − x₀)) ∘ W₀`),
  `‖Vz t − Vlin t‖ ≤ Cquad · exp(K(T−t₀)) · gronwallBound 0 K 1 (t−t₀) · ‖z − x₀‖²` (`Cquad` the
  coefficient Taylor constant `M e + C′ L e g`).  `Vz − Vlin` is the first variation for the *residual*
  coefficient perturbation (`hasDerivAt_firstVariation_perturbation_sub`), whose forcing is
  `≤ Cquad ‖z − x₀‖² · ‖W₀ s‖` (the coefficient Taylor bound
  `norm_derivField_sub_sub_comp_fundamentalSolution_le_sq` × `norm_fundamentalSolution_le`), closed by
  the general a-priori bound `norm_inhomogVariation_le`.
* `norm_fundamentalSolution_sub_sub_linearVariation_le_sq` — **the second-order Taylor remainder of the
  resolvent in the base point** (the spatial `C²` numerator): for a `C^{2,1}` field, the resolvent gap
  `W_z t − W₀ t` (`W₀ =` resolvent of `A₀ s = Dv s (Φ x₀ s)`, `W_z` of `A_z s = Dv s (Φ z s)`) agrees to
  second order with the *linearised* first variation `Vlin`,
  `‖(W_z t − W₀ t) − Vlin t‖ ≤ (L² e₁³ g² + Cquad e₁ g) · ‖z − x₀‖²` on `[t₀, T]`
  (`e₁ = exp(K(T−t₀))`, `g = gronwallBound 0 K 1 (T−t₀)`).  Triangle inequality across `Vz`:
  `‖(W_z t − W₀ t) − Vz t‖ ≤ ε² e₁ g²` (`norm_fundamentalSolution_sub_sub_variation_le_Icc`,
  `ε = L e₁ ‖z − x₀‖` from `norm_derivField_apply_flow_sub_le`) plus `‖Vz t − Vlin t‖`
  (`norm_firstVariation_sub_linearVariation_le_sq`).  Since `Vlin` is *linear* in `z − x₀` this is the
  resolvent analogue of the `C¹` numerator `norm_flow_sub_fundamentalSolution_le_sq`.
* `linearVariation_perturbation_add_eq`, `linearVariation_perturbation_smul_eq` — the **linearity of the
  candidate `C²` derivative**: the map `h ↦ Vlin^h t` is additive and homogeneous
  (`Vlin^{h₁+h₂} t = Vlin^{h₁} t + Vlin^{h₂} t`, `Vlin^{c•h} t = c • Vlin^h t`), since the chain-rule
  forcing `(D²v(Φ x₀ s) ∘ W₀)` is a bounded linear map of `h` (`map_add`/`map_smul`) and the
  first-variation map is linear (`firstVariation_perturbation_add_eq`/`_smul_eq`).  The algebraic half of
  packaging `h ↦ Vlin^h t` as a bounded linear map `D₂ ∈ E →L[ℝ] (E →L[ℝ] E)`.

Remaining for the base-point `C²` bootstrap (future sessions): (i) the **existence** of the true /
linearised first variations `Vz`, `Vlin` for these *time-unbounded* (locally bounded) forcings — the
forcing `(A_z − A₀) ∘ W₀` grows like `exp(K|s−t₀|)`, so the globally-bounded
`exists_hasDerivAt_inhomogVariation` does not apply; a compact-interval linear-ODE existence (Mathlib
local Picard–Lindelöf + continuation, without a global forcing bound) is needed.  (ii) **package**
`h ↦ Vlin^h t` as the bounded operator `D₂ = ∂/∂x₀ (D_x Φ_t)` via `LinearMap.mkContinuous` (linearity
above + the a-priori bound `norm_inhomogVariation_le` for boundedness), and (iii) feed `D₂` and the
Taylor remainder `norm_fundamentalSolution_sub_sub_linearVariation_le_sq` (uniform in `z` near `x₀`)
into `HasFDerivAt (fun z => D_x Φ_t^{A(z)}) D₂ x₀` — the spatial `C²` regularity — then iterate for
`C³`.

Update — **pieces (i) and (ii) of the base-point `C²` bootstrap are now CLOSED**, and the analytic
bridge for piece (iii) is in place (all axioms `propext`/`Classical.choice`/`Quot.sound` only).  The
recurring blocker — existence of the first variations `Vz`, `Vlin` for their *time-unbounded* forcings
— is dissolved by the observation that the **direct** inhomogeneous variation field
`inhomogVariationalField A F s W = (A s) ∘ W + F s` is *uniformly* `K`-Lipschitz in the state (the
forcing `F s` is a state-constant translation and cancels in the state-difference), so a globally
*continuous but unbounded* forcing still feeds the uniform-Lipschitz global existence — no augmented
scalar coordinate (which forced `‖F s‖ ≤ M`) and no time-truncation.

* `inhomogVariationalField`, `lipschitzWith_inhomogVariationalField`,
  `exists_hasDerivAt_inhomogVariation_of_continuous` — **existence of the first variation for a
  merely-continuous (time-unbounded) forcing**: for norm-bounded continuous `A` (`‖A s‖₊ ≤ K`) and
  *any* continuous `F`, the anchored `V' = A ∘ V + F`, `V t₀ = 0` has a global solution, directly from
  `exists_isIntegralCurve_of_lipschitzWith` on the uniformly-`K`-Lipschitz direct field.  The piece the
  globally-bounded `exists_hasDerivAt_inhomogVariation` could not supply.
* `exists_hasDerivAt_firstVariation_true` — **existence of the true first variation `Vz`** (forcing
  `(A_z − A₀) ∘ W₀`, `A₀ s = Dv s (Φ x₀ s)`, `A_z s = Dv s (Φ z s)`), forcing continuity via
  `Continuous.clm_comp` of `A_z − A₀` with `continuous_fundamentalSolution_time`.  Exactly the
  `hVz`/`hVz0` datum of `norm_fundamentalSolution_sub_sub_linearVariation_le_sq`.
* `exists_hasDerivAt_firstVariation_linearised` / `..._dir` — **existence of the linearised first
  variation `Vlin`** (chain-rule forcing `(D²v(Φ x₀ s) ∘ W₀ · h) ∘ W₀`), keyed on the increment
  `z − x₀` and (the `_dir` form) on a free direction `h`; forcing continuity via
  `Continuous.clm_comp`/`Continuous.clm_apply`.  Exactly the `hVlin`/`hVlin0` datum.  This closes
  **piece (i)** (existence of `Vz`, `Vlin`).
* `norm_linearisedFirstVariation_le` — **operator-norm bound for `Vlin`, linear in the direction**:
  `‖Vlin t‖ ≤ C' · exp(2K(T − t₀)) · ‖h‖ · gronwallBound 0 K 1 (t − t₀)` on `[t₀, T]`, with the constant
  independent of `h` (forcing bound `‖D²v‖ · ‖W₀‖ · ‖h‖ · ‖W₀‖ ≤ C' exp(2K(T−t₀)) ‖h‖` via
  submultiplicativity + `norm_fundamentalSolution_le`, closed by `norm_inhomogVariation_le`).  The
  boundedness datum for `mkContinuous`.
* `exists_continuousLinearMap_linearisedVariation` — **the candidate spatial `C²` derivative
  `D₂ = ∂/∂x₀(D_x Φ_t)` as a bounded operator** `E →L[ℝ] (E →L[ℝ] E)`: `D₂ h` equals the time-`t` value
  of *any* solution of the linearised ODE for direction `h`.  Built by `LinearMap.mkContinuous` from the
  canonical `h ↦ Vlin^h t` (chosen via `..._linearised_dir`), additive/homogeneous by
  `linearVariation_perturbation_add_eq`/`_smul_eq`, bounded by `norm_linearisedFirstVariation_le`;
  independence of the chosen solution by `inhomogVariation_unique`.  This closes **piece (ii)**.
* `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` (+ `differentiableAt_`/`fderiv_` corollaries) — **the
  analytic bridge for piece (iii)**: an `O(‖z − x₀‖²)` linearisation error near `x₀` gives
  `HasFDerivAt f f' x₀` (the quadratic error is `o(‖z − x₀‖)` since `C · ‖z − x₀‖ → 0`, via
  `isLittleO_of_norm_le_mul_of_tendsto_nhds_zero` and `HasFDerivAt.of_isLittleO`).  Exactly the shape
  produced by `norm_fundamentalSolution_sub_sub_linearVariation_le_sq` with `f' = D₂`.

Remaining for the base-point `C²` bootstrap (future sessions): **piece (iii)** — assemble the resolvent
map `z ↦ D_x Φ_t^{A(z)}` (via the canonical `fundamentalSolution`, independent of the flow family by
`fundamentalSolution_congr`), establish the eventual quadratic bound
`∀ᶠ z, ‖(W_z t − W₀ t) − D₂ (z − x₀)‖ ≤ C ‖z − x₀‖²` by substituting `D₂ (z − x₀) = Vlin^{z−x₀} t`
(`exists_continuousLinearMap_linearisedVariation`) into
`norm_fundamentalSolution_sub_sub_linearVariation_le_sq`, and feed it to
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq` — giving `HasFDerivAt (fun z => D_x Φ_t^{A(z)}) D₂ x₀`,
the spatial `C²` regularity — then iterate for `C³`.

Update — **the base-point `C²` bootstrap is now CLOSED** (piece (iii) assembled; all axioms
`propext`/`Classical.choice`/`Quot.sound` only).  The spatial `C²` regularity of the flow's resolvent —
the derivative of the resolvent `z ↦ D_x Φ_t` in the initial value, i.e. the *second* spatial
derivative of the flow — is proved from field-level data (`C^{2,1}` field), and both at a base point
and everywhere.  This completes the `C²` layer of the smooth-dependence tower that Items 1 & 2 consume.

* `exists_hasFDerivAt_fundamentalSolution_baseCurve` — **piece (iii), the assembly**:
  `∃ D₂, HasFDerivAt (fun z => fundamentalSolution (hAfun z) (hΨ z) (h0Ψ z) t) D₂ x₀`.  The packaged
  operator `D₂` (`exists_continuousLinearMap_linearisedVariation`) is identified as the Fréchet
  derivative of the resolvent map `z ↦ D_x Φ_t^{A(z)}` at the base point.  The uniform second-order
  Taylor remainder `norm_fundamentalSolution_sub_sub_linearVariation_le_sq` bounds
  `‖(W_z t − W₀ t) − Vlin t‖ ≤ C‖z − x₀‖²`; the operator characterisation gives `D₂(z − x₀) = Vlin t`;
  and `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` upgrades the `O(‖z − x₀‖²)` error to `HasFDerivAt`.
* `differentiableAt_fundamentalSolution_baseCurve` — the **`DifferentiableAt` corollary**: the resolvent
  map is Fréchet differentiable at `x₀`.
* `exists_hasFDerivAt_fderiv_flow_of_lipschitz_secondDeriv` — the **field-level, self-contained**
  second-derivative statement (mirroring the `C¹` `exists_hasFDerivAt_flow_of_lipschitz_deriv`): from a
  `C^{2,1}` field (uniformly `K`-Lipschitz, time-continuous `v` with everywhere-defined, jointly
  continuous, spatially `L`-Lipschitz `Dv` and everywhere-defined, jointly continuous, `M`-Lipschitz
  `D2v`) there is a flow family `Φ` of `v` whose resolvent map — identified via the `C¹` bootstrap
  `hasFDerivAt_flow_of_lipschitz_deriv` with `fderiv ℝ (fun w => Φ w t)` — is Fréchet differentiable at
  `x₀`.  I.e. `z ↦ Φ z t` is twice Fréchet differentiable at `x₀`.  Builds the flow family, the per-`z`
  variational families, and the `D2v ≤ L` bound (`C' = L`) internally.
* `exists_flow_fderiv_differentiable_of_lipschitz_secondDeriv` — the **everywhere** version: one flow
  family `Φ` whose resolvent map `z ↦ fderiv ℝ (fun w => Φ w t) z` is `Differentiable ℝ` (Fréchet
  differentiable at every initial value).  Mirrors the `C¹` `exists_flow_differentiable_of_lipschitz_deriv`.

Remaining for the smooth-dependence tower (future sessions): **the `C³` layer** — differentiate the
resolvent's derivative `x₀ ↦ D₂(x₀)` (the second fundamental solution) once more.  This needs the
*third-order* variational analysis: the `x₀`-dependence of `D₂` via a second variational equation for
the resolvent's resolvent, in the same style as the `C²` numerator
`norm_fundamentalSolution_sub_sub_linearVariation_le_sq` — a new numerator
`‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖ ≤ C‖z − x₀‖²` with `D₃` the packaged third variation — then the same
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq` bridge.  Alternatively, connect the now-complete `C²`
dependence to the manifold gauge-flow consumers of Items 1 & 2 directly.

Update — **the flow map is now `ContDiff ℝ 2` in the initial data** (honest continuous second
differentiability), together with the honest `C¹` (`ContDiff ℝ 1`) statement and the reusable
continuity primitives that bridge the earlier *differentiable*-only dependence results to Mathlib's
`ContDiff` vocabulary (all axioms `propext`/`Classical.choice`/`Quot.sound` only).  The earlier
`exists_flow_differentiable_of_lipschitz_deriv` / `exists_flow_fderiv_differentiable_of_lipschitz_secondDeriv`
only produced *differentiable* flow maps; the compact-manifold gauge flow (Item 2) consumes genuine
`C^k` (a *diffeomorphism* family, whose derivatives must vary continuously), i.e. `ContDiff`.

* `exists_flow_fderiv_continuous_of_lipschitz_deriv`, `exists_flow_contDiff_one_of_lipschitz_deriv` —
  the **`C¹`-in-initial-data upgrade** (`C^{1,1}` field): one flow family `Φ` whose forward slice
  `z ↦ Φ z t` is `Differentiable` **and** whose resolvent map `z ↦ fderiv ℝ (fun w => Φ w t) z = D_x Φ_t`
  is `Continuous` (in fact Lipschitz), hence `ContDiff ℝ 1`.  The resolvent-continuity half is the
  operator-norm continuous dependence of the resolvent on its coefficient
  (`norm_fundamentalSolution_sub_le_of_forall_le_Icc`) composed with the Lipschitz-in-base control of
  the trajectory-linearised coefficient (`norm_derivField_apply_flow_sub_le`).
* `norm_inhomogVariation_sub_le_of_gap` — **Lipschitz dependence of the inhomogeneous variation on its
  coefficient and forcing** (allowing the two coefficient fields to differ, unlike
  `hasDerivAt_inhomogVariation_sub`): `‖V₁ t − V₂ t‖ ≤ (α·N + β)·gronwallBound 0 K 1 (t − t₀)` from a
  coefficient gap `α`, second-solution bound `N`, forcing gap `β`.  The continuous-dependence primitive
  behind the second fundamental solution's base-point regularity.
* `norm_secondDerivField_apply_flow_sub_le` — the **`D²v`-along-flow Lipschitz bound** (second-derivative
  analogue of `norm_derivField_apply_flow_sub_le`): `‖D²v s (Φ z s) − D²v s (Φ w s)‖ ≤ M·exp(K T)·‖z − w‖`.
* `norm_fundamentalSolution_baseCurve_sub_le` — the **resolvent Lipschitz-in-base-point** estimate
  (`‖D_x Φ_t^{A(z)} − D_x Φ_t^{A(w)}‖ ≤ L·exp(K(T−t₀))·‖z−w‖·exp(K(T−t₀))·gronwallBound 0 K 1 (t−t₀)`).
* `norm_chainRuleForcing_sub_le` — the **perturbation estimate for the chain-rule forcing operator**
  `((P∘W)h)∘W`: `≤ (dp·w² + 2·p·w·dw)·‖h‖` under `‖P₁‖ ≤ p`, `‖W₁‖,‖W₂‖ ≤ w`, `‖P₁−P₂‖ ≤ dp`,
  `‖W₁−W₂‖ ≤ dw` (telescoping the composition).  The algebraic core of the forcing gap `β`.
* `exists_flow_contDiff_two_of_lipschitz_secondDeriv` — **the `ContDiff ℝ 2` assembly** (`C^{2,1}` field):
  `z ↦ Φ z t` is twice continuously Fréchet differentiable.  The `C¹` bootstrap gives
  `fderiv ℝ (fun w => Φ w t)` = resolvent; the base-point `C²` bootstrap (replicated with the *packaged*
  operator `D₂ z` of `exists_continuousLinearMap_linearisedVariation`) gives
  `fderiv ℝ (fderiv ℝ (fun w => Φ w t)) = D₂`; and the new **continuity of the second fundamental
  solution** `z ↦ D₂ z` is the Lipschitz bound `‖D₂ z − D₂ z₀‖ ≤ C·‖z − z₀‖`, obtained (for a unit
  direction `h`, via `D₂ z h − D₂ z₀ h = Vlin^{z,h} t − Vlin^{z₀,h} t`) from
  `norm_inhomogVariation_sub_le_of_gap` fed the coefficient gap
  (`norm_derivField_apply_flow_sub_le`), the second-solution bound (`norm_linearisedFirstVariation_le`),
  and the forcing gap (`norm_chainRuleForcing_sub_le` fed `norm_secondDerivField_apply_flow_sub_le` and
  `norm_fundamentalSolution_baseCurve_sub_le`).  Packaged via `contDiff_one_iff_fderiv` /
  `contDiff_succ_iff_fderiv`.

Remaining for the smooth-dependence tower (future sessions): the **`C³` layer** (third-order variational
analysis of `x₀ ↦ D₂(x₀)`, giving `ContDiff ℝ 3`), and/or the **`ContDiff ℝ 1`/`2` everywhere→jointly
in `(x, t)`** refinements and connecting the now-`ContDiff` initial-data dependence to the
manifold gauge-flow consumers of Items 1 & 2.

Update — **the `C³`-layer forcing toolkit is now under construction** (the third-order variational
analysis giving `ContDiff ℝ 3`).  The `C³` bootstrap replicates the `C²` continuity mechanism one order
up: the *third* fundamental solution `x₀ ↦ D₃(x₀)` (`= ∂/∂x₀ D₂(x₀)`) is characterised, per direction,
by an inhomogeneous linear variational ODE whose forcing is `∂/∂x₀` of the second-variation
chain-rule forcing `((D²v(Φz)∘W)h)∘W`.  Differentiating in the base point produces **three** forcing
terms: two *asymmetric composition* terms `((D²v(Φz)∘D₂(z))h)∘W(z)` and `((D²v(Φz)∘W(z))h)∘D₂(z)`
(where `D₂` is the second fundamental solution and `W` the resolvent), plus a *third-derivative* term
built from `D³v(Φz)` contracted once with a resolvent direction.  The generic driver
`norm_inhomogVariation_sub_le_of_gap` (which only needs a forcing gap `β`) is directly reusable at the
`D₃` level, so the new work is exactly the `β` (forcing-gap) and `N` (forcing-size) data for these three
terms.  This session adds the fully-proved, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`)
primitives that supply them:

* `norm_field_apply_flow_sub_le` — the **codomain-generic field-along-flow Lipschitz size datum**: for
  *any* seminormed target `F` and an `N`-Lipschitz field `DF s : E → F`, `z ↦ DF s (Φ z s)` moves by at
  most `N · exp (K T) · ‖z − w‖` on the tube `|s − t₀| ≤ T`.  Subsumes
  `norm_secondDerivField_apply_flow_sub_le` (`F := E →L[ℝ] (E →L[ℝ] E)`) and, crucially, sidesteps the
  fact that the *curried* triple `E →L[ℝ] E →L[ℝ] E →L[ℝ] E` carries **no** operator-norm instance in
  Mathlib v4.29.1 (verified).
* `norm_thirdDerivField_apply_flow_sub_le` — the **`D³v`-along-flow Lipschitz bound**, the third-order
  analogue of `norm_secondDerivField_apply_flow_sub_le`, with the third spatial derivative represented
  by the canonical `iteratedFDeriv`-target `ContinuousMultilinearMap ℝ (fun _ : Fin 3 => E) E` (which
  *does* carry clean `NormedAddCommGroup`/`NormedSpace` instances, unlike the curried triple).
* `norm_bilinearCompForcing_sub_le` — the **asymmetric composition-forcing perturbation**
  `‖((P₁∘A₁)h)∘B₁ − ((P₂∘A₂)h)∘B₂‖ ≤ (dp·a·b + p·da·b + p·a·db)·‖h‖` for *possibly-different* inner/outer
  operands `A ≠ B` (e.g. `A = D₂`, `B = W`).  Specialising `A = B = W` recovers exactly
  `norm_chainRuleForcing_sub_le` (`(dp·w² + 2p·w·dw)·‖h‖`) — verified.  Supplies the `β`-gap of the two
  asymmetric forcing terms.
* `norm_bilinearCompForcing_le` — the **a-priori size** `‖((P∘A)h)∘B‖ ≤ ‖P‖·‖A‖·‖B‖·‖h‖`, the `N`-datum
  bounding the (second) `D₃`-solution through `norm_inhomogVariation_le`.
* `norm_clm_apply_sub_le` — the **bilinear-evaluation gap**
  `‖T₁ u₁ − T₂ u₂‖ ≤ ‖T₁‖·‖u₁ − u₂‖ + ‖T₁ − T₂‖·‖u₂‖`, the telescoping split of a product gap into an
  operand-gap and an operator-gap part.
* `norm_thirdDerivCurryLeft_apply_flow_sub_le` — the **once-contracted `D³v`-field gap** (the `β`-gap of
  the third-derivative forcing term): `‖(D³v(Φz s)).curryLeft u₁ − (D³v(Φw s)).curryLeft u₂‖ ≤
  ‖D³v(Φz s)‖·‖u₁ − u₂‖ + N·exp(K T)·‖z − w‖·‖u₂‖`, assembled from `norm_clm_apply_sub_le`, the
  `curryLeft` isometry `ContinuousMultilinearMap.curryLeft_norm`, and
  `norm_thirdDerivField_apply_flow_sub_le`.

Remaining for the `C³` layer (future sessions): the **existence of the second-order (third) variation**
(`exists_hasDerivAt_secondVariation…`, the `D₃`-analogue of
`exists_hasDerivAt_firstVariation_linearised_dir`), the **packaged `D₃` operator** — which, because
`D₂ : E →L[ℝ] (E →L[ℝ] E)`, must be represented in a form avoiding the instance-less curried triple
(e.g. via `ContinuousMultilinearMap`/`curryLeft`) — the **second-order Taylor remainder**
`‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖ ≤ C‖z − x₀‖²`, and finally the `hasFDerivAt_of_eventually_norm_sub_sub_le_sq`
bridge to `ContDiff ℝ 3`.  The forcing-gap/size toolkit above is exactly the analogue of the
`C²`-continuity data (`norm_secondDerivField_apply_flow_sub_le`, `norm_fundamentalSolution_baseCurve_sub_le`,
`norm_chainRuleForcing_sub_le`) that drove `exists_flow_contDiff_two_of_lipschitz_secondDeriv`.

Update — **the `C³` third-variation existence-and-packaging chain is now complete** (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`).  The whole `D₃`-analogue of the `C²` existence→packaging
mechanism is proved:

* `exists_hasDerivAt_secondVariation_linearised_dir` — the **existence of the second-order (third)
  variation** (the `D₃`-analogue of `exists_hasDerivAt_firstVariation_linearised_dir`): the
  three-term third-variation ODE `V' = A₀ ∘ V + (F_A + F_B + F_C)`, `V t₀ = 0`, with the two asymmetric
  composition terms `F_A = ((D²v ∘ W₂) h) ∘ W`, `F_B = ((D²v ∘ W) h) ∘ W₂` and *any* continuous
  third-derivative term `F₃`, has a global solution (via `exists_hasDerivAt_inhomogVariation_of_continuous`,
  the asymmetric-term continuity by `clm_comp`/`clm_apply`).
* `continuous_thirdDerivForcing` + `exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv` —
  the **concrete** third-derivative forcing `F_C = (curryFin1 ((D³v.curryLeft (W k)).curryLeft (W h))) ∘ W`
  (`e ↦ D³v[W k, W h, W e]`, representing the third derivative via `curryLeft`/`continuousMultilinearCurryFin1`,
  which *do* carry norm/continuity instances, unlike the curried triple `E →L E →L E →L E`) and its
  continuity, giving the **fully-instantiated** third-variation existence.
* `norm_thirdDerivForcing_le` — the **`F_C` size datum** `‖(curryFin1 ((T.curryLeft a).curryLeft b)) ∘ W‖ ≤
  ‖T‖·‖a‖·‖b‖·‖W‖` (the `curryLeft`/`Fin 1` analogue of `norm_bilinearCompForcing_le`, via the `curryLeft`
  and `continuousMultilinearCurryFin1` isometries), completing the forcing-size toolkit for all three terms.
* `norm_thirdVariation_le` — the **a-priori size bound on the third variation** (the `D₃`-analogue of
  `norm_linearisedFirstVariation_le`): `‖V t‖ ≤ (2·C'·N₂·exp(K(T−t₀)) + C''·exp(3K(T−t₀))·‖k‖) ·
  gronwallBound 0 K 1 (t−t₀) · ‖h‖`, from the three forcing-term bounds + `norm_inhomogVariation_le`.
* `thirdVariation_perturbation_add_eq` / `thirdVariation_perturbation_smul_eq` — the **`h`-linearity**
  (additive + homogeneous) of the third variation (the whole three-term forcing is linear in `h` —
  `map_add`/`map_smul` through the operator applications and `curryLeft`/`curryFin1`, `add_comp`/`smul_comp` —
  so uniqueness `inhomogVariation_unique` identifies `V^{h₁+h₂} = V^{h₁} + V^{h₂}`, `V^{c•h} = c • V^h`).
* `exists_continuousLinearMap_thirdVariation` + `exists_continuousLinearMap_thirdVariation_norm_le` — the
  **packaged `D₃(k)` operator** `h ↦ D₃(k, h)` as a bounded linear map (for fixed base direction `k` and
  second fundamental solution curve `W₂`), the `D₃`-analogue of `exists_continuousLinearMap_linearisedVariation`
  (`LinearMap.mkContinuous` fed the `h`-linearity and the a-priori bound; value independent of the chosen
  solution by uniqueness), together with its operator-norm bound `‖D₃k‖ ≤ (…)·gronwallBound…`
  (`opNorm_le_bound` + `0 ≤ gronwallBound 0 K 1 (t−t₀)`).

Remaining for the `C³` layer (future sessions): the **second-order Taylor remainder**
`‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖ ≤ C‖z − x₀‖²` (the `D₃`-analogue of the `C²` numerator
`norm_fundamentalSolution_sub_sub_linearVariation_le_sq`, comparing the base-point difference of the
*second* fundamental solution to the packaged `D₃` via a `norm_inhomogVariation_sub_le_of_gap` Grönwall
estimate — needs the base-point machinery for `z ↦ D₂(z)` and a concrete second fundamental solution
curve `W₂ = ∂_{x₀} W`), then the already-available `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` bridge
to `ContDiff ℝ 3`; and/or the `k`-linearity/full bilinear `(k, h)` packaging of `D₃`.

Update — **the `C³` `D₃` packaging is now bilinear in `(k, h)`, and the second-order Taylor-remainder
scaffold is in place** (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`).  This closes the
`k`-linearity/bilinear-packaging item flagged above and lays the reusable Grönwall scaffold that the
remaining Taylor remainder plugs into:

* `curryLeft_add` / `curryLeft_smul` — the additivity/homogeneity of `ContinuousMultilinearMap.curryLeft`
  in the multilinear argument (via the linearity of `continuousMultilinearCurryLeftEquiv`), exposed as
  `simp`-usable rewrites (the plain `def` form is not matched by `map_add`/`map_smul` directly).  Needed
  to push the base direction `k` through the *outer* `curryLeft` of the third-derivative forcing `F_C`.
* `thirdVariation_baseDir_add_eq` / `thirdVariation_baseDir_smul_eq` — the **`k`-linearity of the third
  variation** (the base-direction analogue of the `h`-linearity `thirdVariation_perturbation_add_eq`/
  `_smul_eq`): with `W₂` itself linear in `k` (as it is when `W₂ k = ∂_{x₀} W · k`), the whole three-term
  forcing `F_A + F_B + F_C` is linear in `k` — `F_A`/`F_B` split via the linearity of `W₂ k`
  (`comp_add`/`add_comp`/`add_apply`, resp. `comp_smul`/`smul_comp`/`smul_apply`), `F_C` via the
  linearity of `W k` (`map_add`/`map_smul`) pushed through the two `curryLeft` layers (`map_add`/`map_smul`
  on the inner `D³v.curryLeft`, `curryLeft_add`/`curryLeft_smul` on the outer) — so
  `inhomogVariation_unique` identifies `V^{k₁+k₂} = V^{k₁} + V^{k₂}`, `V^{c•k} = c • V^k`.
* `exists_continuousLinearMap_thirdVariation_bilinear` — the **full bilinear operator**
  `D₃ : E →L[ℝ] (E →L[ℝ] (E →L[ℝ] E))`, `D₃ k h =` the time-`t` third variation.  Upgrades
  `exists_continuousLinearMap_thirdVariation` (inner `h` only, fixed `k`) to both directions: for each `k`
  the inner operator `D₃(k)` comes from `exists_continuousLinearMap_thirdVariation_norm_le` fed the
  `‖k‖`-scaled curve bound `‖W₂ k s‖ ≤ N₂·‖k‖` (so `‖D₃(k)‖ ≤ (…)·‖k‖`, genuinely `O(‖k‖)`); the outer
  `k`-additivity/homogeneity is the new `thirdVariation_baseDir_add_eq`/`_smul_eq` (through the value
  characterisation `D₃(k) h = V^{k,h} t` and ODE uniqueness), packaged by `LinearMap.mkContinuous`.  This
  is the object the base-point Taylor remainder `‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖` (with `k = z − x₀`)
  compares against.
* `norm_inhomogVariation_sub_sub_le_of_forcingGap` — the **second-order Taylor-remainder scaffold**
  (generic, phrased at the inhomogeneous-variation level): for `V₁` (coefficient `A₁`, forcing `F₁`), `V₀`
  and `V₃` (both reference coefficient `A₀`, forcings `F₀`, `F₃`), all anchored at `t₀`, the triple
  difference obeys `‖(V₁ t − V₀ t) − V₃ t‖ ≤ β · gronwallBound 0 K 1 (t − t₀)` where `β` bounds the
  **forcing gap** `((A₁ − A₀) ∘ V₁ + (F₁ − F₀)) − F₃`.  Proof: `W = (V₁ − V₀) − V₃` solves the
  `A₀`-coefficient inhomogeneous ODE `W' = A₀ ∘ W + (forcing gap)` (from `(hV₁.sub hV₀).sub hV₃` and the
  rearrangement `A₁ ∘ V₁ = A₀ ∘ V₁ + (A₁ − A₀) ∘ V₁`), so `norm_inhomogVariation_le` fed `β` closes it.
  The `D₃`-analogue of the *shape* of `norm_fundamentalSolution_sub_sub_linearVariation_le_sq`, isolating
  the whole remaining second-order content into the single forcing-gap hypothesis `hβ`.

Remaining for the `C³` layer (future sessions): the **forcing-gap estimate** `hβ` — that for the concrete
`D₂`/`D₃` instantiation (`A₁ = Dv(Φ z)`, `A₀ = Dv(Φ x₀)`, `V₁ = Vlin^{z,h}`, `V₀ = Vlin^{x₀,h}`,
`F₃ = F_A + F_B + F_C` with `W₂ = ∂_{x₀} W · (z − x₀)`) the forcing gap
`((A₁ − A₀) ∘ V₁ + (F₁ − F₀)) − F₃` is `O(‖z − x₀‖² · ‖h‖)` (a multi-term second-order Taylor analysis
with cancellation between `(A₁ − A₀) ∘ V₁` and the `D₃` forcing terms, using the built forcing-gap/size
toolkit and a concrete second fundamental solution curve `W₂ = ∂_{x₀} W`); feeding it to
`norm_inhomogVariation_sub_sub_le_of_forcingGap` gives the Taylor remainder, and the already-available
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq` bridge then yields `ContDiff ℝ 3`.

Update — **the design-independent forcing-gap size/remainder bricks and the base-point `C^{0,1}`
operator continuity of `D₂` are now proved** (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`),
chipping the remaining `C³` forcing-gap `hβ` from below with pieces that do **not** depend on the still-open
`F₃` design question flagged at the end of this update:

* `norm_linearisedFirstVariation_baseCurve_sub_le` — the **curve-level `V₁ − V₀ = O(‖z − x₀‖·‖h‖)`
  size datum**: for the two linearised first-variation curves in a common direction `h` at base points
  `z` and `x₀` (`Vz`, `Vx`, chain-rule forcings `((D²v(Φ·)∘W_·)h)∘W_·`), `‖Vz t − Vx t‖ ≤
  exp(K(T−t₀))³·(M + 3·L·C'·gronwallBound 0 K 1 (T−t₀))·‖z − x₀‖·‖h‖·gronwallBound 0 K 1 (t − t₀)`,
  uniformly on the tube.  Exposes as a standalone lemma the second-fundamental-solution-**curve**
  continuity previously only buried (at the time-`t` value) inside
  `exists_flow_contDiff_two_of_lipschitz_secondDeriv`; assembled from `norm_inhomogVariation_sub_le_of_gap`
  fed the coefficient gap (`norm_derivField_apply_flow_sub_le`), the `N`-bound
  (`norm_linearisedFirstVariation_le` + `gronwallBound_mono`), and the chain-rule forcing gap
  (`norm_chainRuleForcing_sub_le` + flow bounds); the messy `(α·N + β)·gronwall` constant collapses to the
  clean `exp³·(M + 3LC'g)` form by `Real.exp_add` + `ring`.
* `norm_coeffVariation_sub_secondDerivComp_le_sq` — the **second-order remainder of the
  coefficient-times-variation forcing term `(A₁ − A₀) ∘ V₁`**: isolates its linear-in-`(z − x₀)` part
  `(D²v(Φ x₀ s)[W_x (z − x₀)]) ∘ V₀` with a quadratic `O(‖z − x₀‖²·‖h‖)` remainder, via the telescope
  `P ∘ Vz − Q ∘ Vx = P ∘ (Vz − Vx) + (P − Q) ∘ Vx` fed `norm_derivField_apply_flow_sub_le ×
  norm_linearisedFirstVariation_baseCurve_sub_le` (cross term) and `norm_derivField_sub_sub_comp_
  fundamentalSolution_le_sq × norm_linearisedFirstVariation_le` (field-Taylor defect `P − Q`).
* `norm_chainRuleForcing_flow_sub_le` — the **standalone clean-constant `β` forcing-gap datum**:
  `‖F(z) s − F(x₀) s‖ ≤ exp(K(T−t₀))³·(M + 2·L·C'·gronwallBound 0 K 1 (T−t₀))·‖z − x₀‖·‖h‖` for the
  chain-rule forcing `F(z) s = ((D²v(Φ z s) ∘ W_z) h) ∘ W_z`, i.e. the base-point Lipschitz continuity of
  the second-variation forcing along the flow (`norm_chainRuleForcing_sub_le` + flow bounds, constant
  collapsed by `ring`).
* `norm_secondFundamentalSolution_op_sub_le` — the **honest operator-norm `C^{0,1}` statement for `D₂`**:
  `‖D₂z − D₂x‖ ≤ exp(K(T−t₀))³·(M + 3·L·C'·gronwallBound 0 K 1 (T−t₀))·gronwallBound 0 K 1 (t−t₀)·
  ‖z − x₀‖` for the packaged base-point second derivatives `D₂z, D₂x` (each characterised, à la
  `exists_continuousLinearMap_linearisedVariation`, by `D₂· h = Vlin t`).  Via `opNorm_le_bound`: per
  direction `h`, build the canonical variations (`exists_hasDerivAt_firstVariation_linearised_dir`),
  identify `D₂z h = Vz t`, `D₂x h = Vx t`, and bound by `norm_linearisedFirstVariation_baseCurve_sub_le`.
  This is the operator-norm `z ↦ D₂(z)` regularity datum the `C³` layer differentiates.

**Forcing-gap design note (open, for the next session).**  Writing `Ψ = (A₁ − A₀) ∘ V₁ + (F₁ − F₀)` for
the extra forcing that `V₁ − V₀` experiences (so `hβ` bounds `‖Ψ − F₃‖`), the first-order-in-`k` part of
`(A₁ − A₀) ∘ V₁` is `(D²v(Φ x₀)[W_x k]) ∘ V₀` (isolated by `norm_coeffVariation_sub_secondDerivComp_le_sq`,
`k = z − x₀`, `V₀ = Vlin^{x₀,h}`), while the current packaged `F₃ = F_A + F_B + F_C` accounts only for the
linear part of `(F₁ − F₀)`.  The two asymmetric terms are `F_A(s) = (e ↦ D²v(Φ x₀ s)[W₂ s h, W_x s e])`,
`F_B(s) = (e ↦ D²v(Φ x₀ s)[W_x s h, W₂ s e])` with `W₂ = Vlin^{x₀,k}` (the second fundamental solution
curve in direction `k`); the isolated leading term is `e ↦ D²v(Φ x₀ s)[W_x s k, V₀ s e]` with
`V₀ = Vlin^{x₀,h}`.  Because `W₂ = Vlin^{x₀,·}(k)` and `V₀ = Vlin^{x₀,·}(h)` are the **same** operator
curve evaluated at the two directions, matching the isolated leading term against `F_A`/`F_B` requires the
**symmetry of `D²v`** (`D²v[a,b] = D²v[b,a]`), which is currently **not** a hypothesis of the smooth-
dependence tower.  So the next `C³` step is either (i) add a `D²v`-symmetry hypothesis (available from
`ContDiff`/`secondDeriv` symmetry) and prove the leading-term cancellation, or (ii) verify whether `F₃`
needs an extra `(D²v[W_x k]) ∘ V₀` summand; then the remaining `hβ` pieces are the `(F₁ − F₀)` second-order
remainder (needs the multilinear `D³v` Taylor — note the curried triple `E →L E →L E →L E` has **no** norm
instance in Mathlib v4.29.1, verified, so use `ContinuousMultilinearMap ℝ (Fin 3) E`) plus the pure
quadratic remainders now available above.

Update — **the open forcing-gap design question is RESOLVED (option (ii)), and the entire
design-corrected `D₃` packaging chain is now built** (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`), in `AnalyticPDE/SmoothDependenceCk.lean`.  The ODE
derivation settles it: differentiating the second-variation ODE `V' = A₀ ∘ V₀ + ((D²v ∘ W) h) ∘ W` in
the base point (direction `k`) gives `∂_k(A₀ ∘ V₀) = (∂_k A₀) ∘ V₀ + A₀ ∘ (∂_k V₀)`; the coefficient
part `∂_k A₀ = D²v[W_x k]` contributes the **coefficient-variation leading term `(D²v[W_x k]) ∘ V₀`**,
which is *not* among `F_A`/`F_B`/`F_C` (those come only from differentiating the forcing) and which is
exactly the operator isolated by `norm_coeffVariation_sub_secondDerivComp_le_sq` as the
first-order-in-`k` part of `(A₁ − A₀) ∘ V₁`.  So the correct third-variation forcing is
`F₃ = (D²v[W_x k]) ∘ V₀ + F_A + F_B + F_C`; **no `D²v`-symmetry hypothesis is required**.  The whole
`C²`-packaging mechanism is replayed for this corrected forcing:

* `exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff` — corrected third-variation
  ODE existence (`F₃` slot fed `newLeading + F_C`).
* `norm_thirdVariation_coeff_le` — corrected a-priori size bound (four-term forcing; the leading term
  bounded via `norm_bilinearCompForcing_le` fed `‖V₀‖ ≤ N₀`).
* `thirdVariation_coeff_perturbation_add_eq` / `_smul_eq` — additivity/homogeneity **in `h`** (the
  leading term forces `V₀` to be linear in `h` as well: `(h, V₀)`-jointly linear, via
  `add_comp`/`comp_add`/`smul_comp`/`comp_smul`).
* `exists_continuousLinearMap_thirdVariation_coeff` / `_norm_le` — the packaged corrected operator
  `D₃(k) : E →L (E →L E)` (`V₀ = V0fun h` supplied linearly, `‖V0fun h s‖ ≤ N₀·‖h‖` so the bound
  factors `‖h‖`) with operator norm `‖D₃k‖ ≤ (2C'N₂exp + C'N₀exp‖k‖ + C''exp³‖k‖)·gronwall`.
* `thirdVariation_coeff_baseDir_add_eq` / `_smul_eq` — additivity/homogeneity **in `k`** (the leading
  term carries `k` explicitly with `V₀` fixed; `W₂` linear in `k`).
* `exists_continuousLinearMap_thirdVariation_coeff_bilinear` — the **full bilinear corrected operator**
  `D₃ : E →L (E →L (E →L E))` (`W₂` linear in `k` with `‖W₂ k s‖ ≤ N₂·‖k‖`, `V0fun` linear in `h`;
  `‖k‖`-linear operator norm).  This is the design-corrected `D₃` that the base-point second-order
  Taylor remainder consumes.

Remaining for `ContDiff ℝ 3` (next session): the **`(F₁ − F₀)` second-order remainder**
`‖(F₁ − F₀) − (F_A + F_B + F_C)‖ ≤ Cquad·‖z − x₀‖²·‖h‖` (the flow-forcing Taylor defect: `D²v(Φz) −
D²v(Φx₀) ≈ D³v[W_x k]` and `W_z − W_x ≈ W₂ k` expansions, using `norm_bilinearCompForcing_sub_le`,
`norm_thirdDerivCurryLeft_apply_flow_sub_le`, and the `D³v` Taylor).  Combined with the already-proved
coefficient remainder `norm_coeffVariation_sub_secondDerivComp_le_sq`, this gives the forcing gap `hβ`
for the **corrected** `F₃`; then `norm_inhomogVariation_sub_sub_le_of_forcingGap` yields the Taylor
remainder `‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖ ≤ C‖z − x₀‖²`, and `hasFDerivAt_of_eventually_norm_sub_sub_le_sq`
yields `ContDiff ℝ 3`.

Update — **the second-order (quadratic-remainder) Taylor engine for the composition forcing is now
proved**, isolating the analytic core of the `(F₁ − F₀)` remainder into a design-independent,
clean-typed algebraic engine (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`), in
`AnalyticPDE/SmoothDependenceCk.lean`:

* `norm_bilinearCompForcing_sub_sub_le` — the **`C³`-layer quadratic-remainder analogue** of the
  first-order (Lipschitz) perturbation bound `norm_bilinearCompForcing_sub_le`.  For the trilinear
  composition forcing `G(P, A, B) := ((P ∘ A) h) ∘ B` (linear in each of `P : E →L (E →L E)`,
  `A, B : E →L E`), it identifies the **three linear-variation terms**
  `G(dP,A₀,B₀) + G(P₀,dA,B₀) + G(P₀,A₀,dB)` with the remainder controlled *quadratically* by the
  factor Taylor remainders (`‖P₁ − P₀ − dP‖ ≤ εp`, etc.) and the first-order gaps
  (`‖P₁ − P₀‖ ≤ δp`, etc.):
  `‖(G(P₁,A₁,B₁) − G(P₀,A₀,B₀)) − (G(dP,A₀,B₀)+G(P₀,dA,B₀)+G(P₀,A₀,dB))‖ ≤ (εp·a·b + p·εa·b + p·a·εb +
  δp·δa·b + δp·a·δb + p·δa·δb + δp·δa·δb)·‖h‖`.  Proof: the exact trilinear (multilinear) expansion
  identity (`simp only [comp_sub, sub_comp, sub_apply]; abel`) + seven-term triangle inequality + the
  a-priori size bound `norm_bilinearCompForcing_le` on each summand.  This is the engine that matches the
  two asymmetric forcing terms `F_A = ((D²v ∘ W₂) h) ∘ W`, `F_B = ((D²v ∘ W) h) ∘ W₂` (with
  `dA = dB = W₂`) against the second-variation forcing gap `F(z) − F(x₀)` with the required `O(‖z − x₀‖²)`
  remainder.
* `norm_bilinearCompForcing_sub_sub_le_sq` — the **`O(‖k‖²)` collapse** of the engine in the **diagonal**
  operand shape `((P ∘ W) h) ∘ W` (inner and outer factors equal — exactly the second-variation
  forcing).  Fed first-order gaps linear in `k` (`dp·‖k‖`, `dw·‖k‖`) and quadratic Taylor remainders
  (`cp·‖k‖²`, `cw·‖k‖²`) and `‖k‖ ≤ 1`, the seven-term bound collapses to the single clean `C³`-target
  rate `(cp·w² + 2·p·cw·w + 2·dp·dw·w + p·dw² + dp·dw²)·‖k‖²·‖h‖` (the lone cubic cross term
  `dp·dw²·‖k‖³ ≤ dp·dw²·‖k‖²` via `‖k‖ ≤ 1`, `nlinarith`).  This is the `(F₁ − F₀)` remainder in the
  diagonal shape, its final `O(‖z − x₀‖²·‖h‖)` rate exposed — exactly the numerator shape the
  `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` bridge to `ContDiff ℝ 3` consumes.

These two reduce the remaining `(F₁ − F₀)` work to a **single** ingredient: identifying the `dP`-linear
term `G(D²v(Φz) − D²v(Φx₀), W, W)` (the exact `D²v`-difference contracted) with the module's `F_C`
(the `continuousMultilinearCurryFin1`/`D³v.curryLeft` form) up to `O(‖z − x₀‖²)` — i.e. the pure
`D²v`-along-flow Taylor `‖(D²v(Φz s) − D²v(Φx₀ s)) − D³v(Φx₀ s)[W_x k]‖ ≤ M·‖k‖²`.  **Representation
note (verified this session):** the curried triple `E →L E →L E →L E` (`= E →L (E →L (E →L E))`) carries
**no** `NormedAddCommGroup`/`NormedSpace` instance in Mathlib v4.29.1, so the natural
`norm_sub_fderiv_le_mul_sq_of_lipschitz` route (with `g = D²v(·)`, `g' = ∂D²v : E →L (E →L (E →L E))`)
does **not** type-check — the `D²v` Taylor must be done in the multilinear representation
`D²v : E → (E[×2]→L E)`, `D³v : E → (E →L (E[×2]→L E))` (both norm-carrying), then bridged to the
composition form via the `continuousMultilinearCurryFin1` isometries.

The **multilinear `D²v`-along-flow Taylor is now proved** (this session; all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`):

* `norm_secondDerivField_sub_sub_thirdDeriv_ml_le` — the pure quadratic Taylor bound
  `‖D²v s b − D²v s a − D³v s a (b − a)‖ ≤ M·‖b − a‖²` in the multilinear representation
  `D²v s : E → (E[×2]→L E)`, `D³v s : E → (E →L (E[×2]→L E))` (both norm-carrying — the point of the
  representation), a one-line specialisation of the codomain-generic
  `norm_sub_fderiv_le_mul_sq_of_lipschitz`; the `D²v`-analogue of `norm_derivField_sub_sub_secondDeriv_le`.
* `norm_secondDerivField_sub_sub_thirdDeriv_ml_flow_le` — its flow-tube form
  `‖D²v s (Φ z s) − D²v s (Φ x s) − D³v s (Φ x s) (Φ z s − Φ x s)‖ ≤ M·exp (2 K T)·‖z − x‖²` (uniform on
  `|s − t₀| ≤ T`), combining the pure bound with the flow-separation square bound `norm_flow_sub_sq_le`;
  the `D²v`-analogue of `norm_field_linearizationDefect_flow_le`.

Remaining for `ContDiff ℝ 3` (next session), now a **pure representation-bridge + assembly** step (no new
analytic estimate): (a) the `continuousMultilinearCurryFin1`/`curryLeft` isometry bridge relating the
multilinear-`D²v` Taylor residual `D³v(Φx₀ s)[Φz s − Φx₀ s]` (in `E[×2]→L E`) to the composition-form
`F_C` operator `((P_C ∘ W) h) ∘ W` (`P_C = ` curried `D³v(Φx₀ s).curryLeft(W_x k)`), turning the
`dP`-linear term of `norm_bilinearCompForcing_sub_sub_le` into `F_C` with `‖k‖²` residual; (b) threading
the concrete flow/resolvent bounds (`norm_fundamentalSolution_sub_sub_linearVariation_le_sq` for `cw`,
`norm_fundamentalSolution_baseCurve_sub_le` for `dw`, `norm_secondDerivField_apply_flow_sub_le` for `dp`,
`norm_fundamentalSolution_le`/`hC'` for `w`/`p`) into `norm_bilinearCompForcing_sub_sub_le_sq` to obtain
the `(F₁ − F₀)` remainder `‖(F₁ − F₀) − (F_A + F_B + F_C)‖ ≤ Cquad·‖z − x₀‖²·‖h‖`; then (with the
already-proved coefficient remainder `norm_coeffVariation_sub_secondDerivComp_le_sq`) the forcing gap
`hβ`, `norm_inhomogVariation_sub_sub_le_of_forcingGap`, and `hasFDerivAt_of_eventually_norm_sub_sub_le_sq`
close `ContDiff ℝ 3`.

Update — **the representation half of the remaining `(F₁ − F₀)` step is now CLOSED, and the `F_C`-form
forcing engine is assembled** (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`), in
`AnalyticPDE/SmoothDependenceCk.lean`.  This discharges step (a) above in full and pre-threads step (b)
into a single ready-to-feed engine:

* `norm_secondDerivField_sub_sub_thirdDeriv_ml_fundamentalSolution_le_sq` — the *single remaining
  analytic ingredient* named above: the multilinear central `C³` coefficient Taylor bound with the
  **resolvent-linearised** residual,
  `‖(D²v(Φ z s) − D²v(Φ x₀ s)) − D³v(Φ x₀ s)(W_x (z − x₀))‖ ≤ (M·e + N·(L·e·g))·‖z − x₀‖²`
  (`e = exp (2K(T−t₀))`, `g = gronwallBound 0 K 1 (T−t₀)`, `N` a bound on `‖D³v(Φ x₀ s)‖`), uniformly on
  the tube — the `D²v`-analogue of the `C²` `norm_derivField_sub_sub_comp_fundamentalSolution_le_sq`.
  Split into the flow-Taylor defect (`norm_secondDerivField_sub_sub_thirdDeriv_ml_flow_le`) plus the
  linearisation residual `D³v(Φ x₀ s)[(Φ z s − Φ x₀ s) − W_x k]` (operator bound × the first-order flow
  remainder `norm_flow_sub_fundamentalSolution_le_sq`).
* `curry2` (+ `curry2_apply`, `curry2_sub`, `norm_curry2_le`) — the **multilinear→composition
  representation bridge**: `curry2 : (E[×2]→L E) → (E →L (E →L E))`, `curry2 X a b = X ![a, b]`, built
  from `X.curryLeft` post-composed with the `Fin 1` isometry `continuousMultilinearCurryFin1`.  Linear
  (`curry2_sub`) and norm-nonexpansive (`norm_curry2_le`, in fact isometric) — the only form in which
  the third derivative carries a norm (`E →L (E[×2]→L E)`) transported into the composition form the
  trilinear engine operates in.
* `norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq` — the **composition-form central `C³` Taylor
  bound**: the multilinear bound transported through `curry2` (linearity collapses the three-term
  combination, `norm_curry2_le` transports the estimate verbatim), giving the `εp = cp·‖k‖²` quadratic
  remainder for the candidate `dP = curry2 (D³v(Φ x₀ s)(W_x k))`.
* `bilinearCompForcing_curry2_eq` — the **`dP`-term = `F_C` identity**:
  `((curry2 S ∘ W) h) ∘ W = (continuousMultilinearCurryFin1 ℝ E E (S.curryLeft (W h))).comp W` (both
  `e ↦ S[W h, W e]`).  With `S = (D³v(Φ x₀ s)).curryLeft (W k)` the right side is *exactly* the module's
  third-derivative forcing `F_C`, so the trilinear engine's composition-form candidate is identified with
  `F_C`.  This closes step (a).
* `norm_secondDerivField_ml_apply_flow_sub_le` / `norm_secondDerivField_curry2_apply_flow_sub_le` — the
  `dp` first-order flow-Lipschitz gap `‖D²v(Φ z s) − D²v(Φ w s)‖ ≤ M·exp(K T)·‖z − w‖` (multilinear and
  its `curry2` image), the `hrP` threading input.
* `norm_bilinearCompForcing_curry2_sub_sub_le_sq` — the **assembled `F_C`-form forcing engine**: the
  trilinear quadratic-remainder engine `norm_bilinearCompForcing_sub_sub_le_sq` fused with
  `bilinearCompForcing_curry2_eq`, so choosing `dP = curry2 S` delivers the `dP`-linear output *directly*
  in the `F_C` shape.  Fed `P₀ = curry2 (D²v(Φ x₀ s))`, `P₁ = curry2 (D²v(Φ z s))`,
  `S = D³v(Φ x₀ s)(W_x k)`, `W₀ = W_x`, `W₁ = W_z`, `dW = W₂` and the six factor bounds — `p` via
  `norm_curry2_le`/`hC'`, `w` via `norm_fundamentalSolution_le`, `dp` via
  `norm_secondDerivField_curry2_apply_flow_sub_le`, `dw` via `norm_fundamentalSolution_baseCurve_sub_le`,
  `cp` via `norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq`, `cw` via
  `norm_fundamentalSolution_sub_sub_linearVariation_le_sq` — it yields the `(F₁ − F₀)` forcing gap
  `‖(F₁ − F₀) − (F_C + F_A + F_B)‖ ≤ Cquad·‖z − x₀‖²·‖h‖`.

Remaining for `ContDiff ℝ 3` (next session): the **concrete `(F₁ − F₀)` assembly theorem** — instantiate
`norm_bilinearCompForcing_curry2_sub_sub_le_sq` with the flow/resolvent objects (`W_x`, `W_z`, `W₂`) and
the six bounds above, using the compatibility `D²v_comp s ξ = curry2 (D²v_ml s ξ)` between the two
second-derivative representations (from `iteratedFDeriv`/`fderiv` for a smooth field) to bridge the
module's composition-form second-variation forcing (of
`exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv`) to the `curry2` bounds.  Then, with the
already-proved coefficient remainder `norm_coeffVariation_sub_secondDerivComp_le_sq`, the forcing gap `hβ`,
`norm_inhomogVariation_sub_sub_le_of_forcingGap`, and `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` close
`ContDiff ℝ 3`.

Update — **the representation-bridge toolkit is now COMPLETE, the concrete `(F₁ − F₀)` assembly is
PROVED, and the forcing-gap combinator is assembled** (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`), in `AnalyticPDE/SmoothDependenceCk.lean`.  This closes the
representation half in full and reduces the remaining `ContDiff ℝ 3` work to a single (large) threading
capstone:

* `curry2_iteratedFDeriv_two` — the **pure `iteratedFDeriv`/`fderiv` representation bridge for `D²v`**:
  `curry2 (iteratedFDeriv ℝ 2 f z) = fderiv ℝ (fderiv ℝ f) z`, identifying the multilinear form
  `E[×2]→L E` (carrying the `C³` Taylor bounds) with the composition form `E →L (E →L E)` (of the
  second-variation ODE forcing).  Unconditional, via `curry2_apply` + Mathlib's `iteratedFDeriv_two_apply`.
  Its `HasFDerivAt`-consumable form `curry2_iteratedFDeriv_two_eq_of_hasFDerivAt`
  (`curry2 (iteratedFDeriv ℝ 2 f x) = D2comp` given `HasFDerivAt f (Df ·)` and `HasFDerivAt Df D2comp x`)
  identifies the module's abstract composition-form second derivative with `curry2` of the multilinear one
  — the compatibility `hcompat` the assembly threads.
* `curryLeft_iteratedFDeriv_three` — the **third-order companion**:
  `(iteratedFDeriv ℝ 3 f x).curryLeft = fderiv ℝ (iteratedFDeriv ℝ 2 f) x`, identifying the module's `F_C`
  contraction `(iteratedFDeriv 3 f ξ).curryLeft (W k)` with the `C³`-Taylor form
  `fderiv (iteratedFDeriv 2 f) ξ (W k)`.  Via `ContinuousMultilinearMap.curryLeft_apply` + Mathlib's
  `iteratedFDeriv_succ_apply_left` at `Fin.cons`.  Consumable form
  `curryLeft_iteratedFDeriv_three_eq_of_hasFDerivAt` (`D3ml = (iteratedFDeriv 3 f x).curryLeft` given
  `HasFDerivAt (iteratedFDeriv 2 f) D3ml x`).
* `norm_chainRuleForcing_flow_sub_sub_le_sq` — the **concrete `(F₁ − F₀)` second-order forcing remainder
  along the flow**, the `C³`-layer field-derived analogue of `norm_chainRuleForcing_flow_sub_le`:
  `∃ C, ∀ s ∈ [t₀, T], ‖(F₁ − F₀) − (F_C + F_A + F_B)‖ ≤ C · ‖z − x₀‖² · ‖h‖`
  with `F₁ = ((D²v(Φz) ∘ W_z) h) ∘ W_z`, `F₀ = ((D²v(Φx₀) ∘ W_x) h) ∘ W_x`.  **Key simplification**: the
  engine `norm_bilinearCompForcing_curry2_sub_sub_le_sq` already accepts arbitrary composition-form
  `P₀, P₁`, so they are set to `D²v_comp` *directly*; the representation compatibility `hcompat` is needed
  *only* for the `cp` quadratic remainder `hεP` (a `←hcompat` rewrite turning the `curry2`-form bound of
  `norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq` into composition form).  The six field bounds:
  `p` via `hC'`, `w` via `norm_fundamentalSolution_le`, `dp` via `norm_secondDerivField_apply_flow_sub_le`,
  `dw` via `norm_fundamentalSolution_baseCurve_sub_le`, `cp` via
  `norm_secondDerivField_curry2_sub_sub_thirdDeriv_le_sq` (+`←hcompat`), `cw` via
  `norm_fundamentalSolution_sub_sub_linearVariation_le_sq` (`W₂ = Vlin`).  The `F_C` term matches the
  module's `(iteratedFDeriv 3).curryLeft`-shape via `D3vm` (bridged by `curryLeft_iteratedFDeriv_three`).
  The existential `∃ C` over the field constant keeps the statement clean (`rotate_left` lets the engine
  determine the witness).
* `norm_forcingGap_le_of_remainders` — the **forcing-gap combinator**: assembles the coefficient-variation
  remainder `‖(A₁ − A₀) ∘ V₁ − newLeading‖ ≤ β₁` (`norm_coeffVariation_sub_secondDerivComp_le_sq`) and the
  chain-rule forcing remainder `‖(F₁ − F₀) − (F_C + F_A + F_B)‖ ≤ β₂`
  (`norm_chainRuleForcing_flow_sub_sub_le_sq`) into the single forcing gap
  `‖((A₁ − A₀) ∘ V₁ + (F₁ − F₀)) − F₃‖ ≤ β₁ + β₂` with `F₃ = F_A + F_B + (newLeading + F_C)` — **exactly**
  the design-corrected third-variation forcing of
  `exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff` and the `hβ` hypothesis of
  `norm_inhomogVariation_sub_sub_le_of_forcingGap` (verified by inspection: the coefficient remainder's
  `newLeading = ((D²v(Φx₀) ∘ W_x) k) ∘ V_x` and the corrected `F₃`'s leading term
  `((D²v(Φx₀) ∘ W_x) k) ∘ V0` coincide with `V_x = V0`).  Pure algebra (`abel` regroup + `norm_add_le`).

Remaining for `ContDiff ℝ 3` (next session): the **single `hβ`-application capstone** — a (large,
~40-hypothesis) field-derived theorem instantiating `norm_inhomogVariation_sub_sub_le_of_forcingGap` with
the three ODE solutions (`V₁, V₀` = first variations at `z, x₀`; `V₃` = the corrected second variation of
`exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff`), feeding its `hβ` via
`norm_forcingGap_le_of_remainders` applied to the two now-proved field remainders (the coefficient
remainder still stated in un-factored `‖z − x₀‖/‖z − x₀‖²`-mixed form, so a `ring`-reshape to
`C₁ · ‖z − x₀‖² · ‖h‖` is needed; supply `D3vm = (D3v_fin3).curryLeft` compat via
`curryLeft_iteratedFDeriv_three_eq_of_hasFDerivAt`).  This yields the base-point second-derivative Taylor
remainder `‖(D₂(z) − D₂(x₀)) − D₃(z − x₀)‖ ≤ C · ‖z − x₀‖²`; then
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq` closes `ContDiff ℝ 3`.  All analytic ingredients now exist;
the capstone is pure threading + one `ring`-reshape.

Update — **the `hβ`-application capstone is now DONE, and the base-point Taylor remainder has been
lifted all the way to the *operator level* — the exact numerator `hasFDerivAt_of_eventually_norm_sub_sub_le_sq`
consumes** (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`), in
`AnalyticPDE/SmoothDependenceCk.lean`.  Six new theorems close the capstone flagged above and package it
into the operator-norm form:

* `norm_forcingGap_flow_le_sq` — the **`C³` forcing-gap `hβ` along the flow**: assembles the
  coefficient-variation remainder `norm_coeffVariation_sub_secondDerivComp_le_sq` (ring-reshaped to the
  clean `C₁·‖z − x₀‖²·‖h‖` rate) and `norm_chainRuleForcing_flow_sub_sub_le_sq` via
  `norm_forcingGap_le_of_remainders` into `‖((Dv(Φz) − Dv(Φx₀))∘Uz + (F₁ − F₀)) − (F_A + F_B +
  (newLeading + F_C))‖ ≤ C·‖z − x₀‖²·‖h‖`, uniformly on `[t₀, T]` — exactly the `hβ` of
  `norm_inhomogVariation_sub_sub_le_of_forcingGap`.
* `norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq` — the **curve-level `C³` Taylor
  remainder** (the `D₃`-analogue of the `C²` numerator `norm_fundamentalSolution_sub_sub_linearVariation_le_sq`):
  feeds the forcing gap into `norm_inhomogVariation_sub_sub_le_of_forcingGap` with the three ODE solutions
  `Uz, Ux, V₃`, giving `‖(Uz t − Ux t) − V₃ t‖ ≤ C·‖z − x₀‖²·‖h‖`.
* `continuous_thirdDerivCurryForcing` — continuity of the `F_C` forcing in the `D3vm` (`E →L (E[×2]→L E)`)
  representation, the companion of `continuous_thirdDerivForcing`.
* `norm_chainRuleForcing_flow_sub_sub_le_sq_uniform` — the **`h`-uniform** (direction-independent
  constant) chain-rule forcing remainder: `∃C, ∀ h, ∀ s ∈ [t₀,T], …≤ C·‖z − x₀‖²·‖h‖` with `C` chosen
  **before** `h` (the engine constant of `norm_bilinearCompForcing_curry2_sub_sub_le_sq` never mentions
  `h`; the `?C` metavariable unifies to it on the single `exact`).  This is what the operator-norm
  packaging needs (`opNorm_le_bound` requires one bound valid for every direction).
* `norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq_uniform` — the `h`-uniform curve-level
  Taylor remainder (`C` before `h` and the `h`-dependent curves `Uz, Ux, V₃`).
* `norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq` — the **operator-level `C³` Taylor
  remainder** (the `D₃`-analogue of the `C²` operator estimate `norm_secondFundamentalSolution_op_sub_le`):
  for packaged `D₂z, D₂x : E →L (E →L E)` and `D₃ : E →L (E →L (E →L E))` with their curve
  characterisations, `‖(D₂z − D₂x) − D₃ (z − x₀)‖ ≤ C·‖z − x₀‖²`.  Via `ContinuousLinearMap.opNorm_le_bound`
  reduced to a per-direction bound; per `h` the three canonical curves are built
  (`exists_hasDerivAt_firstVariation_linearised_dir` ×2, `exists_hasDerivAt_secondVariation_linearised_dir`
  with concrete `newLeading + F_C` forcing), operator values rewritten to curve values via the
  characterisations, and closed by the direction-uniform curve bound.  **This is exactly the numerator
  `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` consumes** (with `k = z − x₀`) to prove
  `HasFDerivAt (fun z => D₂ z) D₃ x₀`.

Remaining for `ContDiff ℝ 3` (next session): the **everywhere assembly** — a `z`-varying second
fundamental solution operator field `z ↦ D₂ z` with a neighbourhood-uniform constant `C`, feeding
`norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq` to
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq` for `HasFDerivAt (fun z => D₂ z) D₃ x₀`, then the
`contDiff_succ_iff_fderiv` chain (with the `C²` `exists_flow_contDiff_two_of_lipschitz_secondDeriv` and
continuity of `z ↦ D₃`) to `exists_flow_contDiff_three_of_lipschitz_thirdDeriv` — the honest `ContDiff ℝ 3`,
mirroring the `C²` `exists_flow_contDiff_two_of_lipschitz_secondDeriv` assembly one order up.  All the
per-base-point analytic content is now proved; the remainder is the neighbourhood/uniformity packaging.

Update — the **neighbourhood-uniform-constant tower is now CLOSED** (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`), in `AnalyticPDE/SmoothDependenceCk.lean`.  The obstruction to
the `HasFDerivAt` step above was that `norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq` states
its constant as a *per-`z` existential* `∃ C`, whereas `hasFDerivAt_of_eventually_norm_sub_sub_le_sq`
requires a **single** `C` valid for every `z` in a neighbourhood of `x₀`.  Since the constant is genuinely
`z`-independent (a closed field expression in `K, L, M₂, M₃, C', N, T, t₀`, with `‖z − x₀‖²` factored out),
the fix is to *expose* it explicitly.  Three explicit-constant twins were added, mirroring the `∃`-form
proofs but writing the constant out (the `∃` was introduced only at the `norm_bilinearCompForcing_*`
engine level, whose output constant is already explicit):

* `norm_chainRuleForcing_flow_sub_sub_le_sq_uniformC` — the chain-rule forcing remainder with the engine
  constant `cp·w² + 2p·cw·w + 2dp·dw·w + p·dw² + dp·dw²` (the six field bounds substituted) written out.
  Verbatim `∃`-form proof, closed by the engine `.trans_eq (by ring)`.
* `norm_secondFundamentalSolution_sub_sub_thirdVariation_le_sq_uniformC` — the curve-level `C³` Taylor
  remainder with constant `(C₁ + C₂)·gronwallBound 0 K 1 (t − t₀)` (`C₁` = the coefficient-variation
  constant, `C₂` = the chain-rule engine constant) written out.  Proof: the `∃`-form's proof with the
  forcing-gap `β` a metavariable determined by `norm_forcingGap_le_of_remainders`, the Grönwall bound
  `norm_inhomogVariation_sub_sub_le_of_forcingGap` reshaped by `ring`.
* `norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC` — the **operator-level** `C³`
  Taylor remainder `‖(D₂z − D₂x) − D₃ (z − x₀)‖ ≤ max ((C₁ + C₂)·gronwallBound 0 K 1 (t − t₀)) 0 · ‖z − x₀‖²`,
  the operator numerator in the exact **single-constant** form
  `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` consumes.  Proof: the `∃`-op proof with the explicit-
  constant curve bound closing each per-direction estimate after `ContinuousLinearMap.opNorm_le_bound`
  (constant `max … 0`, nonnegative by `le_max_right`).

Remaining for `ContDiff ℝ 3` (next session): with the neighbourhood-uniform numerator now available, the
`HasFDerivAt (fun z => D₂ z) D₃ x₀` assembly needs (i) the **canonical linear families** the bilinear `D₃`
packaging `exists_continuousLinearMap_thirdVariation_coeff_bilinear` consumes — a `W2 : E → ℝ → (E →L E)`
linear in the base direction `k` (`= ` the linearised first variation at `x₀` in direction `k`,
pointwise-additive/homogeneous via `linearVariation_perturbation_add_eq`/`_smul_eq`, continuous, `‖·‖ ≤ N₂‖k‖`)
and the analogous `V0fun` linear in `h`; (ii) the `D₃` bounded operator from that packaging, whose
characterisation is bridged to the `hD₃` slot of `norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC`
by building the per-`z` `W₂ z = W2 (z − x₀)` and a first-variation-uniqueness argument for the `V₀`/`V0fun h`
match (`inhomogVariation_unique`); (iii) the per-`z` `Wdiff z` via `exists_hasDerivAt_inhomogVariation_of_continuous`
and `Φ₁ z = Ψ z`; then `hasFDerivAt_of_eventually_norm_sub_sub_le_sq` with `C = max (…) 0` on the ball
`‖z − x₀‖ < 1` gives `HasFDerivAt (fun z => D₂ z) D₃ x₀`.  Finally the continuity of `z ↦ D₃` (a third-order
analogue of the `C²` `hcont_D₂` Lipschitz bound) and the `contDiff_succ_iff_fderiv` chain close
`exists_flow_contDiff_three_of_lipschitz_thirdDeriv`.

Update — the two **constructive inputs (i)–(ii)** above are now BUILT (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`), in `AnalyticPDE/SmoothDependenceCk.lean`:

* `exists_linearisedFirstVariationFamily` — the **canonical linearised-first-variation family** `Vfam :
  E → (ℝ → (E →L E))`, linear in the direction: pointwise-additive (`linearVariation_perturbation_add_eq`),
  homogeneous (`linearVariation_perturbation_smul_eq`), continuous (`Differentiable.continuous` of the
  ODE), solving `(Vfam h)' = A₀ ∘ Vfam h + (D²v(Φ x₀ s) ∘ W₀ · h) ∘ W₀` with `Vfam h t₀ = 0`, bounded
  `‖Vfam h s‖ ≤ C' · exp(2K(T − t₀)) · gronwallBound 0 K 1 (T − t₀) · ‖h‖` on `[t₀, T]`
  (`norm_linearisedFirstVariation_le` + `gronwallBound_mono`).  This single family supplies **both** the
  base-direction curve `W2` (at `k`) and the inner curve `V0fun` (at `h`) the bilinear `D₃` packaging needs,
  and — via its ODE — matches the per-`z` `W₂ = Vfam (z − x₀)`, `V₀ = Vfam h` of the operator numerator.
* `exists_thirdVariationOperator_of_field` — the **self-contained packaged `D₃`** `E →L (E →L (E →L E))`
  built directly from `C^{3}`-field data by feeding `Vfam` as both `W2` and `V0fun` into
  `exists_continuousLinearMap_thirdVariation_coeff_bilinear` (shared `Vfam`-bound giving both `N₂, N₀`).
  Returns `Vfam` alongside `D₃` with its init/ODE/continuity/additivity/homogeneity/bound and the bilinear
  characterisation `D₃ k h = V t` (design-corrected third-variation ODE, `W2 = V0fun = Vfam`, `Fin 3`
  multilinear `D3v`).

Remaining for `ContDiff ℝ 3` (next session): the **characterisation bridge** discharging the `hD₃` slot of
`norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC` from the bilinear characterisation of
`exists_thirdVariationOperator_of_field` — for `V₀` an arbitrary linearised first variation in direction
`h`, `V₀ = Vfam h` pointwise by `inhomogVariation_unique` (same ODE, same anchor), so the numerator's
third-variation forcing (using `V₀` and the `E →L (E[×2]→L E)` representation `D3vm`) equals the bilinear
forcing (using `Vfam h` and the `Fin 3` representation `D3v`) once `D3vm s ξ = (D3v s ξ).curryLeft` is
supplied (`curryLeft_iteratedFDeriv_three_eq_of_hasFDerivAt`); a `funext`/`rw` on the `HasDerivAt`
forcing then lets `hD₃bilinear` (with `k = z − x₀`) close the slot.  Then the **everywhere assembly**: the
`D₂` field via `choose exists_continuousLinearMap_linearisedVariation`, per-`z` `W₂ z = Vfam (z − x₀)`,
`Wdiff z` (`exists_hasDerivAt_inhomogVariation_of_continuous`), `Φ₁ z = Ψ z`, and
`hasFDerivAt_of_eventually_norm_sub_sub_le_sq` (`C = max (…) 0`, ball `‖z − x₀‖ < 1`) for
`HasFDerivAt (fun z => D₂ z) D₃ x₀`; finally `z ↦ D₃` continuity + `contDiff_succ_iff_fderiv` close
`exists_flow_contDiff_three_of_lipschitz_thirdDeriv`.

Update — the **characterisation bridge and the everywhere `HasFDerivAt (fun z => D₂ z) D₃ z`
assembly are now BUILT** (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`), in
`AnalyticPDE/SmoothDependenceCk.lean`.  Three new theorems close the bridge + assembly flagged above:

* `thirdVariationOperator_hD₃_slot_of_bilinear` — the **characterisation bridge**.  Given the canonical
  linearised-first-variation family `Vfam` and the packaged bilinear `D₃` of
  `exists_thirdVariationOperator_of_field` (its `Fin 3`-multilinear characterisation `hD₃bilinear`),
  plus the curry-left compatibility `D3vm(Φ x₀ ·) = (D3v(Φ x₀ ·)).curryLeft`, the operator `D₃`
  satisfies the `hD₃` hypothesis slot of `norm_secondFundamentalSolution_op_sub_thirdVariation_le_sq_uniformC`
  for the direction `z − x₀`.  Proof: Grönwall uniqueness `inhomogVariation_unique` pins
  `W₂ = Vfam (z − x₀)` and `V₀ = Vfam h` pointwise (same coefficient `Dv(Φ x₀ ·)`, same anchor `0`);
  rewriting the design-corrected third-variation forcing by these two identities and `hcurry` turns it
  term-for-term into the bilinear forcing, and `hD₃bilinear (z − x₀) h V` closes `D₃ (z − x₀) h = V t`.
  The last purely-algebraic link between the packaged operator and the neighbourhood-uniform
  operator-level `C³` Taylor remainder.
* `exists_hasFDerivAt_secondFundamentalSolution_baseCurve` — the **single-base-point `C³` bootstrap**.
  For a `C^{3,1}` field, the packaged second fundamental solution `z ↦ D₂ z` (spatial derivative of the
  resolvent, `D₂ z h = Vlin^{z,h} t`) is Fréchet differentiable at `x₀` with derivative the packaged
  `D₃`.  Assembly: `choose` the `D₂`-family (`exists_continuousLinearMap_linearisedVariation`); take
  `D₃`/`Vfam`/`hD₃bilinear` from `exists_thirdVariationOperator_of_field`; per `z` on the unit ball
  build `W₂` and `Wdiff`, discharge `hD₃` via the bridge, apply the numerator and
  `hasFDerivAt_of_eventually_norm_sub_sub_le_sq`.
* `exists_hasFDerivAt_secondFundamentalSolution` — the **everywhere (family) `C³` bootstrap**.  A single
  packaged family `D₂` and a third-fundamental-solution family `D₃fam` with `∀ y, HasFDerivAt D₂ (D₃fam y) y`
  (uniform-in-base-point third-derivative data).  This is the everywhere `fderiv D₂ = D₃fam` half of the
  resolvent's spatial `ContDiff ℝ 3`.

Remaining for `ContDiff ℝ 3` (next session): the **continuity of the third fundamental solution**
`y ↦ D₃fam y` — a third-order operator-difference (Lipschitz) bound `‖D₃fam z − D₃fam z₀‖ ≤ C‖z − z₀‖`,
the analogue of the `C²` `hcont_D₂` one order up (opNorm bound + the third-variation-ODE gap over the
four forcing terms), which does not yet exist and is the true remaining blocker — then
`contDiff_one_iff_fderiv`/`contDiff_succ_iff_fderiv` chain close
`exists_flow_contDiff_three_of_lipschitz_thirdDeriv`.

Update — the **third-variation-ODE base-point gap tower is now BUILT** (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`), in `AnalyticPDE/SmoothDependenceCk.lean`.  Six new theorems
supply the entire third-order operator-difference gap over the four forcing terms that the `D₃fam`
continuity (`hcont_D₂` one order up) needs:

* `norm_curryFin1_biContract_comp_sub_le` — the abstract operator-norm telescoping skeleton for the
  fully-contracted third-derivative forcing term (`(curryFin1 ((T.curryLeft a).curryLeft b)).comp C`),
  under joint perturbation of `T, a, b, C`; via `norm_clm_apply_sub_le` + the `curryLeft`/`curryFin1`
  isometries.
* `norm_thirdDerivForcing_baseCurve_sub_le` — its flow instance (term 4 of the forcing): the linear
  base-point gap of `curryFin1(D³v[Wk,Wh,W·])`, `≤ exp⁴·(M₃ + 3C''Lg)·‖z−x₀‖·‖k‖·‖h‖`.
* `norm_bilinearComp_VfamInner_baseCurve_sub_le` — the base-point gap of the `Vfam`-inner term
  (`((D²v ∘ Vfam_k) h) ∘ W`, term 1), `≤ exp⁴·g·(2M₂C' + 4LC'²g)·‖z−x₀‖·‖k‖·‖h‖`, via the abstract
  `norm_bilinearCompForcing_sub_le` + `norm_linearisedFirstVariation_baseCurve_sub_le`.
* `norm_bilinearComp_VfamOuter_baseCurve_sub_le` — the base-point gap of the `Vfam`-outer terms
  (`((D²v ∘ W) d) ∘ Vfam_e`, terms 2 & 3), the same clean constant with `‖e‖·‖d‖`.
* `norm_add4_sub_add4_le` — the four-fold triangle inequality for the right-nested four-term forcing.
* `norm_thirdVariationForcing_baseCurve_sub_le` — the **full four-term forcing gap `β`**:
  `‖F^z − F^x‖ ≤ (3·exp⁴·g·(2M₂C' + 4LC'²g) + exp⁴·(3C''Lg + M₃))·‖z−x₀‖·‖k‖·‖h‖`, summing the four
  term gaps via `norm_add4_sub_add4_le`.
* `norm_thirdVariation_baseCurve_sub_le` — the **third-variation curve base gap** (the `C³` analogue of
  `norm_linearisedFirstVariation_baseCurve_sub_le`): for the third-variation curves `Vz`, `Vx`,
  `‖Vz t − Vx t‖ ≤ Cλ·‖z−x₀‖·‖k‖·‖h‖·gronwall(t−t₀)` with
  `Cλ = L·exp⁴·g·(3C'²g + C'') + 3·exp⁴·g·(2M₂C' + 4LC'²g) + exp⁴·(3C''Lg + M₃)`, assembled from the
  coefficient gap `α`, the second-curve size `N` (`norm_thirdVariation_coeff_le`) and the forcing gap
  `β` via `norm_inhomogVariation_sub_le_of_gap`.

Remaining for `ContDiff ℝ 3` (next session): the **`D₃fam` continuity assembly** — for the packaged
`D₃fam`, construct per base-point the third-variation curves `Vz`, `Vx` and the four `Vfam` curves,
identify `D₃fam z k h = Vz t` (the operator characterisation `hD₃bilinear`) and apply
`norm_thirdVariation_baseCurve_sub_le`, then `ContinuousLinearMap.opNorm_le_bound` (twice, over `k`
then `h`) gives `‖D₃fam z − D₃fam x₀‖ ≤ Cλ·gronwall·‖z − x₀‖` — i.e. `LipschitzWith`/`Continuous D₃fam`;
the `contDiff_one_iff_fderiv`/`contDiff_succ_iff_fderiv` chain then closes
`exists_flow_contDiff_three_of_lipschitz_thirdDeriv`.

Update — the **`D₃fam` continuity assembly is now PARTLY BUILT, and a hard Mathlib obstruction on the
triple continuous-linear-map norm was discovered** (all new theorems axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`), in `AnalyticPDE/SmoothDependenceCk.lean`:

* `norm_thirdFundamentalSolution_apply_baseCurve_sub_le` — the **per-direction operator base-point
  gap** of the packaged third-variation operator `D₃`.  For two base points `z, x₀` with their
  packaged operators `D₃z, D₃x` (bilinear characterisations `hD₃z`, `hD₃x` through the canonical
  families `Vfamz`, `Vfamx`), `‖D₃z k − D₃x k‖ ≤ Cλ·gronwall(t−t₀)·‖z−x₀‖·‖k‖` with the *same* `Cλ`
  constant as `norm_thirdVariation_baseCurve_sub_le`.  Proof: `opNorm_le_bound` over the inner
  direction `h`; per `h`, `exists_hasDerivAt_secondVariation_linearised_dir_of_thirdDeriv_coeff`
  (fed `Vfamz k`, `Vfamz h`) builds the third-variation curves `Vz`, `Vx`; `hD₃z`/`hD₃x` identify
  `D₃z k h = Vz t`, `D₃x k h = Vx t`; `norm_thirdVariation_baseCurve_sub_le` bounds `‖Vz t − Vx t‖`
  (the existence-lemma forcing associates `(T1+T2)+(T3+T4)` vs the base-gap lemma's `T1+(T2+(T3+T4))`
  — reconciled by `convert … using 2; abel`).  This is the `C³` analogue of the `hkey` operator gap
  inside `exists_flow_contDiff_two_of_lipschitz_secondDeriv`, one order up.
* `lipschitzWith_thirdFundamentalSolution_apply` — **per-direction Lipschitz continuity** of the
  packaged family `D₃fam : E → (E →L E →L E →L E)`: for each fixed outer direction `k`, the slice
  `z ↦ D₃fam z k` (valued in the well-normed *double* space `E →L E →L E`) is
  `LipschitzWith (Cλ·gronwall(t−t₀)·‖k‖).toNNReal`.  Proof: `LipschitzWith.of_dist_le_mul` + the
  base-point gap above.  I.e. `D₃fam` is genuinely continuous in the strong operator topology,
  direction by direction.

**THE OBSTRUCTION (blocks the naive `Continuous D₃fam` and hence `exists_flow_contDiff_three`).**  In
Mathlib v4.29.1 the **triple continuous-linear-map operator norm does not synthesize**: for `E` a
plain `NormedAddCommGroup`/`NormedSpace ℝ`, `Norm (E →L E →L E →L E)`,
`SeminormedAddCommGroup (E →L E →L E →L E)`, `NormedSpace ℝ (E →L E →L E)` and
`UniformSpace (E →L E →L E →L E)` **all fail** (verified even for `EuclideanSpace ℝ (Fin 2)`); the
root is the endomorphism-ring/module diamond — `NormedSpace ℝ (E →L E →L E)` cannot be built.  Only
`TopologicalSpace (E →L E →L E →L E)` synthesizes, via `ContinuousLinearMap.topologicalSpace` (a
non-norm, pointwise/strong topology), **not** through `TopologicalSpace.induced`, so
`continuous_induced_rng` does not apply and there is no off-the-shelf lemma (`apply?`/`exact?` find
nothing) to get `Continuous D₃fam` from the per-direction continuity `∀ k, Continuous (z ↦ D₃fam z k)`.
Consequently the `C²`-style closing (`hkey : ‖D₂ z − D₂ x₀‖ ≤ C·‖z−x₀‖` → `LipschitzWith`/`Continuous`
via the *double* norm) does **not** lift verbatim to `C³`: `‖D₃fam z − D₃fam x₀‖` (the triple norm)
is unstatable.  Note `contDiff_one_iff_fderiv` *does* still typecheck at the double level (its
`Continuous (fderiv g)` uses the triple's pointwise topology), so a `Continuous D₃fam` in that
pointwise topology *might* still feed the chain — but proving it requires unfolding
`ContinuousLinearMap.topologicalSpace` by hand (a genuine detour), and it is unverified whether that
topology is the one the `contDiff_succ_iff_fderiv` chain ultimately consumes.

Remaining for `ContDiff ℝ 3` (next session) — two viable routes:
  1. **Pointwise-topology route (smaller, uncertain):** prove `Continuous D₃fam` in
     `ContinuousLinearMap.topologicalSpace` from the per-direction continuity
     `lipschitzWith_thirdFundamentalSolution_apply` (via the definition of
     `ContinuousLinearMap.topologicalSpace` / a bespoke `continuous_of_apply` bridge), then check the
     `contDiff_one_iff_fderiv`/`contDiff_succ_iff_fderiv` chain actually closes
     `exists_flow_contDiff_three_of_lipschitz_thirdDeriv` with that topology.
  2. **Multilinear route (larger, robust):** reformulate the `C³` closing through `iteratedFDeriv`
     (`ContinuousMultilinearMap ℝ (fun _ : Fin n => E) E`, which carries a proper norm at every order
     and avoids the nested-CLM diamond entirely) instead of the nested `fderiv` tower.
The two per-direction theorems above are the robust analytic content and feed either route.

Update — the **multilinear route (Route 2) is now substantially built and the `ContDiff ℝ 3`
capstone interface is CLOSED** (all sorry-free, axioms `propext`/`Classical.choice`/`Quot.sound` only),
in `AnalyticPDE/SmoothDependenceCk.lean`.  Ten new theorems reformulate the `C³` closing through the
properly-normed multilinear spaces, sidestepping the un-normed nested continuous-linear-map tower:

* `uncurry2CLM` / `uncurry2CLM_apply` — the multilinear packaging
  `(E →L E →L E) →L ContinuousMultilinearMap ℝ (Fin 2) E`, a genuine bounded operation (the inner
  double space is normed).  `uncurry3` / `uncurry3_apply` — the packaging
  `(E →L E →L E →L E) → ContinuousMultilinearMap ℝ (Fin 3) E`, built through normed intermediaries
  (`(curryLeftEquiv_3).symm (uncurry2CLM.comp T)`), so `‖uncurry3 (D₃fam z) − uncurry3 (D₃fam x₀)‖`
  (the *multilinear* norm) IS well-formed even though the triple operator norm is not.
* `lipschitzWith_uncurry3_of_apply_sub_le` — abstract engine: a per-outer-direction operator gap
  `‖F x k − F y k‖ ≤ C·dist x y·‖k‖` promotes to `LipschitzWith C.toNNReal (x ↦ uncurry3 (F x))` via
  `ContinuousMultilinearMap.opNorm_le_bound`.  `lipschitzWith_thirdFundamentalSolution_multilinear` —
  the flow instance: `z ↦ uncurry3 (D₃fam z)` is `LipschitzWith` (hence `Continuous`) in the
  properly-normed `Fin 3` multilinear space, fed by `norm_thirdFundamentalSolution_apply_baseCurve_sub_le`.
  **This is the obstruction-free upgrade of the per-direction `lipschitzWith_thirdFundamentalSolution_apply`.**
* `uncurry3_curryLeft` (`(uncurry3 T).curryLeft = uncurry2CLM.comp T`), `uncurry2CLM_curry2` /
  `curry2_uncurry2CLM` (packaging isomorphism: `uncurry2CLM` and `curry2` are mutually inverse),
  `iteratedFDeriv_two_eq_uncurry2CLM_of_hasFDerivAt`
  (`iteratedFDeriv ℝ 2 f x = uncurry2CLM D2` from the flow 1st/2nd derivative data) and
  `iteratedFDeriv_three_eq_uncurry3_of_hasFDerivAt`
  (`HasFDerivAt (iteratedFDeriv ℝ 2 f) (uncurry2CLM.comp T) x → iteratedFDeriv ℝ 3 f x = uncurry3 T`) —
  the currying bridges between the fundamental-solution data and the canonical `iteratedFDeriv` objects.
* **Capstone (closed):** `continuous_iteratedFDeriv_three_of_hasFDerivAt_continuous` —
  `Continuous (iteratedFDeriv ℝ 3 f)` from a **continuous, multilinear-valued** derivative
  `D3ml : E → (E →L ContinuousMultilinearMap ℝ (Fin 2) E)` of the second iterated derivative (via the
  curry isometry's inverse being continuous);  `differentiable_iteratedFDeriv_two_of_hasFDerivAt`; and
  `contDiff_three_of_contDiff_two_of_hasFDerivAt_continuous` — **`ContDiff ℝ 2 f` + continuous
  multilinear `D3ml` ⟹ `ContDiff ℝ 3 f`** via `contDiff_nat_iff_continuous_differentiable` at `n = 3`.
  The derivative datum is carried as `E → (E →L ContinuousMultilinearMap ℝ (Fin 2) E)` — a **normed**
  codomain — throughout, so the capstone never touches the un-normed `E →L E →L E →L E`.

**THE REMAINING GAP (single, well-isolated).**  To *apply* the `ContDiff ℝ 3` capstone to the flow one
must supply its hypothesis `hD3 : ∀ x, HasFDerivAt (iteratedFDeriv ℝ 2 f) (D3ml x) x` with `D3ml`
**multilinear-valued** (`E → (E →L ContinuousMultilinearMap ℝ (Fin 2) E)`).  The existing flow
machinery (`exists_hasFDerivAt_secondFundamentalSolution`) delivers the *nested* datum
`HasFDerivAt D₂ (D₃fam x) x` with `D₂ : E → (E →L E →L E)`, and the naive conversion
`iteratedFDeriv ℝ 2 f = uncurry2CLM ∘ D₂` differentiated by the chain rule
(`uncurry2CLM.hasFDerivAt.comp x (hD2 x)`) **whnf-diverges / times out** (deterministic `whnf`
heartbeat blowup): the chain rule forces synthesis/reduction of `NormedSpace ℝ (E →L E →L E)`, whose
noncomputable endomorphism-ring instance is prohibitively expensive.  So the nested→multilinear
`HasFDerivAt` conversion is the wall.  **NEXT SESSION:** produce the multilinear `hD3` datum
*without* the nested-CLM chain rule — e.g. differentiate `iteratedFDeriv ℝ 2 f` (a well-behaved
`ML(Fin 2)`-valued map) natively via `iteratedFDeriv_succ_eq_comp_left` / a curry-transported second
fundamental solution stated with a multilinear-valued derivative from the outset — then feed
`contDiff_three_of_contDiff_two_of_hasFDerivAt_continuous` to obtain `ContDiff ℝ 3` dependence on
initial conditions, unblocking Items 1/2.

Update — **THE REMAINING GAP IS CLOSED, and `C³` dependence of the flow on initial data is now
proved** (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`), in
`AnalyticPDE/SmoothDependenceCk.lean`.  The nested→multilinear `HasFDerivAt` wall — whose naive
resolution (`uncurry2CLM.hasFDerivAt.comp x hD2`) whnf-diverges on the `E →L E →L E` instance diamond
— is broken *without* the nested-CLM chain rule, and the whole `ContDiff ℝ 3` chain is assembled up to
the honest flow-level theorem.

**Root-cause diagnosis (this session).**  Every `HasFDerivAt`-lemma application whose codomain is the
*double* space `E →L E →L E` (`.isLittleO`, `.comp`, `isBigO_comp`) fails: (a) `HasFDerivAt.isLittleO`
leaves its metavariables unassigned unless the implicits are supplied *explicitly*
(`HasFDerivAt.isLittleO (𝕜 := ℝ) (f := D2) (f' := D3) (x := x) hD3`); (b) two clashing `Norm`
instances on `E →L E →L E` (`ContinuousLinearMap.hasOpNorm` vs `SeminormedAddCommGroup.toNorm`) that
the unifier will not reduce (nested-space whnf blowup) break `trans_isLittleO`/`isBigO_comp`; (c)
`‖uncurry2CLM‖` itself fails to synthesize (`Norm ((E →L E →L E) →L ML(Fin 2))` unavailable).

**The break (all sorry-free).**
* `norm_uncurry2CLM_le` — `‖uncurry2CLM T‖ ≤ ‖T‖`, via `ContinuousMultilinearMap.opNorm_le_bound` +
  two `le_opNorm` on the double space; never forms the unsynthesizable `‖uncurry2CLM‖`.
* `isLittleO_uncurry2CLM_comp` — post-composes a little-o with `uncurry2CLM`, through
  `Asymptotics.isLittleO_iff` + `filter_upwards` + `.trans` (defeq-robust; sidesteps the double-space
  `Norm` diamond that `isBigO_comp`/`trans_isLittleO` trip on).
* `hasFDerivAt_iteratedFDeriv_two_uncurry2CLM` — **THE BRIDGE**:
  `HasFDerivAt (iteratedFDeriv ℝ 2 f) (uncurry2CLM.comp D3) x` from the nested
  `HasFDerivAt D2 D3 x` (`D2 = fderiv (fderiv f)` composition-form, `D3 : E →L E →L E →L E`), via the
  explicit-implicit `.isLittleO` extraction + the two bricks above + the pointwise
  `iteratedFDeriv_two_eq_uncurry2CLM_of_hasFDerivAt`.
* `contDiff_three_of_hasFDerivAt_nested_of_continuous` — the **obstruction-free assembler**:
  `ContDiff ℝ 3 f` from `ContDiff ℝ 2 f`, the nested chain
  `HasFDerivAt f Df`/`HasFDerivAt Df D2`/`HasFDerivAt D2 D3fam`, and
  `Continuous (z ↦ uncurry3 (D3fam z))`.  Sets `D3ml x = (uncurry3 (D3fam x)).curryLeft`, discharges
  the `HasFDerivAt` slot via the bridge (+ `uncurry3_curryLeft`) and the continuity via the isometry
  `continuousMultilinearCurryLeftEquiv` (whose forward map *is* `curryLeft`), then feeds the existing
  capstone `contDiff_three_of_contDiff_two_of_hasFDerivAt_continuous`.

**The `C³`-side bundle and the flow capstone.**
* `exists_hasFDerivAt_secondFundamentalSolution_multilinearContinuous` — fuses
  `exists_hasFDerivAt_secondFundamentalSolution` (the nested `D₂`/`D₃fam` chain) with
  `lipschitzWith_thirdFundamentalSolution_multilinear` (multilinear continuity) for the **same**
  existentially-bound `D₃fam`/`Vfamfam` (one `exists_thirdVariationOperator_of_field` drives both, so
  the third-variation-ODE characterisation is shared).  Returns
  `∃ D₂ D₃fam, (D₂-char) ∧ (∀ y, HasFDerivAt D₂ (D₃fam y) y) ∧ Continuous (z ↦ uncurry3 (D₃fam z))` —
  exactly the third-derivative-side triple the assembler consumes; lone extra hypothesis `hD3vlip`.
* `exists_flow_contDiff_three_of_lipschitz_thirdDeriv` — **THE ITEM 1/2 UNBLOCK**: for a `C^{3,1}`
  field, `∃ Φ, (∀ z, Φ z t₀ = z) ∧ (∀ z, IsIntegralCurve (Φ z) v) ∧ ContDiff ℝ 3 (z ↦ Φ z t)`.
  Assembles, for one shared `Φ`: `exists_flow_contDiff_two_of_lipschitz_secondDeriv` (`Φ` +
  `ContDiff ℝ 2`), the bundle above (nested chain + continuity), and the `C¹`/`C²` bootstraps
  (`hasFDerivAt_flow_of_lipschitz_deriv` + `norm_fundamentalSolution_sub_sub_linearVariation_le_sq`,
  identifying `fderiv (z ↦ Φ z t) =` resolvent and `fderiv (resolvent) = D₂`), fed to the assembler.
  Along-flow bounds are read off the derivative Lipschitz constants (`C' = L`,
  `‖D3v‖ = ‖D3v.curryLeft‖ = ‖D3vm‖ ≤ N` by the `curryLeft` isometry `ContinuousMultilinearMap.curryLeft_norm`).

Remaining for Point 4 (future sessions): **connect the now-`ContDiff ℝ 3` initial-data dependence to
the manifold gauge-flow consumers of Items 1 & 2** — the compact-manifold gauge-flow constructor
(Item 2, extending `GaugeReduction/Diffeomorph3FlowExistence.lean` through the Banach model bridge
`ModelGaugeFlowODE.lean`), and the tensor time-derivative chain rule (Item 1,
`Diffeomorph3FlowTimeDerivative.lean`) which now has its `C³` initial-data-dependence input available;
plus the general (merely-continuous, non-Lipschitz `Dv`) modulus, and the Item 3 parabolic
Hölder/Schauder frontier (`AnalyticPDE/ParabolicHolder.lean`).

Update — **the general (merely-continuous, non-Lipschitz `Dv`) modulus is now CLOSED for a
finite-dimensional state space**, in the new self-contained module
`AnalyticPDE/SmoothDependenceContinuousDeriv.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`; it imports the cached `SmoothDependenceCk`, so it builds
without recompiling that tower).  The Lipschitz-derivative restriction that
`hasFDerivAt_flow_of_lipschitz_deriv` / `exists_flow_contDiff_one_of_lipschitz_deriv` impose is
removed: a genuine `C^1` field supplies only a *jointly continuous* spatial derivative, which on a
finite-dimensional space suffices by Heine–Cantor.

* `exists_monotone_modulus_of_continuousOn_tube` — **the reusable analytic core**: for a proper
  (e.g. finite-dimensional) space, a continuous `f : ℝ → E → ℝ` that is nonnegative and vanishes at
  the origin over a compact `T ⊆ ℝ` (`f s 0 = 0`) admits a nonnegative, monotone, `0⁺`-vanishing
  modulus `ω` with `f s w ≤ ω ‖w‖` on the radius-`R` tube.  Witness `ω r = sSup` of `f` over the
  radius-`min r R` sub-tube; boundedness from compactness (`IsCompact.bddAbove_image`), monotonicity
  from nested tubes (`csSup_le_csSup`), and the `0⁺` limit from Heine–Cantor uniform continuity
  (`IsCompact.uniformContinuousOn_of_continuous`).  This is the "monotone `ω → 0` from joint
  continuity of `Dv` on the compact trajectory tube" the plan flagged as the missing step.
* `hasFDerivAt_flow_of_continuous_deriv` (+ `differentiableAt`/`fderiv` corollaries) — the pointwise
  `C¹` dependence: from `hDv` (everywhere Fréchet derivative), `hDvc` (joint continuity of `Dv`), and
  `A s = Dv s (Φ x₀ s)`, `z ↦ Φ z t` is Fréchet differentiable at `x₀` with derivative the resolvent.
  Feeds the derivative-oscillation modulus `‖Dv s (Φ x₀ s + w) − Dv s (Φ x₀ s)‖` on the compact
  trajectory tube to `hasFDerivAt_flow_of_uniform_deriv_modulus_eventually`.
* `exists_flow_differentiable_of_continuous_deriv` — the unconditional **everywhere-`Differentiable`**
  version (continuous-derivative analogue of `exists_flow_differentiable_of_lipschitz_deriv`): from
  field-level data only, one flow family `Φ` with `Differentiable ℝ (z ↦ Φ z t)`.
* `exists_flow_fderiv_continuous_of_continuous_deriv` / `exists_flow_contDiff_one_of_continuous_deriv`
  — the **`ContDiff ℝ 1`** version (continuous-derivative analogue of
  `exists_flow_contDiff_one_of_lipschitz_deriv`).  Resolvent continuity is the continuous
  (non-Lipschitz) coefficient dependence of the fundamental solution
  (`norm_fundamentalSolution_sub_le_of_forall_le_Icc`) fed the base-point derivative-oscillation
  modulus at the flow-separation `exp(K(t−t₀))·‖z−z₀‖` (via `tendsto_modulus_comp_norm_sub`), squeezed
  to `0`; packaged through `contDiff_one_iff_fderiv`.  This is the honest "`C¹` in initial data" in
  the `ContDiff` vocabulary Item 2 consumes, now for an arbitrary `C^1` right-hand side.

Remaining for Point 4 (future sessions): unchanged — the manifold gauge-flow consumers of Items 1 & 2
(the compact-manifold gauge-flow constructor, the tensor time-derivative chain rule), the higher
(`ContDiff ℝ 2`/`3`) continuous-derivative layers (needing modulus arguments on `D²v`/`D³v`, lower
leverage since smooth Ricci-flow RHSs already have locally-Lipschitz derivatives and use the
`_lipschitz_` C³ capstone), and the Item 3 parabolic Hölder/Schauder frontier.

Update — **the time-`t` flow map is now a `C^k` diffeomorphism (`k = 1, 2, 3`) of the state
space, for *every* `t`**, in the new self-contained module
`AnalyticPDE/FlowDiffeomorphism.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`; imports the cached `SmoothDependenceCk`, so it builds
without recompiling that tower).  This closes the **inverse/bijectivity half** of "the flow is a
diffeomorphism family" that Item 2's compact-manifold gauge-flow constructor consumes: the
`SmoothDependenceCk` tower already proved the flow map injective (`injective_flow_apply`),
Lipschitz/continuous (`lipschitzWith_flow_apply`, `continuous_flow_apply`, `continuous_flow`) and
`ContDiff ℝ k` in the *forward* direction (`t₀ ≤ t`), but bijectivity, the inverse flow map, and
*backward* regularity did not exist.

* `surjective_flow_apply` / `bijective_flow_apply` — the flow map is a bijection: every `w` is
  `Φ z t` for `z = γ t₀`, `γ` the integral curve through `w` at `t`
  (`exists_isIntegralCurve_of_lipschitzWith`), identified with `Φ (γ t₀)` by uniqueness
  (`eq_of_isIntegralCurve_of_eq_at`).
* `exists_inverse_flow_apply` — the **reverse-time inverse flow** `ψ = (fun w ↦ Ψ w t₀)` from a
  companion family `Ψ` anchored at `t` (`exists_flow_family`); `LeftInverse`/`RightInverse` of
  `x ↦ Φ x t` by uniqueness, `LipschitzWith exp(K|t₀−t|)` as the time-`t₀` map of a flow family.
* `exists_homeomorph_flow_apply` — bundled `Homeomorph E E` whose coercion is `x ↦ Φ x t` (the
  ambient-topological skeleton of the self-diffeomorphism family).
* **Two-sided (all-time) regularity via time reversal.**  The `SmoothDependenceCk` regularity
  layers are all forward-only (`t₀ ≤ t`); the flow *inverse* is a backward flow, so backward
  regularity was the true blocker.  It follows from the forward theorems applied to the
  time-reversed field `w s x = -(v (-s) x)` (reversed derivatives `-(D^k v (-s) x)`; all
  norm/continuity/Lipschitz hypotheses transfer through negation + time reflection, the `C³`
  compatibility conditions via the new `curry2_neg` / `curryLeft_neg_fin3` `map_neg` lemmas),
  anchored at `-t₀`, target `-t ≥ -t₀`, then reflected by `s ↦ -s` (`isIntegralCurve_comp_neg`):
  `exists_flow_{differentiable,contDiff_one,contDiff_two,contDiff_three}_..._backward` and their
  `_two_sided` (all-`t`, by `le_total`) and given-family (`{differentiable,contDiff_one,
  contDiff_two,contDiff_three}_flow_apply_of_..`, one anchored family, every time, by uniqueness
  transport `eq_of_isIntegralCurve_of_eq`) forms.
* **The diffeomorphism capstones** `exists_contDiff_{one,two,three}_diffeomorph_flow_apply` — for a
  given flow family and *every* `t`, the reverse-time inverse `ψ` is a two-sided inverse of
  `x ↦ Φ x t` and **both** `x ↦ Φ x t` and `ψ` are `ContDiff ℝ k` (no forward/backward restriction).
* `exists_flow_contDiff_three_diffeomorph` — the **field-data-only** entry point: from the `C^{3,1}`
  jet of `v` alone, a flow family `Φ` (anchored at `t₀`, integral curve of `v`) whose time-`t` map
  is a `C³` diffeomorphism for every `t`.

Remaining for Point 4 (future sessions): unchanged in scope — connect this `C^k` flow-diffeomorphism
data (now bijective + two-sided-regular, i.e. genuine diffeomorphisms, at the Banach/chart level) to
the compact-manifold gauge-flow constructor (Item 2, `GaugeReduction/Diffeomorph3FlowExistence.lean`
through the Banach model bridge `ModelGaugeFlowODE.lean` and Mathlib's chart/`IsMIntegralCurve`
layer — the remaining work is the local-chart↔global-flow bridging, the diffeomorphism data itself
is now available), the tensor time-derivative chain rule (Item 1), and the Item 3 parabolic
Hölder/Schauder frontier (`AnalyticPDE/ParabolicHolder.lean`).

Update — **the Fréchet → manifold bridge is now built: `ContMDiff`/`HasMFDerivAt` smooth dependence
of the ODE flow on initial data for the model manifold `𝓘(ℝ, E)`**, in the new self-contained leaf
module `AnalyticPDE/SmoothDependenceManifold.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`; imports the cached `FlowDiffeomorphism` tower plus the
Mathlib manifold `ContMDiff`/`MFDeriv`/`Diffeomorph` layer, so it builds without recompiling the
Banach tower).  The Banach smooth-dependence towers (`SmoothDependenceCk`, `FlowDiffeomorphism`) state
everything in the *Fréchet* (`ContDiff`/`HasFDerivAt`/`IsIntegralCurve`) vocabulary of
`Mathlib.Analysis`, but Item 2's compact-manifold gauge-flow constructor
(`GaugeReduction/GaugeFlowAssembly.gaugeFlow_of_inverse_flow`) consumes the *manifold*
(`ContMDiff`/`HasMFDerivAt`) vocabulary of `Mathlib.Geometry.Manifold`.  This module transports the
whole diffeomorphism tower across that gap for the model manifold `E`, which — because the
general-manifold smooth-dependence theorem is proved chart-by-chart with each chart *the model space
`E`* — is the load-bearing chart-level core.  No new PDE/analytic content; nothing touches the heavy
gauge files.

* `hasMFDerivAt_of_isIntegralCurve` — the manifold ODE derivative form of an integral curve: from
  `IsIntegralCurve γ v`, `HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t ((1 : ℝ →L[ℝ] ℝ).smulRight (v t (γ t)))`
  for every `t` — exactly the `hderiv` shape `gaugeFlow_of_inverse_flow` consumes (via
  `hasDerivAt_iff_hasFDerivAt`/`smulRight_one_eq_toSpanSingleton` + `hasMFDerivAt_iff_hasFDerivAt`).
* `contMDiff_{one,two,three}_flow_apply_of_lipschitz_{deriv,secondDeriv,thirdDeriv}` — the manifold
  spatial `C^k` regularity of the flow map `x ↦ Φ x t` (`ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) k`), via
  `contMDiff_iff_contDiff`.
* `exists_flow_contMDiff_three` — field-data-only manifold smooth-dependence existence.
* `exists_flow_contMDiff_three_diffeomorph` — the manifold `C³` **self-diffeomorphism family**
  (per-time two-sided inverse `ψ`, both `x ↦ Φ x t` and `ψ` `ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) 3`): the
  model-manifold instance of the diffeomorphism data Item 2's gauge flow consumes.
* `exists_flow_contMDiff_three_gaugeData` — the **full model-manifold gauge-flow data bundle**:
  anchoring, the manifold ODE derivative equation at every time, and the per-time `C³`
  self-diffeomorphism data, packaged in the exact shapes `gaugeFlow_of_inverse_flow` needs (for
  `M = E`, `𝓘(ℝ, E)`).
* `exists_flow_diffeomorph_{one,two,three}` — the time-`t` flow map bundled as a first-class Mathlib
  `Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E k` (`k = 1, 2, 3`), from the `C^{k,1}` field jet alone: the
  reverse-time inverse flow supplies the smooth inverse, and both directions are `ContMDiff k`.

Remaining for Point 4 (future sessions): the last mile is the **general-manifold** lift — replacing
`M = E` (`𝓘(ℝ, E)`) with an arbitrary compact `M` — which is the chart-by-chart patching that lives
in the heavy `GaugeReduction/ModelGaugeFlowODE.lean` / `Diffeomorph3FlowExistence.lean` (the model
`E`-chart smooth-dependence core those consume is now available); the tensor time-derivative chain
rule (Item 1, `Diffeomorph3FlowTimeDerivative.lean`); and the Item 3 parabolic Hölder/Schauder
frontier (`AnalyticPDE/ParabolicHolder.lean`).

Update — **the model-manifold (`M = E`) raw `C³` gauge-flow existence is now inhabited from
field-jet data: the ODE smooth-dependence tower is connected all the way to the project's actual
gauge-flow structure `RicciFlow.Diffeomorph3GaugeFlowOn`**, in the new self-contained leaf module
`AnalyticPDE/ModelManifoldGaugeFlow.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`; a legacy-mode file importing the cached
`GaugeReduction/GaugeFlowAssembly` and the `AnalyticPDE/SmoothDependenceManifold` tower, so it builds
without recompiling either).  Item 2's reduction target
`GaugeFlowAssembly.gaugeFlow_of_inverse_flow` consumes mutually inverse `ContMDiff I I 3` time-slice
maps `F`, `G : ℝ → M → M`, anchoring, and the within-set manifold ODE derivative equation
`HasMFDerivWithinAt 𝓘(ℝ, ℝ) I (fun τ ↦ F τ x) s t ((1).smulRight (X t (F t x)))`.  For the model
manifold `E` (`𝓘(ℝ, E)`), a `TimeDependentVectorField` is *definitionally* an ordinary field
`ℝ → E → E` (`TangentSpace 𝓘(ℝ, E) x = E`), and the whole smooth-dependence tower supplies exactly
this data — so the previously separate Fréchet tower and manifold gauge API now meet.

* `exists_diffeomorph3GaugeFlowOn_of_field_jet` — from the `C^{3,1}` field jet of `v` alone (globally
  `K`-Lipschitz, time-continuous `v` with the standard globally-Lipschitz/jointly-continuous Fréchet
  jet `Dv`, `D²v` (`D2vc`/`D2vm`), `D³v` (`D3vm`/`D3v`) and the `curry2`/`curryLeft` compatibilities),
  `Nonempty (RicciFlow.Diffeomorph3GaugeFlowOn (I := 𝓘(ℝ, E)) (M := E) (X := v) s t₀)` on an *arbitrary*
  time set `s`.  A pure assembly: the gauge-data bundle `exists_flow_contMDiff_three_gaugeData`
  supplies `Φ`, anchoring, the per-time smooth inverse (`choose`), and the manifold ODE derivative
  (weakened to within-set by `HasMFDerivAt.hasMFDerivWithinAt`), fed to `gaugeFlow_of_inverse_flow`.
  The instance side (`IsManifold 𝓘(ℝ, E) ∞ E`, `ContMDiffVectorBundle 2 E (TangentSpace 𝓘(ℝ, E)) …`,
  `SigmaCompactSpace E`) resolves automatically for `M = E` from `[FiniteDimensional ℝ E]`,
  `[CompleteSpace E]`.  This is the **load-bearing chart-level core** of Item 2's general
  compact-manifold constructor: because the general-manifold smooth-dependence theorem is proved
  chart-by-chart with each chart the model space `E`, per-chart gauge-flow existence is now available;
  the remaining work is the local-chart↔global-flow patching in the heavy gauge files.
* `exists_flow_diffeomorph_three_hasMFDerivAt` — the per-chart *export*: a *single* flow family `Φ`
  that simultaneously anchors, satisfies the manifold ODE derivative equation at every time
  (`HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun τ ↦ Φ z τ) t ((1).smulRight (v t (Φ z t)))`), and is, for every
  `t`, the coercion of a bundled `Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3`.  This threads one `Φ` through
  both `exists_flow_diffeomorph_three` (which exposed the `Diffeomorph` family but dropped the flow
  equation) and the gauge-data bundle (which exposed the ODE but only an unbundled inverse), giving
  the exact per-chart datum — a first-class `C³` self-diffeomorphism family that *is* the flow of the
  chart-local field — the general lift transports.

Update — **`ContDiff` → field-jet bridge** added in `AnalyticPDE/FieldJetContDiff.lean` (axiom-clean
`propext`/`Classical.choice`/`Quot.sound`), beginning to close the usability gap that the whole
smooth-dependence tower is stated behind *artificial field-jet objects*. From a **single** clean
hypothesis — `v` jointly `ContDiff ℝ n (Function.uncurry v)` — the first jet layer is extracted:
`contDiff_apply_of_contDiff_uncurry` (each slice `v s` is spatially `ContDiff n`),
`hasFDerivAt_fderiv_of_contDiff_uncurry` (the spatial derivative object `fderiv ℝ (v s)` is a genuine
Fréchet derivative — the tower's `hDv` input), and `continuous_fderiv_of_contDiff_uncurry` (joint
`(t, x)`-continuity via the partial-derivative identity
`fderiv ℝ (v t) x = fderiv ℝ (Function.uncurry v) (t, x) ∘L inr` — the `hDvc` input).  The `hDvlip`
input follows from a second-derivative bound via
`lipschitzWith_fderiv_of_contDiff_of_nnnorm_secondFDeriv_le`, and the spatial-Lipschitz / time-continuity
inputs from `lipschitzWith_apply_of_contDiff_of_nnnorm_fderiv_le` /
`continuous_apply_of_contDiff_uncurry`.  These package into `contMDiff_one_flow_apply_of_contDiff` and
its fully self-contained form `contMDiff_one_flow_apply_of_contDiff_of_bddDerivs`: **manifold spatial
`C¹` regularity of the flow map stated purely from joint `ContDiff` of the field plus derivative
bounds** — the first tower flow-regularity result carrying no separately-assumed jet objects.  Next:
the layer-2/-3 extraction (second/third partial-derivative joint continuity + the `curry2`/`curryLeft`
compatibilities, reusing `curry2_iteratedFDeriv_two_eq_of_hasFDerivAt` /
`curryLeft_iteratedFDeriv_three_eq_of_hasFDerivAt`) to raise this to the full `C^{3,1}` jet that the
model-manifold `C³` gauge flow `exists_diffeomorph3GaugeFlowOn_of_field_jet` consumes.

Update — **parabolic Hölder normed-algebra constant-function primitives** added to
`AnalyticPDE/ParabolicHolder.lean` (axiom-clean), the constant-term / multiplicative-unit bounds
complementing the existing additive / scalar / product (`_add_le`, `_smul`, `_mul_le`,
`_mul_sub_mul_le`) estimates on the way to the Schauder fixed point: `parabolicHolderSeminorm_const`
(a constant has zero Hölder oscillation, `= 0`, via `ParabolicHolderWith 0`), `parabolicSupNorm_const_le`
(`≤ ‖c‖`, via `ParabolicBoundedWith ‖c‖`), and `parabolicC0AlphaNorm_const_le` (`≤ ‖c‖`).

Remaining for Point 4 (future sessions): the **general-manifold** lift (replace `M = E` with an
arbitrary compact `M`) — the local-chart↔global-flow patching in the heavy
`GaugeReduction/ModelGaugeFlowODE.lean` / `Diffeomorph3FlowExistence.lean`, whose per-chart flow
existence + diffeomorphism + ODE data is now available (`ModelManifoldGaugeFlow`); the Item 1 tensor
time-derivative chain rule (`Diffeomorph3FlowTimeDerivative.lean`); and the Item 3 parabolic
Hölder/Schauder frontier (`AnalyticPDE/ParabolicHolder.lean`).

Update — **parabolic `C^{0,α}` Banach space operator API extended** in
`AnalyticPDE/Parabolic/BanachSpace.lean` (all axiom-clean
`propext`/`Classical.choice`/`Quot.sound`), building the functional-analytic structure the
Ricci–DeTurck Banach chart and chart-closure data (Item 3) consume, layered on the genuine separated
Banach space (`ParabolicC0AlphaBanach`) and the norm-nonincreasing restriction operator `restrictL`:

* `restrictL_self` / `restrictL_comp` (carrier `ParabolicC0AlphaSpace` **and** Banach
  `ParabolicC0AlphaBanach`, with the `_apply` pointwise forms) — the **restriction operators form a
  projective system**: restricting along `s ⊆ s` is the identity, and `restrictL (r ⊆ t)` composed
  with `restrictL (t ⊆ s)` is `restrictL (r ⊆ s)`.  This is the categorical data that gluing of
  local Ricci–DeTurck Banach-chart solutions across overlapping charts consumes.
* `evalCLM z hz` (carrier and Banach, with `evalCLM_apply` / `evalCLM_mk` / `evalCLM_mk_apply`,
  `norm_evalCLM_apply_le`, `norm_evalCLM_le`) — **point evaluation at a space-time point `z ∈ s` as a
  bounded linear functional `… →L[ℝ] E` of operator norm `≤ 1`**.  On the carrier it is the
  composite `LinearMap.proj z ∘ subtype` bounded by `norm_le_parabolicC0AlphaNorm` (the sup part of
  the `C^{0,α}` norm controls the pointwise value on `s`); it **descends to the Banach quotient** via
  `SeparationQuotient.liftCLM` because functions identified on `s` share the value at `z ∈ s`.  This
  is the functional that reads off a Banach-chart solution's value at a space-time point.
* `evalCLM_restrictL_apply` (carrier and Banach) — **the evaluation functionals form a compatible
  cone over the restriction projective system**: `evalCLM z hz ∘ restrictL (t ⊆ s) = evalCLM z (…)`
  for `z ∈ t`.  This is the coherence that keeps the point-values of glued chart-solutions consistent
  across overlaps.
* `eq_iff_forall_evalCLM` — **the point-evaluation functionals separate points**: a parabolic
  `C^{0,α}` Banach class is completely determined by its values at the space-time points of `s`
  (`x = y ↔ ∀ z ∈ s, evalCLM z hz x = evalCLM z hz y`), via `mk_eq_mk_iff` and the `B = H = 0`
  `C^{0,α}` bound (a function vanishing on `s` has zero parabolic `C^{0,α}` norm).  The faithful
  representation showing a Ricci–DeTurck Banach-chart solution is determined by its space-time values.

Remaining for Point 4 (future sessions): the genuine **Schauder a-priori estimates** and the
Ricci–DeTurck RHS operator on the parabolic Banach space (Item 3, the analytic main theorem); the
**general-manifold** gauge-flow lift (Item 2, heavy gauge files); and the Item 1 tensor
time-derivative chain rule.

Update — **parabolic `C^{0,α}` Banach change-of-variables + inhomogeneous operator API extended** in
`AnalyticPDE/Parabolic/BanachSpace.lean` (all axiom-clean
`propext`/`Classical.choice`/`Quot.sound`), continuing the Ricci–DeTurck Banach-chart operator
algebra (`restrictL`/`evalCLM`/`compL`/`mulCoeffL`/`mulL`) toward the Schauder fixed point:

* **Precomposition norm bounds** (`parabolicSupNorm_comp_mapsTo`,
  `parabolicHolderSeminorm_comp_parabolicDistanceLe`, `parabolicC0AlphaNorm_comp_parabolicDistanceLe_le`)
  — the norm-level core: for a space-time map `φ : ℝ × Y → ℝ × X` mapping `t` into `s` and expanding
  parabolic distance by at most `L`, the sup norm of `u ∘ φ` on `t` is `≤` that of `u` on `s`, the
  Hölder seminorm scales by `L ^ α`, and `‖u ∘ φ‖_{C^{0,α}(t)} ≤ max 1 (L ^ α) · ‖u‖_{C^{0,α}(s)}`
  (built on the existing `comp_parabolicDistanceLe` change-of-variables family).
* **The precomposition (change-of-variables) bounded operator** `ParabolicC0AlphaBanach.precompL`
  — `u ↦ u ∘ φ` as a bounded operator `ParabolicC0AlphaBanach X E α s →L ParabolicC0AlphaBanach Y E α t`
  of operator norm `≤ max 1 (L ^ α)` (carrier `ParabolicC0AlphaSpace.precompSubmoduleLinearMap`
  /`precompLinearMap`/`precompL`, descended to the separation quotients because bounded), with
  `precompL_mk`, `norm_precompL_le`, and the pullback∘evaluation cone coherence
  `evalCLM_precompL_apply` (`evalCLM w (precompL φ x) = evalCLM (φ w) x`).  This is the operator behind
  chart-transition gluing, the DeTurck gauge-diffeomorphism action, and parabolic Schauder scaling;
  it **generalises `restrictL`** (the `φ = ` inclusion, `L = 1` case).
* **Precomposition functoriality** `precompL_comp_apply` — the contravariant cocycle law
  `precompL_ψ ∘ precompL_φ = precompL_{φ∘ψ}` (composite `r → s`, `(L·M)`-expanding), the
  chart-transition cocycle condition that gluing across overlapping charts consumes (precomposition
  analogue of `restrictL_comp` / `compL_comp`), proved through the point-separation representation.
* **The constant-function embedding operator** `ParabolicC0AlphaBanach.constL` — `c : E ↦` the class
  of the constant field `z ↦ c`, a bounded operator `E →L ParabolicC0AlphaBanach X E α s` of norm
  `≤ 1` (the inhomogeneous / frozen-data part of the affine `u ↦ A u + f` Ricci–DeTurck RHS), with
  `norm_constL_le`, the point-evaluation coherence `evalCLM_constL_apply` (`evalCLM z (constL c) = c`),
  and the bundle-morphism compatibility `compL_constL` (`compL L (constL c) = constL (L c)`).

Remaining for Point 4 (future sessions): unchanged in scope — the genuine **Schauder a-priori
estimates** and the Ricci–DeTurck RHS operator (assembled from `mulCoeffL`/`compL`/`precompL`/`constL`)
on the parabolic Banach space (Item 3, the analytic main theorem); the **general-manifold**
gauge-flow lift (Item 2, heavy gauge files); and the Item 1 tensor time-derivative chain rule.

Update — **the parabolic `C^{0,α}` Banach nonlinear Schauder fixed-point toolkit** added to
`AnalyticPDE/Parabolic/BanachSpace.lean` (all axiom-clean
`propext`/`Classical.choice`/`Quot.sound`), taking the Ricci–DeTurck Banach chart from *linear/affine*
solvability to the genuine *nonlinear/quasilinear* fixed point that the actual RHS consumes, layered
on the completed affine Neumann solvability (`affineSolveL`, `exists_unique_affineFixedPoint`):

* **Continuous dependence of the linear solution operator on its coefficients** — `affineSolveL_mul_oneSub`
  (the left-inverse companion `affineSolveL A hA * (1 - A) = 1` of the existing right inverse, so
  `affineSolveL A hA = (1 - A)⁻¹` two-sidedly), the **resolvent identity** `affineSolveL_sub_eq`
  (`(1 - A)⁻¹ - (1 - B)⁻¹ = (1 - A)⁻¹ (A - B) (1 - B)⁻¹`), its operator-norm bound
  `norm_affineSolveL_sub_le` (`≤ (1 - ‖A‖)⁻¹ ‖A - B‖ (1 - ‖B‖)⁻¹`: the *Lipschitz dependence of the
  linearised Schauder solution operator on the frozen coefficient operator* that turns the
  coefficient-dependent iteration into a contraction), and the a-priori solution-difference estimate
  `norm_affineSolveL_apply_sub_le` at fixed data `f`.
* **Nonlinear Banach fixed point** — `exists_unique_lipschitzFixedPoint` (a `LipschitzWith k`, `k < 1`
  self-map has a unique fixed point `g u = u`: the nonlinear generalisation of the affine case, i.e.
  solvability of the genuine quasilinear Ricci–DeTurck RHS on a short-time / small-ball chart where it
  contracts), the a-posteriori residual bound `norm_sub_fixedPoint_le_of_lipschitz`
  (`‖x - u‖ ≤ ‖x - g x‖ / (1 - k)`), and the stability estimate `norm_fixedPoint_sub_fixedPoint_le`
  (`‖u₁ - u₂‖ ≤ C / (1 - k)` when `‖g₁ z - g₂ z‖ ≤ C` uniformly — well-posedness under a perturbation
  of the nonlinearity; only `g₁` need contract).
* **Quantitative Picard/Schauder iteration convergence** — `norm_iterate_sub_fixedPoint_le` (the
  a-priori geometric rate `‖g^[n] x - u‖ ≤ ‖x - g x‖ · kⁿ / (1 - k)`, the constructive form of the
  nonlinear existence) and `tendsto_iterate_fixedPoint` (the iterates converge to the solution).
* **The quasilinear RHS shape** — `exists_unique_affinePlusLipschitzFixedPoint`: the actual
  Ricci–DeTurck right-hand side split `A u + N u + f` (bounded linear principal-plus-lower-order part
  `A`, nonlinear `LipschitzWith k` remainder `N`, frozen data `f`) is uniquely solvable when
  `‖A‖ + k < 1`, via `LipschitzWith.add` (contraction constant `‖A‖₊ + k`) + the nonlinear fixed point.
  Generalises the affine `exists_unique_affineFixedPoint` (`N = 0`) and the `compL`/`mulCoeffL`
  corollaries.

Remaining for Point 4 (future sessions): the genuine **parabolic Schauder a-priori estimates** that
make the concrete Ricci–DeTurck RHS operator a short-time contraction (bounding the operator norm by
the time-interval length — the hard analytic content in `AnalyticPDE/ParabolicHolder.lean`), and the
assembly of the concrete RHS from `mulCoeffL`/`compL`/`precompL`/`constL` with the geometric
coefficients (Item 3, the analytic main theorem); the **general-manifold** gauge-flow lift (Item 2,
heavy gauge files); and the Item 1 tensor time-derivative chain rule.

Update — **the manifold-level spatial pushforward (differential) of the ODE flow map is now proved on
the model manifold `𝓘(ℝ, E)`**, extending `AnalyticPDE/SmoothDependenceManifold.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`; a pure Fréchet→manifold transport, nothing touches the heavy
gauge files).  The Banach `SmoothDependenceCk` tower proved spatial `C^k` smoothness (`ContMDiff`) of
the time-`t` flow map `x ↦ Φ x t` and the *time* derivative of a single trajectory
(`hasMFDerivAt_of_isIntegralCurve`), but the **pushforward** — the manifold differential (`mfderiv`) of
the flow map itself, and its explicit value the resolvent `D_x Φ_t` — was stated only in the *Fréchet*
(`HasFDerivAt`/`fderiv`) vocabulary.  Item 1's tensor time-derivative chain rule and Item 2's
compact-manifold gauge-flow constructor both consume the *manifold* (`HasMFDerivAt`/`mfderiv`) form.

* `hasMFDerivAt_flow_apply_of_hasFDerivAt` / `hasMFDerivWithinAt_flow_apply_of_hasFDerivAt` /
  `mfderiv_flow_apply_of_hasFDerivAt` — the **generic pushforward bridges**: from the Fréchet spatial
  derivative `HasFDerivAt (fun z => Φ z t) D x₀` (which the tower supplies via
  `hasFDerivAt_flow_of_lipschitz_deriv` etc.), the time-`t` flow map has manifold differential `D`
  (`HasMFDerivAt`/`HasMFDerivAt[s]`/`mfderiv = D`).  The spatial companion of
  `hasMFDerivAt_of_isIntegralCurve` (`HasFDerivAt.hasMFDerivAt` / `.mfderiv`).
* `hasMFDerivAt_flow_apply_of_lipschitz_deriv` / `mfderiv_flow_apply_of_lipschitz_deriv` — the
  **self-contained `C^{1,1}`-jet identification**: `mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) (fun z => Φ z t) x₀ =
  fundamentalSolution … = D_x Φ_t` — *the manifold pushforward is the resolvent* — transporting
  `hasFDerivAt_flow_of_lipschitz_deriv_of_hasFDerivAt`.  (An `E →L[ℝ] E` type ascription on the
  resolvent is essential: without it, elaborating the concrete `fundamentalSolution …` term *against*
  the expected tangent-space CLM type eagerly triggers `NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) x₀)`
  synthesis, which fails because `TangentSpace I x := E` derives only the `AddCommGroup`/`Module`/
  `TopologicalSpace` structure, not the normed one; the ascription forces elaboration at the Fréchet
  type first, then the tangent-space identification is a defeq unification.)
* `hasMFDerivAt_fundamentalSolution_apply` / `hasMFDerivWithinAt_fundamentalSolution_apply` — the
  **manifold vector variational ODE of a pushed-forward direction** (resolvent column): the path
  `τ ↦ D_x Φ_τ · u₀` (the pushforward of a fixed tangent vector `u₀` along the flow) has manifold
  derivative `(1).smulRight (A t (D_x Φ_t · u₀))` for every `t` (and its `HasMFDerivAt[s]` refinement),
  via `hasMFDerivAt_of_isIntegralCurve` ∘ `isIntegralCurve_fundamentalSolution_apply` — exactly the
  "time-derivative of the pushforward `Φ_t · u`" datum Item 1's scalar chain rule differentiates.
* `contMDiff_fundamentalSolution_apply_time` / `contMDiff_infty_fundamentalSolution_apply_time` — the
  **`C^{n+1}`/`C^∞` time-regularity of the pushed-forward direction** `τ ↦ D_x Φ_τ · u₀` (manifold form
  of `contDiff_fundamentalSolution_apply_time`, via `contMDiff_iff_contDiff`), the pushforward-leg time
  regularity the tensor time-derivative chain rule consumes.

Remaining for Point 4 (future sessions): unchanged in scope — the **general-manifold** gauge-flow lift
(Item 2, the chart↔global patching in the heavy gauge files; the model-`E`-chart pushforward/resolvent
data those consume is now available in the manifold vocabulary), the Item 1 tensor time-derivative
chain rule (which now has both the pushforward `mfderiv` and its time derivative available as manifold
data), and the Item 1 tensor time-derivative
chain rule (which now has both the pushforward `mfderiv` and its time derivative available as manifold
data), and the Item 3 parabolic Schauder a-priori estimates.

Update — **the time-derivative of the *actual flow's* pushforward is now proved on the model manifold
`𝓘(ℝ, E)`**, extending `AnalyticPDE/SmoothDependenceManifold.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`).  The previous milestone gave, separately, the spatial
pushforward `mfderiv Φ_τ = D_x Φ_τ = fundamentalSolution` (`mfderiv_flow_apply_of_lipschitz_deriv`)
and the resolvent's *own* vector variational ODE (`hasMFDerivAt_fundamentalSolution_apply`, about an
abstract coefficient path).  This session **fuses** them into the classical variational law stated
through the actual flow's differential, `d/dt (D_x Φ_t · u₀) = D_x v_t|_{Φ_t x₀} · (D_x Φ_t · u₀)` —
exactly Item 1's "derivative of the pushforward `Φ_t · u`" leg, now for the honest gauge flow rather
than an abstract resolvent:

* `hasMFDerivWithinAt_flow_pushforward_of_lipschitz_deriv` / `hasMFDerivAt_flow_pushforward_of_lipschitz_deriv`
  / `mfderiv_flow_pushforward_of_lipschitz_deriv` — the **abstract** (`C^{1,1}`-jet with a supplied
  reference coefficient/variational family) within-`Ici t₀`, interior (`t₀ < t`), and `mfderiv`-readout
  forms of `HasMFDerivWithinAt/HasMFDerivAt/mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,E) (fun τ ↦ (mfderiv (fun z ↦ Φ z τ) x₀) u₀)`,
  transferred from `hasMFDerivAt_fundamentalSolution_apply` along the pointwise pushforward=resolvent
  equality on `Ici t₀` via `HasMFDerivWithinAt.congr_mono` / `HasMFDerivAt.congr_of_eventuallyEq`
  (the resolvent identity holds only for `τ ≥ t₀`, hence the within-`Ici t₀` / interior split).
* `hasMFDerivWithinAt_flow_pushforward_of_field_jet` / `hasMFDerivAt_flow_pushforward_of_field_jet`
  / `mfderiv_flow_pushforward_of_field_jet` — the **genuinely usable field-data-only** forms: the caller
  supplies only the `C^{1,1}` field jet of `v` (globally `K`-Lipschitz, everywhere Fréchet derivative
  `Dv` jointly continuous and `L`-Lipschitz in space) plus the actual flow `Φ`; the canonical reference
  coefficient `A t := D_x v_t|_{Φ_t x₀}`, the `‖Dv‖ ≤ K` bound (`HasFDerivAt.le_of_lipschitz`), the
  variational family (`exists_variationalFlowFamily`), and the segment deviation bound (spatial Lipschitz
  constant) are all built internally, so the conclusion is the explicit
  `(1).smulRight (D_x v_t|_{Φ_t x₀} · (D_x Φ_t · u₀))`.

With the base-point leg (`hasMFDerivAt_of_isIntegralCurve`, giving `d/dt (Φ_τ x) = v_τ(Φ_τ x)`) and
these pushforward legs, **all three model-`E`-chart ODE-derivative inputs to Item 1's scalar tensor
chain rule `B(τ)(y(τ))(a(τ))(b(τ))` — the base point `y(τ)`, and the two pushed-forward directions
`a(τ), b(τ)` — are now available in the manifold vocabulary**; the remaining Item 1 work is the metric
leg (`∂_t g`, spatial `∂` of `g.inner`) and the scalar assembly in the heavy tensor file.  Remaining
for Point 4 (future sessions): unchanged in scope — the general-manifold gauge-flow lift (Item 2), the
Item 1 metric-leg + scalar-assembly, and the Item 3 parabolic Schauder a-priori estimates.

Update — **the parabolic short-time-smallness a-priori layer is now proved** in
`AnalyticPDE/ParabolicHolder.lean` (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`), the
"operator norm bounded by the time-interval length" content the Ricci–DeTurck / parabolic Schauder
fixed point contracts on.  The parabolic distance from `(t, x)` to the initial-time point `(t₀, x)` is
`√|t − t₀|`, so a function that vanishes at the initial time is uniformly small on a thin time-slab —
this is the mechanism that makes the DeTurck solution map a short-time contraction.  Thirteen new
theorems, in four coherent groups:

* **Short-time smallness from initial vanishing.**  `norm_le_of_parabolicHolderWith_of_initial_zero`
  (pointwise `‖u (t, x)‖ ≤ C · (√T)^α` from a Hölder constant `C`, initial vanishing `u (t₀, x) = 0`,
  and `|t − t₀| ≤ T`); `parabolicSupNorm_le_holderSeminorm_mul_of_initial_zero`
  (`‖u‖_{C⁰} ≤ [u]_α · (√T)^α` on a slab-`+`-initial-cylinder set, `→ 0` as `T → 0`);
  `parabolicC0AlphaNorm_le_holderSeminorm_mul_of_initial_zero`
  (`‖u‖_{C^{0,α}} ≤ ((√T)^α + 1) · [u]_α`, full-norm control by the seminorm alone);
  `sqrt_rpow_eq_rpow_half` (`(√T)^α = T^{α/2}`) and
  `parabolicSupNorm_le_holderSeminorm_mul_rpow_of_initial_zero` (the explicit `T^{α/2}` power-of-slab
  form).
* **Affine (non-vanishing) initial data.**  `norm_le_of_parabolicHolderWith_of_initial_le`,
  `parabolicSupNorm_le_add_holderSeminorm_mul_of_initial_le`
  (`‖u‖_{C⁰} ≤ M₀ + [u]_α · (√T)^α`) and
  `parabolicC0AlphaNorm_le_add_holderSeminorm_mul_of_initial_le`
  (`‖u‖_{C^{0,α}} ≤ M₀ + ((√T)^α + 1) · [u]_α`): the estimates in the honest form the iteration with a
  *prescribed* (bounded-by-`M₀`, not zero) initial condition consumes; splitting
  `u (t, x) = (u (t, x) − u (t₀, x)) + u (t₀, x)`.  `M₀ = 0` recovers the vanishing case.
* **Space/time decomposition of parabolic Hölder regularity.**
  `norm_sub_le_of_parabolicHolderWith_same_time` (spatial `α`-Hölder projection at fixed time,
  `‖u (t, x) − u (t, y)‖ ≤ C · dist x y ^ α`), `norm_sub_le_of_parabolicHolderWith_same_space`
  (temporal `α/2`-Hölder projection at fixed space, `‖u (t, x) − u (τ, x)‖ ≤ C · |t − τ|^{α/2}`), and
  `parabolicHolderWith_of_forall_same_time_same_space` (the reconstruction: separate spatial-`α` +
  temporal-`α/2` control on a set closed under mixing coordinates — a parabolic cylinder — reassemble
  into parabolic `α`-Hölder control with constant `Hs + Ht`, via the intermediate point `(p.1, q.2)`).
  The structural characterisation of parabolic Hölder spaces the Schauder theory rests on.
* **Short-time smallness in the full `C^{0,α}` (Banach) norm.**
  `parabolicSupNorm_le_parabolicC0AlphaNorm_mul_of_initial_zero`
  (`‖u‖_{C⁰} ≤ ‖u‖_{C^{0,α}} · (√T)^α` for initial-vanishing `u` — honest operator smallness on the
  parabolic Banach space) and its contraction form
  `parabolicSupNorm_sub_le_parabolicC0AlphaNorm_mul_of_initial_agree`
  (`‖u − v‖_{C⁰} ≤ ‖u − v‖_{C^{0,α}} · (√T)^α` when `u`, `v` agree at the initial time): the solution
  map has `C⁰`-operator norm `≤ (√T)^α → 0` on the fibre over a fixed initial condition — the
  short-time contraction giving uniqueness / short-time existence of the DeTurck fixed point.

Remaining for Point 4 (future sessions): the remaining genuine parabolic **Schauder interior/global
a-priori estimate** (bounding the full `C^{0,α}` norm of the solution by the data — the heat-kernel
Schauder content) and the assembly of the concrete Ricci–DeTurck RHS operator on the parabolic Banach
chart from `mulCoeffL`/`compL`/`precompL`/`constL` with these short-time-smallness factors (Item 3);
the **general-manifold** gauge-flow lift (Item 2, heavy gauge files — the `C³` initial-data-dependence
input `exists_flow_contDiff_three_diffeomorph` and the model-manifold gauge-flow core
`exists_diffeomorph3GaugeFlowOn_of_field_jet` are now available); and the Item 1 tensor
time-derivative chain rule (metric leg + scalar assembly in the heavy tensor file).

Update — **the parabolic Banach fixed-point mechanism is now proved** in
`AnalyticPDE/ParabolicHolder.lean` (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`), the
Picard/contraction engine that turns the completeness of the parabolic `C^{0,α}` space into the
short-time Ricci–DeTurck solution operator.  Four new theorems:

* **Definiteness/separation.**  `eqOn_of_parabolicC0AlphaNorm_sub_eq_zero` and its `iff` form
  `parabolicC0AlphaNorm_sub_eq_zero_iff_eqOn`: on the class, `‖u − v‖_{C^{0,α}} = 0 ↔ u =ₛ v`, so
  `parabolicC0AlphaNorm` is a genuine norm modulo equality on `s` (the definiteness underlying the
  fixed point's uniqueness).
* **Fixed-point existence + uniqueness.**  `exists_parabolicC0AlphaOn_fixedPt_of_contraction`: a
  class-preserving `q`-contraction `T` (`0 ≤ q < 1`) for the parabolic `C^{0,α}` norm has a class
  fixed point `g` (`T g =ₛ g`), unique on `s`.  Proof: the Picard iterates `Tⁿ u₀` have geometrically
  decaying consecutive differences (`‖T^{n+1}u₀ − Tⁿu₀‖ ≤ qⁿ‖T u₀ − u₀‖`), telescope to a
  `C^{0,α}`-Cauchy sequence (tail `≤ qᴺ‖T u₀ − u₀‖/(1−q)`), and converge by
  `exists_parabolicC0AlphaOn_tendsto_of_cauchy`; the contraction forces the limit fixed and unique.
* **A-priori residual bound.**  `parabolicC0AlphaNorm_fixedPt_sub_le_of_contraction`: any fixed point
  obeys `‖g − u₀‖ ≤ (1−q)⁻¹·‖T u₀ − u₀‖` (no iteration — just `g − u₀ = (T g − T u₀) + (T u₀ − u₀)` on
  `s`, triangle, contraction), the invariant-ball datum.
* **Bundled solution operator.**  `exists_parabolicC0AlphaOn_fixedPt_ball_of_contraction`:
  existence + uniqueness-on-`s` + the explicit `C^{0,α}`-ball bound in one package — the chart-closure
  datum the Ricci–DeTurck short-time existence consumes once its RHS is exhibited as a contraction.

Remaining for Point 4 (future sessions): the genuine parabolic **Schauder interior/global a-priori
estimate** exhibiting the DeTurck RHS as such a `C^{0,α}` contraction (the heat-kernel content), and
its assembly from `mulCoeffL`/`compL`/`precompL`/`constL` with the short-time-smallness factors
(Item 3); the **general-manifold** gauge-flow lift (Item 2, heavy gauge files); and the Item 1 tensor
time-derivative chain rule (metric leg + scalar assembly in the heavy tensor file).

Update — **the compact-manifold time-dependent local flow existence + injectivity + uniqueness is now
proved** in `GaugeReduction/ManifoldFlowExistence.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`; a pure manifold-topology + integral-curve development, no PDE
content, nothing touching the heavy gauge files).  The module previously supplied compact-manifold
*uniform-time* existence only for **autonomous** fields (`exists_uniform_integralCurve_time`, needing the
whole manifold compact) and only **per-point** local existence for time-dependent fields
(`exists_timeDependent_integralCurve`).  The DeTurck gauge field is *time-dependent*, and its
autonomization space `ℝ × M` is never compact — but the **initial-time slice** `{0} × M` is.  This
session closes exactly that gap, delivering the time-dependent existence core the gauge flow consumes
(Item 2), plus the injectivity (diffeomorphism-onto-image) and uniqueness (canonicity) halves:

* `exists_uniform_time_of_nhds_uniform_on_compact` — the **compact-slice** flow-box reduction: the
  neighborhood-uniform flow box (`exists_nhds_uniform_integralCurve`) yields a *single* uniform lifespan
  `ε > 0` over any **compact subset** `S` of a (possibly noncompact) manifold, by a finite subcover of `S`
  and the minimum lifespan.  The refinement of `exists_uniform_time_of_nhds_uniform` (whole space compact)
  needed to integrate over the compact slice `{0} × M ⊆ ℝ × M`.
* `exists_uniform_timeDependent_integralCurve_time` — the **compact-manifold time-dependent uniform-time
  local existence**: for a jointly-`C¹` time-dependent field `X` on a compact boundaryless complete
  manifold there is one `ε > 0` such that *every* start point `x` admits a time-dependent integral curve
  of `X` on the common `Ioo (-ε) ε`.  Autonomize to `ℝ × M`, take the uniform lifespan over the compact
  slice `{0} × M` via the compact-slice reduction, and project through
  `isTimeDependentIntegralCurve_of_autonomous_of_fst`.
* `exists_timeDependent_flow_compact` — the bundled flow `Φ : ℝ → M → M` with `Φ 0 = id` and every orbit
  `τ ↦ Φ τ x` a time-dependent integral curve on `Ioo (-ε) ε` (via `choose`): the anchored
  integral-curve family the gauge construction is built on.
* `timeDependent_integralCurve_eqOn_of_eq` — **uniqueness anchored at any interior time** (generalising
  `timeDependent_integralCurve_unique`, anchor `0`): two time-dependent integral curves on `Ioo a b`
  agreeing at a single interior `t₀` agree throughout, via the autonomous lift + mathlib's
  `isMIntegralCurveOn_Ioo_eqOn_of_contMDiff_boundaryless` at `t₀`.
* `timeDependent_flow_injective` — **injectivity of every time-`t` slice** `x ↦ Φ t x`: two orbits
  agreeing at time `t` agree at time `0`, where the anchor reads off the two start points.  The
  diffeomorphism-onto-image (injectivity) half Item 2 consumes.
* `timeDependent_flow_unique` — **canonicity of the flow**: two anchored flows with orbits solving the
  same field ODE on `Ioo (-ε) ε` coincide there (orbit uniqueness anchored at `0`).
* `exists_timeDependent_flow_compact_injective` — the bundled **existence + orbit-ODE + injective
  time-slices** datum in one package; with `timeDependent_flow_unique` this exhibits the compact-manifold
  local flow as a *canonically determined family of injections* — the forward-family `F` datum
  `GaugeReduction/GaugeFlowAssembly.lean`'s `gaugeFlow_of_inverse_flow` consumes (`hanchored` + `hderiv`).

Remaining for Point 4 (future sessions): unchanged in scope — for Item 2 the **spatial `C³` regularity**
of the flow map `x ↦ F t x` (the `C¹→C³` bootstrap from `SmoothDependenceCk`/`SmoothDependenceManifold`
into this compact-manifold flow) and the **mutual spatial inverse** `G t` (the two-parameter / reverse
time-dependent flow giving surjectivity, whose forward existence pieces — uniform time-dependent
existence and anchored uniqueness — are now in place), then `gaugeFlow_of_inverse_flow` closes Item 2;
plus the Item 1 tensor time-derivative chain rule and the Item 3 parabolic Schauder a-priori estimates.

Update — **the compact-manifold time-dependent flow's slices are now proved bijective, with
a concrete mutually-inverse family — the diffeomorphism-onto-image / `G t`-inverse content
`gaugeFlow_of_inverse_flow` consumes on the window is closed**, extending
`GaugeReduction/ManifoldFlowExistence.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`; a pure manifold-topology + integral-curve
development, no PDE content, nothing touching the heavy gauge files).  The previous milestone
supplied forward existence, **injectivity** (`timeDependent_flow_injective`), and canonicity
(`timeDependent_flow_unique`) of the time-slice maps `x ↦ Φ t x`, but **surjectivity** — the
other half of "diffeomorphism onto image" — is *not* automatic on a compact manifold from
injectivity + continuity (that would need invariance of domain); it requires a genuine backward
flow (an integral curve of `X` run from time `t` *back* to time `0`), whose lifespan must be
reconciled with the forward lifespan.  This session closes exactly that gap:

* `autonomous_fst_eq_add` — the **affine first-coordinate law** generalising `autonomous_fst_eq_id`
  to any anchor time: an autonomous integral curve `Γ` of `(1, X)` on a preconnected open `s ∋ 0`
  with `(Γ 0).1 = t₀` has `(Γ t).1 = t₀ + t` throughout (the first coordinate has constant
  derivative `1`, so it is `t ↦ t₀ + t`).  This lets a curve *anchored at time `t₀`* be recognised,
  after the shift `σ ↦ σ - t₀`, as a genuine time-dependent integral curve.
* `exists_uniform_timeDependent_integralCurve_anchored` — **anchored-anywhere existence over a
  compact time-slab**: for any `r > 0`, a single uniform lifespan `δ > 0` such that *every* start
  time `t₀ ∈ [-r, r]` and *every* point `y` admit a time-dependent integral curve of `X` on
  `Ioo (t₀ - δ) (t₀ + δ)` with `γ t₀ = y`.  Proved by taking the uniform lifespan of the
  autonomization `(1, X)` over the compact **slab** `Icc (-r) r ×ˢ univ ⊆ ℝ × M`
  (`exists_uniform_time_of_nhds_uniform_on_compact`, previously used only over the `{0} × M` slice)
  and time-shifting the autonomous curve anchored at `(t₀, y)` by `σ ↦ σ - t₀`
  (`IsMIntegralCurveOn.comp_add`), whose first coordinate then tracks the parameter by
  `autonomous_fst_eq_add`, so it descends via `isTimeDependentIntegralCurve_of_autonomous`.  The
  slab (not a single slice) is what supplies a lifespan `δ` uniform over the *start times*, the
  crux of the backward-lifespan reconciliation.
* `timeDependent_flow_surjective` — **surjectivity of every time-slice** `x ↦ Φ t x` (`|t| < min ε₁ δ`):
  run the backward curve from `(t, y)` to time `0`, landing at `x`; then `Φ · x` and that backward
  curve are two time-dependent integral curves agreeing at time `0`, so by uniqueness
  (`timeDependent_integralCurve_eqOn_of_eq`, restricted to a common sub-interval `Ioo a b ∋ 0, t`
  via `HasMFDerivWithinAt.mono`) they agree at `t`, giving `Φ t x = y`.
* `exists_timeDependent_flow_compact_bijective` — the bundled **uniform `ε > 0` anchored flow with
  every slice bijective**: reconciles the forward lifespan `ε₁` (`exists_timeDependent_flow_compact`)
  and the slab lifespan `δ` (the anchored existence, with `r := ε₁`) by `ε := min ε₁ δ`; combines the
  existing injectivity with the new surjectivity.  With `timeDependent_flow_unique` this exhibits the
  compact-manifold local flow as a *canonically determined family of bijections*.
* `exists_timeDependent_flow_compact_inverse` — the **concrete mutually-inverse `F := Φ`, `G` datum**:
  the explicit inverse family `G t := Function.invFun (Φ t)`, both anchored at the identity
  (`Φ 0 = G 0 = id`), the forward orbits solving the gauge ODE on `Ioo (-ε) ε`, and `G t` a genuine
  two-sided inverse of the bijection `Φ t` on every window time (`Function.leftInverse_invFun` /
  `rightInverse_invFun`).  This is exactly the `hleft`/`hright` mutually-inverse time-slice datum
  `GaugeFlowAssembly.gaugeFlow_of_inverse_flow` consumes (on the window; needs `[Nonempty M]`).

Reading the adapter `GaugeFlowAssembly.gaugeFlow_of_inverse_flow` confirms its `F`, `G` are the
*spatial* inverse per slice (**not** a backward time-flow), consumed as `LeftInverse`/`RightInverse`
+ `ContMDiff I I 3` + anchoring + the within-set manifold ODE.  With this milestone the
mutual-inverse, anchoring, and ODE-derivative data are all in hand on the window; the **single
remaining Item-2 analytic obligation is the spatial `C³` regularity** `hF`/`hG` of the slice maps
(the `C¹ → C³` bootstrap transported chart-by-chart from `SmoothDependenceCk`/`SmoothDependenceManifold`,
whose model-`E`-chart `C³` smooth dependence is already proved), plus the global-`ℝ` extension of the
windowed `F`/`G` the adapter's `∀ t` hypotheses want.  Remaining for Point 4 (future sessions):
unchanged in scope — that spatial-`C³` regularity + global extension for Item 2, the Item 1 tensor
time-derivative chain rule (metric leg + scalar assembly in the heavy tensor file), and the Item 3
parabolic Schauder a-priori estimates.

Update — **the parabolic Hölder interpolation → short-time-contraction toolkit is now proved**,
in `AnalyticPDE/ParabolicHolder.lean` and the new leaf module
`AnalyticPDE/ParabolicInterpolation.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`).  The classical interpolation between the `C^0` (sup)
norm and the `α`-Hölder seminorm — the mechanism parabolic Schauder estimates use to *absorb
lower-order terms* and, combined with the initial-vanishing short-time smallness, to make the
Ricci–DeTurck solution map a contraction in the *intermediate* Hölder norms (not merely the sup
norm).  Pure norm/rpow/AM–GM algebra, no heat-kernel content:

* `parabolicHolderWith_interpolation` / `parabolicHolderSeminorm_interpolation_le` /
  `parabolicC0AlphaNorm_interpolation_le` (in `ParabolicHolder.lean`) — the **multiplicative
  interpolation** `[u]_{α θ} ≤ (2·sup)^{1−θ}·[u]_α^θ` (a bounded, `α`-Hölder function is Hölder with
  the intermediate exponent `α θ` and constant `(2B)^{1−θ} H^θ`), proved pointwise with no
  `d = 0` case split by writing `‖u p − u q‖ = ‖u p − u q‖^{1−θ}·‖u p − u q‖^θ` and bounding the two
  factors by the sup bound and the Hölder bound; plus its seminorm-functional and full-`C^{0,α θ}`-norm
  forms.
* `rpow_mul_rpow_le_absorb`, `parabolicHolderWith_interpolation_add` / `_le` / `_absorb`,
  `parabolicHolderSeminorm_interpolation_add_le` / `_absorb_le` (in the new leaf
  `ParabolicInterpolation.lean`, which localises the sole heavy dependency
  `Mathlib.Analysis.MeanInequalities` off the widely-imported `ParabolicHolder`) — the **additive /
  Young / absorbing** refinements: the weighted-AM–GM scalar inequality
  `a^{1−θ} b^θ ≤ (1−θ)κ^{−θ/(1−θ)} a + θκ b`, the additive convex-combination constant
  `(1−θ)(2B)+θH` (and the uniform `2B+H`), and the `κ`-scaled absorbing constant whose `θκ`
  coefficient on the leading seminorm is tunable to any target — the honest lower-order-term
  absorption form.
* `parabolicHolderSeminorm_interpolation_short_time_le`,
  `parabolicC0AlphaNorm_interpolation_short_time_le`,
  `parabolicC0AlphaNorm_sub_interpolation_short_time_le` (in `ParabolicInterpolation.lean`) — the
  **short-time contraction** capstone: feeding the initial-vanishing sup bound
  `parabolicSupNorm ≤ [u]_α·(√T)^α` into the multiplicative interpolation gives
  `[u]_{α θ} ≤ 2^{1−θ}·(√T)^{α (1−θ)}·[u]_α` and
  `‖u‖_{C^{0,α θ}} ≤ ((√T)^α + 2^{1−θ}(√T)^{α (1−θ)})·[u]_α` for an initial-vanishing `u` on a thin
  slab (every factor a positive power of the slab thickness `T`, so `→ 0` as `T → 0`), and — the
  form the fixed point consumes — `‖u − v‖_{C^{0,α θ}} ≤ (…)·[u − v]_α` for `u`, `v` agreeing on the
  initial slice: the Ricci–DeTurck solution map contracts in the intermediate parabolic norm on a
  sufficiently thin time-slab.

Remaining for Point 4 (future sessions): unchanged in scope — the genuine parabolic **Schauder
interior/global a-priori estimate** exhibiting the concrete Ricci–DeTurck RHS as such a
`C^{0,α}` contraction (the heat-kernel content) and its assembly from
`mulCoeffL`/`compL`/`precompL`/`constL` with these interpolation / short-time-smallness factors
(Item 3); the **general-manifold** gauge-flow lift (Item 2, heavy gauge files — the spatial-`C³`
regularity + global-`ℝ` extension of the compact-manifold flow slices); and the Item 1 tensor
time-derivative chain rule (metric leg + scalar assembly in the heavy tensor file).

Update — **the abstract Ricci–DeTurck short-time existence & uniqueness is now proved, reduced to the
single parabolic Schauder gain estimate**, extending the leaf module
`AnalyticPDE/ParabolicInterpolation.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`; pure norm/rpow analysis + the parabolic Banach fixed point,
no heat-kernel content, nothing touching the heavy files).  The previous milestone supplied the
*qualitative* short-time smallness `parabolicC0AlphaNorm_sub_interpolation_short_time_le` — for an
initial-vanishing `α`-Hölder difference on a slab of thickness `T`,
`‖u − v‖_{C^{0,α θ}} ≤ factor(T)·[u − v]_α` with
`factor(T) = (√T)^α + 2^{1−θ}(√T)^{α(1−θ)} → 0` as `T → 0`.  That "`→ 0`" is not directly usable by a
fixed point, which needs a *quantitative* contraction ratio `< 1`.  This session closes exactly that
gap and threads it through to short-time well-posedness:

* `exists_thickness_shortTimeInterpFactor_le` — the **quantitative factor smallness**: for `0 < α`,
  `θ < 1` and any target ratio `q > 0` there is a slab thickness `T₀ > 0` with `factor(T) ≤ q` for all
  `0 ≤ T ≤ T₀`.  The factor is continuous in `T` at `0` (both exponents `α`, `α(1−θ)` strictly
  positive) with value `0 < q`, so it stays below `q` on a neighbourhood of `0`
  (`Filter.Tendsto.eventually_lt_const` + `Metric.eventually_nhds_iff`).  The honest quantitative form
  of "`factor → 0`".
* `exists_thickness_parabolicC0AlphaNorm_sub_interpolation_contraction` — the **quantitative
  intermediate-norm contraction of a difference**: for any `q > 0`, a thin enough slab gives
  `‖u − v‖_{C^{0,α θ}} ≤ q·[u − v]_α` for initial-agreeing `α`-Hölder differences.
* `exists_thickness_solutionMap_contraction_of_schauder_gain` — the **reduction to the Schauder gain**:
  composing the interpolation smallness with a hypothesised parabolic Schauder gain
  `[S w₁ − S w₂]_α ≤ C·‖w₁ − w₂‖_{C^{0,α θ}}` (gain from the intermediate input norm to the top output
  seminorm — the heat-kernel content, taken as a hypothesis) turns the solution map into a *genuine
  same-exponent `q`-contraction* `‖S w₁ − S w₂‖_{C^{0,α θ}} ≤ q·‖w₁ − w₂‖_{C^{0,α θ}}` on a thin enough
  slab (choosing `T₀` so `factor(T)·C ≤ q`, via target `q/(C+1)`).  The exact input shape the parabolic
  Banach fixed point `exists_parabolicC0AlphaOn_fixedPt_of_contraction` consumes.
* `exists_shortTime_fixedPoint_of_schauder_gain` — the **short-time existence & uniqueness capstone**:
  a solution map `S` on the parabolic `C^{0,α θ}` class that self-maps, preserves the initial datum,
  has `α`-Hölder output differences, and satisfies the Schauder gain has, on a sufficiently thin
  time-slab, a *unique* fixed point `g = S g` in the class (`½`-contraction fed into the parabolic
  Banach fixed point).  Every hypothesis except the Schauder gain is a structural property of the
  DeTurck solution operator.
* `exists_shortTime_fixedPoint_ball_of_schauder_gain` — the **quantitative form with a-priori bound**:
  the same unique fixed point additionally obeys `‖g − u₀‖_{C^{0,α θ}} ≤ 2·‖S u₀ − u₀‖_{C^{0,α θ}}`
  (the `(1 − ½)⁻¹` ball-form Banach bound), controlling the solution by twice the initial residual of
  any starting guess — the estimate that keeps the DeTurck solution inside the ball on which the
  coefficient data / Schauder gain remain valid.

With this the **entire abstract side of Item 3 is now in place**: given the one parabolic Schauder gain
estimate, short-time DeTurck existence, uniqueness, and the solution bound all follow.  Remaining for
Point 4 (future sessions): the genuine parabolic **Schauder interior/global a-priori estimate**
exhibiting the concrete Ricci–DeTurck RHS as such a `C^{0,α}`-gaining operator (the heat-kernel content,
`HeatKernel1D.lean` + assembly from `mulCoeffL`/`compL`/`precompL`/`constL`) — now the *sole* missing
mathematical input on the Item 3 fixed-point route; the **general-manifold** gauge-flow lift (Item 2,
heavy gauge files — spatial-`C³` regularity + global-`ℝ` extension of the compact-manifold flow
slices); and the Item 1 tensor time-derivative chain rule (metric leg + scalar assembly).

Update — **the abstract Item-3 well-posedness family is now complete with the stability /
continuous-dependence leg** (all axiom-clean: `propext`/`Classical.choice`/`Quot.sound`; pure
parabolic-`C^{0,α}`-norm algebra + the already-proved fixed-point machinery, no heat-kernel content,
nothing touching the heavy files).  The previous milestone had existence, uniqueness and the a-priori
ball bound (reduced to the single parabolic Schauder gain).  Stability — the third Hadamard leg (the
solution depends Lipschitz-continuously on the operator) — was the remaining abstract gap, and closes
it:

* `parabolicC0AlphaNorm_fixedPt_sub_fixedPt_le_of_contraction` (in
  `AnalyticPDE/ParabolicHolder.lean`) — the **two-map Banach perturbation bound**: for two
  class-preserving parabolic `C^{0,α}` maps `T₁`, `T₂` with `T₁` a `q`-contraction (`q < 1`) and
  respective fixed points `g₁ = T₁ g₁`, `g₂ = T₂ g₂`,
  `‖g₁ − g₂‖_{C^{0,α}} ≤ (1 − q)⁻¹·‖T₁ g₂ − T₂ g₂‖_{C^{0,α}}`.  Same triangle-inequality/contraction
  computation as the one-map a-priori bound `parabolicC0AlphaNorm_fixedPt_sub_le_of_contraction`
  (`g₁ − g₂ = (T₁ g₁ − T₁ g₂) + (T₁ g₂ − T₂ g₂)`), now between two genuine fixed points, using only
  `T₁`'s contraction.
* `parabolicC0AlphaOn_fixedPt_unique_of_contraction` (same module) — **completeness-free uniqueness**:
  the `T₁ = T₂ = T` corollary (`‖g₁ − g₂‖ ≤ (1 − q)⁻¹·‖T g₂ − T g₂‖ = 0`), so any two *given* fixed
  points of a parabolic `C^{0,α}` `q`-contraction coincide on `s` — no `CompleteSpace E`, no
  Picard-constructed reference solution (the form the Ricci–DeTurck short-time uniqueness / chart
  `encode` consumes directly).
* `exists_shortTime_fixedPoint_stability_of_schauder_gain` (in
  `AnalyticPDE/ParabolicInterpolation.lean`) — the **short-time continuous dependence reduced to the
  Schauder gain**: two solution maps `S₁`, `S₂` on the parabolic `C^{0,α θ}` class with `S₁`
  self-mapping / initial-preserving / `α`-Hölder-output / Schauder-gain (⇒ `½`-contraction on a thin
  slab, via `exists_thickness_solutionMap_contraction_of_schauder_gain`) and `S₂` self-mapping have
  fixed points obeying `‖g₁ − g₂‖_{C^{0,α θ}} ≤ 2·‖S₁ g₂ − S₂ g₂‖_{C^{0,α θ}}` on every slab
  `T ≤ T₀` — the stability companion of the existence / a-priori-bound capstones, completing the
  reduced-to-Schauder-gain quartet (existence, uniqueness, a-priori bound, stability).

With this the **entire abstract side of Item 3** — existence, uniqueness, a-priori control *and*
Hadamard continuous dependence — is in place, all conditional only on the one parabolic Schauder gain
estimate.  Formulation note resolved this session: `chart.picard : IsPicardLindelof A` is a Banach
Cauchy-Lipschitz requirement (bounded / Lipschitz / time-continuous on a `C⁰` ball); the genuine
second-order Ricci–DeTurck RHS (real Levi-Civita curvature + DeTurck correction) is *unbounded* on the
`C⁰` section space, so it cannot inhabit `IsPicardLindelof` directly — `ofLipschitzBoundedContinuous`
is honestly usable only by a mild / regularised representative (or on a sub-class where the RHS is
uniformly `C⁰`-bounded/Lipschitz), and the general operator's `picard` is supplied by the parabolic
Schauder a-priori bound (Hölder-space contraction), not a `C⁰` ball.  Remaining for Point 4: the
concrete parabolic **Schauder gain / a-priori estimate** exhibiting the Ricci–DeTurck RHS as a
`C^{0,α}`-gaining operator (heat-kernel content, `HeatKernel1D.lean`) — the sole missing mathematical
input on the fixed-point route; the general-manifold gauge-flow lift (Item 2); and the Item 1 tensor
time-derivative chain rule.

Update — **Item 2 windowed → global assembly and compact-flow wiring done** (in
`GaugeReduction/GaugeFlowAssembly.lean`; both axiom-clean: `propext`/`Classical.choice`/`Quot.sound`).
The two remaining Item-2 obligations recorded above were the spatial-`C³` regularity of the flow
slices **and** the global-`ℝ` extension of the windowed `F`/`G` the adapter `gaugeFlow_of_inverse_flow`
wants (`∀ t`, whereas the compact flow lives on a window `Ioo (-ε) ε`).  The latter — plus the first
wiring of the compact-flow existence machinery into the adapter — is now proved:

* `exists_diffeomorph3GaugeFlowOn_of_windowed_inverse_flow` — the **global-`ℝ` extension**: given
  mutually-inverse, anchored slice maps `Φ`, `G` that are spatially `C³` on the window and solve the
  gauge ODE there, extend both by the identity outside `Ioo (-ε) ε` (identity is its own inverse /
  smooth / anchored) and thread the windowed ODE through `HasMFDerivWithinAt.congr_mono` to hit the
  adapter, giving `Nonempty (Diffeomorph3GaugeFlowOn X (Ioo (-ε) ε) 0)`.  Pure assembly, no analysis.
* `exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3` — the **compact-flow wiring**:
  feeds `ManifoldFlow.exists_timeDependent_flow_compact_inverse` (which needs only the `C¹` field datum
  `hX`) into the extension lemma, so that from the `C¹` gauge field alone the raw `C³` DeTurck
  gauge-flow `Diffeomorph3GaugeFlowOn X (Ioo (-ε) ε) 0` is inhabited for some `ε > 0`, **conditional
  only** on the flow slices' spatial-`C³` regularity `hslicesC3` (the `C¹ → C³` bootstrap,
  characterising the unique compact flow of `X`).  `ManifoldFlowExistence.lean` was previously imported
  by nothing; this is its first consumer.

Net effect: Item 2 is now **unconditional up to a single named analytic input** — the spatial-`C³`
regularity of the compact flow slices (the chart-by-chart `C¹ → C³` transport from the model-`E`
`SmoothDependenceManifold` core).  Remaining for Point 4 (unchanged otherwise): that spatial-`C³`
regularity (Item 2); the Item 1 tensor time-derivative chain rule; and the Item 3 parabolic Schauder
gain (heat-kernel content).

Update — **time-dependent Banach Cauchy–Lipschitz well-posedness for the chart `A`/`picard` route
is now proved** (in `AnalyticPDE/HeatKernel1D.lean`; all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`; full library green).  The pre-existing Banach-ODE bridge
`isPicardLindelof_of_bounded_lipschitz` / `bounded_lipschitz_evolution_exists_unique` covered only
**time-independent** fields, but the Ricci–DeTurck chart's `A : ℝ → …` (hence its `picard` field and
the solution operator it generates) is genuinely **time-dependent**; this session supplies the missing
time-dependent generalization on both the `0`-anchored and the general interval `[t₀, T]` (the exact
`IsPicardLindelof A (tmin := t₀) (tmax := T) ⟨t₀,…⟩ x₀ a 0 L Kpic` interval/anchor shape of the chart
`picard` field):

* `isPicardLindelof_of_bounded_lipschitz_timeDependent` / `…_timeDependent_Icc` — a globally bounded
  (`‖g t x‖ ≤ L`) + uniformly Lipschitz (`∀ t, LipschitzWith K (g t)`), time-continuous
  (`ContinuousOn (g · x) [t₀,T]`) time-dependent field `g : ℝ → E → E` is `IsPicardLindelof` with
  `a = L·(T−t₀) + 1`, `r = 0`, anchored at the left endpoint `t₀`; the last (`mul_max_le`) field is the
  one-sided interval-length computation `L·(T−t₀) ≤ a`.
* `bounded_lipschitz_evolution_exists_timeDependent` / `…_Icc` — existence of a solution `α` with
  `α t₀ = x₀` on `[t₀,T]` (via `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀`, `E`
  complete).
* `ode_solution_unique_timeDependent` / `…_Icc` — Gronwall uniqueness (`ODE_solution_unique` with
  `v := g` time-dependent), and `bounded_lipschitz_evolution_exists_unique_timeDependent` / `…_Icc`
  package existence + uniqueness in the shape the mild/regularised chart operator consumes.
* `ode_solution_dist_le_timeDependent_Icc` — continuous dependence (`dist (α t) (β t) ≤
  dist (α t₀) (β t₀)·exp(K·(t−t₀))`, via `dist_le_of_trajectories_ODE`): the third Hadamard leg, so the
  time-dependent Banach ODE route now has the full existence / uniqueness / stability triple (uniqueness
  is its `dist₀ = 0` case).

**Formulation note (re-confirmed with committed lemmas).** These discharge the honest **mild / bounded /
regularised** route to `picard`: the chart builder `TimeDependentGeometricRicciDeTurckBanachChart.ofLipschitzBoundedContinuous`
already discharges `picard` inline from ball-restricted bounded/Lipschitz/time-continuous data, and the
above give the standalone time-dependent PL + evolution existence/uniqueness/stability for such a
representative on any `[NormedAddCommGroup E] [NormedSpace ℝ E]` (`+ CompleteSpace` for existence),
instantiated at `E = ContinuousSectionSpace`.  Unchanged: for a **general** initial metric the true
second-order Ricci–DeTurck RHS is unbounded on `C⁰`, so `hgeom` (`A = intrinsicRicciDeTurckRHS` on the
positive-definite locus) cannot simultaneously hold for a `C⁰`-bounded `A`; the general operator's
`picard` still requires the parabolic Schauder a-priori bound.  Remaining for Point 4 (unchanged): the
Item 3 parabolic Schauder gain (heat-kernel content); the Item 2 spatial-`C³` flow-slice regularity;
and the Item 1 tensor time-derivative chain rule.

Update — **layer-2 `ContDiff → field-jet` bridge is now proved (`C²` manifold flow regularity from a
single joint-`ContDiff` hypothesis)** in `AnalyticPDE/FieldJetContDiff.lean` (all axiom-clean:
`propext`/`Classical.choice`/`Quot.sound`; full library green).  Extending the layer-1 `C¹` bridge
(`contMDiff_one_flow_apply_of_contDiff`), this session adds:

* `continuous_fderiv_of_contDiff_uncurry'` and `contDiff_uncurry_fderiv_of_contDiff_uncurry'` — the
  **codomain-general** (`w : ℝ → E → F`) forms of the layer-1 continuity lemma and of the "derivative
  field is itself jointly `ContDiff` one order lower" step (`uncurry (fderiv ℝ (w ·)) = fderiv ℝ
  (uncurry w) ∘L inr`, a bounded-linear post-composition).  These are exactly what lets the field-jet
  extraction **recurse**: the layer-1 derivative field `fun s ↦ fderiv ℝ (v s)` is `(E →L[ℝ] E)`-valued,
  not `E`-valued, so the original (codomain-`E`) layer-1 lemmas do not re-apply to it.
* `hasFDerivAt_fderiv_fderiv_of_contDiff_uncurry` (`hD2v`) and
  `continuous_fderiv_fderiv_of_contDiff_uncurry` (`hD2vc`) — the second-jet inputs of the tower's `C²`
  flow theorem `contMDiff_two_flow_apply_of_lipschitz_secondDeriv`, obtained by applying the primed
  layer-1 lemmas to the derivative field.
* `contMDiff_two_flow_apply_of_contDiff` and `contMDiff_two_flow_apply_of_contDiff_of_bddDerivs` — the
  `C²` bridges (the second discharges `hv`/`hvc` from a first-derivative bound, matching the layer-1
  `_of_bddDerivs` API).

**Key finding (blocks the naive layer-3/fully-bounded route).** The nested-`fderiv` representation of
the jet **caps out at `C²`**: the triple-nested continuous-linear space `E →L[ℝ] E →L[ℝ] E →L[ℝ] E` has
**no directly-synthesizable `SeminormedAddCommGroup`/`Norm`/`NNNorm` instance** in this context (verified
by probe — `fderiv ℝ (fderiv ℝ (fderiv ℝ f))` type-checks, but `‖·‖₊` on its value does not synthesize),
so a third-derivative bound `‖fderiv ℝ (fderiv ℝ (fderiv ℝ (v s))) ξ‖₊ ≤ M` cannot even be *stated*.
Consequently `hD2vlip` (Lipschitz of the second-derivative field) is taken as a hypothesis in the `C²`
bridges rather than derived from a bound.  **Layer-3 / `C³` therefore MUST use the multilinear /
`iteratedFDeriv` representation** — which is precisely why the tower's `C³` theorem
`contMDiff_three_flow_apply_of_lipschitz_thirdDeriv` consumes `D2vm : E → (E[×2]→L E)`,
`D3vm : E → (E →L (E[×2]→L E))`, `D3v : E → (E[×3]→L E)` with the `curry2`/`curryLeft` compatibility
fields `hcompat`/`hcurry` (`curry2` in `SmoothDependenceCk.lean`).

**Next target (layer-3 `C³` `ContDiff` bridge).** Produce, from a single `ContDiff ℝ n (uncurry v)`
(`n ≥ 4`), the multilinear jet objects `D2vm := iteratedFDeriv ℝ 2 (v ·)`, `D3v := iteratedFDeriv ℝ 3
(v ·)`, `D3vm := fderiv ℝ (iteratedFDeriv ℝ 2 (v ·))`, with their `HasFDerivAt`/joint-continuity/
`LipschitzWith` inputs (the multilinear norms are clean at every arity, so the third-order bound is now
statable) and the compatibility identities `hcompat : fderiv ℝ (fderiv ℝ (v s)) ξ = curry2
(iteratedFDeriv ℝ 2 (v s) ξ)` and `hcurry`, to assemble `contMDiff_three_flow_apply_of_contDiff` — the
`C^{3,1}` jet the model-manifold `C³` gauge flow consumes.

Update — **layer-3 `C³` `ContDiff → field-jet` bridge is now proved (`contMDiff_three_flow_apply_of_contDiff`)**
in `AnalyticPDE/FieldJetContDiff.lean` (all axiom-clean `propext`/`Classical.choice`/`Quot.sound`; full
library green, `scripts/point4_scan.py cheats` = `TOTAL 0`).  This completes the previously-stated "next
target": the `C^{3,1}` field jet the model-manifold `C³` gauge flow consumes is now extracted from a
*single* joint-`ContDiff ℝ n (uncurry v)` hypothesis (`3 ≤ n`).  This session adds, on the unconditional
Item-2 critical path:

* `fderiv_fderiv_eq_curry2_iteratedFDeriv_two` (`hcompat`) and `fderiv_iteratedFDeriv_two_eq_curryLeft`
  (`hcurry`) — the two multilinear compatibility identities, both **unconditional** (no smoothness
  hypothesis): the first bridges the nested-`fderiv` second derivative to `curry2 (iteratedFDeriv ℝ 2 …)`
  via `curry2_apply` + `iteratedFDeriv_two_apply`; the second is the definitional `fderiv_iteratedFDeriv`
  (the currying equiv is `ContinuousMultilinearMap.curryLeft`).
* `contDiff_uncurry_iteratedFDeriv_of_contDiff_uncurry` — the **multilinear field-jet joint-`ContDiff`
  recursion**: `(t, x) ↦ iteratedFDeriv ℝ k (v t) x` is jointly `ContDiff ℝ m` for `m + k ≤ n`, by
  induction on `k` rewriting `iteratedFDeriv ℝ (k+1)` as the left-currying isometry of
  `fderiv ℝ (iteratedFDeriv ℝ k)` (`iteratedFDeriv_succ_eq_comp_left`) and applying the codomain-general
  layer-1 derivative-field recursion `contDiff_uncurry_fderiv_of_contDiff_uncurry'` to the `k`-th jet.
  (Plumbing note: `ContDiff.comp` with `LinearIsometryEquiv.contDiff`/`ContinuousLinearEquiv.contDiff`
  of the multilinear curry equiv `whnf`-times-out or hits a Seminormed/Normed instance diamond; `fun_prop`
  discharges the post-composition robustly — the reliable incantation for composing `ContDiff` with a
  curry isometry.)
* `hasFDerivAt_fderiv_iteratedFDeriv_two_of_contDiff_uncurry` (`hD3vm`),
  `continuous_fderiv_iteratedFDeriv_two_of_contDiff_uncurry` (`hD3vmc`), and
  `continuous_iteratedFDeriv_three_of_contDiff_uncurry` (`hD3vc`) — the multilinear second/third jet
  `HasFDerivAt`/joint-continuity inputs, from `ContDiff.iteratedFDeriv_right` (single slice) and the
  recursion + the codomain-general layer-1 continuity lemma.
* `contMDiff_three_flow_apply_of_contDiff` and `contMDiff_three_flow_apply_of_contDiff_of_bddDerivs` — the
  `C³` bridges themselves, feeding all the above plus the assumed top-order Lipschitz controls
  (`hDvlip`/`hD2vclip`/`hD2vmlip`/`hD3vmlip`/`hD3vlip`, supplied directly, as expressing them as
  fourth-derivative bounds would need a further multilinear jet) into the tower's
  `contMDiff_three_flow_apply_of_lipschitz_thirdDeriv`.  The `_of_bddDerivs` form additionally discharges
  `hv`/`hvc` from a first-derivative bound.

**Formulation note (unchanged, re-confirmed).** The Item-3 chart route stays parabolic-Schauder-blocked
for a general initial metric: `hgeom` (`A = intrinsicRicciDeTurckRHS` on the positive-definite locus)
cannot hold for a `C⁰`-bounded `A`, and the empty / rank-`≤1` closures already exist directly
(`intrinsicLocalExistenceUniquenessFamily_of_isEmpty`,
`intrinsicLocalExistenceUniquenessFamily_of_finrank_model_le_one`).  So this session advanced the
**unconditional Item-2** leg instead.  **Next target.** Wire `contMDiff_three_flow_apply_of_contDiff`
(equivalently `exists_flow_contMDiff_three_gaugeData`) into the compact-manifold gauge-flow existence
(`GaugeReduction/Diffeomorph3FlowExistence.lean` via the model bridge in `ModelGaugeFlowODE.lean` and
`GaugeFlowAssembly.gaugeFlow_of_inverse_flow`), discharging Item-2's spatial-`C³` flow-slice regularity
input from a `ContDiff` field of the DeTurck gauge vector field.

Update — **model-manifold `C³` gauge-flow existence is now available behind a single `ContDiff`
hypothesis** (`AnalyticPDE/ModelManifoldGaugeFlow.lean`; both new theorems axiom-clean
`propext`/`Classical.choice`/`Quot.sound`, cheat-scan `TOTAL 0`).  This session completed the model
(chart-level) leg of the previously-stated "next target" — driving the raw `C³` DeTurck gauge flow
from a `ContDiff` field — by adding the two `_of_contDiff` entry points to the model-manifold gauge-flow
exports, mirroring the `FieldJetContDiff` jet-extraction API:

* `exists_diffeomorph3GaugeFlowOn_of_contDiff` — the model-manifold (`M = E`, `𝓘(ℝ, E)`) raw `C³`
  gauge-flow existence target `Diffeomorph3GaugeFlowOn (X := v) s t₀`, with the *entire* `C^{3,1}`
  Fréchet jet (`Dv`, `D²v` in curry/multilinear guises, `D³v`) and all its `HasFDerivAt`/joint-continuity/
  compatibility obligations discharged from a single `ContDiff ℝ n (Function.uncurry v)` hypothesis
  (`3 ≤ n`) — only the honest top-order Lipschitz controls remain, matching the tower's `C³` interface.
  A pure assembly: the `FieldJetContDiff` extraction fed into `exists_diffeomorph3GaugeFlowOn_of_field_jet`.
* `exists_flow_diffeomorph_three_hasMFDerivAt_of_contDiff` — the `ContDiff`-packaged form of the second
  documented per-chart export `exists_flow_diffeomorph_three_hasMFDerivAt` (a single flow family `Φ`
  that anchors, solves the manifold integral-curve ODE at every time, and is for every `t` a first-class
  bundled `Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E 3`).

(Plumbing note: `ModelManifoldGaugeFlow.lean` is a *classic* (non-`module`) file; it already imports the
`module` file `SmoothDependenceManifold`, so adding `import …AnalyticPDE.FieldJetContDiff` — also a
`module` file — is legal (classic files may import module files) and cycle-free (nothing imports
`ModelManifoldGaugeFlow`).)

**Honest remaining Item-2 gap (compact manifold).**  The compact-manifold gauge-flow existence
`GaugeReduction/GaugeFlowAssembly.exists_pos_diffeomorph3GaugeFlowOn_of_compact_of_flowSlicesC3` is
unconditional *up to* its `hslicesC3` hypothesis — the spatial-`C³` regularity (the `C¹ → C³` bootstrap)
of the *compact-manifold* flow slices produced by
`ManifoldFlowExistence.exists_timeDependent_flow_compact_inverse` (which itself needs only the `C¹`
field datum).  The model-manifold `C³` dependence is now fully available (incl. the `_of_contDiff`
entry points above), but transporting it to a general compact manifold `M` — expressing `Φ t` in
charts, applying the model-space `C³` dependence to the chart-local field, and patching back to
`ContMDiff I I 3 (Φ t)` — is the substantial chart-transfer work that lives in the heavy
`GaugeReduction/ModelGaugeFlowODE.lean` (~24k lines) / `GaugeReduction/Diffeomorph3FlowExistence.lean`.
**Next target.** Discharge `hslicesC3` from a `ContDiff` datum on the chart-local DeTurck gauge field
by the chart-transfer of model-manifold `C³` smooth dependence, yielding an *unconditional* compact
`exists_pos_diffeomorph3GaugeFlowOn_of_compact` (no `hslicesC3` hypothesis).

**Formulation note (unchanged, re-confirmed).** Item-3's chart route stays parabolic-Schauder-blocked
for a general initial metric: the chart field `A`'s `geometric` obligation (`A τ s =
intrinsicRicciDeTurckRHS …` on the positive-definite locus) forces `A` to be the genuine 2nd-order
Ricci-DeTurck operator, which cannot simultaneously satisfy `picard`'s `IsPicardLindelof` (a `C⁰`-Banach
Lipschitz/bounded requirement); the empty / rank-`≤1` closures already exist directly.  So this session
advanced the **unconditional Item-2** leg.

Update — **the ND heat semigroup is now a first-class bounded LINEAR operator (norm ≤ 1) on the
Banach space of bounded continuous functions `(Fin n → ℝ) →ᵇ ℝ`**, extending
`AnalyticPDE/HeatKernel1D.lean` (all axiom-clean `propext`/`Classical.choice`/`Quot.sound`,
cheat-scan `TOTAL 0`).  The committed Duhamel Schauder estimates were all stated pointwise on the
bare curried type `ℝ → (Fin n → ℝ) → ℝ`, which carries no complete-metric-space structure, so the
Banach fixed point that yields a mild Ricci–DeTurck representative had no state space to live on.
This session builds that state space's homogeneous propagator:

* `continuous_heatSemigroupND` — spatial continuity of `x ↦ (Hₜf)(x) = ∫ Kₙ(t, x−y)·f y dy` for
  `t > 0` and bounded continuous `f`.  The reflection change of variables `y ↦ x − y`
  (`integral_sub_left_eq_self`; `volume` on `Fin n → ℝ` is negation- and translation-invariant)
  rewrites `Hₜf x = ∫ z, Kₙ(t, z)·f(x − z) dz`, whose integrand is continuous in `x` per fixed `z`
  and dominated by the `x`-independent integrable envelope `z ↦ Kₙ(t, z)·C`, so
  `continuous_of_dominated` closes it.  (A constant envelope on the direct `∫ Kₙ(t, x−y)·f y` form is
  *not* integrable on `ℝⁿ` — the change of variables is what makes the domination work.)
* `heatSemigroupNDbcf` / `heatSemigroupNDbcf_apply` — `Hₜf` bundled as a `BoundedContinuousFunction`
  via `ofNormedAddCommGroup` (continuity above + the maximum-principle uniform bound `‖f‖`).
* `norm_heatSemigroupNDbcf_le` (`‖Hₜf‖ ≤ ‖f‖`), `norm_heatSemigroupNDbcf_sub_le`
  (`‖Hₜf − Hₜg‖ ≤ ‖f − g‖`, via `heatSemigroupND_sub` linearity + maximum principle), and
  `lipschitzWith_heatSemigroupNDbcf` (`LipschitzWith 1`) — the `L^∞` non-expansiveness in norm,
  difference, and Lipschitz vocabularies, the last directly consumable by the `ContractingWith` /
  Banach-fixed-point API this module already imports.
* `heatSemigroupNDbcf_add` / `heatSemigroupNDbcf_smul` / `heatSemigroupNDclm` /
  `norm_heatSemigroupNDclm_le` — additivity + real homogeneity upgrade the map to a bounded
  `ℝ`-linear operator `((Fin n → ℝ) →ᵇ ℝ) →L[ℝ] ((Fin n → ℝ) →ᵇ ℝ)` of operator norm `≤ 1`
  (`LinearMap.mkContinuous`), the operator-theoretic object the abstract parabolic Banach fixed-point
  machinery (`AnalyticPDE/Parabolic/BanachSpace.lean`) consumes.

(Plumbing note: the `→ᵇ` superscript notation does not elaborate in this `module` file
[`superscriptTerm` elaborator unavailable]; the explicit `BoundedContinuousFunction (Fin n → ℝ) ℝ`
must be written instead.)

**Formulation finding (re-confirmed, stated per directive).** The general-`M` Item-3 chart route
stays blocked: `TimeDependentGeometricRicciDeTurckBanachChart` requires `A` to be `IsPicardLindelof`
(bounded + Lipschitz on the `C⁰` section space, via `isPicardLindelof_of_bounded_lipschitz…`) *and*
(via `geometric`) to equal the genuine 2nd-order `intrinsicRicciDeTurckRHS` of some smooth metric
family.  `geometric`'s existential `∃ g` gives freedom (a "realise `s` to a smooth `g[s]`, then apply
RHS" operator can be bounded-Lipschitz for a *fixed* regularisation, so the **chart** is inhabitable),
but the genuine obstruction moves into `D`'s `realization`/`encode`: a *regularised* Banach solution
does not decode to a genuine `ChosenIntrinsicDeTurckLocalSolution`.  Closing it needs the parabolic
Schauder a-priori estimate controlling the *true* operator — i.e. the mild fixed point on the Banach
space this session's operator now lives on — not a direct Mathlib Banach ODE.  Next target: the
**Duhamel term as a `BoundedContinuousFunction`** (`x ↦ ∫_{t₀}^{t} H_{t−s}(q s) x ds` continuous +
bounded; needs the Duhamel integrand's `s`-continuity/measurability), then the short-time-contraction
Banach fixed point `Hₜu₀ + Duhamel(Q u)` giving a genuine mild solution of the ND reaction–diffusion
model.

Update — **the model (`ℝⁿ`) mild-solution map is now built as a genuine Banach-space object with its
complete short-time fixed-point datum**, extending `AnalyticPDE/HeatKernel1D.lean` (all axiom-clean
`propext`/`Classical.choice`/`Quot.sound`, cheat-scan `TOTAL 0`, full aggregate green).  The previous
milestone realised the *homogeneous* propagator `Hₜ` as a bounded linear operator on the Banach space
`(Fin n → ℝ) →ᵇ ℝ`; the committed pointwise Duhamel Schauder bounds still lived on the bare curried
type carrying no complete-metric structure.  This session bundles the *inhomogeneous* half and the full
map value on that Banach state space, completing the model mild map's self-map + contraction data:

* `heatDuhamelNDbcf` / `heatDuhamelNDbcf_apply` — the Duhamel term `x ↦ ∫_{t₀}^{t} H_{t−s}(q s)(x) ds`
  as a `BoundedContinuousFunction`, for a sup-norm-`C`-bounded source `q : ℝ → (Fin n → ℝ) →ᵇ ℝ` whose
  Duhamel integrand is per-`x` interval-integrable.  Continuity is **Lipschitz** continuity from the
  committed spatial `C¹` Schauder gain `heatSemigroupND_duhamel_spatial_lipschitz_sqrt_bound`
  (`|D(x)−D(x')| ≤ 2nC√(t−t₀)/√π·‖x−x'‖`, splitting the Duhamel integral of the difference via
  `intervalIntegral.integral_sub`); boundedness (`‖·‖ ≤ C·(t−t₀)`) is `heatSemigroupND_duhamel_sup_bound`.
* `norm_heatDuhamelNDbcf_le` / `norm_heatDuhamelNDbcf_sub_le` — the Banach-space (`norm_le`) forms of the
  Duhamel sup / sub-sup bounds: `‖heatDuhamelNDbcf q‖ ≤ C·(t−t₀)` (self-map) and
  `‖heatDuhamelNDbcf q₁ − heatDuhamelNDbcf q₂‖ ≤ D·(t−t₀)` (short-time contraction, from
  `‖q₁ s y − q₂ s y‖ ≤ D`).
* `measurable_uncurry_heatKernel1D` / `measurable_uncurry_heatKernelND` — the heat kernel is **jointly
  measurable** in `(t, x)` (Gaussian formula via `fun_prop`; finite product for the `n`-D kernel).
* `intervalIntegrable_heatSemigroupND_duhamel` — **discharges the integrability side-condition** from
  mere *continuity* of the source: measurability of the parametric Duhamel integral
  `s ↦ ∫_y Kₙ(t−s, x−y)·(q s)(y) dy` via `AEStronglyMeasurable.integral_prod_right'` (kernel factor
  jointly measurable, source factor from joint eval-continuity of `q : ℝ → BCF`), bounded a.e. by `C` on
  `(t₀, t]` (`abs_heatSemigroupND_le`, `s = t` null), hence interval-integrable.
* `heatDuhamelNDbcf_of_continuous` (+ `_apply`, `norm_…_le`, `norm_…_sub_le`) — the Duhamel BCF with
  **no free integrability hypothesis**, the form the mild fixed point (`q s = Q(u s)` continuous)
  consumes.
* `heatMildValueNDbcf` (+ `_apply`) — the **full mild-map value** `Φ(t) = H_{t−t₀}u₀ +
  ∫_{t₀}^{t} H_{t−s}(q s) ds` as a `BCF`, and its two fixed-point bounds:
  `norm_heatMildValueNDbcf_le` (self-map, `‖Φ(t)‖ ≤ ‖u₀‖ + C·(t−t₀)`, triangle + `L∞`-nonexpansive `H`)
  and `norm_heatMildValueNDbcf_sub_le` (contraction, `‖Φ(q₁)(t) − Φ(q₂)(t)‖ ≤ D·(t−t₀)` — the
  source-independent homogeneous part cancels, leaving the Duhamel contraction).  The complete Banach
  fixed-point datum (self-map ∧ short-time contraction) for the model mild ND heat flow.

**Formulation finding (re-confirmed, per directive).**  Unchanged: for a *general* initial metric the
true 2nd-order Ricci–DeTurck RHS is `C⁰`-unbounded, so the chart field `A`'s `geometric` obligation
(`A = intrinsicRicciDeTurckRHS` on the positive-definite locus) cannot coexist with a `C⁰`-bounded `A`
satisfying `picard : IsPicardLindelof A` directly; the honest route is the **mild / regularised**
representative — the Banach fixed point `Hₜu₀ + Duhamel(Q u)` on the complete state space this session's
`heatMildValueNDbcf` now inhabits — with the obstruction moving into `D`'s `realization`/`encode` (a
regularised Banach solution decoding to a genuine geometric solution needs the parabolic Schauder gain,
now available in the Duhamel `_spatial_holder`/`_spatial_lipschitz` bounds).  The trivial (empty /
rank-`≤1`) closures already exist directly and are **not** on the general-`M` critical path.

**Next target.**  Lift the fixed-time mild-map value to the **time-path space** `C([t₀, T], (Fin n → ℝ)
→ᵇ ℝ)`: the missing analytic input is **time-continuity** of the propagator/Duhamel/mild-value paths
`t ↦ heatMildValueNDbcf …` (ND heat-semigroup time-continuity), after which the committed per-time
`norm_heatMildValueNDbcf_sub_le` gives the path-space short-time contraction and the Banach fixed point
yields a genuine mild solution of the ND reaction–diffusion model — the model template for the mild
Ricci–DeTurck representative feeding `A`/`picard`.

Update — **the propagator half of that time-continuity input is now proved** (extending
`AnalyticPDE/HeatKernel1D.lean`; all axiom-clean `propext`/`Classical.choice`/`Quot.sound`, cheat-scan
`TOTAL 0`, module green).  The recorded next target asked for time-continuity of the
propagator/Duhamel/mild-value paths; this session closes the **propagator** path (the homogeneous
`H_{t−t₀}u₀` term of `heatMildValueNDbcf`):

* `continuousAt_heatSemigroupND_time` / `continuousOn_heatSemigroupND_time` — for bounded continuous
  data `f` (`|f y| ≤ C`), the propagator path `t ↦ (Hₜf)(x) = ∫ Kₙ(t, x−y)·f(y) dy` is continuous at
  every `t₁ > 0` (and `ContinuousOn (0, ∞)`).  Dominated convergence: near `t₁` (on `Ioo (t₁/2) (2t₁)`)
  the integrand is dominated by the `t`-independent integrable envelope `c^n·Kₙ(2t₁, x−y)·C`, is
  `t`-continuous for a.e. `y`, and measurable in `y`.
* `heatKernelND_le_const_mul_heatKernelND_of_mem_Icc` — the supporting **time-monotone Gaussian
  domination** on a compact time interval: for `0 < a ≤ t ≤ b`,
  `Kₙ(t, w) ≤ ((4πa)^(-1/2)·(4πb)^(1/2))^n·Kₙ(b, w)` (antitone prefactor `(4πt)^(-1/2)` × monotone
  Gaussian `exp(-|w|²/(4t))`, product over coordinates) — the `t`-independent dominating function.
* `continuousAt_heatKernelND_time` — time-continuity of the `n`-D heat kernel `t ↦ Kₙ(t, z)` on
  `(0, ∞)` (finite product of the existing `continuousOn_heatKernel1D_time`), the a.e.-`t`-continuity
  input to the dominated-convergence argument.
* `continuousAt_heatSemigroupND_shift_time` / `continuousOn_heatSemigroupND_shift_time` — the shifted
  form `t ↦ (H_{t−t₀}f)(x)` continuous at every `t₁ > t₀` (composition with `t ↦ t − t₀`), i.e. the
  time-continuity of the homogeneous term of the mild-solution map value.

**Next target.**  The remaining **Duhamel** path time-continuity `t ↦ ∫_{t₀}^{t} H_{t−s}(q s)(x) ds`
(then the mild-value path `t ↦ heatMildValueNDbcf(t)(x)` as their sum).  Subtlety to handle: the
Duhamel integrand is *singular at the upper endpoint* `s = t` (`H_{t−s}` as `t−s → 0⁺`), so plain
`continuousAt_of_dominated` does not apply directly; the honest route is the substitution `u = t − s`
turning it into `∫_0^{t−t₀} H_u(q(t−u))(x) du = ∫_ℝ 1_{[0,t−t₀]}(u)·H_u(q(t−u))(x) du`, where the
integrand is bounded by `C`, `t`-continuous for a.e. `u` (exceptional set `{0, t−t₀}` is null), and
dominated on a `t₁`-neighbourhood by `C·1_{[0, t₁+δ−t₀]}` — a dominated-convergence argument for the
substituted (non-singular-in-`u`) form.  With propagator + Duhamel time-continuity in hand, the
per-time `norm_heatMildValueNDbcf_sub_le` gives the path-space short-time contraction and the Banach
fixed point yields a genuine mild solution of the ND reaction–diffusion model.

Update — **the Duhamel + mild-value path time-continuities are now proved** (extending
`AnalyticPDE/HeatKernel1D.lean`; all axiom-clean `propext`/`Classical.choice`/`Quot.sound`, cheat-scan
`TOTAL 0`, module green).  This session closes the recorded next target — the singular Duhamel-path
time-continuity and the mild-value path as the sum — via the substitution route:

* `heatSemigroupND_duhamel_eq_comp_sub` — the `u = t − s` change of variables
  `∫_{t₀}^{t} H_{t−s}(q s)(x) ds = ∫_{0}^{t−t₀} H_u(q(t−u))(x) du`
  (`intervalIntegral.integral_comp_sub_left`), moving the diagonal singularity `s = t` to the *fixed*
  heat time `u = 0`.
* `continuous_heatSemigroupND_comp_sub_time` — for fixed `u > 0`, `t ↦ H_u(q(t−u))(x)` is continuous
  (composition of the continuous shifted source `t ↦ q(t−u)`, the bounded linear propagator
  `heatSemigroupNDclm`, and evaluation at `x`).  The a.e.-`u` time-continuity ingredient.
* `aestronglyMeasurable_heatSemigroupND_comp_sub` — `u ↦ H_u(q(t−u))(x)` is a.e.-measurable (joint
  kernel×eval measurability + `AEStronglyMeasurable.integral_prod_right'`), adapting the measurability
  pattern of `intervalIntegrable_heatSemigroupND_duhamel`.
* `continuousAt_heatSemigroupND_duhamel_time` — the **Duhamel path** `t ↦ ∫_{t₀}^{t} H_{t−s}(q s)(x) ds`
  is continuous at every `t₁ > t₀`.  After the substitution, the integral over the `t`-dependent domain
  `(0, t−t₀]` is written as a full-space integral of the indicator
  `u ↦ 1_{(0, t−t₀]}(u)·H_u(q(t−u))(x)`, and `continuousAt_of_dominated` applies: a.e.-measurable in
  `u`, dominated on a `t₁`-neighbourhood by the `t`-independent envelope `1_{(0, t₁−t₀+1]}·C`
  (`abs_heatSemigroupND_le`), continuous in `t` for a.e. `u` (indicator boundary set `{0, t₁−t₀}` null).
* `continuousAt_heatMildValue_time` (+ `continuousOn_…` on `Ioi t₀`) — the **pointwise mild-solution
  path** `t ↦ Φ(t)(x) = H_{t−t₀}(u₀)(x) + ∫_{t₀}^{t} H_{t−s}(q s)(x) ds` continuous at every `t₁ > t₀`,
  the sum of the propagator-shift and Duhamel time-continuities (`heatMildValueNDbcf_apply`).
* `continuousOn_heatSemigroupND_duhamel_time` — the `ContinuousOn (Ioi t₀)` form of the Duhamel path.

**Next target.**  Upgrade the *pointwise*-in-`x` mild-value path time-continuity to **`BCF`-norm**
(sup-over-`x`) continuity, so `t ↦ Φ(t)` is a genuine element of the path space
`C([t₀, T], (Fin n → ℝ) →ᵇ ℝ)`.  Blocker identified: sup-norm continuity of the homogeneous part
`t ↦ H_{t−t₀}u₀` needs the heat-semigroup **composition (Chapman–Kolmogorov) property**
`H_s(H_t f) = H_{s+t} f` (not yet in `HeatKernel1D.lean`; requires a Gaussian-convolution identity
`Kₙ(s,·) ⋆ Kₙ(t,·) = Kₙ(s+t,·)`) to run the `ε`-regularisation `H_t = H_{t−ε}(H_ε ·)` reducing to
strong continuity on the *bounded-uniformly-continuous* range `H_ε u₀`.  The tractable next PIECE is
therefore that convolution/semigroup identity (or, if the eventual mild fixed point can be set up with
pointwise continuity + uniform bounds instead of `BCF`-norm continuity, the abstract path-space
`ContractingWith` self-map on the sup-bounded continuous trajectories directly from the committed
per-time `norm_heatMildValueNDbcf_sub_le`).

Update — **the `BCF`-norm propagator-path time-continuity blocker is now fully resolved** (extending
`AnalyticPDE/HeatKernel1D.lean`; all axiom-clean `propext`/`Classical.choice`/`Quot.sound`, cheat-scan
`TOTAL 0`, module green).  This session closes the recorded next target — the sup-over-`x` (`BCF`-norm)
time-continuity of the homogeneous propagator path `t ↦ H_t f` — via the semigroup route flagged above,
building the missing Chapman–Kolmogorov ⇒ approximate-identity ⇒ Hölder-1/2 modulus ⇒ continuity tower:

* `heatSemigroupND_comp` — the **`n`-dimensional heat-semigroup composition law** `Hₜ(Hₛf) = H_{t+s}f`
  for bounded a.e.-measurable `f`, by Fubini (`integral_integral_swap`) from the already-committed nD
  Chapman–Kolmogorov identity `heatKernelND_chapman_kolmogorov` (the `ND` analog of the committed
  `heatSemigroup1D_comp`).  This is the previously-missing semigroup identity the `ε`-regularisation
  `Hₜ = H_{t−ε}(H_ε ·)` needs.
* `abs_heatSemigroupND_sub_self_le_of_lipschitz` — **strong continuity at time `0` on Lipschitz data**:
  for bounded `L`-Lipschitz `w`, `|Hₛw x − w x| ≤ L·n·((4πs)^{−1/2}·4s) → 0`.  Mean-zero rewrite
  `Hₛw x − w x = ∫ Kₙ(s,x−y)(w y − w x)` (using `∫Kₙ = 1`), pointwise `|w y − w x| ≤ L‖x−y‖ ≤
  L·∑ₖ|xₖ−yₖ|` (`pi_norm_le_iff_of_nonneg` + `Finset.single_le_sum`), each coordinate integral
  collapsed by the closed-form first moment `integral_abs_coord_mul_heatKernelND_eq` (via
  `integral_sub_left_eq_self`).
* `abs_heatSemigroupND_add_sub_le` / `norm_heatSemigroupNDbcf_add_sub_le` — the **pointwise and
  `BCF`-norm consecutive-time modulus** `|H_{t'+s}w x − H_{t'}w x| ≤ (n·C/√(πt'))·n·((4πs)^{−1/2}·4s)`.
  Via `heatSemigroupND_comp` (`H_{t'+s} = H_s(H_{t'} ·)`) this is the strong-continuity estimate applied
  to `v := H_{t'}w`, which is *already* Lipschitz with the committed `√t'`-parabolic-smoothing constant
  `n·C/√(πt')` (`heatSemigroupND_spatial_lipschitz_sqrt_rate_norm`) — so no Lipschitz hypothesis on `w`.
* `heatSemigroupND_timeModulus_sq` / `_eq_sqrt` / `norm_heatSemigroupNDbcf_add_sub_le_sqrt` — the
  **sharp `Hölder-1/2` `√s` form**: `(4πs)^{−1/2}·4s` squares to `4s/π` (rpow arithmetic), hence equals
  `(2/√π)·√s`, giving `‖H_{t'+s}f − H_{t'}f‖ ≤ (n·‖f‖/√(πt'))·n·(2/√π)·√s`.
* `continuousAt_heatFlowPathBcf` (+ total path `heatFlowPathBcf`, `heatFlowPathBcf_of_pos`,
  `heatSemigroupNDbcf_congr`) — the **capstone `BCF`-norm time-continuity**: for bounded continuous `f`
  and every `τ₁ > 0`, `t ↦ H_t f` is `ContinuousAt τ₁` in `(Fin n → ℝ) →ᵇ ℝ`.  Within `|t − τ₁| < τ₁/2`
  the `BCF`-distance is squeezed by `M·√|t − τ₁|` (the `√s` modulus in both `t ≷ τ₁` directions, the
  smaller-time prefactor bounded uniformly by `M = (n·‖f‖/√(π·τ₁/2))·n·(2/√π)`), and `√|t − τ₁| → 0`
  (`Real.sqrt_lt'`).  This upgrades the earlier *pointwise-in-`x`* `continuousAt_heatMildValue_time` to
  genuine sup-norm continuity.

**Next target.**  The remaining half of the mild-value path lift: **`BCF`-norm time-continuity of the
inhomogeneous Duhamel path** `t ↦ heatDuhamelNDbcf(t)` (the singular-endpoint term), after which the
mild-value path `t ↦ heatMildValueNDbcf(t) = H_{t−t₀}u₀ + Duhamel(q)` is `BCF`-norm continuous as the
sum of `continuousAt_heatFlowPathBcf` (homogeneous) and the Duhamel continuity — a genuine element of
the path space `C([t₀, T], (Fin n → ℝ) →ᵇ ℝ)`.  Then the committed per-time `norm_heatMildValueNDbcf_sub_le`
gives the path-space short-time contraction and the Banach fixed point (`ContractingWith`) yields a
genuine mild solution of the ND reaction–diffusion model — the model template for the mild Ricci–DeTurck
representative feeding the chart `A`/`picard`.

Update — **the `BCF`-norm mild-value path lift is now complete** (extending
`AnalyticPDE/HeatKernel1D.lean`; all axiom-clean `propext`/`Classical.choice`/`Quot.sound`, cheat-scan
`TOTAL 0`, module green).  This session closes the recorded next target — the singular Duhamel-path
`BCF`-norm time-continuity and the mild-value path as the sum — via the `u = t − s` substitution route
(which decouples the heat time from `t`, so the propagator `H_u` acts *nonexpansively* and the
`(t−s)^{−1/2}` diagonal singularity never appears):

* `intervalIntegrable_heatSemigroupND_comp_sub` — **interval-integrability of the substituted Duhamel
  integrand** `u ↦ H_u(q(t−u))(x)` on `[0, b]`.  After the substitution the only singular time `u = 0`
  is a null endpoint, so the bound `|H_u(q(t−u))(x)| ≤ C` (`abs_heatSemigroupND_le`) holds on all of
  `Ioc 0 b`; with a.e.-measurability (`aestronglyMeasurable_heatSemigroupND_comp_sub`) and finite
  interval measure this gives integrability, discharging the interval-split side-conditions.
* `continuousAt_intervalIntegral_normSub_shift` — **continuity of the source time-modulus integral**
  `t ↦ ∫_0^b ‖q(t−u) − q(t₁−u)‖ du` at `t₁` (where it vanishes), by interval dominated convergence
  (`continuousAt_of_dominated_interval`): the integrand is continuous, dominated by the constant `2C`
  on the finite interval, and continuous in `t` for every `u`.  This is the *non-singular* modulus
  governing the main term.
* `continuousAt_heatDuhamelPathBcf` (+ total path `heatDuhamelPathBcf`, `heatDuhamelPathBcf_of_le`) —
  the **singular-endpoint capstone**: for continuous sup-`C`-bounded `q`, the Duhamel path
  `t ↦ ∫_{t₀}^{t} H_{t−s}(q s) ds` is `ContinuousAt t₁` in `(Fin n → ℝ) →ᵇ ℝ` for every `t₁ > t₀`.
  Substituting `u = t − s` and splitting at `b = t₁ − t₀` gives (with `a = t − t₀`)
  `Duhamel(t)(x) − Duhamel(t₁)(x) = ∫_b^a H_u(q(t−u))(x) du + ∫_0^b H_u(q(t−u) − q(t₁−u))(x) du`; the
  tail is `≤ C·|t − t₁|` (nonexpansiveness, uniform in `x`) and the main term `≤ ∫_0^b ‖q(t−u) −
  q(t₁−u)‖ du = G(t)` (linearity + nonexpansiveness of `H_u`, uniform in `x`).  Taking the sup over `x`
  (`BoundedContinuousFunction.norm_le`) gives `‖Duhamel(t) − Duhamel(t₁)‖ ≤ C·|t − t₁| + G(t) → 0`, so
  the distance is squeezed to `0` (`squeeze_zero'`).
* `continuousAt_heatMildValuePathBcf` (+ total path `heatMildValuePathBcf`, `heatMildValuePathBcf_of_lt`)
  — the **mild-value path lift**: `t ↦ Φ(t) = H_{t−t₀}u₀ + Duhamel(q)` is `ContinuousAt t₁` for every
  `t₁ > t₀`, the sum of `continuousAt_heatFlowPathBcf_shift` (homogeneous) and
  `continuousAt_heatDuhamelPathBcf` (Duhamel).  `heatMildValuePathBcf_of_lt` identifies the bundled
  path with the fixed-time `heatMildValueNDbcf` for `t > t₀`.
* `continuousOn_heatDuhamelPathBcf` / `continuousOn_heatMildValuePathBcf` — the `ContinuousOn (Ioi t₀)`
  forms: the Duhamel and mild-value paths are `BCF`-norm-continuous on the open forward time ray, i.e.
  genuine elements of `C((t₀, T], (Fin n → ℝ) →ᵇ ℝ)`, the domain on which a mild trajectory lives.

**Next target.**  With the mild-value path now a `BCF`-norm-continuous element of `C((t₀, T],
(Fin n → ℝ) →ᵇ ℝ)`, build the **path-space Banach fixed point**: pick the complete metric space (e.g.
`BoundedContinuousFunction ↥(Set.Ioc t₀ T) ((Fin n → ℝ) →ᵇ ℝ)`, noting the heat semigroup on `C_b` is
*not* `C₀`, so the closed-interval left endpoint `t₀` needs care — the trajectory matches `u₀` at `t₀`
only in the mild sense), define the mild-solution self-map `Φ(u)(t) = H_{t−t₀}u₀ + ∫_{t₀}^{t}
H_{t−s}(Q(u s)) ds`, and use the committed per-time contraction `norm_heatMildValueNDbcf_sub_le`
(`‖Φ(u₁)(t) − Φ(u₂)(t)‖ ≤ Kstate·(t − t₀)·‖u₁ − u₂‖`, uniform over `t ∈ (t₀, T]`) to get a
`ContractingWith` on a short time window, whose fixed point is the model mild solution — the analytic
template for the mild Ricci–DeTurck representative feeding the chart `A`/`picard`.

Update — **the path-space Banach fixed point is now CLOSED for the model (`ℝⁿ`) mild solution**
(extending `AnalyticPDE/HeatKernel1D.lean`, all axiom-clean, `scan cheats` `TOTAL 0`, module green).
This session closes the recorded next target — the model semilinear mild-solution existence+uniqueness
via `ContractingWith` — by assembling the complete state-space datum and the self-map fixed point:

* `heatMildValuePathBcfIoc` / `heatMildValuePathBcfIcc` (+ `_apply`, `_apply_eq`, self-map norm bounds
  `norm_heatMildValuePathBcfIoc_le` / `norm_heatMildValuePathBcfIcc_le`) — the mild-value path realized
  as a genuine element of the complete Banach state spaces `↥(Set.Ioc t₀ T) →ᵇ ((Fin n → ℝ) →ᵇ ℝ)`
  (half-open, no endpoint hypotheses) and `↥(Set.Icc t₀ T) →ᵇ ((Fin n → ℝ) →ᵇ ℝ)` (closed, Lipschitz
  data), via `ofNormedAddCommGroup` from the `Ioi`/`Icc` continuity and the `‖u₀‖+C·(T−t₀)` bound.
* `dist_heatMildValuePathBcfIoc_le` / `dist_heatMildValuePathBcfIcc_le` — the short-time contraction
  datum `dist(Φ(q₁))(Φ(q₂)) ≤ D·(T−t₀)` in each state-space norm (fixed-time `norm_heatMildValueNDbcf_sub_le`,
  homogeneous term cancels; at the closed endpoint both values are `u₀`).
* `norm_heatSemigroupNDbcf_sub_self_le_of_lipschitz` (`‖H_s u₀−u₀‖ ≤ L·n·(2/√π)·√s`) +
  `continuousWithinAt_heatFlowPathBcf_zero` — **strong continuity of the `C_b` heat semigroup at the
  initial time on Lipschitz data**, the endpoint datum closing the `Icc` route.
* `continuousWithinAt_heatDuhamelPathBcf_initial`, `continuousWithinAt_heatMildValuePathBcf_initial`,
  `continuousOn_heatMildValuePathBcf_Icc`, `heatMildValuePathBcf_initial` (`Φ(t₀)=u₀`) — the mild-value
  path is `ContinuousOn` the **closed** interval on Lipschitz data.
* `heatMildSelfMap` (source via `Set.IccExtend`), `dist_heatMildSelfMap_le`
  (`dist(Φu)(Φv) ≤ Kstate·(T−t₀)·dist(u,v)`), and **`exists_unique_heatMildFixedPoint`**: for
  `L`-Lipschitz `u₀`, bounded `Kstate`-Lipschitz reaction `Q`, and `Kstate·(T−t₀) < 1`, the mild
  self-map has a **unique fixed point** in `↥(Set.Icc t₀ T) →ᵇ ((Fin n → ℝ) →ᵇ ℝ)` — the genuine model
  mild solution of `u_t = Δu + Q(u)`, `u(t₀)=u₀`, via `banach_fixedPoint_exists_unique`.

**Next target.**  Transport the model mild fixed point to the chart. Two honest sub-steps:
  (a) generalise the model state space `(Fin n → ℝ) →ᵇ ℝ` to the manifold bundle state space
      `ContinuousSectionSpace … et Kc …` (the chart's `A` domain), lifting `heatMildSelfMap` /
      `exists_unique_heatMildFixedPoint` to sections; and
  (b) identify the mild representative with the geometric Ricci–DeTurck RHS (`chart.geometric`), where
      the reaction `Q` is the lower-order (non-Laplacian) part — the point at which the *bounded
      Lipschitz `Q`* hypothesis meets the real operator (the remaining Schauder/higher-regularity gap:
      the genuine Ricci–DeTurck reaction is bounded-Lipschitz only relative to a higher-regularity
      norm, not `C⁰`). The model template now makes precise exactly what must be supplied to inhabit
      `A`/`picard` through the mild route.

Update — **the model mild solution is now fully *well-posed* (existence + uniqueness + continuous
dependence) with an explicit Duhamel form** (extending `AnalyticPDE/HeatKernel1D.lean`, all axiom-clean
`propext`/`Classical.choice`/`Quot.sound`, `scan cheats` `TOTAL 0`, module green).  This session adds
the two remaining pillars of well-posedness beyond `exists_unique_heatMildFixedPoint`:

* `dist_heatMildFixedPoint_le` — **continuous (Lipschitz) dependence on the initial datum**: two
  mild-solution fixed points `z, w` for initial data `u₀, v₀` (common bounded `Kstate`-Lipschitz
  reaction `Q`, short window `Kstate·(T − t₀) < 1`) satisfy
  `dist z w ≤ ‖u₀ − v₀‖ / (1 − Kstate·(T − t₀))` in `↥(Set.Icc t₀ T) →ᵇ ((Fin n → ℝ) →ᵇ ℝ)`.  The
  triangle estimate `dist z w = dist (Φ_{u₀} z) (Φ_{v₀} w) ≤ dist (Φ_{u₀} z) (Φ_{u₀} w) +
  dist (Φ_{u₀} w) (Φ_{v₀} w)` combines the short-time contraction `dist_heatMildSelfMap_le`
  (`≤ Kstate·(T − t₀)·dist z w`) with the new **initial-datum `1`-Lipschitz** self-map bound
  `dist_heatMildSelfMap_initial_le` (`≤ ‖u₀ − v₀‖`), which lifts the fixed-time homogeneous-propagator
  non-expansiveness `norm_heatMildValueNDbcf_sub_initial_le` (Duhamel cancels; `H_{t−t₀}u₀ − H_{t−t₀}v₀`
  bounded by `norm_heatSemigroupNDbcf_sub_le`) through `dist_heatMildValuePathBcfIcc_initial_le` to the
  closed-interval path space.  The third pillar of well-posedness — stability under perturbation of the
  data — the analytic template for the corresponding stability of the mild Ricci–DeTurck representative.
* `heatMildFixedPoint_apply` — **the fixed point genuinely solves the Duhamel integral equation**:
  every interior value of a fixed point `z` is the pointwise mild-solution formula
  `z(t)(x) = H_{t−t₀}(u₀)(x) + ∫_{t₀}^{t} H_{t−s}(Q(z(projIcc s)))(x) ds`, obtained by unfolding the
  fixed-point identity through `heatMildValuePathBcfIcc_apply` / `heatMildValuePathBcf_of_lt` /
  `heatMildValueNDbcf_apply`.  This upgrades the abstract Banach fixed point to a genuine mild solution
  of `u_t = Δu + Q(u)`, `u(t₀) = u₀` in concrete integral-equation form — exactly what a downstream
  decode of the mild representative into a genuine local solution (`realization`) consumes.

**Next target.**  The model semilinear mild solution is now a fully-specified well-posed template
(existence, uniqueness, Lipschitz dependence, explicit Duhamel form).  The transport step (a) —
generalising the model value space `(Fin n → ℝ) →ᵇ ℝ` to the manifold-bundle state space
`ContinuousSectionSpace … et Kc …` — remains blocked on an **intrinsic parabolic (heat) semigroup on
the compact manifold** `M`; the `ℝⁿ` heat propagator `heatSemigroupND` is coordinate-specific and does
not transport directly.  Two honest sub-routes: (i) build the intrinsic bundle heat semigroup (large);
or (ii) route the section-space picard through the ODE foundation
`isPicardLindelof_of_bounded_lipschitz_timeDependent_Icc` with a genuinely bounded-Lipschitz
*regularised* representative `A` (the mild/Yosida route), where the well-posedness template above pins
down exactly the boundedness + Lipschitz + time-continuity estimates that must be supplied.

Update — **the section-space route (ii) `picard`/evolution transport is now assembled from a
complete coordinate→section handoff suite** (extending `VectorBundle/ContinuousSection.lean` and a
new dedicated module `AnalyticPDE/SectionSpacePicard.lean`; all axiom-clean
`propext`/`Classical.choice`/`Quot.sound`, `scan cheats` `TOTAL 0`, full `lake build` green). The
model `ℝⁿ` mild solution is fully well-posed but its `ℝⁿ` heat propagator is coordinate-specific;
this session builds the missing bridges that let the *section-space* `A`/`picard` be supplied
directly through the already-proved Banach ODE foundation
`isPicardLindelof_of_bounded_lipschitz_timeDependent_Icc` (route (ii)), for a general
finite-rank bundle:

* `norm_le_of_forall_coord_norm_le` — **boundedness handoff**: a uniform sup-bound `C` on every
  compact trivialization readout of a section gives `‖s‖ ≤ C` in the transported finite-cover norm
  (the `t = 0` companion of `dist_le_of_forall_coord_dist_le`). Supplies the foundation's `hbound`.
* `lipschitzWith_of_forall_coord_dist_le` — **global-Lipschitz handoff**: coordinatewise
  `LipschitzWith`-style readout estimates over *all* sections give `LipschitzWith K A`
  (`stateSet = univ` companion of `lipschitzOnWith_of_forall_coord_dist_le`). Supplies `hlip`.
* `continuousOn_of_forall_coord_continuousOn` — **time-continuity handoff**: continuity of each
  readout `x ↦ (f x)ᵢ` into `C(Kc i, F)` gives continuity of `x ↦ f x` in the section norm (the
  transport `equivCompatibleCoordFamilySubmodule` is a definitional isometry into `∀ i, C(Kc i, F)`,
  composed with the submodule-coercion isometry; `IsInducing.continuousOn_iff` + `continuousOn_pi`
  over the finite trivialization index). Supplies `hcont`.
* `isPicardLindelof_continuousSectionSpace_of_forall_coord` (new module) — **route (ii) `picard`-field
  constructor**: assembles the three handoffs with the Banach ODE foundation to produce
  `IsPicardLindelof A` in exactly the interval/anchor/constant shape
  (`⟨t₀,_⟩ x0 (L·(T−t₀)₊+1) 0 L K`) of `TimeDependentGeometricRicciDeTurckBanachChart.picard`, from
  purely coordinatewise boundedness / Lipschitz / continuity data.
* `sectionSpace_evolution_exists_unique_of_forall_coord` (new module) — **transport step (a)**: the
  same coordinate data yields a *unique* `[t₀, T]`-evolution `α` in the complete section space with
  `α t₀ = x0`, `α'(t) = A t (α t)` (via `bounded_lipschitz_evolution_exists_unique_timeDependent_Icc`).
  Lifts the model `ℝⁿ` mild-solution existence–uniqueness to the manifold-bundle section space.

**Fractional progress on `{A, picard, realization, encode}`.** `picard` is now *constructible* from
coordinatewise analytic control of `A` (route (ii)), and the section-space evolution it produces is
in hand. The remaining gap for `A`/`picard` is the *genuine* mild/regularised operator: exhibiting a
concrete time-dependent `A` on the section space whose trivialization readouts are actually bounded +
Lipschitz + time-continuous (the boundedness being where the C⁰-unbounded second-order Ricci–DeTurck
operator meets the mild/Yosida regularisation) — at which point these constructors close `picard`.

**Next target.** Construct a concrete bounded-Lipschitz section-space representative `A` (mild/Yosida
form) and prove the three coordinatewise estimates (`hbound`/`hlip`/`hcont`) it must satisfy to feed
`isPicardLindelof_continuousSectionSpace_of_forall_coord`; alternatively begin the `realization`
decode (`BanachEvolutionLocalSolutionIn A → ChosenIntrinsicDeTurckLocalSolution`) that the
section-space evolution now makes available.

Update — **the honest *ball-local* `picard` route for the section space is now complete** (extending
`AnalyticPDE/SectionSpacePicard.lean`; all axiom-clean `propext`/`Classical.choice`/`Quot.sound`,
`scan cheats` `TOTAL 0`, bare `lake build` green — 2911 jobs). The prior section-space picard
constructor `isPicardLindelof_continuousSectionSpace_of_forall_coord` demanded the *global*
boundedness the `C⁰`-unbounded second-order Ricci–DeTurck operator cannot supply; this session builds
the honest ball-local route producing the chart's **exact** `a` radius (matching its `lipschitz`-on-
locus field), via the already-committed ball-local Banach ODE foundations
(`isPicardLindelof_of_boundedOn_lipschitzOn_superset_timeDependent_Icc`,
`isPicardLindelof_of_lipschitzOn_centerBound_closedBall_timeDependent_Icc`,
`exists_forwardTime_mul_sub_le`):

* `isPicardLindelof_continuousSectionSpace_of_forall_coord_superset` — coordinatewise readout
  boundedness ≤ `L` + `K`-Lipschitz-in-section on a set `S ⊇ closedBall x0 a` (e.g. the positive-
  definite locus) + time-continuity + `L·(T−t₀) ≤ a` ⟹ `IsPicardLindelof A ⟨t₀,_⟩ x0 a 0 L K` — the
  chart `picard` shape with radius `a` (not the global `L·(T−t₀)₊+1`).
* `isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound` — sharpest honest form: the
  only norm datum is the coordinatewise readout size of `A t` at the **fixed centre** `x0` (= `g₀`);
  the ball bound `Mc + K·a` is *derived* from ball-Lipschitz. Output `… x0 a 0 (Mc + K·a) K`.
* `exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound` — capstone:
  from *forward*-time-uniform (on `Ici t₀`) centre-bound data there **exists** a forward endpoint
  `T > t₀` carrying the full `picard` (endpoint from `exists_forwardTime_mul_sub_le`, auto-satisfying
  `(Mc + K·a)·(T−t₀) ≤ a`) — supplying *both* `T`-dependent chart fields (`hT`, `picard`) at once,
  the chart's `lipschitz`/`geometric` fields being `T`-independent.
* `sectionSpace_evolution_exists_of_forall_coord_centerBound` — honest ball-local companion of
  `sectionSpace_evolution_exists_unique_of_forall_coord`: the centre-bound data yields the actual
  `[t₀,T]`-evolution curve `α` (`α t₀ = x0`, `α'(t) = A t (α t)`) via
  `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀` — the raw material a `realization`
  decode consumes, now from honest (not globally bounded) input.

**Fractional progress on `{A, picard, realization, encode}`.** `picard` is now constructible from the
*honest* ball-local / centre-bound coordinatewise analytic control — radius `a`, ball-Lipschitz `K`,
centre size `Mc = ‖(A t g₀)ᵢ x‖` — the exact shape the real `C⁰`-unbounded operator can supply once a
parabolic Schauder estimate provides `K` and `Mc`. The remaining `A`/`picard` gap is purely the
*analytic* production of those two coordinatewise estimates for a concrete mild/regularised
representative; the picard plumbing above then closes `picard` and hands over the evolution curve.

**Next target.** Either (i) the parabolic Schauder ball-Lipschitz `K` + centre-size `Mc` estimates
(`hlip`/`hcenter`) for a concrete mild/regularised section-space representative `A` — the sole
remaining analytic input the picard route now needs; or (ii) the a-posteriori ball-membership
`curve t ∈ closedBall x0 a` on `[t₀,T]`, upgrading `sectionSpace_evolution_exists_of_forall_coord_centerBound`
to a full `BanachEvolutionLocalSolutionIn A locus t₀ x0` (the direct `realization` input) given
`closedBall x0 a ⊆ locus`.

Update — **the a-posteriori ball-membership route (ii) is now closed**: the honest ball-local
centre-bound Picard data now yields a genuine state-constrained `BanachEvolutionLocalSolutionIn` on
the *full* window (extending `AnalyticPDE/SectionSpacePicard.lean`, which now `public import`s
`AnalyticPDE` so it can produce the `BanachEvolutionLocalSolutionIn` carrier; all axiom-clean
`propext`/`Classical.choice`/`Quot.sound`, `scan cheats` `TOTAL 0`, bare `lake build` green — 2911
jobs, and the module itself green — 2960 jobs):

* `IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt_mem_closedBall` — **the missing
  single-solution Picard–Lindelöf state-membership readout.**  Mathlib's differential
  `exists_eq_forall_mem_Icc_hasDerivWithinAt` produces the local integral curve `α` but *discards*
  the a-priori bound `α t ∈ closedBall x₀ a` (for all `t ∈ [tmin,tmax]`) that its own proof
  establishes via `ODE.FunSpace.compProj_mem_closedBall`.  This variant mirrors that proof and
  *retains* the ball-membership conjunct — the exact datum that upgrades a raw evolution curve to a
  state-constrained solution.
* `IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset` — **the closed-ball
  a-posteriori bridge.**  From `IsPicardLindelof F ⟨t₀,_⟩ u₀ a 0 L K` and the containment
  `closedBall u₀ a ⊆ stateSet`, the forward Picard solution — which stays in `closedBall u₀ a` on the
  *whole* `[t₀,T]` — is a genuine `BanachEvolutionLocalSolutionIn F stateSet t₀ u₀` on the full
  window, with **no** interval shrinking and **no** openness hypothesis (contrast
  `exists_banachEvolutionLocalSolutionIn_of_mem_isOpen`, which shrinks the terminal time to keep the
  curve inside an *open* set).  Since a `TimeDependentGeometricRicciDeTurckBanachChart` already
  supplies `hT` and `picard`, this bridge takes `chart.hT`/`chart.picard` plus the ball containment
  straight to the `realization` input shape.
* `sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound` — **route (ii)
  capstone.**  From the honest centre-bound ball-local coordinatewise control (`K`-Lipschitz-in-
  section on `closedBall x0 a`, time-continuity there, centre readout bound `‖(A t x0)ᵢ x‖ ≤ Mc`,
  `(Mc + K·a)·(T − t₀) ≤ a`) *plus* the a-priori containment `closedBall x0 a ⊆ locus`, the
  section-space operator `A` admits a genuine `BanachEvolutionLocalSolutionIn A locus t₀ x0` on
  `[t₀,T]` — assembling `isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound` with the
  closed-ball bridge.  This is precisely the state-constrained Banach solution a downstream
  `realization` decode consumes, now from honest (not globally bounded) analytic input.

**Fractional progress on `{A, picard, realization, encode}`.**  The `realization` *input* — a genuine
`BanachEvolutionLocalSolutionIn chart.A (positiveDefiniteLocus …) …` on the full window — is now
CONSTRUCTIBLE from `chart.picard` (equivalently, from the honest ball-local centre-bound analytic
data) plus the single a-priori containment `closedBall (initial section) a ⊆ positiveDefiniteLocus`.
The `picard` plumbing (both global-window and forward-endpoint forms) and this closed-ball
solution-existence bridge are complete; the residual `A`/`picard` gap is purely the *analytic*
production of the two coordinatewise size estimates (ball-Lipschitz `K`, centre-size `Mc`) for a
concrete mild/regularised representative — the parabolic Schauder input — together with the geometric
positivity fact `closedBall (g₀ section) a ⊆ positiveDefiniteLocus`.

**Next target.** Either (i) the parabolic Schauder ball-Lipschitz `K` + centre-size `Mc` estimates
(`hlip`/`hcenter`) for a concrete mild/regularised section-space representative `A` — the sole
remaining analytic input the picard/solution route now needs; or (ii) the geometric a-priori
positivity lemma `closedBall (g₀ section) a ⊆ positiveDefiniteLocus` (a short-time metric-cone
containment) that discharges the last hypothesis of the closed-ball bridge; or (iii) the
`realization` decode `RicciDeTurckSmoothRealizationData → ChosenIntrinsicDeTurckLocalSolution` that
consumes the `BanachEvolutionLocalSolutionIn` now constructible.

Update — **the geometric a-priori positivity containment (next-target (ii)) is now closed**, as a
FOUNDATIONAL, root-reachable lemma (in `VectorBundle/RiemannianSection.lean`, beside its open-ball
sibling `exists_dist_lt_subset_positiveDefiniteLocus`; bare `lake build` green — 2911 jobs; axiom-
clean `propext`/`Classical.choice`/`Quot.sound`; `scan cheats` `TOTAL 0`):

* `exists_pos_closedBall_subset_positiveDefiniteLocus` — **closed-ball companion of the open-ball
  neighbourhood lemma.**  From a section `s` lying in the *open* positive-definite locus
  (`isOpen_setOf_forall_pos` + `Metric.isOpen_iff`), extract a positive `ℝ≥0` radius `a` (take
  `(ε/2).toNNReal`) whose **entire** `Metric.closedBall s (a : ℝ)` stays inside
  `positiveDefiniteLocus` (via `Metric.closedBall_subset_ball`).  This is *exactly* the
  `hsub : Metric.closedBall x₀ (a : ℝ) ⊆ locus` hypothesis shape consumed by the closed-ball
  Banach-solution bridge `IsPicardLindelof.exists_banachEvolutionLocalSolutionIn_of_closedBall_subset`
  and by the route (ii) capstones `sectionSpace_banachEvolutionLocalSolutionIn_exists_of_forall_coord_centerBound`
  / `exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound`.
* `Bundle.ContinuousRiemannianMetric.exists_pos_closedBall_toSection_subset_positiveDefiniteLocus`
  — **metric specialization.**  For a genuine continuous Riemannian metric `g`, the section
  `⟨g.toSection, g.continuous_toSection⟩` (in the locus via
  `mem_positiveDefiniteLocus_of_continuousRiemannianMetric`) has such a positive Picard radius `a` —
  discharging the last containment obligation of route (ii)'s realization-input construction for the
  **initial metric** of a Ricci–DeTurck IVP.  Keeping this at the foundational (root-reachable) layer
  means any future BilinearFormBundle-concrete chart/`D` constructor can consume it directly.

**Fractional progress on `{A, picard, realization, encode}`.**  The `realization` *input* is now
CONSTRUCTIBLE end-to-end from honest analytic data with the geometric containment **discharged, not
assumed**: `picard` from ball-local centre-bound coordinatewise control (`K`, `Mc`), forward endpoint
`T` auto-chosen, closed-ball bridge to `BanachEvolutionLocalSolutionIn`, and now `hsub` supplied by
the positivity margin of `g₀`.  The sole remaining `A`/`picard` gap is the *analytic* production of
the two coordinatewise size estimates (ball-Lipschitz `K`, centre-size `Mc`) for a concrete
mild/regularised representative `A` — the parabolic Schauder input (GAP 2).

**Formulation note (per directive).**  `picard : IsPicardLindelof A` is inhabited via the honest
ball-local Cauchy–Lipschitz route: the only analytic data required about the `C⁰`-unbounded
Ricci–DeTurck operator is its coordinatewise `K`-Lipschitz-in-section control on `closedBall g₀ a`
and its centre readout size `Mc = ‖(A t g₀)ᵢ x‖` — i.e. a *parabolic Schauder a-priori bound* is what
actually supplies `picard`, NOT a globally bounded mild formulation.  The geometric/topological parts
(positivity containment `hsub`, forward-endpoint `T`, closed-ball→solution bridge) are all now
closed; only the Schauder `K`/`Mc` estimates remain for `A`/`picard`.

**Blocker recorded for next session — BilinearFormBundle-concrete instantiation of the abstract
route (ii) capstones triggers a `whnf` blow-up.**  Instantiating
`exists_forwardTime_isPicardLindelof_continuousSectionSpace_of_forall_coord_centerBound` +
`exists_banachEvolutionLocalSolutionIn_of_closedBall_subset` at `V := BilinearFormBundle`,
`F := (F →L[ℝ] F →L[ℝ] ℝ)`, centre `⟨g.toSection, _⟩` (to fold the positivity containment into a
`∃ T, BanachEvolutionLocalSolutionIn A (positiveDefiniteLocus) t₀ g` capstone) times out at `whnf`
even at `maxHeartbeats 1600000` — a genuine defeq blow-up in the `equivCompatibleCoordFamilySubmodule`
readout / section-space `CompleteSpace` unification, NOT a heartbeat shortage.  The abstract capstones
compile only because they stay generic over `V`.  Next session: pin the section-space instances with
explicit `letI`/`haveI` (or `set … with` the centre section and `CompleteSpace` instance) before
applying the bridges, or state the concrete capstone with the readout maps abstracted behind a local
`let`, to avoid re-synthesising the BilinearFormBundle transported-instance diamond during
elaboration.

**Next target.**  Either (i) the parabolic Schauder ball-Lipschitz `K` + centre-size `Mc` estimates
(`hlip`/`hcenter`) for a concrete mild/regularised section-space representative `A` — the sole
remaining analytic input; or (ii) the instance-pinned BilinearFormBundle-concrete route (ii)
realization-input capstone (folding in `exists_pos_closedBall_toSection_subset_positiveDefiniteLocus`)
once the `whnf` blow-up above is tamed; or (iii) the `realization` decode
`RicciDeTurckSmoothRealizationData → ChosenIntrinsicDeTurckLocalSolution`.

---

## Milestone (2026-07-05) — model mild-solution a-priori estimate suite + local-existence-with-containment capstone (GAP 2 analytic core)

Six additive, fully-proved, axiom-clean (`propext`/`Classical.choice`/`Quot.sound`) theorems appended
to `AnalyticPDE/HeatKernel1D.lean`, completing the model semilinear reaction–diffusion
(`u_t = Δu + Q(u)`) well-posedness theory with the a-priori control the chart `picard`/closed-ball
route consumes. Bare `lake build` green (2911 jobs); `scan cheats` `TOTAL 0`.

* `norm_heatMildFixedPoint_le` — **a-priori sup bound** (fourth well-posedness pillar): any fixed point
  `z` of the mild-solution self-map obeys `‖z‖ ≤ ‖u₀‖ + CQ·(T − t₀)`. The `C⁰` centre-size estimate.
* `norm_heatMildValueNDbcf_sub_initial_le_of_lipschitz` — **fixed-time deviation from the initial
  datum** (parabolic modulus of continuity): `‖Φ(t) − u₀‖ ≤ L·n·(2/√π·√(t − t₀)) + C·(t − t₀)`, via
  the decomposition `Φ(t) − u₀ = (H_{t−t₀}u₀ − u₀) + Duhamel` (heat-semigroup Lipschitz modulus +
  Duhamel bound).
* `dist_heatMildFixedPoint_const_le` — **path-space containment near the initial datum**: the whole
  fixed-point trajectory satisfies `dist z (const u₀) ≤ L·n·(2/√π·√(T − t₀)) + CQ·(T − t₀)`. Pointwise
  from the previous lemma + the `t₀`-endpoint value `u₀`; `→ 0` as `T → t₀⁺`.
* `exists_forwardTime_sqrt_add_mul_sub_le` — **√-shape window chooser** (analog of
  `exists_forwardTime_mul_sub_le`): for `M₁,M₂ ≥ 0`, `a > 0` there is `T > t₀` with
  `M₁·√(T − t₀) + M₂·(T − t₀) ≤ a`.
* `exists_forwardTime_sqrt_add_mul_sub_le_and_lt_one` — **combined containment + contraction window**:
  a `T > t₀` meeting both `M₁·√(T − t₀) + M₂·(T − t₀) ≤ a` and `K·(T − t₀) < 1`, by shrinking to
  `min (T₁ − t₀) (1/(K + 1))` (containment monotone in window length).
* `exists_heatMildFixedPoint_dist_const_le` — **CAPSTONE: model local existence with a-priori ball
  containment.** For any target radius `a > 0` there is a forward window `T > t₀` carrying a mild
  solution `z` (fixed point) with `dist z (const u₀) ≤ a` — a solution that never leaves the prescribed
  ball. Assembles the combined chooser (with `M₁ = L·n·(2/√π)`, `M₂ = CQ`),
  `exists_unique_heatMildFixedPoint`, and `dist_heatMildFixedPoint_const_le`.

**Fractional progress on `{A, picard, realization, encode}`.** This is the genuine model template for
the mild Ricci–DeTurck representative feeding `A`/`picard`: the honest analytic well-posedness data
(existence, uniqueness, continuous dependence, a-priori sup/deviation/containment) is now complete on
the model space `↥(Icc t₀ T) →ᵇ ((Fin n → ℝ) →ᵇ ℝ)`, with the per-datum window chosen so the solution
stays in the target ball. The remaining `A`/`picard` gap is the transfer of this model template to the
section space of `BilinearFormBundle` (the genuine chart state space) and the identification of the
mild representative with `intrinsicRicciDeTurckRHS` on the positive-definite locus (the `geometric`
field).

**Next target.** Either (i) lift the model containment capstone to the section-space representative
(matching `dist_heatMildFixedPoint_const_le`'s output to the closed-ball `hsub` already discharged by
`exists_pos_closedBall_toSection_subset_positiveDefiniteLocus`); or (ii) the `realization` decode
`RicciDeTurckSmoothRealizationData → ChosenIntrinsicDeTurckLocalSolution`; or (iii) further parabolic
Schauder gain (spatial second-derivative Hölder control) toward the `geometric` identification.
