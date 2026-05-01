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
scalar data directly. The bundled
non-identity gauge-flow API now has proof-bearing scalar-to-tensor wrappers, so
solving this single dynamic scalar identity automatically supplies the
`HasTimeDerivativeOn` package required by the gauge-reduction theorem routes.
The first proof-bearing piece of the dynamic calculation is now in place:
`hasDerivAt_bilinearForm_apply_apply` differentiates
`B(t) (u(t)) (v(t))`, and
`hasDerivAt_bilinearForm_linear_apply_apply[_of_comp_deriv]` specializes this
to the local-coordinate form `B(t) (A(t) u) (A(t) v)` of a gauge-pulled metric
component, including the expected vector-slot/Lie-derivative contributions.
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
also have direct model-derivative-to-time-derivative wrappers. Coordinate-level
derivative data still lifts through the fixed-IVP, theorem-family, and
raw-existence gauge-flow APIs, so a future chart calculation can feed the
point-4 theorem routes without first repackaging it as a tensor derivative.
The model algebra now also includes the metric-component half of this remaining
primitive: `hasDerivAt_bilinearFormField_along_curve` differentiates a bilinear
form field `Bfield(τ, y(τ))`, and
`hasDerivAt_bilinearFormField_linear_apply_apply_along_curve` combines that with
the variational tangent-map equation to differentiate
`Bfield(τ, y(τ)) (A(τ)u) (A(τ)v)`. This is also bundled as
`CoordinatePullbackMetricFieldDerivativeOn`, which promotes to
`CoordinatePullbackMetricModelDerivativeOn`, the geometric scalar derivative, and
tensor `HasTimeDerivativeOn`, including raw-gauge-flow wrappers. The variational
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
`of_hasMFDerivWithinAt` / `of_hasMFDerivAt` constructors, named-derivative-family
adapters, geometric-to-raw adapters, raw-flow derivative/local-at-time extractors,
and raw-flow time-set restriction, so an ODE construction that already returns
pointwise manifold derivative data or a named geometric gauge-flow bundle can be
connected directly to `Diffeomorph3GaugeFlowOn` and
`IntrinsicDeTurckGaugeFlowExistenceFamily`.
The first Banach-model ODE bridge for this item is now proof-bearing in
`GaugeReduction.ModelGaugeFlowODE`: mathlib's time-dependent Picard-Lindelöf
theorem is packaged as `LocalFlowSolution` and `LipschitzLocalFlowSolution`,
including the ODE derivative on the closed time interval, initialization on a
closed ball of initial data, and Lipschitz dependence on initial data.
It also packages the continuous space-time partial-flow form as
`ContinuousLocalFlowSolution`, so the chart-level output now includes the
continuity needed before gluing local solutions.  The same module now also
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
base and tangent ODEs from any packaged `LocalFlowSolution` of that product
system, providing the intended route from Picard-Lindelöf on a product Banach
space to variational tangent data. A continuous local flow for this product
system, initialized on `(x, 1)` and restricted to a base ball contained in the
product Picard ball, now extracts directly to `VariationalLocalFlowSolution`.
Consequently, a Picard-Lindelöf hypothesis for the product variational system
also constructs `VariationalLocalFlowSolution` directly after the same base-ball
restriction, with a specialized constructor that discharges this restriction
automatically when the chosen base radius is no larger than the product Picard
radius. The ODE package now also supplies ordinary interior time
derivatives for both the base flow `y(t)` and tangent map `A(t)`, and
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
it to tangent vectors.  This connects the Banach Picard metric curve directly to
the weaker time-only dynamic pullback interface.
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
first.

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
the heavy PDE realization file unchanged and adds only raw-gauge endpoint
projections on top of the already-proved global and interval chart-closure data.
