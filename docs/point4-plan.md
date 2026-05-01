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

**Module location.** Extend
`Geometry/Manifold/RicciFlow/GaugeReduction/Diffeomorph3FlowExistence.lean`
with a constructor for the general (non-Levi-Civita-background) case.

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
