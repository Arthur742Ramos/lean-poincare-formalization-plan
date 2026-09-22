# Point 4: Ricci-flow local existence and uniqueness

Point 4 aims to prove short-time existence and uniqueness of Ricci flow for
general initial data on a compact smooth manifold. It is the first open
dependency in the [Poincaré roadmap](../roadmap.md).

This file records the current boundary and next work. The long chronological
development record has moved to
[`../history/point4-development-log.md`](../history/point4-development-log.md).

## Definition of done

The executable authority is
[`curvature/scripts/point4_audit.sh`](../../curvature/scripts/point4_audit.sh).
Point 4 is closed only when a full invocation, without `--no-build`, prints
`VERDICT: POINT 4 CLOSED` and exits successfully.

The audit requires:

1. a library free of `sorry`, `admit`, `sorryAx`, `axiom`, `opaque`,
   `native_decide`, and `decide!` after comments and strings are removed;
2. a successful `lake build`;
3. an unconditional theorem constructing
   `IntrinsicLocalExistenceUniquenessFamily` on a general compact manifold;
4. an axiom set contained in `propext`, `Classical.choice`, and `Quot.sound`;
5. an elaborated theorem type with no empty, subsingleton, rank, preconstructed
   chart, or preconstructed closure-data restriction.

The canonical declaration is named by
[`curvature/scripts/point4_target.txt`](../../curvature/scripts/point4_target.txt),
currently `intrinsicLocalExistenceUniquenessFamily_pointFour`.

## Current verdict

The fast audit run on 2026-09-11 passed the forbidden-term scan but did not find
the canonical target. The build gate was intentionally skipped in that fast
run. Gates 3–5 therefore failed and the verdict remained `POINT 4 OPEN`.

See [Current formalization status](../status.md) for the repository-wide dashboard.

The preceding supporting PDE milestone is the genuine Ricci--DeTurck
Hölder-seminorm difference estimate in
`GenuineRicciDeTurckHolderDifference.lean`. It combines the compact-domain
derivative bound for the actual Ricci--DeTurck fiber map with the explicit
2-jet extraction bound, and specializes the range hypotheses to the Euclidean
small-data ball. The same file now proves the pointwise/supremum component of
the difference bound, the sharp Hölder certificate using the extracted jet of
`s - t`, and a linear Hölder-seminorm bound in `‖s - t‖`, including its
canonical Euclidean-section specialization. It also proves the
`IsHolderNorm`-to-`HolderBCF` continuity/boundedness bridge, derives a genuine
compact-fiber output bound, and packages the actual nonlinear 0-jet as a
`MatrixHolderBCF` and a `Jet2HolderSection`. This advances workstream C, but
the next refinement now controls the full `HolderBCF` norm and proves a
closed-ball `LipschitzOnWith` estimate for the packaged `Jet2HolderSection`
map, with a uniform extracted-jet bound. It is still intentionally not
reported as the completed PDE closure: strong continuity of the big Hölder
heat propagator and the variable-coefficient quasilinear evolution remain
open.

The following supporting milestone makes the little-Hölder Duhamel boundary
explicit in `GenuineRicciDeTurckLittleHolderDuhamel.lean`. It lifts the
componentwise little-Hölder heat propagator to the genuine `Jet2Section`,
proves its zero-time identity, contraction bound, and joint continuity, and
provides a parameterized `LocalDuhamelData` constructor for any little-Hölder
endomap satisfying the required closed-ball Lipschitz estimate. The actual
geometric output currently packaged above is still `Jet2HolderSection`
(big-Hölder valued), so this constructor is not yet instantiated with the
Ricci--DeTurck nonlinearity. The remaining nonlinear gate for that geometric
output is a tensorial little-Hölder preservation theorem, including the
required commutator/seminorm control; neither this interface nor the preceding
Lipschitz estimate is a claim of PDE existence.

The next analytic gate is now also explicit in
`LittleHolderDuhamel.lean`: `isGoodHolder_of_isHolderConst_one` proves that
globally Lipschitz Hölder data are genuinely little-Hölder. It combines the
heat-flow sup-norm approximate-identity estimate with the interpolation bound
for the Hölder seminorm of the error. This establishes a nontrivial input
subspace for the little-Hölder theory, but it does not yet show that arbitrary
little-Hölder data are preserved by the geometric Nemytskii map; the
commutator/seminorm estimate for that nonlinear output remains open.

The genuine nonlinear output now has a proved restricted preservation theorem
in `GenuineRicciDeTurckLittleHolderOutput.lean`. Given an explicit global
Lipschitz `IsHolderNorm 1` certificate for the extracted 2-jet, the actual
Ricci--DeTurck fiber map is packaged componentwise into `LittleHolder`, and
the section-shaped source is returned in `Jet2Section`. The theorem exposes
the remaining boundary precisely: the certificate is an additional
regularity hypothesis, so it is not yet an endomap theorem for every
little-Hölder section.

The next closure theorem is now packaged in
`LittleHolderNemytskiiClosure.lean`. The theorem
`isGoodHolder_comp_of_commutator_seminorm` proves the exact algebraic-to-
topological implication needed for nonlinear closure: the already proved
supremum commutator convergence, a vanishing Hölder-seminorm commutator, and
full `HolderBCF` continuity of the composed heat path imply genuine
little-Hölder preservation. This is a real closure result, but its two
analytic inputs remain explicit; the current repository still does not claim
the missing nonlinear seminorm estimate or the unrestricted Ricci--DeTurck
endomap.

The full-norm path input is discharged under global `C^{1,1}` fiber-map
hypotheses in `LittleHolderNemytskiiPath.lean`. The theorem
`tendsto_holderBCF_comp_heatPropagator_of_c11` uses the existing quantitative
`isHolderNorm_comp_sub` estimate together with the two little-Hölder heat
path components. Its wrapper
`isGoodHolder_comp_of_commutator_seminorm_of_c11` now packages the resulting
conditional little-Hölder conclusion. The assumptions are deliberately
stated for an abstract scalar fiber map; the tensor-valued Ricci--DeTurck map
still needs its own derivative and commutator discharge.

The unconditional scalar closure step is now proved in
`LittleHolderNemytskiiClosureC11.lean`. For positive heat time,
`heatSemigroupND_lipschitzWith_spatial` supplies a global Lipschitz certificate
for the smoothed datum, and `isGoodHolder_of_isHolderConst_one` makes its
Nemytskii image little-Hölder. The full-norm path theorem and
`isClosed_littleHolderSubmodule` then pass the limit to `F ∘ f`. The theorem
`isGoodHolder_comp_of_c11` is an actual scalar preservation result with no
commutator premise; it remains deliberately separate from the unresolved
tensorial Ricci--DeTurck endomap.

The next matrix-valued closure layer is now proved in
`GenuineRicciDeTurckMatrixLittleHolderClosure.lean`. The theorem
`isGoodHolder_geometricNRDHolder_of_heat_path` applies the genuine
matrix-valued Ricci--DeTurck output to the componentwise little-Hölder heat
approximants. It proves the full `Jet2Section` heat-path convergence, an
explicit exponent-one certificate for every positive-time extracted jet, and
the entrywise little-Hölder carrier transfer using the existing genuine
`HolderBCF` difference estimate. The result is packaged as
`geometricNRDLittleHolderOfHeat` and `geometricNLittleHolderOfHeat`, so the
actual matrix reaction is now represented in `Jet2Section`. The geometric
compact jet-range condition along the heat path remains an explicit premise;
this milestone therefore closes the matrix carrier conditional on that
invariant region, while the local Duhamel endomap and its closed-ball
Lipschitz estimate remain open.

The gauge-flow interface now records the remaining analytic dependency instead
of attaching it to every ordinary flow record. `Diffeomorph3FlowDerivative.lean`
keeps the raw anchored `C^3` gauge-flow API buildable, while
`ChosenIntrinsicDeTurckDiffeomorph3GaugeFlowWithVariationalData` is the
explicit refinement that carries the per-point coordinate variational data.
Under that refinement, `Diffeomorph3FlowMilestone41.lean` proves the actual
scalar and tensor pullback-metric time-derivative identities for the DeTurck
gauge family. The refinement is intentionally not constructed here: producing
its full tangent-map, bilinear-form, and Lie-bracket data from the compact-
manifold ODE/PDE regularity remains an analytic obligation.

The follow-up bridge in
`DeTurckFlowVariationalDataBridge.lean` now assembles a
`FullVariationalWitness` into the exact per-point `VariationalData` consumed by
M4.1 at ordinary-neighborhood times. The Picard tangent equation discharges
the coordinate pushforward derivative, and a genuine Fréchet derivative of
the metric-coordinate field discharges the moving bilinear derivative. The
Lie-bracket identity, final gauge-velocity assembly, endpoint chart control,
and the actual construction of such full witnesses remain explicit gates;
this bridge therefore narrows the boundary without claiming the full
variational refinement or Point 4 closure.

The next bridge in `DeTurckFlowVariationalBracketBridge.lean` discharges the
Lie-bracket gate from one explicit model-side obligation: the Picard
linearization `Df` must equal the fixed-chart `fderivWithin` of the genuine
intrinsic DeTurck gauge field at the selected Picard point. The existing
manifold bracket theorem then supplies the exact `hD_bracket` identity, and a
constructor builds `FullVariationalWitness` from that derivative data while
leaving the gauge-velocity assembly `hvalue` explicit. No ODE equation alone
is treated as an identification of the model vector field with the geometric
gauge field.

`DeTurckFlowVariationalAssemblyBridge.lean` now discharges that assembly from
two explicit analytic inputs: the exact metric-coordinate time-difference
identity and differentiability of the intrinsic DeTurck vector field at the
selected image point. The fixed-time Levi-Civita derivative, the torsion-free
Picard bracket calculation, and the pulled-back velocity/correction theorem
prove the spatial cancellation and reconstruct `hvalue` exactly. The new
`FullVariationalWitnessCore` separates those constructive inputs from
the derived scalar field, so the assembly bridge no longer makes witness
construction circular. The pointwise differentiability input and the actual
analytic construction of the core data remain explicit; this is a genuine
assembly bridge, not a closure of the variational refinement or Point 4.

`DeTurckFlowVariationalTimeBridge.lean` now derives the temporal
`MetricTimeDifferenceData` input from the intrinsic DeTurck solution's existing
`HasTimeDerivativeOn` field and the genuine full Fréchet derivative of the
metric-coordinate field. The proof separates the time slice from the frozen
spatial `fderivWithin` contribution. It works on the six-field witness core;
the core-to-full constructor remains in the chosen-background bridge.

`DeTurckFlowVariationalChosenBackground.lean` discharges that pointwise
differentiability input for the actual chosen solution: its recorded
Levi-Civita background supplies the required `C^1` connection regularity. It
also constructs a core from Picard, metric-coordinate derivative, and
model-bracket data; the chosen solution supplies `gdot` as its canonical
gauge-corrected pullback velocity. That core then combines with the temporal
bridge to obtain a `FullVariationalWitness`. Constructing the remaining
analytic core inputs, endpoint data, and the general gauge flow remain open.

`DeTurckWitnessPhase1.lean` now carries the next constructive boundary: after
the explicit `C²`/joint-continuity regularity package yields component Picard
estimates, the cycle-free model ODE core constructs an actual
`VariationalLocalFlowSolution`, including the product-field continuity and norm
bound. The estimate API now also exposes that the selected base time belongs to
the returned Picard interval. This is conditional on the still-open geometric
regularity package; it does not prove that package or close Point 4.

The Phase-1 constructor now also composes with
`DeTurckPicardRegularityReduction.smoothJetMap_implies_picardRegularity`:
explicit smooth jet data and joint jet continuity produce the regularity
package, which then produces the model variational flow. This removes a
redundant three-hypothesis boundary without hiding the geometric jet-map
construction; the jet and its continuity remain explicit inputs.

The follow-up canonical-coordinate milestone discharges the zeroth-order
geometric part of that input. `DeTurckPicardRegularityReduction.lean` now
defines `tangentCoordinateEquiv`, `geometricChartDiff`,
`geometricMetricSharp`, and `geometricDeTurckCoordinateOneForm` from the actual
extended-chart differential, tangent-bundle trivialization, metric Riesz map,
and intrinsic DeTurck one-form, and proves
`geometricDeTurckChartFactorization`. `CanonicalDeTurckChartJetData` converts
these representatives into the existing jet interface without an independent
factorization hypothesis. Its derivative and joint-continuity fields remain
explicit: the chart-level regularity bridge and the parabolic time--space
regularity needed for the unconditional Point-4 theorem are still open.

The next fixed-time regularity bridge is packaged in
`DeTurckFixedTimeRegularity.lean`. Under the explicit `C¹` background
connection-slice hypothesis, it converts the already proved intrinsic
DeTurck-section regularity through the fixed-center chart-pushforward theorem
and identifies that pushforward with the exact
`deTurckGaugeCoordinateField` definition. Thus the genuine coordinate field
is now proved `ContDiffOn ℝ 1` on the chart target at each such time. This
narrows the chart-level boundary, but it does not supply the `C²` spatial
estimate, the joint time--space continuity of the field and derivative, or
the general Ricci-flow local-existence theorem.

The next fixed-time `C²` bridge is packaged in
`DeTurckFixedTimeC2CoordinateBridge.lean`. Given an explicit `C²` intrinsic
DeTurck tangent-bundle section on the chart source, it proves `C²` regularity
of the genuine coordinate field on the chart target through the fixed-center
chart pushforward and exact coordinate identity. On a closed coordinate ball
whose one-unit enlargement lies in the chart target, it also extracts the
field and spatial-derivative `LipschitzOnWith` constants consumed by the
Picard estimate. The intrinsic `C²` premise, chart containment, and all
time-joint/uniform regularity remain explicit; this does not close Point 4.

The next product-domain bridge is packaged in
`DeTurckJointC2CoordinateBridge.lean`. Given a jointly `C²` intrinsic
DeTurck tangent-bundle section on `ℝ × M`, it proves jointly `C²` regularity
of the genuine coordinate field on `ℝ × E` by composing the existing product
chart-pushforward theorem with the exact coordinate identity. This is the
correct geometric shape for the remaining time--space input, but the joint
section premise is not implied by the current slicewise `MetricFamily` and
`ConnectionFamily` interfaces; derivative-continuity packaging and the final
Picard/local-existence theorem remain open.

The next analytic bridge is packaged in
`DeTurckJointC2PicardRegularity.lean`. From the jointly `C²` coordinate field,
it derives continuity of the field, its spatial derivative, and its second
spatial derivative by differentiating along the fixed-time product inclusion.
It then specializes these facts, with an explicit chart-containment buffer, to
the exact `hreg`, `hjoint`, and `hjoint2` premises of the coordinate Picard
estimate. The jointly intrinsic `C²` section remains an explicit premise (and
the specialization uses the boundaryless chart-target setting); no general
parabolic regularity or Point-4 existence theorem is claimed.

The flow-composition milestone is packaged in
`DeTurckJointC2FlowBridge.lean`. It feeds that exact regularity package into
the existing cycle-free Picard constructor and therefore produces an actual
model-space `VariationalLocalFlowSolution` with selected time `t₀`, under the
same joint intrinsic `C²`, chart-containment, and boundaryless hypotheses. The
constructor interface is now explicitly exported from
`DeTurckWitnessPhase1.lean` so this composition is a public downstream
theorem; the geometric premises and the later manifold identification,
endpoint, and Ricci-flow conclusions remain open.

The compact-flow comparison assembly is packaged in
`DeTurckCompactFlowModelComparison.lean`. It composes the existing raw compact
flow, chart-transfer `C³` gluing, and inverse-slice argument into an actual
`Diffeomorph3GaugeFlowOn`, provided slice continuity/surjectivity and genuine
`C³` coordinate model-diffeomorph comparisons are supplied. The theorem keeps
both the dependent manifold field and coordinate comparison field explicit; it
does not claim that the single local `VariationalLocalFlowSolution` above
supplies those global comparison data.

## Proved architecture

The implementation already provides a real conditional route:

```text
Ricci–DeTurck Banach chart and parabolic solution
  + smooth geometric realization
  + reverse encoding of competing candidates
  + sufficiently regular DeTurck gauge flow
  + pullback-metric derivative identity
  ⇒ intrinsic Ricci-flow local existence and uniqueness
```

It also proves restricted theorem families and substantial reusable
infrastructure. These are meaningful intermediate results, but the audit
correctly prevents them from being mistaken for the unrestricted theorem.

## Remaining integration workstreams

The historical plan grouped the missing construction into three workstreams.
Many supporting lemmas inside each workstream have landed; the labels below
refer to the remaining end-to-end obligations, not to an absence of code.

### A. Gauge-pulled metric time derivative

Complete the general nonidentity time-dependent formula

```text
d/dt (Φ_t^* g_t) = Φ_t^* (∂_t g_t + Lie_{X_t} g_t)
```

in the repository's bundled tensor vocabulary. Scalar-to-tensor reductions,
bilinear chain rules, endpoint variants, and several model-coordinate pieces
already exist, and `Diffeomorph3FlowMilestone41.lean` now proves the complete
identity under the explicit `WithVariationalData` refinement. What matters for
closure is constructing that refinement for the actual gauge family used by
the general Ricci–DeTurck solution; the current theorem does not turn a raw
gauge-flow existence record into variational data.

### B. Compact-manifold `C³` gauge flow

For the time-dependent DeTurck vector field, construct a short-time family of
self-diffeomorphisms satisfying

```text
∂_t Φ_t(x) = X_t(Φ_t(x)),    Φ_{t₀} = id,
```

with the spatial and temporal regularity required by gauge transport. The
repository contains extensive model-flow, chart-transfer, compact-cover,
inverse-flow, and special-construction machinery. Closure requires an
unconditional construction specialized to the actual general DeTurck field.

### C. Quasilinear Ricci–DeTurck PDE closure

Construct, for every relevant initial metric:

- the genuine time-dependent geometric Ricci–DeTurck Banach chart;
- local well-posedness for its strictly parabolic quasilinear evolution;
- preservation of the positive-definite metric locus;
- smooth realization of the Banach solution as geometric data;
- reverse encoding of every competing smooth candidate needed for uniqueness;
- identification of the analytic representative with the intrinsic geometric
  Ricci–DeTurck right-hand side.

This is the main Hamilton–DeTurck theorem and the longest remaining analytic
workstream. Existing Hölder, section-space, coordinate, mild-solution, and frozen
operator results reduce the distance to it but do not replace the quasilinear
parabolic theorem.

## Recommended execution order

1. Close the general compact-manifold gauge-flow specialization.
2. Close the pullback-metric derivative formula for that same gauge family.
3. Complete the quasilinear parabolic chart and closure data.
4. Assemble the existing conditional bridge into the canonical theorem.
5. Run the full Point-4 audit and retain its output as completion evidence.

Workstreams A–C can proceed independently where their APIs are already stable.
The order above minimizes uncertainty at final assembly; it is not a claim that
the PDE work must wait entirely for the gauge work.

## Reporting rule

Use theorem-specific language for partial progress. Examples:

- "proved the frozen affine evolution";
- "constructed a gauge flow under hypothesis H";
- "proved the chart-to-intrinsic conditional bridge".

Do not report "Ricci-flow local existence is proved" until the canonical
unconditional theorem exists and the complete audit closes.

## Historical detail

The former working plan and the separate July progress journal are preserved as
historical records:

- [Full Point-4 development log](../history/point4-development-log.md)
- [July 2026 Point-4 progress log](../history/point4-progress-log-2026-07.md)

Those files contain useful theorem names, failed approaches, performance notes,
and intermediate milestones. Their locally dated "next" statements are not
current-status claims.
