# Manifold-only literal-C² fixed-background local tensor heat

Status: **uncompiled release integration; R2 proof source approved, fresh release review and exact Lean 4.33 gates pending. Point 4 remains OPEN.**

This additive milestone has three new Lean modules. All 1,640 inherited files
other than the combined C2 source guard at master
`e6b54dd0d7e73a51eb8efb083764b68ae8305a5a` are byte-for-byte unchanged.
That guard receives one exactly reconstructed inventory adapter, preserving
all existing gate bodies and admitting only this enumerated release union.
The root import surface and root formalization metadata remain byte-identical.
See `manifold-only-heat-release-integration.md` for the release boundary. PR130's pending initial-metric localization draft is
not used. Structured provenance is in the companion
`manifold-only-fixed-background-heat/formalization.yaml`.

## Exact hypothesis frontier

The historical PR126 producer at
`58c6fc21bafeb8a659d6751a1a9db7a74127a300` assumes `I.Boundaryless`.
Its global auxiliary C² affine-connection construction and induced
regularity proofs do not need that hypothesis. The coefficient path uses it
only to obtain ordinary-coordinate neighborhoods of chart-target points.
The existing analytic theorem
`exists_radius_actualLocalTensorHeatSolutionL_of_contDiffOn_unitBall_zeroTrace`
does not assume global model boundarylessness.

The existing proved theorem
`PoincareCurvature.BoundarylessChartTransport.isOpen_extChartAt_target`
provides exactly the needed open target from `BoundarylessManifold I M`.
Because the target is contained in `range I`, its neighborhood gives a local
range neighborhood. Thus the actual inverse-chart derivative and subsequent
`fderivWithin` coefficient derivatives agree locally with ordinary ones.
No assertion that `range I = univ` or instance of `I.Boundaryless` is used.

## Additive proof spine

1. `BoundarylessTensorHeatCoefficients.lean` adapts only the coefficient
   dependency spine of `TensorHeatGeometricRegularity.lean`, in the new
   `CovariantDerivative.ManifoldBoundaryless` and
   `RicciFlow.AnalyticPDE.ManifoldBoundaryless` namespaces. It derives C²
   inverse-Gram/frame/two-tensor-connection readouts, C¹ three-tensor readouts,
   and hence the original actual principal, first and zero coefficients' C¹
   regularity. The geometric formulas and norms are unchanged.
2. `BoundarylessTensorHeatLocalization.lean` adapts the point-centered
   unit-ball wrapper. It proves the actual overlap domain open, uses those
   derived coefficient bounds, and invokes the existing analytic construction
   unchanged. The returned scale makes the fields agree with the actual
   geometric coefficients throughout the normalized closed unit ball; the
   bounded right inverse satisfies the actual coordinate-Cauchy identity and
   zero canonical initial trace.
3. `BoundarylessTensorHeatFixedBackground.lean` adapts PR126's producer. The
   only metric input is the supplied `g₀ : ContMDiffRiemannianMetric I 2 E TM`.
   One global auxiliary C² affine connection is constructed internally before
   any chart, basis or time/source choice. Its C¹/C² induced regularity is
   proved internally. The output quantifies over every finite basis, every
   actual tangent trivialization containing the center, every `t₀ < T`, and
   every `0 < α < 1` in the inherited unweighted Hölder source space.

The main new theorem is
`RicciFlow.AnalyticPDE.ManifoldBoundaryless.exists_fixedBackground_actualLocalTensorHeat`.
It has no ambient metric, connection regularity, assembled coefficient
regularity, or solver premise. Smooth tangent-bundle orders come from the
smooth manifold. No metric smoothing/replacement, rank restriction,
nonempty-manifold restriction or compactness premise has been added.

## Verification and limits

The prepared probe prints eleven axiom surfaces and four full theorem-level
hypothesis surfaces. The source guards check every inherited file against
master, allowing only the exact documented inventory-adapter transform, the literal metric input, actual connection/induced construction,
actual coefficients and analytic inverse use, manifold-only scope, and
immutable structured provenance. A comment/string-stripped scan reports
zero forbidden proof tokens. Pinned Mathlib `ContMDiff/Atlas.lean` and
`VectorField/Pullback.lean` were inspected read-only, including the exact
inverse-chart and pullback-regularity signatures.

Source checks are not Lean elaboration. No local Lean process has run. The
prepared compile-first workflow must build the new producer at its exact
candidate head under pinned Lean 4.33, run the complete type/axiom probes, and
then run the unchanged full-package Point-4 audit. Independent source review
is a separate prerequisite, and eventual compiler failures must be preserved
as historical evidence, not hidden or substituted with other-toolchain checks.

This milestone does not construct a global literal-C² initial extension,
patch a global heat generator, prove weighted nonlinear contraction estimates,
produce a Ricci--DeTurck solution, compare weak competitors on the approved
common closed interval, or prove the canonical Point-4 theorem.
