# Actual frozen metric principal and holonomic Cauchy action

This supporting source candidate builds on the immutable repository source at
`1d1f97fe481e0899a0cd54889b0f99ba159ba3fa`. The source relationship,
paths, inherited results and new theorem boundary are recorded in
`curvature/formalization.yaml`. Contributor notices and Apache-2.0 licensing
are preserved. No registry intake is part of this milestone.

## Exact statement boundary

The geometric interface retains an arbitrary finite-dimensional complete real
model, smooth Hausdorff boundaryless manifold, C² tangent bundle and sigma
compactness inherited from the chosen-LC metric-coordinate producer. It takes
a genuine `MetricFamily` slice, an arbitrary basis indexed by `Fin d`, and a
freeze point in the preferred fixed chart source. It requires no compactness,
nonempty/rank restriction, additional time regularity, C³ metric, or supplied
principal-coefficient identification. No general manifold statement or audit
contract is changed.

`Analysis/LinearReadoutSecondDerivative.lean` proves actual iterated Fréchet
derivative transport under fixed continuous linear coordinate and readout
maps. The first derivative field is certified everywhere; its second derivative
is certified at the evaluation point. These certificates are supplied by the
existing compatible finite-cylinder space in the geometric application.

`AnalyticPDE/ChosenLCFrozenTensorHeat.lean` proves:

1. The actual preferred frame pulled into its own chart is the model basis
2. The actual frame inverse Gram matrix is the inverse of the actual
   `chosenLCMetricCoordinates` matrix at `chosenLCCoordinatePoint`
3. The existing frozen tensor-heat principal coefficient is exactly the
   double finite inverse-metric contraction of its Hessian input
4. The finite-cylinder tensor readout is the genuine value representative
   after the finite-basis coordinate change, with output `(j,i)` preserved
5. Compatibility identifies its actual iterated spatial Fréchet derivative
   with the stored second derivative. This needs no extra C² candidate
   hypothesis or positive-alpha assumption
6. On `Ioo t₀ T`, compatibility identifies its actual time derivative with
   the stored time derivative
7. Evaluation of the existing bounded frozen Cauchy operator on `Ioc t₀ T`
   is the stored time slot minus the actual inverse-metric coordinate Hessian
   trace; on `Ioo t₀ T` both sides use actual ordinary derivatives

The wrapper definitions select the Riemannian bundle from the given metric
slice. Thus an unrelated ambient metric cannot enter the principal contraction.
The readout does not assume tensor symmetry to hide the output reversal.

The finite cylinder is finite only in time; its spatial domain is all of the
model space. The input is the existing proved closed compatible derivative
graph `FiniteParabolicC2AlphaBanach`, not independent first/second jet slots.
The terminal time `T` is not advertised as an ordinary two-sided time
derivative point.

## Verification and remaining frontier

Exact Lean 4.33 kernel verification is pending. Source review or a development
check on the installed newer toolchain is not exact-toolchain certification.
The dedicated pinned read-only exact-head workflow first compiles generic
linear derivative transport and the actual geometric assembly, then compiles
interface regressions and checks all eight headline theorem axiom surfaces.
Only the foundational `propext`, `Classical.choice`, and `Quot.sound` axioms
are allowed. It then runs the unchanged full Point-4 completion audit and
preserves its exact-head evidence. No audit gate or canonical target is changed.

This identifies a differential operator. It supplies no C₀-semigroup claim,
closed-manifold encoding, overlap/gluing or initial-trace realization,
spatially-varying-background nonlinear estimate, localization/smallness,
positive metric preservation, nonlinear Ricci–DeTurck solution, recovery gauge
flow, or uniqueness theorem. Point 4 remains **OPEN**.
