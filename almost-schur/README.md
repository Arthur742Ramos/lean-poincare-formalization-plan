# Almost-Schur: geometric-analysis development

Target: the De Lellis–Topping almost-Schur inequality and its Einstein equality
case on nonempty connected closed smooth Riemannian manifolds of dimension at
least three with nonnegative Ricci curvature.

**Incomplete development; not a Palomar submission artifact.** There is no
Challenge, Solution or Comparator in this directory yet. The full inequality
and equality rigidity are not proved. Do not submit these foundations as the
research theorem.

## Proved foundations

- `AlmostSchur.Gradient`: actual differential-to-gradient Riesz duality,
  uniqueness, zero-gradient characterization, and norm identities.
- `AlmostSchur.Hessian`: connection Hessian and Laplacian, with an
  orthonormal trace formula independent of basis/index type.
- `AlmostSchur.HilbertSchmidt`: intrinsic squared tensor norm, its full
  double-contraction formula, nonnegativity, and exact trace-free decomposition.
- `AlmostSchur.HessianNorm`: the pointwise trace-free norm identity for the
  actual covariant Hessian. This is not an integrated Bochner formula.
- `AlmostSchur.Volume`: intrinsic Hausdorff volume is positive on neighborhoods
  and has finite positive total mass on nonempty compact boundaryless manifolds.
  Compatibility with the smooth Riemannian density remains unproved.
- `AlmostSchur.LocalIntegration`: positive-density Green identity for C1
  compactly supported vector fields, with the actual Fréchet divergence and
  all integrability obligations discharged.
- `AlmostSchur.MetricDensity`: `sqrt(det G)` transforms by the absolute
  Jacobian, with both Bochner change of variables and integrability transport.
- `AlmostSchur.DensityDerivative`: Jacobi's determinant derivative is proved
  from multilinearity; metric compatibility then gives the density derivative.
- `AlmostSchur.LocalMetricDivergence`: the trace of a metric-compatible,
  torsion-free coordinate connection equals density divergence, yielding its
  local geometric Green identity.
- `AlmostSchur.LocalEnergy`: energy identity, integrability, formal symmetry,
  nonpositive quadratic form, and zero energy iff the actual differential
  vanishes everywhere for a strictly positive cometric.
- `AlmostSchur.ChartMetric`: positive-definite Gram matrices of the actual
  tangent metric and their density transformation by the genuine derivative
  of a manifold chart change.
- `AlmostSchur.ChartIntegration`: measurable chart images and equality of
  metric-density integrals in two charts on any measurable overlap, including
  nonnegative integrals with infinite values. Constructs local density measures
  and proves equality of their restrictions to measurable chart overlaps.
- `AlmostSchur.GlobalMeasure`: constructs the global density measure on a
  nonempty Lindelöf manifold, proves its chartwise characterization, independence
  of the countable chart cover, and uniqueness for the prescribed local density.
  Coordinate Haar measure and basis remain explicit normalization parameters.
- `AlmostSchur.MetricRegularity`: continuity of the actual Gram matrix and
  density, local finiteness, positive mass on nonempty open sets, and finite
  positive total density mass on nonempty compact Hausdorff manifolds with
  a continuous Riemannian metric.
- `AlmostSchur.NormalizedMeasure`: pairs each coordinate basis with its
  basis Lebesgue measure and proves cancellation of their determinant factors.
  Defines normalized `riemannianVolume`, proves independence of the basis
  and index type, and establishes its chart formula and finite positive mass.
- `AlmostSchur.VolumeIntegration`: Bochner integration against normalized
  volume equals chart-density integration on every measurable chart subset;
  integrability on chart domains is equivalent to weighted coordinate
  integrability. This includes the required measure pullback proof.
- `AlmostSchur.OpenDomainIntegration`: scalar, vector, weighted-density,
  and metric-connection Green identities on open coordinate domains with
  compactly supported flux. Regularity and metric positivity are required
  only on the domain; no positive smooth extension outside a chart is assumed.
- `AlmostSchur.ConnectionCoordinates`: derives the actual connection's local
  frame expansion from additivity, Leibniz, and differentiable coefficient
  reconstruction. Constructs bilinear frame-connection coefficients and proves
  the coordinate formula with the actual chart Fréchet derivative.
- `AlmostSchur.MetricConnectionCoordinates` and `TorsionCoordinates`:
  derive coordinate metric compatibility and symmetry from the actual
  metric-compatible, torsion-free manifold connection.
- `AlmostSchur.DivergenceCoordinates`, `ChartFlux`, and `ChartGreen`:
  identify intrinsic divergence with coordinate density divergence and prove
  Green's identity for chart-supported fields.
- `AlmostSchur.DivergenceRegularity` and `GlobalGreen`: continuity and
  integrability of the relevant fields, a finite smooth chart partition of
  unity, and global integration by parts against normalized Riemannian volume.
- `AlmostSchur.GradientRegularity` and `HessianSymmetry`: regularity of the
  actual Riesz gradient and symmetry of the C2 covariant Hessian, derived from
  metric compatibility and vanishing torsion.
- `AlmostSchur.GlobalEnergy`: the global Dirichlet form, nonnegative energy,
  Green's identity for the actual Laplacian, and its zero integral.
- `AlmostSchur.EnergyKernel`: a vanishing differential forces local constancy
  by the coordinate mean-value theorem and constancy on connected manifolds.
  Together with `GlobalEnergy`'s everywhere-zero-gradient characterization,
  this identifies the energy kernel. It is not a uniform coercivity estimate.
- `AlmostSchur.MeanZeroEnergy`: qualitative positivity on nonzero mean-zero
  functions and uniqueness of C2 solutions with prescribed Laplacian and mean.
- `AlmostSchur.DensityComparison`: exact chart pushforward of normalized
  volume and finite two-sided comparison with Euclidean volume on compact
  chart subsets. This uses the positive continuous density, not Hausdorff
  measure identification.
- `AlmostSchur.SobolevReconstruction`: the imported graph-closure Sobolev
  construction's L2 projection of a C1 graph is the actual original function
  almost everywhere, via chart pullback and the partition-of-unity identity.
- `AlmostSchur.WeakDerivativeMollification`: a locally integrable function
  annihilating derivatives of compact smooth tests has mollifications with
  zero classical derivative on interior balls.
- `AlmostSchur.WeakKernelLocal`: the approximation-limit argument gives
  almost-everywhere constancy on each relatively compact interior ball,
  without assuming classical differentiability of the weak function.
- `AlmostSchur.ChartNormBounds`: uniform inverse-tangent-chart operator norms
  on compact chart subsets and bounded derivatives of the fixed cutoffs.
- `AlmostSchur.LocalizationGradient`: uniform pointwise control of localized
  coordinate gradients by the scalar function and its intrinsic gradient.
- `AlmostSchur.GradientL2` and `AlmostSchur.LocalizationEnergy`: the scalar
  gradient L2 norm equals the square root of intrinsic energy, and actual
  energy plus the L2 function norm control the finite-chart H1 graph norm.
- `AlmostSchur.ChartL2Pullback` and `AlmostSchur.ChartDerivativeBound`: bounded
  pullback of actual-volume L2 classes, with an AE representative identity,
  and unlocalized coordinate-derivative bounds without cutoff error terms.
- `AlmostSchur.L2WeakLimit`: strong L2 limits preserve test pairings and
  mean zero; integration-by-parts identities pass to the limit when the
  derivative factor tends to zero in L2.
- `AlmostSchur.WeakKernelGluing`: local almost-everywhere constants glue on
  preconnected Lindelöf domains, using a countable subcover; zero weak
  derivatives therefore imply constancy on open preconnected Euclidean domains.
- `AlmostSchur.SobolevCompactness`: compactness of the actual graph-closure
  H1-to-L2 map for normalized Riemannian volume, including strongly convergent
  subsequences of graph-norm-bounded sequences. All local measure comparison
  hypotheses are discharged; no Hausdorff identification is assumed.
- `AlmostSchur.EnergyAlgebra` and `EnergyCompactness`: linearity and scaling
  of the intrinsic energy and strongly convergent L2 subsequences under
  actual function-norm and energy bounds.
- `AlmostSchur.ChartLpRegularity`, `WeakChartLimit`, and `ChartWeakKernel`:
  chartwise local integrability of actual L2 classes, passage of coordinate
  integration by parts to strong L2 limits with vanishing energy, and global
  almost-everywhere constancy from the resulting weak derivative identities.
- `AlmostSchur.PoincareCountersequence` and `Poincare`: the mean-zero
  Poincaré inequality for the actual normalized Riemannian volume and gradient,
  proved by compactness and weak-kernel rigidity.
- `AlmostSchur.EnergySpace`, `EnergyL2`, and `EnergyL2Completion`: the genuine
  mean-zero C1 energy inner product, its Hilbert completion, and the bounded
  actual L2 realization derived from Poincaré.
- `AlmostSchur.WeakPoisson`: actual L2 forcing and a unique completed
  variational solution by Riesz, with a quantitative energy bound and the
  forcing-integral identity on C1 mean-zero tests.
- `AlmostSchur.EnergyMean` and `EnergyGreen`: the completed realization has
  zero mean, and the actual global Green identity extends by density. For
  mean-zero L2 forcing, the realized variational solution satisfies the
  transposed Laplace equation on every C2 test. Smoothness remains unproved.
- `AlmostSchur.EnergyChartDerivative`, `L2TestUniqueness`, and
  `EnergyChartKernel`: bounded completed coordinate derivatives, their actual
  weak integration-by-parts identities, and local AE vanishing of those
  derivatives whenever the realized L2 function is zero.
- `AlmostSchur.EnergyPairingCoefficients`, `EnergyPairingReconstruction`, and
  `EnergyL2Injectivity`: continuous compactly supported coefficient functions,
  finite-chart reconstruction of the completed energy pairing, and injectivity
  of the actual L2 realization. Only the proved density of the C1 core is used.
- `AlmostSchur.HilbertWeakLimit`: a bounded Hilbert-space family has a weak
  cluster representative preserving every convergent pairing, with the same
  norm bound. This is a preliminary ingredient for difference-quotient analysis,
  not an elliptic regularity theorem.
- `AlmostSchur.CoordinateEllipticity`, `CoordinateCoefficientRegularity`,
  `MatrixInverseRegularity`, and `MetricHigherRegularity`: the actual
  density-weighted inverse metric has compact uniform ellipticity, coefficient
  and derivative bounds, and the higher regularity supplied by the metric.
- `AlmostSchur.ChartTestLift`, `CoordinateGradient`, `EnergyLocalVariational`,
  `CoordinateForcing`, `CoordinateWeakPoisson`, and `ChartTestEnergy`: actual
  compact chart tests, coordinate gradient reconstruction, local L2 forcing,
  the divergence-form weak equation, and bounded lifting into energy completion.
- `AlmostSchur.DifferenceQuotientAlgebra`, `DifferenceQuotientProduct`, and
  `DifferenceQuotientWeakDerivative`: translation adjoints, the discrete product
  rule and coefficient-error estimate, and extraction of a genuine L2 weak
  derivative from uniformly bounded quotients.
- `AlmostSchur.L2Multiplier`, `ChartCutoff`, `EnergyCutoffGraph`,
  `TestGraphCutoff`, `TestGraphDifferenceQuotient`, `TestGraphUniformQuotient`,
  and `TestGraphVariational`: actual supported C1 graph approximation, cutoff
  and quotient admissibility, a step-independent quotient bound, and extension
  of L2 variational pairings by continuity. The uniform bound reuses the
  attributed vendored translation estimate.
- `AlmostSchur.LocalWeakPoissonGraph`, `TestedDifferenceQuotient`,
  `LocalTestedQuotient`, `CutoffPlateau`, `CutoffQuotientFields`,
  `InteriorCoefficientMasks`, `L2MatrixForm`, `WeightedFluxTest`,
  `LocalQuotientEnergyEstimate`, `LocalH2QuotientBound`, and
  `WeakPoissonH2Bound`: the actual local weak Poisson equation on the graph
  closure, support-safe plateau representatives, the four-term tested energy
  expansion, and a step-independent weighted difference-quotient bound for
  every coordinate first derivative. No regularity of a zero extension is
  asserted. Extracting the weak second derivatives and completing elliptic
  bootstrapping remain to be done.
- `AlmostSchur.WeakDerivativeBootstrap`: genuine weak product rules and the
  differentiated divergence equation for L2 weak derivatives, including its
  coefficient commutator. This is an iterable identity, not by itself an
  elliptic gain-of-derivatives theorem.
- `AlmostSchur.CovariantAlongRegularity`, `ThirdHessianCommutator`,
  `ThirdHessianSymmetry`, `CovariantTraceDerivative`, `BochnerFluxRegularity`,
  `RawBochnerFlux`, and `IntegratedRawBochner`: genuine covariant commutators,
  moving-frame trace differentiation, flux regularity, and the integrated
  Bochner identity for the explicit raw curvature contraction. Each separated
  integrand is proved integrable.
- `AlmostSchur.MetricTorsionCorrection`, `PointwiseConnection`,
  `LeviCivitaCorrection`, `LeviCivitaConnection`, `KoszulFormula`,
  `MetricDualFrame`, `LeviCivitaRegularity`, `LeviCivitaBochner`, and
  `LeviCivitaIntegratedBochner`: an explicitly constructed
  metric-compatible torsion-free connection, Koszul uniqueness on
  differentiable fields, a proved C1 connection instance reconstructed from
  metric pairings, and the pointwise and integrated raw Bochner identities
  specialized to that connection. Bundled Ricci identification and higher
  connection regularity remain separate obligations.

The local analytic results use finite-dimensional coordinate spaces and are
transported through `extChartAt` to the manifold connection. Coordinate metric
compatibility, torsion cancellation, and the global Green identity are proved,
not assumed. No global Poisson solver or Bochner formula is assumed.

The Hessian is defined relative to a supplied connection; symmetry holds for
metric-compatible torsion-free connections. The final result must use Levi–Civita.
All definitions are total as in Mathlib; differentiability obligations must be
discharged when interpreting or differentiating them.

## Reproduction

Lean `v4.33.0`; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

```sh
cd almost-schur
lake exe cache get
lake build
python3 scripts/check-axioms.py
python3 scripts/check-vendored.py
```

Local development reused an ignored dependency-cache symlink; committed source
and manifest do not require a sibling project. The Linux workflow reconstructs
dependencies from the pinned manifest.

The tensor-only milestone at `e9670df01f616070babfbfd5ddff6748ba2d4970`
passed [Linux CI](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/34055014715).
The volume extension passed a local build (3493 jobs) and
[Linux CI](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/34055430137).
The subsequent local integration/density/energy extension passed a local
build (3536 jobs) and the vendored-source check.
The integrated development passes a local build (3810 jobs), the 36-file
vendored-source check, and an axiom audit of all 611 project declarations
plus six selected vendored Sobolev/compactness endpoints.
Their transitive axioms are confined to `propext`, `Classical.choice`, `Quot.sound`. The check rejects
missing reports and three classes of unapproved axioms. Hosted CI is separate
evidence and must be checked at the exact source commit.
The volume/chart modules retain non-fatal local-instance style warnings.

## Remaining work, in order

1. Extract weak second derivatives from the proved uniform local quotient
   bound, then complete smooth elliptic bootstrapping for the weak Poisson
   solution.
2. Bundled Ricci identification, contracted Bianchi, and the geometric
   almost-Schur inequality (the constructed Levi-Civita raw integrated
   Bochner identity is proved).
3. Einstein equality rigidity, exact source/hypothesis audit.
4. Only then: independent Challenge/Solution packaging and kernel replay.

The normalized density measure is now constructed, with finite positive total
mass under the hypotheses above. Equality with intrinsic Hausdorff volume is
not proved and is not used to justify the density measure's properties.

The external compactness library was rebuilt and migrated;
see [dependency evidence](dependencies/README.md). Thirty-six attributed
modules are vendored with immutable provenance and checksum checks, including
the generic chart Sobolev construction and Euclidean compactness proof. The
Hausdorff-specialized manifold compactness theorem is not imported. Its
chartwise transport argument has been generalized to finite measures with
two-sided local density bounds and instantiated for our normalized volume.
The intrinsic-energy localization bound, passage to chartwise weak limits,
manifold weak-kernel rigidity, and Poincaré inequality are proved. Completed
variational solvability and the transposed Poisson equation are also proved;
identifying the solution with a smooth function solving the classical equation
remains separate work.

## Sources and contribution

Mathematical source: De Lellis and Topping,
[Almost-Schur lemma](https://arxiv.org/abs/1003.3527v2), Theorem 0.1 (published
Theorem 1.1). This is source-based work, not a new mathematical discovery.
The pointwise trace decomposition is supporting linear algebra, not a
standalone research-interest claim.

The new modules were developed with Codex at the maintainer's request.
The tensor and local differential/integration modules import only Mathlib;
the volume and Sobolev modules also import the attributed external subset.
The existing `schur-rigidity/` proof library is planned integration material,
not yet imported. Its immutable provenance must be recorded if reused.
The separate migration patch preserves the external project's attribution and
license; it does not imply its author's endorsement or review.

The local Green proof uses Mathlib's general Fréchet integration-by-parts
theorem (Sébastien Gouëzel), and density transport uses Mathlib's Jacobian
change-of-variables theorem (also Gouëzel). Jacobi's formula is derived here
from Mathlib's continuous-multilinear derivative and Cramer/adjugate identities.
These are classical supporting results, not separate research-interest claims.
