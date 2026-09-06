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
  zero classical derivative on interior balls. Local almost-everywhere
  constancy still requires the approximation-limit argument.

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
The integrated development passes a local build (3710 jobs), the 33-file
vendored-source check, and an axiom audit of all 245 project declarations
plus six selected vendored Sobolev/compactness endpoints.
Their transitive axioms are confined to `propext`, `Classical.choice`, `Quot.sound`. The check rejects
missing reports and three classes of unapproved axioms. Hosted CI is separate
evidence and must be checked at the exact source commit.
The volume/chart modules retain non-fatal local-instance style warnings.

## Remaining work, in order

1. Mean-zero coercivity, weak Poisson existence and smooth elliptic regularity.
2. Integrated Bochner and the geometric almost-Schur inequality.
3. Einstein equality rigidity, exact source/hypothesis audit.
4. Only then: independent Challenge/Solution packaging and kernel replay.

The normalized density measure is now constructed, with finite positive total
mass under the hypotheses above. Equality with intrinsic Hausdorff volume is
not proved and is not used to justify the density measure's properties.

The external compactness library was rebuilt and migrated;
see [dependency evidence](dependencies/README.md). Thirty-three attributed
modules are vendored with immutable provenance and checksum checks, including
the generic chart Sobolev construction and Euclidean compactness proof. The
Hausdorff-specialized manifold compactness theorem is not imported. Its
chartwise transport argument still needs adaptation to our density measure.
The weak-limit constancy and intrinsic-energy localization bounds needed for
Poincaré remain unproved; the smooth energy-kernel theorem does not replace them.

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
