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

The new local analytic results use finite-dimensional coordinate spaces.
They are not yet transported through `extChartAt` to the manifold connection.
The coordinate metric-compatibility assumption is the usual differential
Gram-matrix identity; its connection-trace consequence is proved, not assumed.
The local cometric operator is not yet identified with the manifold
`AlmostSchur.laplacian`. No global Poisson solver or Bochner formula is assumed.

The Hessian is defined relative to a supplied connection; symmetry and smooth
regularity are not yet proved here. The final result must use Levi–Civita.
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
The development passes a local build (3590 jobs), the vendored-source check,
and an axiom audit of all 144 public declarations.
Their transitive axioms are confined to `propext`, `Classical.choice`, `Quot.sound`. The check rejects
missing reports and three classes of unapproved axioms. Hosted CI is separate
evidence and must be checked at the exact source commit.
The volume/chart modules retain non-fatal local-instance style warnings.

## Remaining work, in order

1. Transport the coordinate connection/metric compatibility and Green
   identities through manifold charts; assemble with a partition of unity.
   Finish smooth manifold gradient/Hessian theory. Local energy is proved,
   but global integration by parts is not.
2. Mean-zero coercivity, weak Poisson existence and smooth elliptic regularity.
3. Integrated Bochner and the geometric almost-Schur inequality.
4. Einstein equality rigidity, exact source/hypothesis audit.
5. Only then: independent Challenge/Solution packaging and kernel replay.

The normalized density measure is now constructed, with finite positive total
mass under the hypotheses above. Equality with intrinsic Hausdorff volume is
not proved and is not used to justify the density measure's properties.

The external compactness library was rebuilt and migrated experimentally;
see [dependency evidence](dependencies/README.md). Four adapted volume/chart
modules are now vendored with immutable provenance and checksum checks. The
full compactness library is not yet imported. Nothing here assumes its theorems
to obtain the target.

## Sources and contribution

Mathematical source: De Lellis and Topping,
[Almost-Schur lemma](https://arxiv.org/abs/1003.3527v2), Theorem 0.1 (published
Theorem 1.1). This is source-based work, not a new mathematical discovery.
The pointwise trace decomposition is supporting linear algebra, not a
standalone research-interest claim.

The new modules were developed with Codex at the maintainer's request.
The tensor and local analytic modules import only Mathlib; the volume module also imports the
four attributed, adapted external chart/volume files.
The existing `schur-rigidity/` proof library is planned integration material,
not yet imported. Its immutable provenance must be recorded if reused.
The separate migration patch preserves the external project's attribution and
license; it does not imply its author's endorsement or review.

The local Green proof uses Mathlib's general Fréchet integration-by-parts
theorem (Sébastien Gouëzel), and density transport uses Mathlib's Jacobian
change-of-variables theorem (also Gouëzel). Jacobi's formula is derived here
from Mathlib's continuous-multilinear derivative and Cramer/adjugate identities.
These are classical supporting results, not separate research-interest claims.
