# Palomar Submission 04

## Parabolic scaling, compact localization, and inverse stability

This corrected candidate packages the parabolic-analysis interface in
`PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/ParabolicHolder.lean`
and its finite-cover composition in
`PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/InverseLocalization.lean`.
It replaces the failed time-indexed Levi–Civita surface with a connected
analytic result family:

- `PoincareCurvature.Palomar.parabolicDistance_dilation`, the exact
  square-time/linear-space scaling identity;
- `PoincareCurvature.Palomar.parabolicClosedBall_zero_mapsTo_dilation`, the
  corresponding closed-ball transport statement;
- `PoincareCurvature.Palomar.parabolicBall_exists_finset_cover_closedBall_subset_open_of_isCompact`,
  finite compact localization with closed-ball control;
- `PoincareCurvature.Palomar.parabolicC0AlphaWith_comp_parabolicDistanceLe`,
  pullback scaling of explicit parabolic Hölder constants;
- `PoincareCurvature.Palomar.parabolicC0AlphaWith_inv_sub_inv`, an explicit
  reciprocal-difference estimate; and
- `PoincareCurvature.Palomar.parabolicC0AlphaOn_of_finset_parabolicBall_cover_closedBall`
  together with
  `PoincareCurvature.Palomar.parabolicC0AlphaOn_inverse_difference_of_finset_parabolicBall_cover_closedBall`,
  finite-cover globalization and its inverse-stability composition.

The intended research audience is geometric analysts working with parabolic
chart estimates: the selected statements expose the exact anisotropic scaling,
the compact localization mechanism, and explicit nonlinear reciprocal bounds
needed when inverse coefficient families are globalized across a finite cover.
The mathematical ingredients are standard, and the repository makes no claim
of original discovery or priority. The new inverse-localization declaration is
a repository-derived composition of the checked source lemmas, not a claimed
independent external theorem.

The Challenge exposes the actual formulas for the parabolic distance, its open
and closed balls, the bounded/Hölder predicates, the combined `C^{0,α}`
predicate, and both reciprocal constants. It has seven deliberate theorem
holes and no definition holes. It makes no manifold, Hausdorff, or
sigma-compactness claim; the selected domain is arbitrary pseudo-metric
time-space.

## Nested-project intake paths

The package lives at `curvature/` inside the roadmap repository. The intended
repository-relative intake fields are:

- repository: `Arthur742Ramos/lean-poincare-formalization-plan`;
- branch: `dev/point4-campaign`;
- project directory: `curvature`;
- Comparator configuration: `curvature/comparator.json`;
- formalization metadata: `curvature/formalization.yaml`;
- license: the repository-root `LICENSE` file.

The accepted Submission 01, passed Submission 02, and accepted Submission 03
artifacts remain reproducible at their own immutable commits. This corrected
candidate supersedes the failed Submission 04 time-dependent surface and uses
a distinct parabolic-analysis Comparator theorem surface.

## Local checks

Run from this directory:

```sh
bash scripts/verify-palomar.sh
```

For the independent Comparator plus NanoDa replay on this macOS development
machine, use:

```sh
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh
```

The replay pins Comparator, Lean4Export, Landrun, and NanoDa by full commit.
Linux runs use the pinned Landrun sandbox directly.

## External status

This document records local preparation only. A Palomar submission requires a
fresh action for the final public commit, with the exact repository, full SHA,
project directory, Comparator path, metadata path, and authorization
relationship verified at submission time. Local checks do not imply hosted
mechanical verification, renderability, editorial review, registration, or
public indexing.
