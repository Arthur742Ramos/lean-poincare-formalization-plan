# Submission 04 contribution and oversight record

This document records preparation of the corrected Palomar surface in the
public repository `Arthur742Ramos/lean-poincare-formalization-plan`, branch
`dev/point4-campaign`, project directory `curvature/`. The submitted metadata
pins this document to an immutable public commit that contains this exact
record.

## Mathematical source and origin

The selected parabolic distance, ball/localization, Hölder closure, pullback,
and reciprocal estimates are proved in
`PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/ParabolicHolder.lean`.
The exact finite-cover inverse-localization statement is proved in
`PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/Parabolic/InverseLocalization.lean`.

The parabolic distance and its scaling identity are standard anisotropic
parabolic analysis: time has weight two and space has weight one. The compact
finite-cover, pullback, Hölder, and reciprocal statements are likewise
standard reusable estimates. The final inverse-localization declaration is a
repository-derived composition: it first globalizes the three local controls
and then applies the explicit reciprocal-difference estimate. It is not being
presented as an independently discovered theorem, an adaptation with a new
priority claim, or an external result whose provenance is being obscured.
The package is a checked formalization/proof-engineering contribution for the
analytic interface used in geometric PDE chart estimates. It makes no claim
about Ricci-flow existence, arbitrary manifolds, or a new mathematical result.

## Agent contribution

GPT-5 Codex materially performed the following preparation work:

- audited the failed time-dependent surface and the parabolic source APIs;
- selected the corrected parabolic scaling/localization/inverse-stability
  boundary and rewrote the Challenge/Solution declarations;
- exposed actual Challenge formulas, removed the Ricci/scalar definition
  holes, added the finite-cover inverse-localization composition, and updated
  the Comparator surface;
- repaired the Lean 4.33 compatibility points required by the selected source
  closure, updated the repository verifier, and prepared the Palomar and
  portfolio documentation; and
- ran the Lean, source-closure, metadata, and independent Comparator/NanoDa
  checks needed for reproducible packaging.

The agent did not decide authorship, source priority, or mathematical novelty.
It did not convert this package into a claim about a time-dependent PDE,
Ricci-flow existence, or a first presentation of the underlying estimates.

## Human authorship and oversight

The recorded human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. Human authors selected and approved the corrected
theorem family, author list, source relationship, scope limits, and public
artifact. The responsible maintainer reviewed the source selection and
repository diff, authorized the public push, and retains responsibility for
the Palomar submission and any later publication action. Human oversight
includes review of the mathematical boundary and the exact immutable artifact;
Lean kernel elaboration and the independent pinned Comparator/NanoDa replay
check formal consistency and reproducibility, not authorship or novelty.

## Artifact boundary

`Challenge.lean` imports only Mathlib and has seven deliberate theorem holes.
Its selected definitions have actual bodies: the parabolic distance, open and
closed balls, bounded/Hölder predicates, combined `C^{0,α}` predicate, and the
two displayed reciprocal constants. There are no definition holes. `Solution.lean`
imports the checked PoincareCurvature parabolic source modules and supplies the
seven proved wrappers. The final public commit and external Palomar status are
recorded separately; local preparation is not itself a submission or an
acceptance claim.
