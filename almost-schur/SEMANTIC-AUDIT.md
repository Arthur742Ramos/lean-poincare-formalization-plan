# Almost-Schur entry audit — 7 September 2026

## Defects found and repaired

The earlier Comparator configuration selected only cancellation and
equality-bookkeeping lemmas about real numbers. Its successful verification
did not independently verify the advertised geometric statement. Merely
importing or exporting the manifold endpoints from Solution did not select
them for comparison.

The repaired entry selects `AlmostSchurEntry.Geometry.almostSchur`. Its
Mathlib-only Challenge explicitly defines curvature, Ricci, scalar curvature,
the squared trace-free tensor norm, volume, average and the geometric
proposition. All nine definitions are selected alongside the theorem.

The bibliography incorrectly named Pierre De Lellis and gave volume 42 (2011).
The [author's publication record](https://www.math.ias.edu/delellis/node/199)
and [published paper](https://doi.org/10.1007/s00526-011-0413-z) identify
Camillo De Lellis and Peter M. Topping, volume 43 (2012), pages 347–354.
README, structured metadata and provenance now agree. The source is Theorem
1.1, including its Einstein equality case; optimality is not formalized here.

An obsolete module comment said smooth scalar-curvature forcing remained an
input. The final theorem already derives it via `smooth_coordinate_forcing`;
the comment now describes that proof accurately.

## Meaning of the selected statement

On a nonempty connected compact smooth boundaryless Riemannian manifold, the
theorem constructs a metric-compatible torsion-free connection with checked
regularity and a finite positive measure satisfying the chart metric-density
formula. For these geometric objects, nonnegative Ricci curvature and
dimension greater than two imply the almost-Schur bound and equality exactly
when `Ric(u,v) = (R/n) inner(u,v)` everywhere.

These constructions occur outside the implication's hypotheses. The
Challenge assumes neither existence of a Poisson solution nor a Bianchi,
Bochner, integration, Cauchy–Schwarz or target almost-Schur identity.
Compactness, connectedness and the other manifold hypotheses are explicit in
the selected theorem signature. Haar normalization fixes coordinate scale;
the measure is not normalized to total mass one.

The proof in `AlmostSchur/GeometryComparison.lean` checks the following
identifications against the complete implementation:

| Independent definition | Proved identification |
| --- | --- |
| Covariant-derivative commutator | `curvature_eq`: bundled curvature tensor |
| Orthonormal Ricci and scalar contractions | `ricci_eq`, `scalar_eq` |
| Sum of squares of trace-free Ricci components | `traceFreeRicciSq_eq`: intrinsic Hilbert–Schmidt square |
| Chart Gram-determinant density | `riemannianVolume_spec`: constructed volume |
| Tensor Einstein condition | `einstein_iff`: vanishing raised trace-free operator |

The witness theorem then invokes `almostSchur_bound_complete` and
`almostSchur_equality_iff`. The canonical smooth-extension definition agrees
definitionally with the attributed curvature implementation; it does not
assume an unidentified curvature tensor.

## Regression and verification boundaries

`check-entry-regressions.py` rejects the previous algebra-only selection,
omission of a geometric definition, the incorrect source author, and failure
to list the selected geometric theorem in structured main results.
`check-challenge-boundary.py` compiles the Challenge with only dependency
libraries and checks that a candidate-library import fails.
`check-axioms.py` audits implementation declarations, selected declarations
and vendored endpoints transitively, allowing only the standard three axioms.
Comparator/NanoDa checks statement/definition agreement and the selected proof.

The complete local and hosted evidence is distinguished in VERIFICATION.md.
No independent human expert review or source-author endorsement is recorded.
No Hausdorff-volume identification, optimality theorem, space-form
classification or new mathematical priority is claimed. The two earlier
artifact SHAs are historical; they must not be submitted as this repaired entry.
