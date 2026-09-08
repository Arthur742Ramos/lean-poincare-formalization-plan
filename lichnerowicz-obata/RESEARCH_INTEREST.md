# Selected theorem and research-interest case

The selected result connects a local curvature lower bound, a global spectral
quantity, and a complete geometric classification. Its coefficient is sharp,
and the equality conclusion determines the whole manifold, not just one
tensor or one integral. This is the classical Lichnerowicz--Obata theorem;
no mathematical originality or first-formalization priority is claimed.

## Why this is distinct from the inherited result

The earlier almost-Schur entry controls scalar-curvature variance and
characterizes its Einstein equality case. This entry instead proves first
eigenvalue attainment and a global round-sphere characterization. Reusing
its analytic and curvature infrastructure does not provide the missing
global sphere map, smooth pole extensions, or sphere converse. Those are
proved in the new subproject, with the inherited source frozen and attributed.

## Exact selected proof obligations

| Requirement | Authoritative Lean evidence |
| --- | --- |
| Positive first eigenvalue, attained smoothly and minimal | `LichnerowiczObata.exists_first_smooth_eigenvalue` |
| Sharp Ricci-to-eigenvalue estimate | `LichnerowiczObata.eigenvalue_lower_bound` |
| Equality forces the actual covariant Hessian equation | `LichnerowiczObata.hessian_equation_of_extremal_eigenfunction` |
| Global sphere diffeomorphism and metric at both poles | `LichnerowiczObata.obata_round_metric_diffeomorph` |
| Sphere converse with an actual nonconstant eigenfunction | `LichnerowiczObata.round_metric_diffeomorph_exists_extremal_eigenfunction` |
| Standard Euclidean target, not an auxiliary ambient choice | `LichnerowiczObata.exists_standard_round_metric_diffeomorph` |
| Entire theorem, with an independently constructed connection | `LichnerowiczObataEntry.Geometry.lichnerowiczObata` |

The table gives fully qualified declaration names. The Comparator selects
the last row and every independent geometric definition on which its type depends.

## Source fidelity and review limits

The source alignment is Lichnerowicz's 1958 bound and Obata's 1962
[Theorem A and Theorems 1--2](https://doi.org/10.2969/jmsj/01430333).
The selected theorem concerns closed manifolds; it does not advertise
Obata's broader noncompact-complete Hessian theorem. The source's Laplacian
sign is translated explicitly in `PROVENANCE.md`.

The Challenge does not assume a Bochner identity, eigenfunction existence,
Hessian equation, geodesic comparison, global sphere map, or connection
preservation. It states the geometric objects with Mathlib-only imports.
The Solution discharges every comparison. Its round metric is an exact
tangent inner-product identity under a smooth diffeomorphism, not a claim
that ambient chordal distance equals intrinsic Riemannian distance.

Kernel checks and source alignment support a substantive classical
formalization candidate. They are not independent human review, source-author
endorsement, a registry decision, or authorization to publish an intake.
