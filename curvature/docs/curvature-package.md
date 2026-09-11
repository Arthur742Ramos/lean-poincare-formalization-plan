# Curvature package map

This page maps capability groups to their source locations. The authoritative
roadmap state is maintained in [`../../docs/status.md`](../../docs/status.md).

## Foundational geometry: proved

The public package exposes:

- covariant derivatives along vector fields;
- raw and bundled curvature;
- Ricci, scalar, and sectional curvature;
- metric compatibility, torsion-free connections, and Levi–Civita uniqueness
  and existence;
- first, second, and contracted Bianchi identities;
- time-dependent sections, metrics, connections, and curvature quantities.

The main source areas are:

- `Geometry/Manifold/VectorBundle/CovariantDerivative/`
- `Geometry/Manifold/VectorBundle/CovariantDerivative/Curvature/`
- `Geometry/Manifold/VectorBundle/CovariantDerivative/TimeDependent.lean`

Together these close roadmap milestones 1–3 under the repository's proof-only
standard.

## Supporting analytic infrastructure: proved components

The package also contains proved components for:

- continuous-section models and smooth approximation;
- the open positive-definite metric locus;
- Ricci-flow and Ricci–DeTurck statement boundaries;
- gauge transport and gauge-reduction identities;
- parabolic Hölder and higher-function-space vocabulary;
- local-frame and matrix estimates;
- model Picard and mild-evolution results;
- frozen affine Ricci–DeTurck evolution and operator-exponential solutions.

These modules are concentrated under:

- `Geometry/Manifold/VectorBundle/`
- `Geometry/Manifold/RicciFlow/`
- `Geometry/Manifold/RicciFlow/AnalyticPDE/`

## Open boundary

The general compact-manifold theorem named by
[`../scripts/point4_target.txt`](../scripts/point4_target.txt) has not been
constructed. Consequently, the supporting modules above do not close roadmap
milestone 4.

See [`../../docs/point4/README.md`](../../docs/point4/README.md) for the current
integration workstreams and completion gate. The former long package inventory
remains available in Git history.
