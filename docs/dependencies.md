# Dependencies and execution order

The roadmap is organized into six mathematical layers above Mathlib's existing
smooth-manifold baseline. A later layer may be explored early, but it cannot be
reported complete until its stated dependencies are proved or explicitly
replaced by another formal route.

For detailed milestone statements, see [the roadmap](roadmap.md). For verified
completion state, see [current status](status.md).

## Critical path

```text
Mathlib manifold baseline
  ↓
Layer 1: foundational geometry (milestones 1–3) — PROVED
  ↓
Layer 2: Ricci-flow foundations (milestones 4–5) — OPEN AT 4
  ↓
Layer 3: singularity analysis (milestones 6–8)
  ↓
Layer 4: ancient solutions and canonical neighborhoods (9–10)
  ↓
Layer 5: surgery, topology, and extinction (11–13)
  ↓
Layer 6: topological and smooth Poincaré corollaries (14–15)
```

## Layer 0: Mathlib baseline

The project builds on smooth manifolds, tangent bundles and sections,
Riemannian metrics, differentiation, integration, topology, and functional
analysis from Mathlib. Missing API at this level should normally become
reusable library infrastructure rather than a one-off local encoding.

## Layer 1: foundational geometry

Milestones 1–3 provide static curvature, curvature identities and Levi–Civita
existence, and time-dependent geometric structures. They are proved in the
`curvature/` project and form the current reusable foundation.

## Layer 2: Ricci-flow foundations

Milestone 4 must produce genuine short-time existence and uniqueness on compact
manifolds. Milestone 5 then develops evolution equations and maximum principles
on those solutions.

This is the current frontier. Conditional Ricci–DeTurck bridges and special-case
solutions do not unlock the layer by themselves. See the
[Point-4 plan](point4/README.md).

## Layer 3: singularity analysis

Milestones 6–8 combine distance distortion and compactness, Perelman's reduced
geometry, and non-collapsing. Definitions and isolated estimates can proceed in
parallel, while the main theorems consume the solution and evolution APIs from
Layer 2.

## Layer 4: classification and surgery preparation

Milestones 9–10 classify relevant noncollapsed ancient solutions in dimension
three and derive canonical-neighborhood and neck-detection results. This layer
consumes blow-up compactness and non-collapsing.

## Layer 5: surgery and extinction

Milestones 11–13 construct Ricci flow with surgery, control its topological
effect, and prove finite-time extinction. Analytic surgery construction and
topological bookkeeping are separate workstreams that meet at extinction.

## Layer 6: final corollaries

Milestone 14 extracts the topological Poincaré statement. Milestone 15 supplies
the distinct three-dimensional bridge to the smooth statement.

## Parallelization guidance

Useful parallel work that does not overstate dependency completion includes:

- general-purpose parabolic analysis and maximum-principle infrastructure;
- compactness, metric-comparison, and three-manifold topology APIs;
- exact definitions and elementary properties for reduced geometry;
- packaging proved intermediate theorem clusters as independent library or
  publication artifacts.

Every such contribution should name the theorem it proves and the assumptions
it retains. It should not claim to close a downstream milestone merely because
its interface has been designed.
