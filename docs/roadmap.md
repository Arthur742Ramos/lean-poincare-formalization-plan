# Roadmap to the Poincaré conjecture

This roadmap follows Perelman's proof through Ricci flow with surgery. It is a
dependency-ordered research program, not a claim that the final theorem has
already been formalized.

For the verified state of each milestone, see [Current status](status.md). For
the dependency graph, see [Dependencies and execution order](dependencies.md).

## Completion standard

A milestone is complete only when its intended mathematics is proved in Lean.
Interfaces, axioms, placeholders, conditional theorem packages that assume the
main missing construction, and documentation-only scaffolding do not close a
milestone.

## Layer 1: foundational geometry

### 1. Riemannian curvature package

Develop covariant derivatives along vector fields, the raw curvature
commutator, bundled Riemann curvature, Ricci and scalar curvature, metric
compatibility, torsion-free connections, and Levi–Civita uniqueness.

**Current state:** proved in `curvature/`.

### 2. Curvature identities and existence

Prove Levi–Civita existence, sectional-curvature constructions, and the first
and second Bianchi identities, connected to the manifold API.

**Current state:** proved in `curvature/`.

### 3. Time-dependent geometric structures

Provide one-parameter families of metrics, connections, sections, curvature
quantities, and slice-wise Levi–Civita data so that evolving geometry can be
stated cleanly.

**Current state:** proved in `curvature/`.

## Layer 2: first Ricci-flow theorems

### 4. Ricci-flow local existence and uniqueness

Prove short-time existence and uniqueness of Ricci flow from general initial
data on a compact smooth manifold. The planned route is the Hamilton–DeTurck
argument: solve a strictly parabolic Ricci–DeTurck equation, construct the gauge
flow, and transport the result back to intrinsic Ricci flow.

**Current state:** open. The repository contains substantial proof-bearing
analytic, gauge-transport, special-case, and conditional infrastructure, but
not the unconditional theorem required by the completion audit. See the
[Point-4 plan](point4/README.md).

### 5. Evolution equations and maximum principles

Formalize evolution formulas for scalar curvature, Ricci curvature, the
curvature operator, and other natural quantities. Develop the parabolic maximum
principles needed for preservation, pinching, and monotonicity arguments.

**Current state:** future milestone; not unlocked by Point-4 scaffolding alone.

## Layer 3: singularity analysis

### 6. Distance distortion, comparison, and compactness

Develop length and distance control under evolving metrics, injectivity-radius
interfaces, compactness for sequences of Ricci flows, and blow-up and rescaling
machinery.

### 7. Perelman's reduced geometry

Define and analyze reduced length, reduced distance, reduced volume, and their
monotonicity properties.

### 8. Non-collapsing

Prove Perelman's no-local-collapsing theorem and package the quantitative
estimates needed for singularity analysis.

**Current state for milestones 6–8:** future. These depend on the first
Ricci-flow theorem layer.

## Layer 4: classification and surgery preparation

### 9. Ancient solutions in dimension three

Formalize the classification theory for noncollapsed ancient solutions that
arise as high-curvature limits.

### 10. Canonical neighborhoods and neck detection

Recognize necks, caps, and other canonical high-curvature regions with the
quantitative control required for surgery.

**Current state for milestones 9–10:** future. They depend on compactness and
non-collapsing.

## Layer 5: surgery and extinction

### 11. Ricci flow with surgery

Construct Ricci flow with surgery for the relevant compact three-manifolds,
including the parameter choices and continuation theorem.

### 12. Topological control of surgery

Formalize how neck cutting, capping, discarded components, and connected-sum
bookkeeping affect the underlying manifold.

### 13. Finite-time extinction

Prove finite-time extinction for the class of compact three-manifolds required
by the Poincaré argument.

**Current state for milestones 11–13:** future. This is the deepest downstream
analytic and topological layer.

## Layer 6: final corollaries

### 14. Topological Poincaré corollary

Deduce that a closed simply connected topological three-manifold is homeomorphic
to the three-sphere.

### 15. Smooth Poincaré corollary

Bridge the three-dimensional topological result to the statement that a smooth
closed simply connected three-manifold is diffeomorphic to `S³`.

**Current state for milestones 14–15:** future final endpoints.

## Scale and project boundaries

The roadmap is expected to require roughly 11–16 substantial formalization
projects. Milestones 1–2 are reusable library work; milestones 3–5 are naturally
theorem-package projects; the topological and smooth endpoints should remain
separate until their actual Lean dependencies justify combining them.

The milestone count is not a percentage-of-effort estimate. Although three of
fifteen milestones are proved, the major quasilinear PDE, singularity-analysis,
surgery, and extinction arguments remain ahead.
