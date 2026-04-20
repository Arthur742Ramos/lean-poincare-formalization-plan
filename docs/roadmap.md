# AFM-Scale Roadmap

This document breaks the Lean formalization of the Poincare Conjecture into
granular deliverables where each item would plausibly stand on its own as a
substantial formalization paper.

The intended proof route is:

1. build enough Riemannian and geometric-analysis infrastructure in Lean
2. formalize Ricci flow and its core estimates
3. formalize Perelman's monotonic quantities and non-collapsing theory
4. formalize Ricci flow with surgery
5. derive finite-time extinction and the 3D Poincare statement

## Candidate paper-scale projects

### 1. Curvature package

Formalize the foundational differential-geometry layer needed for Ricci flow:

- Levi-Civita connection
- Riemann curvature tensor
- Ricci curvature
- scalar curvature
- first and second Bianchi identities
- compatibility statements tying all of this back to the manifold API

Why this is paper-worthy:
it converts a broad patch of standard Riemannian geometry into reusable Lean
infrastructure and becomes a dependency for almost everything else in the
program.

### 2. Time-dependent geometric structures

Formalize one-parameter families of metrics, connections, tensors, and
differential operators on a manifold.

Why this is paper-worthy:
Ricci flow is a PDE on evolving metrics, so this is the layer that lets Lean
talk coherently about geometry at time `t` and compare it across times.

### 3. Ricci-flow local existence and uniqueness

Formalize a first existence theorem for Ricci flow on compact manifolds,
together with uniqueness in the appropriate setting.

Why this is paper-worthy:
this is the first theorem package that turns the geometric infrastructure into
genuine geometric analysis.

### 4. Evolution equations and parabolic maximum principles

Formalize the evolution formulas for scalar curvature, Ricci curvature, and
other natural quantities under Ricci flow, together with the maximum-principle
arguments used to control them.

Why this is paper-worthy:
this is the engine behind many later monotonicity and pinching arguments.

### 5. Distance distortion, comparison, and compactness toolkit

Build the reusable analytic toolkit around evolving metrics:

- control of lengths and distances under the flow
- injectivity-radius style interfaces where needed
- compactness principles for sequences of Ricci flows
- blow-up and rescaling machinery

Why this is paper-worthy:
this creates the language for passing to singularity models and ancient limits.

### 6. Perelman's `L`-geometry

Formalize Perelman's reduced length, reduced distance, and reduced volume.

Why this is paper-worthy:
these are not just definitions; they are central conceptual inventions in the
proof and would produce a distinct formalized theory with independent value.

### 7. Non-collapsing theorems

Formalize Perelman's no-local-collapsing theory and the estimates needed to use
it in the singularity analysis.

Why this is paper-worthy:
this is one of the signature results of the proof and a major benchmark for any
proof assistant formalization of geometric analysis.

### 8. Ancient-solution theory in dimension 3

Formalize the classification results for non-collapsed ancient solutions that
feed into the description of high-curvature regions in dimension 3.

Why this is paper-worthy:
the theory of ancient solutions is already a major theorem cluster even before
it is connected back to surgery.

### 9. Canonical-neighborhood and neck-detection machinery

Formalize the local geometric recognition results that identify necks, caps, and
other canonical neighborhoods in high-curvature regions.

Why this is paper-worthy:
this is the interface between the singularity analysis and the actual surgery
construction.

### 10. Ricci flow with surgery

Formalize the existence of Ricci flow with surgery for the relevant class of
compact 3-manifolds.

Why this is paper-worthy:
this is a landmark result even in isolation and is one of the clearest natural
paper boundaries in the whole program.

### 11. Topological control of surgery

Formalize the effect of surgery on the topology of the manifold and the precise
bookkeeping that lets the flow continue while preserving the classification
target.

Why this is paper-worthy:
the surgery theorem is not useful without a mathematically precise bridge back
to topology.

### 12. Finite-time extinction

Formalize the finite-time extinction theorem for the relevant compact
3-manifolds.

Why this is paper-worthy:
this is the main end-stage theorem in the Ricci-flow-with-surgery route and one
of the cleanest major milestones before the final corollary.

### 13. Topological Poincare corollary

Extract from the extinction theorem the statement that a closed simply connected
3-manifold is homeomorphic to the 3-sphere.

Why this is paper-worthy:
even if short on paper, in Lean this requires careful packaging of everything
above into a final topological theorem with a clean interface to existing
topology APIs.

### 14. Smooth Poincare corollary

Bridge from the topological 3-dimensional statement to the smooth statement that
a smooth closed simply connected 3-manifold is diffeomorphic to `S^3`.

Why this is paper-worthy:
this final bridge is mathematically distinct from the analytic part of the
program and would likely deserve its own paper-scale treatment in Lean.

## What seems most urgent

If someone wanted to start now, the most leverage likely comes from:

1. the curvature package
2. time-dependent geometric structures
3. Ricci-flow existence and uniqueness
4. evolution equations and maximum principles

Without those, later Perelman-specific projects have nowhere to land.
