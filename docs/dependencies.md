# Dependencies and Suggested Order

This file turns the roadmap into a rough dependency graph.

## Layer 0: existing manifold baseline

Assume the ambient Lean environment already has enough support for:

- smooth manifolds
- tangent bundles and sections
- Riemannian metrics
- covariant derivatives and related manifold abstractions

This layer is not the project, but it is the substrate.

## Layer 1: foundational geometry

These are the first major projects to land:

1. Riemannian curvature package
2. curvature identities and existence package
3. time-dependent geometric structures

The first three projects should be designed as library infrastructure, not as
one-off theorem proofs.

Current repo status:
point 1 now lives in `curvature/`; the remaining Layer 1 work is point 2 plus
time-dependent geometric structures.

## Layer 2: first Ricci-flow theorems

Once Layer 1 exists:

4. Ricci-flow local existence and uniqueness
5. evolution equations and parabolic maximum principles

These unlock the first serious Ricci-flow API.

## Layer 3: singularity-analysis toolkit

Once Layer 2 exists:

6. distance distortion, comparison, and compactness toolkit
7. Perelman's `L`-geometry
8. non-collapsing theorems

This is where the program stops looking like generic differential geometry and
starts looking specifically like Perelman's proof.

## Layer 4: classification and surgery preparation

Once Layer 3 exists:

9. ancient-solution theory in dimension 3
10. canonical-neighborhood and neck-detection machinery

These results should prepare the exact hypotheses needed by surgery.

## Layer 5: surgery and extinction

Once Layer 4 exists:

11. Ricci flow with surgery
12. topological control of surgery
13. finite-time extinction

At this point, the hard analytic core is effectively complete.

## Layer 6: final corollaries

Once Layer 5 exists:

14. topological Poincare corollary
15. smooth Poincare corollary

These are the final endpoints of the roadmap.

## Suggested project strategy

- Treat Layers 1 and 2 as reusable mathlib-facing library work.
- Treat Layers 3 through 5 as theorem-package papers.
- Keep the topological and smooth endpoints separate unless a later design
  review shows they genuinely collapse into one formalization artifact.

## Rough scaling intuition

This roadmap is not a one-paper project.

A realistic first-pass estimate is that a complete public Lean formalization of
the 3D Poincare Conjecture would decompose into roughly 11 to 16 substantial
projects, many of which would already be natural AFM submissions even before the
final theorem is reached.
