# PoincareCurvature

This subproject now covers the connection-theoretic package together with the
bundled curvature and Ricci/scalar contraction layers of the broader Poincare
Conjecture roadmap in the parent repository.

## What is here

- a Lean 4 + mathlib package pinned to a working toolchain
- `CovariantDerivative.along`, packaging the section `∇_X σ`
- `CovariantDerivative.contMDiff_along`, a first regularity theorem for that
  operation
- `CovariantDerivative.curvatureAux`, the raw curvature commutator
- alternating identities for the raw curvature commutator
- `CovariantDerivative.curvatureTensor`, packaging curvature fibrewise as a
  multilinear map
- `CovariantDerivative.ricciCurvature` and `CovariantDerivative.scalarCurvature`
  on the tangent bundle
- `CovariantDerivative.IsMetricCompatible`, a reusable metric-compatibility
  interface for Riemannian vector bundles
- tangent-bundle predicates `CovariantDerivative.IsTorsionFree` and
  `CovariantDerivative.IsLeviCivita`
- a Levi-Civita uniqueness theorem at the current mathlib boundary:
  if two affine connections are torsion-free and metric-compatible, then their
  difference one-form vanishes

## Follow-on point 2: curvature identities and existence

The next roadmap point starts from this package and adds:

- Levi-Civita existence
- sectional curvature
- Bianchi identities

## Build

From this directory:

```powershell
lake +leanprover/lean4:v4.29.1 build PoincareCurvature
```
