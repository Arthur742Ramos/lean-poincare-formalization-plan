# PoincareCurvature

This subproject is the first concrete Lean/mathlib implementation milestone of
the broader Poincare Conjecture roadmap in the parent repository.

## What is here

- a Lean 4 + mathlib package pinned to a working toolchain
- `CovariantDerivative.along`, packaging the section `∇_X σ`
- `CovariantDerivative.contMDiff_along`, a first regularity theorem for that
  operation
- `CovariantDerivative.curvatureAux`, the raw curvature commutator
- alternating identities for the raw curvature commutator

## What is not here yet

- the bundled curvature tensor as a fibrewise multilinear map
- Levi-Civita existence and uniqueness
- metric compatibility
- Riemann, Ricci, scalar, or sectional curvature
- Bianchi identities

## Build

From this directory:

```powershell
lake +leanprover/lean4:v4.29.1 build PoincareCurvature
```
