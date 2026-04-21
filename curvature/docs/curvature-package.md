# Curvature package status

This package now contains the connection-theoretic layer together with the
bundled curvature tensor and its Ricci/scalar contractions.

## Landed in code

- a Lean package with a pinned toolchain and a mathlib dependency
- `CovariantDerivative.along`, packaging the section `∇_X σ`
- algebraic lemmas for the vector-field slot of `∇_X σ`
- pointwise Leibniz/additivity lemmas in the section slot
- a smoothness theorem showing that `∇_X σ` has the expected regularity
- `CovariantDerivative.curvatureAux`, the raw curvature commutator
- alternating identities `R_aux(X, Y) = -R_aux(Y, X)` and `R_aux(X, X) = 0`
- `CovariantDerivative.curvatureTensor`, packaging curvature fibrewise as a
  multilinear map
- `CovariantDerivative.ricciCurvature` and `CovariantDerivative.scalarCurvature`
  on the tangent bundle
- `CovariantDerivative.IsMetricCompatible`, phrased for Riemannian vector bundles
- tangent-bundle predicates `CovariantDerivative.IsTorsionFree` and
  `CovariantDerivative.IsLeviCivita`
- skew-adjointness of the difference of two metric-compatible affine connections
- symmetry of the difference of two torsion-free affine connections
- uniqueness of Levi-Civita connections in the current representation, packaged
  as `cov.difference cov' = 0`

## Follow-on point 2: curvature identities and existence

The next roadmap point starts from this package and adds:

- Levi-Civita existence
- sectional curvature
- Bianchi identities

## Current boundary

The tensorial curvature layer and its Ricci/scalar contractions are now part of
the package itself, so the remaining follow-on work starts at sectional
curvature, Levi-Civita existence, and the Bianchi identities.
