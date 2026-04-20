# Curvature Package Milestone

This package now contains a real Lean/mathlib bootstrap for project 1 of the roadmap.

## Landed in code

- a Lean package with a pinned toolchain and a mathlib dependency
- `CovariantDerivative.along`, packaging the section `∇_X σ`
- algebraic lemmas for the vector-field slot of `∇_X σ`
- pointwise Leibniz/additivity lemmas in the section slot
- a smoothness theorem showing that `∇_X σ` has the expected regularity
- `CovariantDerivative.curvatureAux`, the raw curvature commutator
- alternating identities `R_aux(X, Y) = -R_aux(Y, X)` and `R_aux(X, X) = 0`

## Not landed yet

- tensoriality of the raw curvature operator in all slots
- the bundled curvature tensor as a multilinear map on fibres
- Levi-Civita existence and uniqueness
- metric compatibility as a reusable Lean interface
- Riemann, Ricci, scalar, and sectional curvature
- Bianchi identities

## Why this is still a meaningful first milestone

The current code pins down the exact interface where the existing mathlib covariant-derivative and
vector-field libraries meet the future curvature development. It removes the ambiguity about where
the next proofs have to land and gives the project a compilable starting boundary instead of just a
research note.
