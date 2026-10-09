# Actual coordinate inverse and Christoffel derivatives

This supporting unit starts from the actual coordinate-jet milestone at
`90bd24af2652bfb6781ffbd698f4f997b41d3ade`. It reuses the existing
`MatrixInverseDerivative` and `MatrixSmoothness` proofs and preserves their
source notices. It does not change a submission identity or register an intake.

## Proof and dependency map

`Analysis/LocalMatrixInverseDerivative.lean` localizes the proved global
`hasDerivAt_nonsing_inv_entry` to `(A t).det ≠ 0`. The original curve's
entrywise derivative certificates give determinant continuity. Nonvanishing
therefore holds eventually near t. The replacement curve agrees with A wherever
its determinant is nonzero and equals A(t) elsewhere. It is globally invertible
and locally equal to A. Derivative congruence transfers both the original curve
and its actual inverse to the global theorem. No inverse-derivative certificate
and no global invertibility premise are required.

`Analysis/CoordinateMatrixConnection.lean` then derives actual coordinate
calculus identities. Its project dependencies are only generic matrix calculus
and `CoordinateMatrixJet`; it imports no tensor-heat or `HeatKernel1D` chain.
The API used is the pinned Mathlib calculus at revision
`db584cd6d46c92f209a44c0f1c829460d327499d`:

- `ContinuousAt.eventually_ne` and `HasDerivAt.congr_of_eventuallyEq` localize
  invertibility and derivative data
- `MatrixSmoothness.contDiff_det` and `.contDiff_adjugate`, composed with actual
  field differentiability, derive inverse-entry differentiability
- `HasFDerivAt.comp_hasDerivAt_of_eq` restricts genuine Fréchet derivatives to
  the actual affine coordinate line `x + t • Pi.single m 1`
- `HasDerivAt.unique` identifies the inverse directional derivative with the
  proved matrix-curve formula
- `HasFDerivAt.fun_sum`, `.mul`, `.add`, `.sub`, and `.const_mul` differentiate
  the actual Christoffel expression using genuine C²-produced first slots

The final `CoordinateJetConnectionDerivative.lean` adapter imports the actual
jet/principal milestone and identifies both algebraic jet derivative formulas
with these genuine Fréchet derivatives. This adapter inherits the larger
analytic dependency chain, but the generic calculus proof does not.

## Actual formulas and hypotheses

The inverse is always the explicitly typed nonsingular matrix inverse
`(show Matrix (Fin d) (Fin d) ℝ from g x)⁻¹`.

For the actual field g, the inverse coordinate derivative is
`-g(x)⁻¹ * first(g,x,m) * g(x)⁻¹`. The explicit double-sum theorem proves this
is exactly `-Σab g^{ia} (∂m g_ab) g^{bk}`. The adapter then identifies it with
`derivInvMetricOfJet (coordinateJet g x)`.

The actual coordinate Christoffel expression is
`Γ^k_ij(x) = (1/2) Σl g^{kl}(x) (∂i g_jl + ∂j g_il − ∂l g_ij)`.
Differentiation gives both product-rule contributions: the inverse derivative
multiplying the first-derivative combination and the inverse multiplying the
actual second-derivative combination. The adapter identifies this result with
`derivChristoffelOfJet (coordinateJet g x)`.

Every derivative theorem assumes an explicit open coordinate domain U,
`ContDiffOn ℝ 2 g U`, membership x∈U, and invertibility at x. It assumes neither
inverse derivative data nor global invertibility. Symmetry is not needed for
these differentiation identities; the earlier principal cancellation obtains
its additional symmetries from a symmetric actual field.

## Verification and remaining boundary

Exact Lean-4.33 verification is pending. The dedicated
`.github/workflows/point4-coordinate-connection.yml` first builds the localized
inverse theorem, then the generic coordinate derivative module and its jet
adapter, checks fourteen selected axiom surfaces, and runs the unchanged
full-package completion audit.

These coordinate identities do not yet identify the expressions with the
manifold Levi--Civita connection, Ricci tensor, or Lie derivative. Producing the
varying fixed-background first jet, extracting C² chart fields from metric data,
frozen heat-generator identification, nonlinear estimates and quasilinear PDE
existence/uniqueness remain separate obligations.

The canonical target and completion auditor are unchanged. Point 4 remains
**OPEN**.
