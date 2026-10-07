# Actual C² coordinate matrix jets

## Dependency and statement map

The generic file `curvature/PoincareCurvature/Analysis/CoordinateMatrixJet.lean`
imports only Mathlib calculus. It has no project dependency and in particular
no `HeatKernel1D` dependency. The matrix-entry space is the explicit finite Pi
space `Fin d → Fin d → ℝ`, equipped with its usual sup norm, as in the existing
`MatrixSmoothness` file. The coordinate domain is `Fin n → ℝ`.

The pinned Mathlib revision is
`db584cd6d46c92f209a44c0f1c829460d327499d` (Lean 4.33). The source API map is:

- `ContDiffOn.contDiffAt` with `IsOpen.mem_nhds` turns actual domain C²
  regularity into regularity at the selected interior point
- `contDiffAt_pi` twice gives C² regularity of each actual matrix component
- `ContDiffAt.differentiableAt` and `ContDiffAt.fderiv_right` give genuine first
  and second Fréchet derivative existence certificates
- `fderiv_apply` twice identifies the componentwise first slot with the full
  matrix-entry differential evaluated on a coordinate vector
- `HasFDerivAt.clm_apply` with a constant coordinate vector gives a genuine
  derivative certificate for the produced first-coordinate component
- `ContDiffAt.isSymmSndFDerivAt` and `IsSymmSndFDerivAt.eq` give Schwarz
  interchange of the two derivative slots
- `Filter.EventuallyEq.fderiv` and `.fderiv_eq` differentiate actual local
  component equality twice to give tensor-slot interchange

No alternate source revision is the final verification authority.

## Actual slots and regularity boundary

For a field `g` and `e_a = Pi.single a 1`, define

- first slot: `first g x a i k = fderiv ℝ (fun y => g y i k) x e_a`
- second slot: `second g x a b i k =
  fderiv ℝ (fderiv ℝ (fun y => g y i k)) x e_a e_b`

The derivative order is outer direction `a`, inner direction `b`.
`fderiv_first_apply` proves that differentiating the actual first slot in
direction `a` gives precisely the second slot with directions `(a,b)`.
The first slot also agrees with `(fderiv ℝ g x e_a) i k`.

The existence theorems assume an explicit open domain `U`, `x ∈ U`, and
`ContDiffOn ℝ 2 g U`. These ensure the total `fderiv` readouts really are
ordinary derivatives at the selected point. There is no claim at a boundary
point of a nonopen domain, and no assumption of a preconstructed jet or
holonomy certificate.

Matrix symmetry is the actual field identity
`∀ y ∈ U, ∀ i k, g y i k = g y k i`. This local identity, differentiated twice,
gives tensor-slot Hessian symmetry. C² regularity separately supplies
Schwarz derivative-slot symmetry. The congruence theorem alone does not assert
derivative existence without the regularity hypotheses.

## Principal reaction adapter

`CoordinateJetPrincipalRemainder.lean` assembles these actual derivative
readouts into the existing `Jet2` carrier as `coordinateJet`. Its three
reaction corollaries discharge every metric-value and Hessian-symmetry input
of the previously proved algebraic principal splits from the actual symmetric
C² coordinate field. The determinant condition at `x` is retained separately.

The background-first-jet slots are still displayed explicitly. The corrected
reaction preserves the two proven Lie-derivative background terms and their
negative sign. The frozen coefficient is arbitrary and has not been identified
with a particular Banach-space heat generator.

## Verification and remaining obligations

Exact Lean-4.33 compilation is pending. The dedicated workflow
`.github/workflows/point4-coordinate-jet.yml` compiles the Mathlib-only calculus
producer first, then its actual-jet principal adapter, checks fourteen selected
axiom surfaces, and runs the unchanged full-package Point-4 audit.

This milestone produces real coordinate derivatives, but the following still
require proofs:

- extracting a C² coordinate metric field from actual manifold metric data
- identifying the inverse-metric and Christoffel derivative formulas with
  derivatives of those actual coordinate expressions
- producing the varying fixed-background Christoffel first derivatives
- identifying the corrected jet reaction with manifold Ricci and Lie derivative
- identifying the frozen contraction with the selected heat generator in the
  same chart/frame, including lower-order frame contributions
- positive-metric invariant regions and nonlinear quasilinear PDE existence
  and uniqueness

The canonical target and completion auditor are unchanged. Point 4 remains
**OPEN**.
