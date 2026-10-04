# Actual corrected coordinate Ricci--DeTurck spatial operator

This supporting unit builds on the actual coordinate inverse/Christoffel
producer at `362b3a666bacf2d36b26219d0d91f6aa3ab54726`. It preserves the
existing proof and contributor notices. It neither creates nor registers a
formalization intake.

## Actual differentiation and dependency map

`Analysis/CoordinateMatrixOperator.lean` imports only
`Analysis/CoordinateMatrixConnection.lean`. Its generic calculus closure
contains no tensor-heat or `HeatKernel1D` dependency. The matrix field is an
explicit finite Pi space, and the inverse is the previously defined,
explicitly Matrix-typed nonsingular inverse.

For a real coordinate domain U, a metric-coefficient field g and a background
coefficient array B, the new definitions are:

- `backgroundFirst B x m k a b`: the component Fréchet differential of B at x,
  applied to the standard coordinate vector in direction m
- `deTurck g B x k`: the positive conventional vector
  `Σab gInv(x)ab (Γg(x)kab − B(x)kab)`
- `deTurckFirst g B x m k`: the component Fréchet differential of that actual
  vector, applied to the standard coordinate vector
- `coordinateRicci g x i j`: the conventional coordinate Ricci expression
  from actual Γg and actual component Fréchet differentials of Γg
- `coordinateLie g B x i j`: the three conventional coordinate Lie terms,
  using actual g, its actual first differential, W and its actual differential
- `coordinateRD`: `−2 coordinateRicci + coordinateLie`

Open-domain C¹ regularity of B supplies actual component
`HasFDerivAt` certificates via `ContDiffAt.differentiableAt` and finite Pi
projection. C² regularity of g and pointwise invertibility supply the already
proved actual inverse and Christoffel derivative certificates.
`HasFDerivAt.fun_sum`, `.mul` and `.sub` differentiate the actual W expression.
The resulting proved formula retains both product contributions:

`∂m Wk = Σab [(∂m gInvab)(Γgkab − Bkab) + gInvab(∂m Γgkab − ∂m Bkab)]`.

The background derivative has negative sign. No inverse, Christoffel or
background derivative formula is supplied as an assumption. The `fderiv`
readouts are total definitions, and their interpretation as actual derivatives
is justified by the displayed regularity hypotheses.

## Complete corrected operator identity

`CoordinateRicciDeTurckOperator.lean` imports the generic calculus module and
`CoordinateJetConnectionDerivative.lean`. This adapter deliberately inherits
the larger finite-jet/principal algebra closure. It proves, in order:

1. the actual W value equals the conventional produced-jet value
2. the actual derivative of W equals
   `derivDeTurckVectorWithBackgroundJetOfJet (B x) (backgroundFirst B x)
   (coordinateJet g x)`
3. the actual coordinate Ricci readout equals `ricciOfJet (coordinateJet g x)`
4. the actual coordinate Lie readout equals the corrected Lie jet formula
5. the complete actual coordinate operator equals
   `phiRDWithBackgroundJetOfJet (B x) (backgroundFirst B x) (coordinateJet g x)`

The corrected spatial-operator identity uses an open U, `ContDiffOn ℝ 2 g U`,
`ContDiffOn ℝ 1 B U`, membership x∈U and `(g x).det ≠ 0`, with the determinant
explicitly taken on a Matrix. No matrix symmetry is required for these
identifications. Invertibility is required only at the selected point.

For principal cancellation, the adapter additionally assumes actual symmetry
of g on U. The existing actual coordinate-jet producer derives both Hessian
symmetries from Schwarz and differentiated component equality. The proved
principal operator is then `Σpq gInv(x)pq ∂p∂q g(x)ij`, plus the corrected
lower-order reaction, including both background-first-jet Lie contributions.
For an arbitrary frozen coefficient array A the last theorem displays the
full split explicitly: `Σpq A pq ∂p∂q gij`, plus
`Σpq (gInv(x)pq − A pq) ∂p∂q gij` and the same lower-order reaction.
The remainder can still depend on the Hessian through this coefficient error.

## Verification and precise boundary

The Mathlib-only generic module passed a single-file Lean 4.35.0-rc2
**development** check. This is not exact Lean-4.33 certification. The adapter
and the complete unit still require exact Lean-4.33 hosted verification.
`.github/workflows/point4-coordinate-operator.yml` compiles the generic calculus
first, then the complete corrected-operator/principal adapter, checks the ten
selected headline theorem axiom surfaces against only `propext`,
`Classical.choice` and `Quot.sound`, and runs the unchanged full completion
audit at the exact candidate head. Actions are pinned, permissions read-only,
and checkout credentials are not persisted.

B is an actual C¹ coordinate coefficient array; this unit does not assert that
it is the chart representative of a manifold background connection. Nor does
it identify `coordinateRicci` or `coordinateLie` with manifold curvature or a
manifold Lie derivative. Constructing C² chart coefficients from the geometric
metric family, proving those manifold identifications, identifying A with a
tensor heat generator, establishing the required nonlinear evolution estimates,
and constructing the PDE solution remain separate obligations.

The canonical target and completion auditor are unchanged. Point 4 remains
**OPEN**.
