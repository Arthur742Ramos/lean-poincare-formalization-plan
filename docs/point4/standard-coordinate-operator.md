# Actual conventional geometric coordinate operator

This is a supporting **source candidate**, based exactly on combined spatial
stack `3f997315c2173474225d9e02407a2af444fcd4f3`. No local Lean compiler was
run for this unit. Exact Lean 4.33 compilation, all new axiom probes, and the
full unchanged audit remain pending on its source-reviewed draft. No registry
submission or intake is involved.

## Actual geometric construction

The focused modules are:

- `ActualBackgroundCoordinateCoefficients.lean`: the actual background
  covariant derivative of the same preferred frame, its scalar coefficients,
  genuine C¹ section/readout production, and actual first-jet transport
- `StandardDeTurckCoordinateIdentification.lean`: the conventional positive
  two-input inverse-Gram contraction, an open-chart value germ, separate
  genuine differentiability, scalar manifold derivative transport, and actual
  chosen-LC differentiation of W
- `ChosenLeviCivitaCoordinateMetricCompatibility.lean`: actual torsion
  cancellation in the proved commuting frame and actual metric compatibility
- `StandardRicciDeTurckCoordinateOperator.lean`: actual conventional Lie
  correction and intrinsic Ricci combine into the coordinate RHS, followed by
  the corrected produced-jet, principal, and frozen-remainder identities

No coordinate value, derivative, connection, W, Lie, Ricci, or regularity
identification is assumed. The distinct legacy intrinsic DeTurck vector/RHS
is not used. The existing ordinary Ricci trace and transpose-to-symmetry
reasoning are preserved unchanged.

## Exact hypotheses

The common section retains the existing smooth Hausdorff finite-dimensional
complete real model, C² tangent bundle, sigma compactness, and boundaryless
chart setting. An arbitrary basis indexed by `Fin d` is supplied. The actual
metric family provides its C² slice; a single actual C¹ background connection
slice is explicit for derivative and correction statements. The value and
total-fderiv germ equalities do not add that regularity premise.

There is no compactness, positive-dimension, time-regularity, background
torsion-free, globally smooth zero-extended frame, or stronger metric/background
smoothness premise. Dimension zero is allowed by the general finite-sum proofs.

## Signs and frozen remainder

W remains the conventional positive contraction of chosen LC minus background.
Its product derivative keeps the negative derivative of the actual background.
The corrected jet expression therefore retains both negative background-first-
jet Lie terms. The lower-order reaction has no Hessian slot; the full frozen
remainder still includes `(inverse G - A) * second G`. Freezing at arbitrary A
does not identify A with the manifold tensor heat generator.

The genuine one-dimensional varying-background geometric sign regression is
not included in this candidate. Its construction as an actual affine
connection remains a useful next regression; coordinate-only tests would not
replace that geometric test.

## Verification boundary

The public root exports the new geometric spatial operator and its dependencies.
The new pinned read-only workflow compiles the four focused modules first,
then checks all 21 explicit new headline `#print axioms` outputs against only
`propext`, `Classical.choice`, and `Quot.sound`, and finally runs the full
unchanged Point-4 auditor. Checkout, Lean action and evidence-upload actions
are pinned by immutable action SHAs; checkout uses the exact candidate head.

Local source checks: `git diff --check` passed; the library forbidden-term
scan returned `TOTAL 0`; unchanged `point4_audit.sh --no-build` returned G1
PASS, G2 SKIP, G3/G4/G5 FAIL because the canonical target is absent, and
**POINT 4 OPEN**. This source-only audit is not kernel certification.

No heat-generator identity, analytic estimate, time-space regularity, PDE
construction, gauge recovery, or closure claim is supplied. The canonical
completion target and auditor are unchanged.
