# Actual chosen Levi–Civita coordinate producer

This supporting candidate builds on the coordinate-operator source at
`fc6f66bcc22edef3f2188f99afa8b4a9950216c0`. It reuses the actual metric,
chosen Levi–Civita family, Gram/Riesz reconstruction and coordinate inverse/
Christoffel calculus. The pointwise Koszul proof adapts the existing
`HamiltonIveyKoszul.lean` proof; its metric compatibility and torsion arguments
remain the actual geometric predicates. Existing notices are preserved.

## One fixed chart and actual finite model coordinates

`Analysis/PreferredCoordinateFrame.lean` uses the actual preferred tangent
trivialization at a selected chart center p. Its frame comes from a finite
basis of the model E. It proves throughout that fixed chart patch:

- a frame vector is the actual inverse-chart differential of its basis vector
- pulling the frame back through the same inverse chart gives constant vectors
- a scalar manifold derivative along the frame is the ordinary Fréchet
  derivative of the scalar readout in that fixed chart
- the frame's actual manifold Lie brackets vanish

Frame commutation follows from Lie-bracket naturality, the proved constant
pullbacks and invertibility of the chart differential. It is not a hypothesis.
The basis supplies a continuous linear equivalence between E and
`Fin d → ℝ`; the standard coordinate vector is proved to map to its basis
vector. Ordinary scalar differentiation through this actual equivalence is
proved by the Fréchet chain rule.

The supporting boundaryless hypothesis makes the chart target open and
replaces derivatives within `range I` by ordinary derivatives. The fixed chart
is selected from the manifold's existing preferred atlas. A commuting frame,
coordinate derivative package or Christoffel formula is never supplied as data.

## Actual metric and connection producers

`LeviCivitaKoszulAt.lean` derives pointwise Koszul using only actual `MDiffAt`
certificates for the three fields at the selected point. It uses metric
compatibility and three applications of the actual `torsion_eq_zero_iff`.
This avoids treating a locally smooth frame, extended by zero, as globally C¹.

`ChosenLeviCivitaCoordinateChristoffel.lean` then constructs the coordinate
matrix field from a genuine C² metric-family slice. At coordinate z, it
reads the metric on the two actual frame vectors at the inverse-chart point.
The coordinate domain is the inverse image of the open chart target under the
finite-basis equivalence. The module derives:

1. the coordinate domain is open
2. the actual matrix field is C² and symmetric
3. its value is the actual positive frame Gram matrix, hence its explicitly
   Matrix-typed determinant is nonzero throughout the coordinate domain
4. its actual first derivatives equal scalar manifold derivatives along the
   proved coordinate frame
5. localized Koszul gives the three metric-first-derivative pairing terms for
   the actual chosen Levi–Civita connection
6. actual inverse-Gram/Riesz reconstruction gives the chosen connection's frame
   coefficient as `CoordinateMatrixJet.christoffel` of the produced matrix

The connection's differentiated vector is frame j and its direction is frame i;
the resulting coefficient is `Γ^k_ij`. This order is displayed in the statement.
The matrix inverse is explicitly typed as a Matrix wherever read out.

The last declarations define the actual chosen-connection coefficient function
in the same fixed coordinates. Its Christoffel identification holds throughout
the open domain, hence gives a genuine ordinary-neighborhood germ. Produced C²
metric regularity and invertibility give actual component differentiability.
Differentiating the proved germ and applying the existing actual Christoffel
calculus yields `christoffelFirst` as the component's actual Fréchet derivative.
No inverse, Christoffel or connection derivative formula is assumed.

## Scope and verification

The geometric producer works with a finite-dimensional complete real model E,
a smooth Hausdorff manifold, its C² tangent bundle, sigma compactness for the
chosen Levi–Civita family, an actual `MetricFamily` slice, and `I.Boundaryless`.
It accepts any finite basis indexed by `Fin d`. Such a basis is ordinary
finite-dimensional linear algebra data; there is no fixed rank, empty-manifold
or subsingleton restriction. The work is spatial at a fixed time, so no joint
time regularity or PDE solution is supplied or inferred.

All six preferred-frame/model lemmas passed a Mathlib-only Lean 4.35.0-rc2
**development** check. The localized Koszul and full geometric assembly have
not been compiled locally. Exact Lean-4.33 verification of this whole candidate
is pending. The dedicated workflow first compiles the preferred-frame module,
then pointwise Koszul and the actual geometric producer, checks eighteen
headline axiom surfaces against only the standard axioms, and runs the unchanged
full-package completion audit at the exact candidate SHA. Actions are pinned,
permissions read-only and checkout credentials are not persisted.

The actual coordinate Ricci trace and coordinate Lie correction still need
identification with the manifold tensors. The Ricci transpose convention must
be handled explicitly using actual Ricci symmetry. Tensor heat-generator
identification, nonlinear analytic estimates and Ricci-flow PDE construction
remain further obligations. The producer does not change the canonical target
or completion auditor. Point 4 remains **OPEN**.
