# Boundaryless preferred-chart and frame transport

This supporting milestone builds on the unchanged geometric source at
`1d1f97fe481e0899a0cd54889b0f99ba159ba3fa`. Structured provenance is recorded
in `curvature/formalization.yaml`; contributor notices are preserved.

## Local geometric result

`Analysis/BoundarylessChartTransport.lean` has Mathlib-only imports. Under
`BoundarylessManifold I M` on a smooth finite-dimensional complete real model,
it proves four statements for the existing preferred chart centered at p:

1. its extended-chart target is open
2. the target is contained in the interior of the model range
3. at every target point, the inverse-chart manifold derivative within the
   model range equals its ordinary manifold derivative
4. inverse-chart pullback within that range equals ordinary pullback for any
   dependent tangent vector field

For a target point z, the actual inverse chart sends z to its source. The
manifold-boundarylessness hypothesis says that point is interior. Mathlib's
atlas-independence theorem transfers interiority to the same fixed chart;
the chart right-inverse identity returns z. Thus the target is open. Its
containment in the interior of the model range supplies a neighborhood of z,
which gives the derivative equality. Unfolding the actual pullback gives the
fourth result, without assumptions on the vector field.

This does not assert that the model range is the whole vector space, derive
`I.Boundaryless`, or construct a global homeomorphism.

## Actual preferred frames

`Analysis/PreferredCoordinateFrame.lean` now assumes only
`BoundarylessManifold I M`. Its actual inverse-chart frame identity, constant
frame pullback, scalar ordinary derivative identity and zero manifold Lie
bracket are preserved. The derivative chain rule uses the proved local range
neighborhood; bracket naturality uses target openness and actual differential
invertibility. No supplied chart, germ, derivative or commuting certificate
is introduced. Existing `I.Boundaryless` callers still obtain the weaker
instance from Mathlib.

Chosen-LC, frozen, weak and gauge consumers retain their existing assumptions.
The canonical Point-4 contract is unchanged. In particular this supporting
result does not change its C², weak-candidate, ordinary-time or closed-interval
requirements. Quantitative norm transport, heat-generator transport,
quasilinear estimates and Ricci-flow existence/uniqueness remain open.

## Verification gates

The focused read-only workflow compiles the two local modules at the exact
candidate head under pinned Lean 4.33 and Mathlib. Its probe checks ten axiom
surfaces against only `propext`, `Classical.choice` and `Quot.sound`, displays
seven theorem-level hypothesis surfaces and compiles the model-boundaryless
compatibility regression. The workflow then runs the unchanged full-package
Point-4 completion audit. A development check on another toolchain is not
exact pinned verification, and a focused pass is not Point-4 closure.

Both local modules passed a Mathlib-only Lean 4.35.0-rc2 development check
(3.51 and 6.52 seconds, peak 2.71 GiB RSS). The immutable pinned Mathlib
InteriorBoundary, ExtChartAt, MFDeriv.Basic and Pullback source APIs were
also inspected without fetching or modifying the shared source cache.
The comment/string-stripped scan found zero forbidden tokens. The unchanged
fast completion audit reports OPEN, with its build gate skipped and the
canonical theorem still absent. None of these is a full build or exact Lean
4.33 verification; those gates remain pending until the hosted workflow runs.
Point 4 remains **OPEN**.
