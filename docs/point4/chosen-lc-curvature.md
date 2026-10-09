# Actual chosen-LC curvature and intrinsic Ricci coordinates

This supporting source candidate builds on the immutable same-repository
chosen-LC coordinate producer at
`73212853b1c48e5fea511191e89072dd003b2d0a`. It preserves the existing
contributor notices, geometric predicates and canonical Point-4 audit.
Structured builds-on provenance is recorded in `curvature/formalization.yaml`.
No registry intake or new registry identity is part of this milestone.

## Exact statement boundary

The candidate retains the previous producer's hypotheses: a finite-dimensional
complete real model, smooth Hausdorff boundaryless manifold, C² tangent bundle,
sigma compactness for the actual chosen Levi–Civita family, a genuine metric
family slice and an arbitrary model basis indexed by `Fin d`. Dimension zero
needs no special instance. No compactness, rank, nonempty, time-regularity,
global coordinate-field smoothness or identification premise is added.

`Analysis/CoordinateMatrixCurvature.lean` first proves lower Christoffel-slot
symmetry from the actual metric symmetry on the open coordinate domain.
It packages a genuine neighborhood equality, differentiates that equality and
uses the actual C² Christoffel derivative formula. It then identifies the
coordinate Ricci expression with the ordinary unweighted curvature trace
whose geometric slot order is R(F_k,F_j)F_i.

`ChosenLeviCivitaCoordinateCurvature.lean` supplies the geometric readout:

1. The chosen slice's real C¹ connection instance is constructed from the
   metric family's existing Levi–Civita existence theorem
2. The fiber-norm-free restriction theorem and C² local frame fields give
   actual C¹ regularity of the section cov(F_j)(F_i), then of its scalar
   frame coefficients and fixed-chart scalar readouts
3. The actual scalar manifold derivative is transported through the preferred
   frame and finite-basis model equivalence to `christoffelFirst`
4. The already-proved local-to-actual curvature theorem identifies the raw
   commutator with bundled curvature without assuming global frame smoothness
5. The frame connection formula and proved frame commutation give the actual
   curvature coefficients, with derivative signs and all slots explicit
6. The ordinary basis trace first proves
   `coordinateRicci_chosenLCMetricCoordinates_eq_intrinsicRicciTensor_transpose`,
   whose right-hand side is intrinsic Ricci(F_j,F_i)
7. `coordinateRicci_chosenLCMetricCoordinates_eq_intrinsicRicciTensor` then
   invokes actual intrinsic Ricci symmetry, separately deriving both finite
   manifold-smoothness instances from the existing infinity instance

There is no inverse-Gram factor in the Ricci trace. Lower connection-slot
symmetry and intrinsic Ricci-slot symmetry are different proof steps.

## Verification and remaining frontier

The generic `CoordinateMatrixCurvature.lean` passed a bounded Lean
4.35.0-rc2 **development-only** check with the unchanged generic dependency
proof bodies; the actual geometric assembly has not been compiled locally.
Exact Lean-4.33 verification of the whole source candidate is pending.
The dedicated exact-head workflow
first compiles the generic curvature trace, the prior actual chosen-LC producer
and the new geometric readout with exact Lean 4.33. Only after these succeed
does it print/check all eleven new headline axiom surfaces and run the full
unchanged package audit. Checkout credentials are not persisted, permissions
are read-only and all actions are pinned. Source review and any newer-toolchain
development check are not exact Lean-4.33 certification.

The candidate supplies no conventional Lie/DeTurck coordinate bridge, frozen
manifold tensor-heat-generator identification, nonlinear analytic estimates,
quasilinear PDE solution, joint time-space regularity or recovery gauge flow.
The canonical general local-existence/uniqueness theorem remains absent.
Point 4 is **OPEN**.
