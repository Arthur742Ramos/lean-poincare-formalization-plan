# Weak-regularity actual tensor Laplacian

## Scope and verification state

This is a supporting proof unit, not the canonical Point-4 theorem or a new
registry submission. Its source is authored but has not yet been checked by
the pinned Lean 4.33.0 toolchain. Independent source review and the exact-head
hosted workflow are required before reporting it as verified.

The main declaration is
`RicciFlow.AnalyticPDE.connectionLaplacian_apply_eq_localTensorHeatSecondOrder_of_baseC1_and_localC2`
in `TensorHeatWeakLaplacian.lean`.

It identifies the genuine intrinsic connection Laplacian with the existing
coordinate expression `Aheat D²u + Bheat Du + Cheat u`, evaluated at output
`(q, p)` for the intrinsic arguments `frame p, frame q`. It does not assume the
coordinate identity, first-covariant-derivative readout regularity, or raw
coordinate differentiability certificates.

## Exact regularity boundary

- Smooth finite-dimensional complete-model Hausdorff manifold with the
  model-level `[I.Boundaryless]` assumption
- Existing Riemannian bundle with C¹ metric regularity
- Existing C³ tangent-vector-bundle regularity, used by the already-proved C²
  pulled-back moving-frame theorem; this is not a C³ metric assumption
- A C¹ base tangent connection
- The tensor section is C² only on the open frame patch `e.baseSet`
- The evaluation point lies in the frame patch and the chosen chart source

The model-level `[I.Boundaryless]` assumption is stronger than the canonical
Point-4 target's manifold-level `BoundarylessManifold`. Transporting this local
identity to that canonical hypothesis remains an open adapter obligation; this
proof unit does not change or weaken the canonical target.

There is no C² connection hypothesis or induced-three regularity hypothesis.
The induced-two C¹ connection class is constructed from the base C¹ connection
using `contMDiffCovariantDerivative_covariantTwoTensor_one`.

## Proof chain

1. The new C¹ coefficient helper applies the C¹ connection to a C² genuine
   two-tensor frame, evaluates on a C¹ tangent frame, and reads out the actual
   scalar frame coefficient. It is transported to the fixed chart.
2. C² tensor regularity on the frame patch gives C² coordinate components.
3. The proved class-to-open-set restriction gives local C¹ regularity of the
   actual first covariant derivative from that local C² tensor section. Its
   scalar coefficient readouts agree near the point with the first-covariant
   component functions and are therefore differentiable.
4. The open chart/frame overlap supplies the within-derivative neighborhood
   certificates, first-coordinate-derivative differentiability, and frame and
   coefficient differentiability required by the raw intrinsic adapter.
5. The existing exact intrinsic-to-coordinate theorem supplies the final
   actual connection-Laplacian equality.

The old stronger automatic adapter remains unchanged for existing callers.
The C¹ coefficient helpers do not imply C¹ regularity of the assembled
zeroth-order heat coefficient, which contains derivatives of the connection
coefficients. No Schauder, nonlinear local-existence, encoding, localization,
manifold realization, or uniqueness gap is claimed closed.

## Reproducible evidence gates

`curvature/scripts/point4_weak_laplacian_probe.lean` prints the exact elaborated
main type and audits the four new theorem dependencies for foundational axioms.
`.github/workflows/point4-weak-laplacian.yml` pins checkout, Lean setup, and
artifact actions to immutable SHAs, checks the exact candidate head, has only
read permissions and disables persisted checkout credentials. It then runs
the unchanged full Point-4 audit. OPEN is expected until the canonical theorem
actually exists; the workflow still requires a clean source scan and full build.
No local compiler/dependency installation is part of this proof unit.

## Immutable provenance

Inherited source:
[base 1d1f97fe481e0899a0cd54889b0f99ba159ba3fa](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/1d1f97fe481e0899a0cd54889b0f99ba159ba3fa/curvature).
In particular this unit builds on `TensorHeatCoordinateOperator.lean`,
`TensorHeatGeometricRegularity.lean`, and `InducedHomRegularity.lean`, preserving
the existing Apache-2.0 licensing, authorship notices, and coordinate convention.
The same dependency is recorded structurally in `curvature/formalization.yaml`.
