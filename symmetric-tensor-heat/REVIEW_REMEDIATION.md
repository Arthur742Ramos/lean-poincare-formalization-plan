# Geometric tensor-heat review remediation

Status: mathematical repair required. The existing selected proposition is
not a submission-ready statement of geometric symmetric-tensor heat
well-posedness. This document records requirements, not completed proofs.

## Scope

Retain the geometric theorem. Merely renaming the present result as an
abstract coefficient presentation would address some descriptive objections,
but would not establish the requested research-interest case.

The intended endpoint is existence, uniqueness, and a Schauder estimate for
the actual connection heat equation on covariant two-tensors over a compact
boundaryless smooth Riemannian manifold, with symmetry preservation for
symmetric initial data and forcing. Any represented-data restriction must
remain explicit and have a proved geometric meaning.

## Evidence from the current code

The following findings describe the reviewed statement before repair.

1. `TensorHeatChallenge.completeStatement` existentially chooses
   `atlasCoordinate : Index → M → E`, weights, frames, and time maps. It
   requires nonnegative weights summing to one and frames spanning wherever
   the weight is nonzero. It does not require chart membership, inverse
   identities, open chart domains, regularity, subordination, or the derivative
   of the time map.
2. Its solution and time-derivative reconstruction equations explicitly
   average the two tensor slots. In `TensorHeatSolution`, the corresponding
   witnesses are `A.symmetrizedAtlasField`. Symmetry therefore holds for every
   coefficient witness by construction.
3. `coordinateClass` is an existentially selected predicate. The displayed
   uniqueness cannot by itself establish uniqueness among all regular
   geometric fields solving the equation with the same initial trace.
4. Useful geometry exists internally: `FiniteTensorHeatParametrixAtlas`
   uses `extChartAt`, tangent trivializations, positive radii, and
   `FiniteSmoothPointwiseSubordinateCover`. The missing statement constraints
   should expose these actual objects and their properties.
5. `atlasFieldOfHigher_transpose_toFun` and
   `atlasFieldOfHigher_transpose_timeDerivative` already relate coefficient
   transposition to geometric transposition. However,
   `existsUnique_symmetricAtlasSpatialClassicalSolution` obtains symmetry
   through `symmetrizedAtlasField_isSymmetric`; its uniqueness proof uses
   the ambient coefficient predicate. It does not prove symmetry of the
   unprojected reconstruction.

## Required mathematical changes

### Charts, weights, frames, and time

Expose a finite family of actual manifold charts whose open sources cover the
manifold, with compatibility supplied by the given smooth atlas. Express the
normalized spatial coordinates as the selected extended chart followed by
the documented affine translation and positive scaling. Relate every local
estimate to that coordinate domain.

Expose a smooth partition of unity subordinate to those sources, with
support containment, nonnegativity, and sum one. Tie the local frames to
smooth tangent-bundle trivializations on the same patches; pointwise spanning
alone is insufficient.

For radius r_i > 0, state the actual time normalization
tau_i(t) = t₀ + (t - t₀) / r_i² and forcing scale r_i⁻², including the
chain-rule identity and common-interval containment. Use the implementation's
precise convention and prove its equivalence to the displayed formula.

### Unprojected solution and geometric uniqueness

Define the solution as the ordinary sum of local tensor reconstructions.
Prove its initial trace, spatial and temporal regularity, geometric equation,
and estimate before invoking symmetry.

Establish uniqueness in an explicitly defined geometric classical solution
class. Coefficient uniqueness is usable only after proving that it implies
this geometric uniqueness, including coverage of the comparison fields.
Partition-weighted reconstruction need not be injective on arbitrary
coefficient families; do not assume it is.

The higher-jet value component now has a formal uniform trace estimate in
`FiniteInitialTrace.lean`: at positive time, its spatial supremum distance
from its canonical initial trace is bounded by the jet norm times
`|t-t₀|^(α/2)`. A pointwise version is proved as well. This controls the
represented coefficient fields at the initial face; it does not establish
uniqueness of geometric solutions or show that every comparison field has
such a coefficient representation.

Huang's current arXiv v8, Theorems 2.3 and 2.4, obtains intrinsic uniqueness
from a global Schauder estimate for every solution in the stated bundle
Hölder class. The existing atlas estimate bounds only witnesses satisfying
the stronger chartwise equation. A comparable all-solutions estimate, or a
proved localization that brings every geometric solution under the existing
coefficient estimate, is needed here. Source:
https://arxiv.org/html/1506.05030v8#S2

Prove that transposition preserves this solution class and commutes with the
induced connection Laplacian. For symmetric initial data and forcing, the
transpose then solves the same Cauchy problem. Geometric uniqueness gives
uᵀ = u. The selected symmetry conclusion must refer to that unprojected u.

An alternative coefficient proof must establish all transpose-equivariance
and representation results needed to reach the same conclusion. Symmetry of
the reconstructed data alone must not be replaced silently by symmetry of
each coefficient family.

### Data coverage and research interest

Specify admissible data independently of a proof-chosen predicate. Prove a
localization/representation theorem for the claimed class of geometric
Hölder sections, with controlled norms, or state and justify a narrower class
precisely. Constant coefficient witnesses alone do not establish this.

Only after the replacement statement and proof exist, compare its exact
hypotheses and conclusion with primary geometric-analysis literature. State
the mathematical/formalization contribution and audience without claiming
that a classical theorem is novel. The current research-interest case is
not established by the existing certificate.

## Acceptance gates

- Mathlib-only Challenge with the complete mathematical statement selected.
- Unprojected reconstruction and symmetry derived from the equation.
- Geometric solution class and a proved uniqueness theorem for that class.
- Actual chart, partition, frame, time, and data-representation constraints.
- Compiled-body boundary audit and semantic regression checks.
- Provenance reconciled with any changed or added proof modules.
- Lean, Comparator, NanoDa, and full pinned Linux renderer replay at the
  replacement commit.
- Research-interest assessment of that exact result.

No replacement proof, successful verification, editorial approval, or new
intake is recorded by this document. Existing immutable intakes still refer
to their original commits.

## Implementation progress

The Challenge and Solution now expose actual chart centers and positive
radii. Their coordinate maps equal normalized `extChartAt` maps. Weights are
smooth, their topological supports lie in those chart sources, and the chart
sources cover the manifold. Time normalization and forcing scale have exact
formulas using the same radii. The displayed frames are now identified with
`localFrame` of the tangent-bundle trivialization at each chart center. The
Solution and Mathlib-only Challenge have passed direct Lean elaboration with
these strengthened constraints. The Challenge's one intentional theorem
placeholder remains.

`TensorHeatGeometricSymmetry.lean` proves that transposing the unprojected
atlas field commutes with its intrinsic tensor heat operator and transforms
its initial trace. It also proves that a geometric uniqueness theorem covering
all represented solutions with the same geometric trace and source would imply
symmetry of the ordinary reconstruction. That uniqueness is an explicit
hypothesis of the new lemma, not a result obtained from the existing
chartwise-coefficient uniqueness theorem. The selected theorem still uses
symmetrization; geometric uniqueness, data coverage, the remaining analytic
bridges, and complete submission verification remain open. These local changes
do not establish submission readiness.

The current proof module also isolates `GeometricAtlasCauchySolution`, whose
inputs are the global initial tensor and global physical source. The existing
strong atlas solution yields a member of this class, and transposition
preserves the class for symmetric data. Neither result supplies uniqueness in
that class. The required next proof must establish that two members with the
same global Cauchy data have equal ordinary reconstructed fields; equality of
their chartwise traces is unavailable from the current hypotheses.

The viable proof interfaces are now explicit:

1. Define an intrinsic or proved-equivalent atlas Hölder norm on geometric
   covariant two-tensor fields, and prove a zero-data global Schauder estimate
   for every field in `GeometricAtlasCauchySolution`. Then the difference of
   two solutions is zero by that estimate.
2. Alternatively, construct a canonical localization of every such field into
   `HigherCoefficientSpace`; prove that localization preserves its global
   initial trace and PDE as the exact strong atlas equation. Only then can
   `strongAtlasSolutionEquation_unique` be applied.
3. Use the proved transpose closure plus that uniqueness theorem to replace
   both selected averaged reconstruction equations and the selected solution
   predicate with the ordinary atlas field. Re-run the Challenge, package,
   provenance, Comparator, NanoDa, and pinned hosted renderer gates on the
   resulting immutable commit.

The geometric difference lemmas now show that two classical solutions with
the same data have a field with zero trace and zero heat operator. This is a
reduction, not zero-data uniqueness. `FiniteClassicalTensorHeatField` itself
only requires pointwise convergence to the initial trace; the planned
uniqueness theorem must specify and prove enough uniform spatial-temporal
regularity for a global estimate or maximum-principle argument. The atlas
higher-coefficient class is a possible source of that control, but its transfer
to a geometric norm remains unproved.

The package provenance check now reads the disclosed `curvature` source from
its immutable Git commit. The main repository's `curvature/` tree has advanced
since that commit, so comparing all of current `curvature/` with the old tree
would incorrectly reject an unchanged, byte-verified vendor snapshot. The
package and provenance checks pass locally with the corrected comparison.
