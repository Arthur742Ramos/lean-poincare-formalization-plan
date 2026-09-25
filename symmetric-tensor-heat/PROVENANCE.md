# Provenance

This is a new focused Palomar entry package. It has no prior Palomar ID and
must not be submitted as a later version of another result.

## Reused formalization

The vendored curvature proof development is reused from:

- repository: `https://github.com/Arthur742Ramos/lean-poincare-formalization-plan`
- commit: `13fa15d6a8352ed08bf71b3533b1c2e922c21388`
- source project: `curvature/`
- selected source file:
  `curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasSymmetricWellPosedness.lean`
- relationship: `builds-on`
- source tree object: `255c32fa869ec955e7c09b21fb74914b9ce13ec7`
- selected source SHA-256:
  `beadeb28c37b72ffc0700756ba506e213f97c351fb1ee3125de41667314012a7`

The package carries a mechanically extracted baseline in `vendor/curvature/`
so the selected project is self-contained. The inherited README, contributor
notices, manifest, toolchain, and all implementation files outside the
explicit Lean 4.35 compatibility adaptations and proof-support module split
remain byte-for-byte identical to the disclosed commit. `scripts/check-provenance.py`
checks those source blobs and pins every adapted file by SHA-256. The package's root Lakefile
exposes those sources as a `PoincareCurvature` library with
`srcDir = "vendor/curvature"`; it deliberately has no nested path dependency,
so Palomar's single writable package build root contains every build output.
The repository's Apache-2.0 license is preserved beside the snapshot.
`scripts/check-provenance.py` verifies the baseline curvature tree object, the
selected source hash, the complete vendored file inventory, every unchanged
vendored byte, each adapted file hash, and the structured metadata.
`scripts/check-package.py` separately rejects any path package or change to
the root-library topology.

The new work in this package is the selected, unprojected theorem surface,
the Mathlib-only Challenge, matching Solution bridge, Comparator configuration,
metadata, provenance checks, and renderer workflow. The vendored source
already contains finite-atlas estimates, reconstruction, norm continuity,
and geometric zero-data uniqueness; those proofs remain credited to the
source subproject.

## Lean 4.35 compatibility adaptations

The ten Lean 4.35 compatibility files and their exact submitted hashes are listed in
`scripts/check-provenance.py`. No selected theorem statement or source theorem
file was changed. The edits are confined to:

- `HeatKernel1D.lean` and `TensorHeatEuclidean.lean`: the renamed ordered
  product inequality;
- `SmoothDependenceCk.lean`: a changed `convert` tactic goal;
- `ContinuousSection.lean`: an explicit additive equivalence for Mathlib's
  revised instance transfer;
- `Curvature/Tensor.lean` and `ConnectionLaplacianChart.lean`: explicit real
  Hausdorff witnesses in the revised derivative API;
- `ConnectionLaplacianCoordinate.lean` and `EndomorphismTrace.lean`: explicit
  identity casts for germ-equal manifold derivatives;
- `Parabolic/NormalizedCutoff.lean` and
  `Parabolic/CompactCoefficientExtension.lean`: the compact cutoff and
  extension arguments formerly inherited through the unrelated gauge-flow
  import. These proof patterns come from
  `curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/ModelManifoldGaugeFlow.lean`
  at the disclosed source commit, and remain credited to that development.

## Proof-support module split

The vendored RiemannianSection.lean contains a broad section-space API. The
heat dependency closure uses its four tangent-space structure instances and the
ContMDiffRiemannianMetric.ext lemma through LeviCivita.lean. The
TensorDivergence.lean coordinate-regularity proof also needs the
trivializationAt_bilinearFormBundle_apply_eq identity. These source
declarations and the BilinearFormBundle abbreviation are factored into
RiemannianSectionCore.lean. The wider section module imports that core to
preserve its API, while LeviCivita.lean and TensorDivergence.lean import the
core directly. This keeps both consumers independent of the unrelated
section-space API and omits its ContinuousSection dependency from the focused
closure. The fiberwise linearity lemma for bilinear-form trivializations now
lives in the core alongside its coordinate identity. It retains the original
100,000 typeclass-search heartbeat allowance. `TensorHeatAtlasClosedReconstruction.lean`
imports that lemma directly instead of depending on the wider section-space API.
The provenance check pins the edited source files and the new core module by
hash, then checks that the moved declarations occur in the immutable source
and the core. The selected heat theorem and its proof are unchanged.

The short-time commutator retains its explicit
TensorHeatAtlasCommutatorLift.lean import. The Solution build confirmed that
the short-time module uses its atlas source-space and coordinate declarations,
so the commutator-lift module and its reachable atlas-coordinate and cutoff
dependencies remain in the exact closure. scripts/check-package.py derives
and checks that closure. No selected theorem statement or proof changed.

The 556-line ParabolicInterpolation.lean module describes itself as a leaf,
and none of its declarations are referenced by the selected source modules.
Parabolic/FiniteCylinderInterpolation.lean had an unused import of that
module. Removing it preserves a successful Lean build of the finite-cylinder
module and drops the unrelated interpolation module from the candidate roots.
The edited import file is hash-pinned alongside the other source-derived
adaptations. No theorem statement or proof script changed.

`Parabolic/BanachSpace.lean` also directly imported
`Mathlib.Analysis.Normed.Group.SeparationQuotient` without using declarations
from it. Lean's declaration-aware import audit identified the unused import,
and the complete source module compiled after its removal. The adapted source
hash and the import-removal regression are pinned in
`scripts/check-provenance.py`. This changes only the direct import list; no
theorem statement or proof term changed.

## Mathlib

The focused root manifest pins Mathlib commit
`065356127b1dc0016f66b7283ce0ce2c4055aa55` for Lean 4.35.0-rc2.
The immutable vendored manifest retains its historical Mathlib pin.
The Challenge boundary check removes all local candidate build paths and
recompiles from the pinned
dependency closure.

## Literature and overlap

The mathematical result is classical. The direct formalization source is the
closed-manifold vector-bundle parabolic Schauder theory in Huang,
arXiv:1506.05030, especially Section 2. Hamilton's 1982 Ricci-flow paper and
DeTurck's 1983 strictly parabolic reduction provide the geometric context.

A live Palomar search on 2026-09-23 found no entry indexed by `heat` or
`schauder`. The sole `parabolic` hit is the distinct
[Caffarelli--Kohn--Nirenberg partial regularity entry](https://palomar-registry.org/entry?id=PALOMAR-2026-09-22-000003&version=1)
for Navier--Stokes. The `tensor` hits include this repository's earlier
[Levi--Civita curvature entry](https://palomar-registry.org/entry?id=PALOMAR-2026-09-02-000007&version=3)
and [double-contracted Bianchi entry](https://palomar-registry.org/entry?id=PALOMAR-2026-09-06-000004&version=1),
whose selected results are different from the tensor heat theorem. The search
supports a distinct new-entry identity; it is not a mathematical novelty or
editorial-interest claim.

## Authorship and automation

Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz are the
human authors. Agent assistance is disclosed in
[AGENT-CONTRIBUTION.md](AGENT-CONTRIBUTION.md) and is not authorship.
