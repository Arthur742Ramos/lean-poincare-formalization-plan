# Provenance

This is a new focused Palomar entry package. It has no prior Palomar ID and
must not be submitted as a later version of another result.

## Reused formalization

The vendored curvature proof development is reused, unchanged, from:

- repository: `https://github.com/Arthur742Ramos/lean-poincare-formalization-plan`
- commit: `13fa15d6a8352ed08bf71b3533b1c2e922c21388`
- source project: `curvature/`
- selected source file:
  `curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasSymmetricWellPosedness.lean`
- relationship: `builds-on`
- source tree object: `255c32fa869ec955e7c09b21fb74914b9ce13ec7`
- selected source SHA-256:
  `beadeb28c37b72ffc0700756ba506e213f97c351fb1ee3125de41667314012a7`

The package carries a mechanically extracted snapshot in `vendor/curvature/`
so the selected project is self-contained. Every vendored implementation
source, README, contributor notice, inherited manifest, and toolchain is
byte-for-byte identical to the disclosed commit. The package's root Lakefile
exposes those sources as a `PoincareCurvature` library with
`srcDir = "vendor/curvature"`; it deliberately has no nested path dependency,
so Palomar's single writable package build root contains every build output.
The repository's Apache-2.0 license is preserved beside the snapshot.
`scripts/check-provenance.py` verifies the baseline curvature tree object, the
selected source hash, the complete vendored file inventory, every vendored
byte, and the structured metadata. `scripts/check-package.py` separately
rejects any path package or change to the root-library topology.

The new work in this package is the selected, unprojected theorem surface,
the Mathlib-only Challenge, matching Solution bridge, Comparator configuration,
metadata, provenance checks, and renderer workflow. The vendored source
already contains finite-atlas estimates, reconstruction, norm continuity,
and geometric zero-data uniqueness; those proofs remain credited to the
source subproject.

## Mathlib

The inherited manifest pins Mathlib commit
`db584cd6d46c92f209a44c0f1c829460d327499d`. The Challenge boundary check
removes all local candidate build paths and recompiles from the pinned
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
