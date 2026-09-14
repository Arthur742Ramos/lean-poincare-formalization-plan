# Provenance

This is a new focused Palomar entry package. It has no prior Palomar ID and
must not be submitted as a later version of another result.

## Reused formalization

The proof development is reused, unchanged, from:

- repository: `https://github.com/Arthur742Ramos/lean-poincare-formalization-plan`
- commit: `d6ef7f253bb95fa44d1fe61c9b1a52e061ca0951`
- source project: `curvature/`
- selected source file:
  `curvature/PoincareCurvature/Geometry/Manifold/RicciFlow/AnalyticPDE/TensorHeatAtlasSymmetricWellPosedness.lean`
- relationship: `builds-on`
- source tree object: `a448a1d7d62c04a5ab85ba0d943b67db293e77c2`
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

The new work in this package is the focused Mathlib-only Challenge surface,
matching independent Solution bridge, Comparator configuration, metadata,
provenance checks, and renderer workflow. It does not relabel inherited
implementation as new formal code.

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

A live Palomar search on 2026-09-14 found no entry indexed by `parabolic`,
`schauder`, or `heat`; the indexed `tensor` entries concerned different
curvature results. That search supports a distinct new-entry identity but is
not a mathematical novelty or editorial-interest claim.

## Authorship and automation

Arthur Freitas Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz are the
human authors. Agent assistance is disclosed in
[AGENT-CONTRIBUTION.md](AGENT-CONTRIBUTION.md) and is not authorship.
