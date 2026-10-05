# Guarded two-sided heat release integration

Status: source-only, uncompiled and not published. Point 4 remains OPEN. Fresh
independent release review and exact-head Lean 4.33 verification remain gates.
No local Lean process, toolchain/cache expansion or remote action was performed.

## Immutable scope

Baseline: `e6b54dd0d7e73a51eb8efb083764b68ae8305a5a` (merged PR129).
The original isolated R1 patch remains historical, unchanged, with SHA256
`aeb8a459b25e3eb45bf05dc8763f7ec00552a01136e4fe992d19f52e152bd1c6`.
Its `EuclideanHeatTwoSidedInitial.lean` module and full type/axiom/rank-zero
probe are byte-identical in this release. Mathematical source approval for R1
is conditional on actual compilation; these repairs are source-only.

All 1,640 other inherited files retain exact bytes and Git/physical executable
modes. This includes every proof, pin, workflow, probe, contract, kernel
negative fixture, auditor, contributor notice, root import and root metadata.
The only changed inherited file is the C2 union guard. Its original SHA256 is
`2ce315f52a5f8de5c2f2eed6543cd4ef26bf7f4411e8d94025251b7d62e68a47`.
The new source guard reconstructs and pins one insertion immediately before
the original main entry point, leaving every inherited function body intact.
That adapter first executes the original immutable union reconstruction,
checks its exact baseline correspondence, then admits this enumerated unit.
Existing geometry and weighted adapters continue delegating to the same C2
checks; all 9 C2 and 13 geometry fixtures remain byte-identical.

The R1 source guard is repaired to require every addition, reject unexpected
tracked/untracked/ignored/physical source, use NUL-safe inventories and reject
symlinks and executable-mode drift. Untracked Python caches are rejected here,
even though an unchanged legacy synthetic fixture demonstrates the legacy
filter's historical behavior. The only non-public generated files after CI starts the compiler are bounded
Lake build/config output formats under the immutable curvature and inherited
Hamilton-Ivey path-dependency roots. Dependency source is admitted only under
manifest-enumerated package names after checking the pinned HEAD and every
tracked blob/mode. Pinned dependency symlinks are checked by literal target
bytes without following them. Arbitrary source and Python caches are rejected
even inside `.lake` or a dependency; main-repository tracked caches are never
exempt. The source checks suppress bytecode creation. No arbitrary `.toolchain`,
`.lake`, hidden proof, workflow or canonical-target exception is introduced.
The guard/test source itself is independently reviewed as part of the exact
release patch/tree; all proof/probe/workflow/document/dossier blobs are pinned
inside the guard. This avoids a self-referential digest claim.

The original R1 workflow and narrative are updated only for truthful release
integration, strict verification sequencing and provenance. The new source
dossier identifies both reused immutable curvature and Mathlib sources and is
validated against the full digest-pinned official v0.4 schema. Root metadata
and selected artifact identity stay unchanged. PR130, the manifold-only unit,
historical artifacts and any registry intake are untouched.

## Pending evidence gates

The workflow first checks the exact source union, full schema and all inherited
and new adversarial fixtures. It explicitly builds the new module, since the
unchanged library root intentionally does not import it, then runs the full
probe and checks all twelve exact axiom records, allowing only `propext`,
`Classical.choice` and `Quot.sound`. Printed theorem types need review; passing
synthetic validator fixtures is never actual compiler/type evidence.

It builds the unchanged full library before running the 13 inherited probes
(150 axiom occurrences, 144 declarations and seven boundaryless types), runs
the unchanged contract and kernel negative fixtures, then invokes the
unchanged full Point-4 audit. Only its actual full-build five-gate OPEN pattern
and exit 1 are accepted. This unit cannot turn fabricated all-PASS evidence
into canonical closure. All these compiler/kernel/audit gates remain NOT RUN
locally and mandatory before merge. Reviewed draft publication for CI is a
separate decision; this preparation performs no publication.
