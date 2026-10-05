# Guarded two-sided heat release integration

Status: source-only runtime-inventory repair, not locally compiled or published.
Point 4 remains OPEN. Fresh independent release review and exact-head Lean 4.33
verification remain gates. No local Lean process, toolchain/cache expansion or
publication was performed for this repair. The preceding public draft compiled
the new module, then failed its post-probe source inventory; that partial
historical evidence does not qualify this new head.

## Immutable scope

Baseline: `e6b54dd0d7e73a51eb8efb083764b68ae8305a5a` (merged PR129).
The original isolated R1 patch remains historical, unchanged, with SHA256
`aeb8a459b25e3eb45bf05dc8763f7ec00552a01136e4fe992d19f52e152bd1c6`.
Its original `EuclideanHeatTwoSidedInitial.lean` module retains SHA256
`488c1fdaa617f306e9bd2c714d5917b07319a88cc251195cd0e950b240747529`
at immutable historical commit `96e666f0520ca261fe745c5cf2c2a4abef38f645`.
The guard admits only eight exact count-one proof-body replacements from that
source, pins the repaired digest, and rejects every other byte change. All
public theorem signatures, hypotheses, mathematical definitions and stored
value/first/second derivative data are unchanged. The full type/axiom/rank-zero
probe is byte-identical. Mathematical source approval remains conditional on
actual exact-head verification; the current repair changes no proof bytes.

All 1,637 unaffected inherited files retain exact bytes and Git/physical
executable modes. This includes every proof, pin, probe, contract, kernel
negative fixture, auditor, contributor notice, root import and root metadata.
Four inherited files have only exact, digest-pinned adapters: the C2 union
guard and three workflow job-startup environments. Its original SHA256 is
`2ce315f52a5f8de5c2f2eed6543cd4ef26bf7f4411e8d94025251b7d62e68a47`.
The new source guard reconstructs and pins one insertion immediately before
the original main entry point, leaving every inherited function body intact.
That adapter first executes the original immutable union reconstruction,
checks its exact baseline correspondence, then admits this enumerated unit.
Existing geometry and weighted adapters continue delegating to the same C2
checks; all 9 C2 and 13 geometry fixtures remain byte-identical. The workflow
validator adapter verifies the exact C2 startup transform, removes only that
count-one insertion and calls the unchanged original validator on original
bytes. No path-read monkeypatch or broad workflow acceptance is introduced.

The inherited geometry, C2 and weighted workflow jobs each gain exactly one
job-level environment insertion, `PYTHONDONTWRITEBYTECODE: '1'`. Their original
bytes, steps, action pins, permissions, triggers and all other YAML semantics
are retained and checked with duplicate-key-aware parsing. CPython caches an
imported module before executing its body, so a flag inside the C2 adapter
cannot suppress its own import cache. The prior draft head
`96e666f0520ca261fe745c5cf2c2a4abef38f645` failed that inherited startup gate; its
failed evidence remains historical. Regression fixtures use ordinary Python
commands with the exact pinned job environment and also reject preexisting
empty caches, hidden Lean, invalid bytecode and byte-identical gate bytecode
without deleting or overwriting the attack evidence.

The R1 source guard is repaired to require every addition, reject unexpected
tracked/untracked/ignored/physical source, use NUL-safe inventories and reject
symlinks and executable-mode drift. Untracked Python caches are rejected here,
even though an unchanged legacy synthetic fixture demonstrates the legacy
filter's historical behavior. The non-public generated files after CI starts the compiler are bounded
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

## One verified ProofWidgets input fingerprint

The only added runtime exception is
`curvature/.lake/packages/proofwidgets/widget/package-lock.json.hash`.
It is optional before Lake generates it. The underlying dependency must pass
the unchanged complete HEAD, tracked-blob and mode inventory. The fixed
ProofWidgets manifest entry must retain repository
`leanprover-community/ProofWidgets4` and revision
`4be2e3d5087eeb272cf5a8853b8f9dd025ef5957`; its regular, non-executable,
non-symlink lockfile must have exactly 172,140 bytes and Git blob
`06d5baf2fae78fed1fdae485f4c2c054a0bccfb2`. Every sidecar ancestor must
be a real directory. The sidecar must be a regular, non-executable,
non-symlink file with exactly 16 lowercase hexadecimal bytes, no newline.
Its bytes must equal the pinned Linux/little-endian Lake 4.33 text fingerprint
`179e66574f04806e`; a correctly formatted stale/wrong fingerprint is rejected.

This is supported by the immutable official
[ProofWidgets lakefile](https://github.com/leanprover-community/ProofWidgets4/blob/4be2e3d5087eeb272cf5a8853b8f9dd025ef5957/lakefile.lean):
`widgetPackageLock` uses `buildFileAfterDep` with `text := true` on this
[tracked lockfile](https://github.com/leanprover-community/ProofWidgets4/blob/4be2e3d5087eeb272cf5a8853b8f9dd025ef5957/widget/package-lock.json).
Lean 4.33.0 resolves to commit `d8b18978322de05a8f3dba51ef03cf5461676c17`.
Its [Lake build functions](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/lake/Lake/Build/Common.lean)
append `.hash` and write `Hash.toString`; its
[hash definitions](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/lake/Lake/Build/Trace.lean)
normalize CRLF and encode 16 lowercase hex digits. The source-derived value
uses `Hash.ofText`, the `1723` nil seed, and string hashing with seed `11`
from the pinned
[runtime string entry point](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/runtime/object.cpp),
[MurmurHash64A](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/runtime/hash.cpp)
and [hash mixing](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/runtime/hash.h).
This derivation is static source evidence, not a local Lean execution or
observation of the failed job's sidecar bytes. The new exact-head CI must still
validate the genuine generated file against these restrictions.

There is no arbitrary `.hash` or package-directory exemption, no new tracked
cache allowance, and no evidence deletion or cache cleanup. Adversarial
physical fixtures reject wrong package/path, missing verified parent, source
or manifest/HEAD drift, directory/symlink/executable changes, malformed,
oversized or wrong-value fingerprints, hidden Lean and Python caches. All
previous fixtures and evidence gates remain unchanged.

The original R1 workflow and narrative are updated only for truthful release
integration, strict verification sequencing and provenance. The new source
dossier identifies both reused immutable curvature and Mathlib sources and is
validated against the full digest-pinned official v0.4 schema. Root metadata
and selected artifact identity stay unchanged. PR130, the manifold-only unit,
historical artifacts and any registry intake are untouched.

## Pending evidence gates

The historical head `a30173cea3c70df93cfe17bec130b870324b8526` passed the
source union, full official schema and startup regression gates in
[dedicated run 37271905230](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37271905230).
Actual Lean 4.33.0 compiled the inherited heat imports, then rejected the new
module at original lines 103, 159, 166, 190, 197, 256 and 258. Later types,
axiom, full-build, contract, kernel and audit steps were not reached.

The source repair makes the coerced generator function equality explicit,
rewrites only the heat path's zero value, types the scalar continuity limit,
uses eta-expanded derivative addition and constant scalar multiplication,
extracts strict negativity from `Iio` membership, and unfolds composition in
the left difference quotient. It does not change the mathematical argument,
weaken ordinary `HasDerivAt`, strengthen bounded C² data, or claim negative
Hessian-norm convergence, global positivity or canonical completion. These
were pinned-API/source diagnoses before the next historical run.

At historical head `c88d9c2ebeef9f72193400a8202f40285aa86d04`,
[actual Lean 4.33.0 run 37280378637](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37280378637)
successfully compiled the new module. Its type/axiom step printed the probe
output, then exited 1 solely because the strict source inventory rejected the
generated fixed ProofWidgets sidecar above. This is partial historical output,
not a passing type/axiom gate or qualification of this guard-only candidate.
The workflow, module, theorem headers, ordinary derivative and rank-zero
probe, 12 new and 150 inherited axiom gates, contract, kernel fixtures and
full OPEN audit are byte-identical to that head.

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
into canonical closure. All compiler/type/axiom/full-build/contract/kernel/full
OPEN audit gates remain mandatory at the new exact head and NOT RUN locally.
Reviewed draft publication for CI is a
separate decision; this preparation performs no publication.

## Final audit interpreter-startup repair (c72 historical failure)

The exact c72 job passed its actual Lean 4.33 two-sided probe, inherited
probes, full library build, closed-contract kernel fixtures and full OPEN
audit. The final source inventory then correctly rejected an interpreter
cache created by a Python subprocess of the unchanged audit shell. Its
failed run 37287043942 and artifact 11341389499 remain historical.

This new source-only candidate adds exactly one job-level
`PYTHONDONTWRITEBYTECODE: '1'` setting to the two-sided primary job.
Removing that count-one insertion reproduces the complete c72 workflow
byte for byte; all steps, action pins, triggers and audit code remain
unchanged. The strict cache rejection is retained, including preexisting
cache attacks. No mathematical source, probe, compiler pin or dependency
changes. The workflow and documentation digests are updated to these exact
bytes. Independent source review and fresh exact-head official verification
remain required; this candidate is not a Lean certificate. Point 4 is OPEN.
