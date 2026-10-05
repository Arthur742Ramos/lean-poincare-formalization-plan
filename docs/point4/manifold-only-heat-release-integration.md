# Guarded manifold-only heat release integration

Status: source-only printer-option repair, not compiler-verified. Point 4 remains OPEN. Fresh independent
release review and all exact-head Lean 4.33 gates are required before merging.
No local Lean, installation, cache expansion, publication or registry action
was performed while preparing this release unit.

## Immutable boundary

Baseline: `e6b54dd0d7e73a51eb8efb083764b68ae8305a5a` (merged PR129).
The approved R2 patch is SHA256
`7ad46de150fee41810bdc78b3751d8b0451b4d99f4b6c741e886789d94084134`.
All three R2 proof modules are byte-identical to that source-reviewed patch.
The full theorem/axiom probe differs only by the count-one replacement of
`set_option pp.width 180` with `set_option format.width 180`. All eleven axiom
commands, four full-type commands, markers and imports remain byte-identical.
The release guard preserves the original R2 probe digest and reconstructs this
exact substitution from immutable PR131 head
`c1537f72b6f354f63c5f76678a4c4d33d55d52f7`, in addition to pinning the new digest.
All 1,640 other baseline paths are exact bytes
and modes, including every proof, workflow, pin, contract, auditor, contributor
notice, root library import and root formalization metadata.

The only changed inherited path is
`curvature/scripts/point4_c2_initial_heat_source_test.py`. A count-one insertion
before its original main entry point installs the release inventory union.
The new release guard pins the original master guard by digest, reconstructs
that exact insertion and rejects any other bytes. It calls the original C2
`expected_sources` implementation and checks its complete immutable union
against master before enumerating the additional release paths. No inherited
function body, test, evidence parser, audit requirement or workflow is removed.
The legacy geometry and weighted adapters still call the unchanged C2 gates.

The new R2 source guard explicitly checks this sole transformed baseline guard
rather than falsely reporting all inherited files unchanged. Its original R2
identity, and the original nine R2 hashes, are recorded in the release guard.
New documentation and subproject provenance disclose this distinction; all
root selected-artifact metadata remains byte-identical.

Full official v0.4 schema validation also exposed the original R2 dossier's
missing required `sources` list. This release adds accurate immutable-source
entries to that new dossier only, and validates both root and new metadata
against the full digest-pinned official schema. No root metadata is changed.

The public inventory is the exact baseline plus the nine R2 paths plus this
document and the two release guard/test paths. There is no arbitrary proof,
workflow, canonical-target, tracked-cache or duplicate-provenance exception.
Inherited public-path filtering ignores only genuine untracked CPython cache
files; tracked files are never exempted. Existing source and evidence gates
remain mandatory. The additional mode check rejects symlink substitutions and
executable-mode drift.

## Evidence boundary and pending gates

At the original PR131 head `c1537f72b6f354f63c5f76678a4c4d33d55d52f7`,
[exact-head run 37264707859](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37264707859)
successfully built the actual producer with Lean 4.33.0, commit
`d8b18978322de05a8f3dba51ef03cf5461676c17`. The next full type/axiom probe
failed at line 4 with `Unknown option pp.width`; its terminal job log remains
historical evidence. The later unchanged full-library build, inherited probes,
contract/kernel fixtures and completion audit were not reached in that run.
The pinned official
[Lean format-option source](https://github.com/leanprover/lean4/blob/d8b18978322de05a8f3dba51ef03cf5461676c17/src/Lean/Data/Format.lean)
(Git blob `ff82cfbcd4419a8a3c9ae0e6213902c60f4466cf`) registers `format.width`.
Only that printer-option name is repaired, retaining the intended width of
180. No local Lean process has run for this repair. Fresh exact-repair-head
compilation and every subsequent gate remain required; a historical producer
pass or source/mock validation cannot certify the repaired release unit.

The focused workflow first directly builds the actual new producer, since
it is intentionally not imported by the unchanged root library. It then
checks the eleven new axiom surfaces and four manifold-only full types,
builds the unchanged full root library before inherited evidence probes, and
replays every inherited C2/geometry probe (150 occurrences, 144 declarations,
seven inherited boundaryless types), runs the unchanged current full contract
and kernel negative fixtures, and invokes the unchanged full-package audit.
Only a real full build with the exact five-gate OPEN pattern is accepted.
The new unit cannot claim canonical closure, even from fabricated all-PASS
records. Full type logs still require human inspection; occurrence checks do
not establish exact kernel-level assignment of every intended hypothesis.

The original 9 C2, 13 geometry and 7 R2 synthetic fixtures remain unchanged.
Additional fixtures cover exact adaptation, public/physical inventory,
mode semantics, immutable root metadata, duplicate parsed provenance,
workflow/evidence preservation and canonical-target rejection. Synthetic
records test validators only and are never compiler evidence.

R1 and R2 source-only artifacts, their source reviews, and any rejected release
attempt remain historical and unchanged. This new release integration does
not promote those artifacts to verified status or replace an immutable intake.
PR130 and ordinary heat source are outside this release and are untouched.
