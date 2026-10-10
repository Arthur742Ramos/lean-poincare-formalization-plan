The local chart connection theorem identifies the project's chosen
Levi-Civita connection with the actual upstream `chartLeviCivita` at points
in `chartLeviCivitaGoodSet`, for sections differentiable there. The metric
family is constant and uses the existing `RicciFlow.SmoothForward.toC2`.
The finite-dimensional complete real tangent model, smooth manifold,
`T2Space` and `SigmaCompactSpace` premises are retained. The proof does not
add a positive-rank or nonempty premise.

`ChartPort.projectChosen_eq_chartLeviCivita` uses the genuine proved chart
torsion and metric compatibility, local Koszul uniqueness and a smooth
section through a tangent vector. Its source cone contains all 55 upstream
modules, the two new mathematical modules and 13 inherited project modules.
`ChartPort/ChartIdentityEvidence.lean` is the unchanged reviewed probe. It
prints the full theorem type and proof, actual chart formula and good set,
chart-property proofs and six axiom surfaces. Each checked declaration must
report exactly `propext`, `Classical.choice` and `Quot.sound`.

The source base is `Arthur742Ramos/lean-poincare-formalization-plan` at
`1664872ce762ee027b76cb515befb0ae829b2711`, tree
`6d74e9612cf6e16f2d027012cede68e5e0a23483`. PR135's head and this Git tree
were read from the public API. All inherited files remain
unchanged except `curvature/lakefile.toml`, which appends conventional
`DifferentialGeometry` and `ChartPort` library registrations with the reviewed
strict compiler options. Existing default targets, manifests, official 4.33
toolchain and Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d` pin remain.
The existing sibling `../hamilton-ivey-reaction` dependency remains in place;
CI checks out the complete repository and loads that path dependency normally.

Attribution and exact source provenance are under
`curvature/third-party/differential-geometry/`. The original Apache license,
upstream README and reviewed upstream port patch retain their original bytes.
The new NOTICE uses repository-relative paths. Twelve earlier desktop project
copies differ from the public files only in CRLF/LF encoding. The candidate
uses the public base files and preserves those desktop evidence bytes.

The focused workflow runs automatically for ordinary pull requests and checks
out the exact head repository and SHA. It records that head's actual Git tree
and binds all admission/build receipts to it. This PR route works before the
new workflow reaches the default branch. A manual dispatch also accepts a
reviewed full candidate commit SHA and Git tree SHA and requires an exact
match. An automatic PR result and independent source review remain separate.
The ordinary admission check requires the exact base tree, unchanged inherited
path/hash/mode entries, the two-library configuration delta and precisely the
listed additions. The inherited validators, trusted bootstrap semantics and
workflows retain the current 1664 base bytes. Its composition dispatcher and
identity map remain unchanged, and the unpublished startup repair is excluded.
The external review packet supplies a complete ordinary path/hash/mode map,
including the workflow and new validation scripts. The manual reviewed tree
input binds those bootstrap bytes. On the PR route, the exact head tree is
recorded for independent reconciliation. The source check also pins the
approved 58-file mathematical/probe hash table.

Admission enumerates the physical public tree, including ignored and untracked
files and empty directories. It verifies committed HEAD, index and physical
path/hash/mode identities. Initial admission rejects pre-existing local caches.
After dependency setup, only pinned dependency source trees, Git metadata and
finite declared Lake configuration/module artifact paths are allowed. Unknown
outputs fail admission. The pinned Mathlib and ProofWidgets legacy configurations
use workspace indices 2 and 6. Each permits only `lakefile.olean`,
`lakefile.olean.trace` and `lakefile.olean.lock` under
`curvature/.lake/config/<index>/`. Other indices, names and extensions fail.
Newly rebuilt project artifacts stay outside the public
checkout in the owned evidence directory.

The new job runs as the runner user in an owned systemd cgroup with a 6 GiB
memory limit, no swap and a two-CPU quota. The build owner restricts affinity
to two CPUs and runs one Lean compiler at a time. It records argv, source and
artifact hashes, exits, raw logs, peak resource use and process completion.
Missing cgroup support fails the job. A stage timeout or resource failure
retains the available evidence and fails the qualification.

Dependency setup loads the pinned Lake manifest. The job bootstraps the real
pinned Mathlib Cache CLI serially, with a 200-module cap for its non-Mathlib
imports, and calls its ordinary `get` command only for the 126 direct external
Mathlib roots and their imports. Downloads and fallback outputs use an owned
evidence directory. At most the 31 unchanged pinned support modules may be
compiled if their required import artifacts remain missing. Readiness follows
official Lean 4.33: module-system imports require olean server/private companions
and separate IR files; legacy IR is embedded in its olean unless a separate IR
signature is present. The first import root controls selection. An incomplete
earlier olean cannot be treated as ready because a later root is complete.
Missing companions use bounded owned repair or fail explicitly. A missing module outside that
finite fallback fails with its name; the job does not start a bulk Mathlib
build. Shared or global cache state is not changed.

The proof stage compiles all 13 inherited modules, all 55 ported modules and
both new mathematical modules into a fresh owned import directory. All 70
modules use `-DautoImplicit=false` and `-DmaxSynthPendingDepth=3`. It then runs
the full reviewed probe with those strict options and checks its actual output.
Project artifacts from prior stages or CI caches do not satisfy this build.
The job rechecks source admission after compilation and retains the raw probe
and all stage receipts. Dependency cache imports remain ordinary development
dependencies; this is not a complete dependency rebuild.

This candidate is frozen for source, configuration, attribution and inventory
review. Its focused CI has not run. Hosted systemd behavior, Cache bootstrap
and fresh Linux compilation must qualify the exact reviewed candidate before
publication. The inherited 1664 dispatcher/map still describe their original
1727-path composition. This additive chart source admission does not claim that
their unchanged release route admits the enlarged chart tree. Any necessary
finite release adapter requires separate review. Their original validator
bodies and bootstrap semantics remain intact.
Historical source binding and full master admission remain pending.

Point4 and both general targets remain OPEN. Global chart coverage,
evolving-family comparison, upstream global chosen-connection equality,
curvature and Ricci comparisons, and PDE existence remain OPEN.


## Geometric Ricci extension on PR138

This extension starts from published PR138 head `3818bef6722e8c9810739a9fce26b5ec07bec98a`,
tree `990d9fbe4fc8994c9dbafe278bbc1ccc71371f7b`, sole parent
`9e24ec38b8f11d8720a8c1bce638cdb54bbec0d2`. Its corrected finite tests are
preserved byte for byte. The 13 inherited project sources match PR135 support
`90322f1d63e4798afa385fa2c160edf07365191b`, tree
`1379f674eafee5e4545b5ea80cf940e43ac47f09`. PR135 merged at
`79ac3111a438dee1bf3b800e403e1c1a7824046a`; that commit is the future master
destination. Integration onto master remains UNRUN.

The 23 added Lean files are 13 proof sources and 10 probes. Their reviewed
bytes identify the actual chosen connection, curvature components and Ricci
trace in the chart frame. On the genuine `chartLeviCivitaGoodSet`,
`ChartPort.chartRicciTensor_eq_timeFamilyChosen_ricciCurvature` identifies
`chartRicciTensor (g t) α i k` at the chart coordinate of `x` with actual
chosen `ricciCurvature x (frame i x) (frame k x)`. The retained transposed
trace theorem supplies arguments `k,i`; genuine project Levi-Civita Ricci
symmetry gives the same-order result. Every metric and regularity instance
comes from the exact `g t` through the existing proved `SmoothForward.toC2`
and chosen family. The good-set and M-scoped boundarylessness premises
remain explicit; there is no `NeZero`, unrelated ambient metric, assumed
compatibility, curvature or symmetry certificate.

The reviewed desktop evidence uses official Lean 4.33 and Mathlib `db584`.
Rank-zero, actual zero trace for arbitrary tangent vectors, empty-manifold,
metric-C2 and chosen-Levi-Civita probes passed with standard axioms only.
These retained identities authorize reuse of the mathematical bytes.
Hosted qualification of this dependent draft remains **UNRUN**.

The original 70-source rebuild and `ChartIdentityEvidence` gate remain
required. CI then rebuilds all 13 added proof sources and executes all 10
added probes with exact per-probe declaration and axiom contracts. The
admitted union is 94 modules; successful compilation requires 83 source
emits and 11 probes. Legacy and extension verdicts are recorded separately,
and combined success follows the final exact physical admission. The
terminal-process correction changes `owned_process_identity` and `run`.
All other original helper bodies, deadlines, strict flags, dependency pins,
artifact validation and first-failure reporting remain unchanged. The
original finite 31-source fallback remains; a missing import outside it
still stops the build explicitly.

Existing `DifferentialGeometry` and `ChartPort` Lake registrations cover all
new paths. Their strict options and default targets are unchanged. A named
ordinary target is `lake build +ChartPort.ChosenChartRicciSameOrder:olean`.
That normal-Lake build is unrun; focused CI uses the existing owned serial
compiler in the actual admitted Lake environment.

Published `9e24ec3` had eight positional fixture failures. The reviewed
PID-order correction is published at `3818bef` on existing PR138.
Run `37554812585`, job `112578498292`, passed ordinary controls, source
admission and official setup, then failed at `cache-bootstrap-4` with
"More than one Lean compiler in an owned stage". The old fixture failure
is resolved. That run supplies no current port proof pass.

The finite model explicitly supplies the mandatory extension fields,
13 synthetic source rows and ten synthetic probe rows. Every old assertion
and the published PID-order fix is retained. Seven schema controls cover
complete execution, missing fields/contracts, incomplete counts, changed
source bytes, rejected probes and setup-only mode. These synthetic fixtures
are ordinary driver controls, not Lean mathematical evidence.

The separately frozen terminal-process correction is composed here. The
authenticated native snapshot reported a child in state Z with zero RSS,
an absent executable and no observed argv. This does not establish that
child's executable or purpose. `owned_process_identity` now performs a
second stat read for an initially Z row. Both observations must retain
Z, matching PID, parent, group, session and start time, equal group/session,
and zero RSS. A failed or malformed read or any mismatch retains the
conservative compiler count. `run` excludes only that verified terminal
row from the current count. The exact prefix-query predicate is unchanged.

All owned rows remain in snapshots and RSS accounting. The one-compiler
limit, two CPUs, 6 GiB RSS, zero swap, -j1/-M5632 heap/thread flags,
deadlines, kill/reap and survivor rejection remain required. A surviving
zombie still fails cleanup. Alive, unreadable, raced and pre-exec images
retain conservative counting. Linux process semantics are documented at
https://docs.kernel.org/filesystems/proc.html and
https://man7.org/linux/man-pages/man2/wait.2.html .

The combined candidate passes 62 ordinary controls locally: 60 passed,
two genuine Unix checks remain UNRUN on Windows. No Lean compiler ran.
Both separate packets and all failure history remain preserved. Independent
task8 review precedes a source-only draft update to existing PR138. Hosted
new qualification, master integration, Point4 and both general targets
remain OPEN or UNRUN. Merged master79ac is a future destination.
