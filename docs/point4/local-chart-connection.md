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
