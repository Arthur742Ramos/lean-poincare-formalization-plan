# Exact-candidate build cache pilot

The actual Gaussian heat resolvent uniqueness workflow pilots reuse of
`curvature/.lake/build` for the **same candidate**. Every existing explicit Lake
target, focused rejection test, whole-signature probe, kernel/axiom guard, pinned
version check and Source authentication still runs. A cache hit gives no proof
credit. No mathematical conclusion follows from the cache inventory.

This pilot additionally builds the joint metric-defect component target and
compiles its complete signature assignment and `Fin 0` specialization probe.
Both explicit build targets occur in the cache identity. The added gate requires
one ordered type-output marker group and exactly the assignment and theorem
axiom records, with unique standard axiom names only. Since the frozen probe
prints universes, the gate permits a bounded universe suffix on those standard
names and retains the raw values in its log. The complete literal signature and
zero-dimensional specialization are checked by native Lean elaboration; rendered
axiom text alone does not establish them. Actual per-candidate native receipts
are required before proof credit; Source review alone supplies none.

The pinned Lean action's GitHub cache is disabled because its package-root key
and early save do not implement this pilot's contract. Its official Mathlib cache
remains enabled. Dependency sources, dependency `.git` directories and dependency
build outputs are not in this additional cache. The pilot changes one workflow;
it does not rewrite the other Point-4 workflows or their 74 explicit targets.

## Identity and origin trust

The key binds the actual checkout HEAD and tree, source repository, GitHub
repository/ref/workflow identity, operating system, architecture and runner image;
the package's actual toolchain, compiler version/commit and executable hash;
`curvature/lake-manifest.json`, `lakefile.toml`, effective package options and
hashed Lean/Lake/compiler option environment; every resolved dependency revision
and tree; the committed bytes of the local Hamilton path dependency and package;
and the literal target list and build arguments. Dirty tracked source, a changed
dependency revision or a changed identity between phases fails. No restore-key
prefix or cross-platform fallback is used. Workflow and candidate changes produce
new keys; this pilot makes no cross-candidate reuse claim.
Nonempty `LEAN_*` or `LAKE_*` environment overrides are unsupported and fail
before use: hashing an external search path does not authenticate its contents.

Origin trust comes from the GitHub Actions cache service's repository/branch
scope and the reviewed workflow's declared writer. The inventory is an integrity
check, **not a signature or independent proof of who produced a cache**. The
trusted repository's ability to run other workflows/write caches is part of this
boundary. A pull-request cache stays within GitHub's pull-request ref scope;
fork PRs must not receive privileged credentials or a `pull_request_target`
writer. This workflow keeps `contents: read`, uses `pull_request` or manual
dispatch, and does not add credentials, secrets or a separate privileged writer.
GitHub may refuse a save or evict an entry. Correctness does not depend on a hit.

## Restore and save

The cache action, pinned to `caa296126883cff596d87d8935842f9db880ef25`, restores
only into a runner-temporary transport directory. Before candidate outputs are
replaced, the helper requires an exact matched key, identical identity and a
closed finite inventory of regular files, modes, lengths and SHA-256 hashes.
Symlinks, special files, traversal, duplicate JSON keys, case aliases, extra or
missing files and corrupt bytes fail. The bounded inventory allows at most
100,000 files and 8 GiB of file bytes. A verified staging copy is renamed into
place; a failed final verification restores the previous output directory.

A clean cache miss proceeds to all mandatory compilation and proof checks.
An incomplete or corrupt restore fails before compilation, rather than treating
its contents as usable outputs. A hit also proceeds to all mandatory checks.
The first candidate run must compile successfully on the cold path before this
workflow can write its snapshot. Only this pilot's post-success save step is
declared as a writer, after the existing final Source authentication succeeds.
The helper independently repeats identity validation before restore, snapshot
and report. An existing exact entry is not overwritten; a hit skips saving.

## Evidence and measurement

The helper's focused Python tests exercise key invalidation, corrupt/partial
inventories, traversal/alias/link rejection, staged restore and rollback. They
do not replace Lean compilation. The workflow artifact retains the cache log
and inventory alongside all existing proof logs. The job summary records actual
hit/miss, restored/output bytes, identity/validation/snapshot timing, restore
elapsed time and the save-action step outcome. Restore elapsed time includes
identity and transfer; elapsed-since-identity includes mandatory compilation.
Save-action wall time includes the surrounding action overhead. A successful
save step is not a claim that the provider stored an entry.

A speedup claim requires observed hosted cold and warm timings. Compare
repeated runs of the same candidate only after the hosted workflow has
passed all existing gates and produced those measurements. Cache absence never
relaxes a proof, source, version or axiom requirement.
