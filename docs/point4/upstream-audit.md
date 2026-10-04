# Exact upstream Hamilton release audit

This is an audit of a possible reusable proof source, not an import into the
curvature package and not a Point-4 completion claim.

## Immutable source and attribution

- Source: [qinz1yang/differential-geometry at
  `8bd406e35c33a200e9b88895cf11ee8429194e15`](https://github.com/qinz1yang/differential-geometry/tree/8bd406e35c33a200e9b88895cf11ee8429194e15)
- Paper: Bennett Chow, Yuan Liao, and Ziyang Qin,
  [A Lean Formalization of Hamilton's Three-Manifold Theorem,
  arXiv:2608.21502v1](https://arxiv.org/abs/2608.21502v1)
- Upstream license: Apache-2.0; retain the upstream LICENSE and NOTICE for any
  eventual reuse
- Upstream Lean: `leanprover/lean4:v4.29.0`
- Upstream Mathlib: `8a178386ffc0f5fef0b77738bb5449d50efeea95`

The audit checks out that release separately and compiles only the project-source
import closure of these endpoints:

1. `DifferentialGeometry.PDE.RicciFlow.ricci_flow_short_time_existence`, in
   `DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.Existence`
2. `DifferentialGeometry.PDE.RicciFlow.ricci_flow_forward_unique`, in
   `DifferentialGeometry.Geometry.Flow.RicciFlow.Extension.Construction`

The immutable source is compiled under its own toolchain and Mathlib pin.
Upstream proof modules are not supplied by a precompiled upstream cache.
The focused source closure is computed and scanned before compilation, and
the compiled endpoint types and axioms are retained in the workflow artifact.
Allowed endpoint axioms are exactly `propext`, `Classical.choice`, and
`Quot.sound`. The audit uses a read-only checkout and does not contact a
registry or grant access to a third party.

The source preflight supports Unicode module names. Its independently checked
combined endpoint closure contains 2,270 project modules and 64,667,615 source
bytes, including the full 1,635-module existence closure. This does not count
Mathlib's own transitive dependencies. Full-body placeholder/axiom and
execution/trust scans run after comment/string stripping; suspicious execution
or trust constructs stop the workflow for review before compilation.

## Evidence boundary

The fresh source rebuild passed in
[run 37193292343](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37193292343)
at audit commit `7e9f36a72f899b88f089d38ff51f11c6a053740d`, completed on
2026-10-04 at 13:51:35 UTC. All **2,270** project modules compiled with exit zero.
The graph, build order, compiled-module set, compiler-result set, and indexed
module logs agree exactly. Both endpoint signatures were printed, and each
depends only on `propext`, `Classical.choice`, and `Quot.sound`. Independent
artifact review checked these results against the source graph and audit code.

The evidence is preserved in artifact `11305411419`. Its `report.json` SHA-256
is `5784c244c7c4c5d4475e729cc5f5a5e68b82f6de864fb1e80865c231844da30a`.
This certifies the immutable upstream project-source closure under Lean 4.29.0
over the official pinned Mathlib cache; it is not a fresh rebuild of Mathlib's
own source and does not certify a Lean 4.33 port. The original incomplete run
and its evidence remain preserved below. Future failures, resource exhaustion,
or timeouts must still be reported without promoting them to a passing gate.

Even a passing upstream audit leaves a semantic integration obligation. The
upstream existence endpoint assumes a smooth initial metric and a boundaryless,
positive-dimensional compact manifold. It returns a jointly smooth metric
family with a one-sided initial-time Ricci equation. Existence accepts a
finite-dimensional normed model. Upstream forward uniqueness additionally
requires an inner-product model and `BoundarylessManifold`; it compares its own
jointly smooth, continuous chart-Gram candidate class.
The current Point-4 target uses different
metric/curvature constructions, allows arbitrary model-with-corners scope and
spatially `C²` initial metrics, and compares its broader recorded candidate
class. It also requires an ordinary, two-sided derivative at the initial time,
where the upstream existence endpoint supplies a one-sided derivative on a
half-open forward interval. Shrinking the terminal time handles the right
endpoint but does not prove the initial-time extension or missing regularity.
No equivalence, model-space transport, or regularity-extension bridge is
provided by this audit.

Thus Point 4 remains **OPEN**, and the canonical target, its solution predicates,
and the completion auditor are unchanged. A theorem-specific bridge or an
explicit reviewed scope decision is required before altering that contract.

## First independent source build and recovery

Exact candidate `8832fa011a0f3576e42cd8f03a66af476d822dcf` ran under the
configured 350-minute job budget in
[run 37174751920](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37174751920).
It ended cancelled during source compilation, with **1,807 of 2,270** project
modules successfully compiled and no failed module recorded. The endpoint
signature/axiom probe was not reached. This is an incomplete independent build,
not a source-error finding or a verified endpoint. Its report and build log are
preserved in artifact `11299626645`.

The historical `7e9f36a7` recovery rebuilt the entire immutable closure from
fresh source, using at most two dependency-ready workers on the same standard public Linux runner.
[GitHub's runner reference](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)
lists that runner as free for public repositories, with four CPUs and 16 GB RAM.
That historical implementation used the same `lake --no-cache build
<module>:olean` command. A child is submitted only after all its project imports
have successfully compiled. No compiled upstream objects from the first run or
an external cache are reused. The worker count falls back to one on smaller
machines; memory pressure suppresses starting the second worker, and the 1 GiB
free-disk guard remains. Compiler exits and per-module logs are retained.

A source failure stops new submissions and retains results of independent
compilations already running. An interruption or incomplete graph cannot pass
the final gate. The original pinned source, dependency checks, trust scans,
endpoint type/axiom probe, clean-source check, and unresolved Point-4 bridge all
remain required. Small mocked scheduler tests check dependency ordering,
single compilation, worker bounds, failure handling, and resource-guard failure.
The workflow runs on pull requests and manual dispatch, avoiding the original
duplicate push-plus-pull-request audit.

## Documentation-only repeat and throughput correction

The documentation-only candidate `e161243f09dcdb72596ebb9a5e1949f5f33ad41c`
repeated the same audit code in
[run 37209311774](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37209311774).
It reached the unchanged 350-minute timeout on 2026-10-04 at 20:17:35 UTC,
with 1,981 successful project compiler-command results and no failed source
module or source finding recorded. It did not reach the endpoint probe. The
historical complete `7e9f36a7` certificate remains valid for its exact immutable
upstream source; it cannot be relabeled as passing current-head CI.

The new audit plumbing reduces repeated Lake graph planning while retaining
Lake's own original module configuration, dependency resolution, setup files,
and ordinary Lean compiler/kernel invocation. It partitions the 2,270-module
source DAG into batches covered by at most two explicit direct-import chains.
Every module after a chain's first module directly imports its predecessor.
Every off-batch project dependency must already have a successful real compiler
record in an earlier batch. A single official `lake --no-cache --no-ansi
--verbose build +<module>:olean ...` handles each batch. The pinned graph produces
347 two-chain batches, or 705 serial-chain batches on the smaller-runner fallback,
instead of 2,270 separate Lake plans. This is a structural planning reduction,
not a measured wall-time guarantee or a new kernel certificate.

### Compiler identity and unchanged compilation

The audit resolves the actual Lean 4.29.0 installation through the original
`lake env`, records its version and compiler SHA-256, and creates a separate
symlink view under the audit evidence directory. All official installation
files are unchanged. Only that view's `bin/lean` is a reviewed observation
launcher. Process-local `LAKE_OVERRIDE_LEAN=true` and `LEAN_SYSROOT` select the
view for the batch command. Before executing the actual pinned compiler, the
launcher restores the real `LEAN_SYSROOT` and `LEAN` values, forwards every
Lake-generated argument unchanged, and preserves Lake's `LEAN_PATH` and the
untouched `--setup` JSON. Metadata queries (`--githash`, `--version`, and
`--print-prefix`) also execute the real compiler with the real installation;
the launcher does not invent metadata or successful exits.

This routing is grounded in the official Lean 4.29.0 implementation:

- [Lake installation detection](https://github.com/leanprover/lean4/blob/v4.29.0/src/lake/Lake/Config/InstallPath.lean#L321-L323)
  honors the explicit sysroot, and
  [the override branch](https://github.com/leanprover/lean4/blob/v4.29.0/src/lake/Lake/Config/InstallPath.lean#L369-L374)
  selects it even when Lake is co-located with Lean
- [Lake's compiler action](https://github.com/leanprover/lean4/blob/v4.29.0/src/lake/Lake/Build/Actions.lean#L26-L77)
  supplies artifact paths, setup JSON, original arguments, and library paths,
  and rejects an actual nonzero compiler exit
- [The module build](https://github.com/leanprover/lean4/blob/v4.29.0/src/lake/Lake/Build/Module.lean)
  retains configured options and its complete transitive import-artifact setup

No direct-Lean emulation, source repair, import skipping, proof oracle, or
undocumented Lake concurrency flag is used. Ordinary Mathlib dependency objects
come only from the existing official pinned cache setup. Unexpected compiler
invocations, including a dependency-source compilation that would cross this
cache boundary, fail closed for diagnosis.

### Resource bounds and stronger evidence

The direct-import chains structurally bound ready project compilations to two.
The observer additionally holds kernel file locks through each real compiler's
lifetime. It checks the existing 1 GiB free-disk floor before every launch and
requires 8 GiB available memory before starting a second compiler. Smaller
machines retain a one-compiler fallback. A failure blocks further launches;
independent compilers already running may finish and retain their actual results.
The hosted timeout and standard public runner are unchanged.

Before compilation, two checks reject every precompiled project object in the
root source/build locations. Lake's project artifact cache and system artifact
cache are explicitly disabled in addition to `--no-cache`. Fresh evidence
directories, a source SHA-256 per module, exact closure size/bytes, and unchanged
tracked sources are mandatory. Every project import must have its own prior
successful real compiler record; aggregate batch success is insufficient.

The evidence format distinguishes:

- `compiler-results` in `report.json` (key `compiler_results`) and indexed
  `compiler-records/*.json`: actual individual Lean process return codes,
  complete argv, compiler/source/setup hashes, options, elapsed time, and
  resulting project-object hashes
- Indexed `module-build-logs/*.stdout.log` and `*.stderr.log`: exact individual
  compiler output, with recorded hashes
- Indexed `module-setups/*.json.gz`: losslessly compressed copies of the exact
  Lake-generated setup JSON used by each compiler, with uncompressed hashes
- `batch_results` and `batch-build-logs`: separate aggregate Lake commands,
  process exits, timing, and verbose output
- The actual final `#check @` signatures and `#print axioms` output, command,
  process exit, and log hash for both endpoints

Missing, duplicate, unexpected, interrupted, resource-blocked, or nonzero
compiler evidence cannot pass. A zero compiler exit without a newly produced
project object also cannot pass. Logs, setup files, sources, and final objects
are checked against their recorded hashes. Both actual signatures must appear
exactly once; the same three foundational axioms are the entire allowlist.
The symlink view is removed before artifact upload without touching its official
file targets. Historical evidence remains in its original format and is not
rewritten to match this new format.

Twenty-two bounded Python mock tests cover the old scheduler plus chain ordering
and width, fresh-object rejection, exact argument forwarding, genuine nonzero
and signal exits, timeout and fake-success failures, missing/duplicate/unexpected
records, dependency evidence, per-launch memory/disk guards, concurrent lock
bounds, untouched official files, metadata forwarding, setup/log tampering, and
the unchanged endpoint signature/axiom gate. A scoped SIGTERM handler marks
cancellation inconclusive and restores the previous handler. Cancellation drains
the detached Lake process group under a 30-second graceful wait followed by
SIGKILL and a five-second final reap bound; remaining descendants are killed even
if Lake exits first. Signals during process creation are deferred until the
cleanup handle exists, without blocking SIGTERM in the child. Two cancellation
regressions send actual SIGTERM to disposable Python mocks, including a child
and grandchild that ignore SIGTERM. These tests execute no Lean build.
A fresh complete hosted run is still required to verify this new audit code.
Point 4 remains **OPEN**; no canonical contract or semantic bridge was changed.

## Running the audit

The workflow `Point-4 upstream Hamilton release audit` performs the pinned
checkout, source preflight, official Mathlib cache setup, bounded-chain
source compilation with real compiler observation, and final signature/axiom probe. The local audit entry point
is `scripts/point4/audit-hamilton-release.py`; it requires a fresh exact upstream
checkout and the upstream pinned Lean/Mathlib environment. It intentionally does
not invoke the upstream umbrella library target.
