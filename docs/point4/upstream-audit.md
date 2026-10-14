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

The prior bounded-batch audit plumbing reduced repeated Lake graph planning while retaining
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

Twenty-three bounded Python mock tests cover the old scheduler plus chain ordering
and width, fresh-object rejection, exact argument forwarding, genuine nonzero
and signal exits, timeout and fake-success failures, missing/duplicate/unexpected
records, dependency evidence, per-launch memory/disk guards, concurrent lock
bounds, untouched official files, metadata forwarding, setup/log tampering, and
the unchanged endpoint signature/axiom gate. A scoped SIGTERM handler marks
cancellation inconclusive and restores the previous handler. Cancellation drains
the detached Lake process group under a 30-second graceful wait followed by
SIGKILL and a five-second final reap bound; remaining descendants are killed even
if Lake exits first. Every exited Lake group is conservatively drained,
including success, nonzero, and signal exits, while retaining Lake's actual exit
code. Signals during process creation are deferred until the
cleanup handle exists, without blocking SIGTERM in the child. Two cancellation
regressions send actual SIGTERM to disposable Python mocks, including a child
and grandchild that ignore SIGTERM. Another actual-process regression checks
owners that exit first with code zero, code seven, or SIGKILL while leaving
living descendants. These tests execute no Lean build.
A fresh complete hosted run was still required to verify that audit code.
Point 4 remained **OPEN**; no canonical contract or semantic bridge was changed.

## Current source-only persistent-plan optimization

Candidate `44fad5fc56c5b3a9b9e0303554920d1c50c699fc` did not obtain a
complete certificate. Its [run 37234261245](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37234261245)
was cancelled at the unchanged 350-minute limit after **1,728 of 2,270** actual
project compiler exits succeeded. The other 542 project sources and the two
endpoint probes remained unchecked. No source/trust defect or failed source
compiler was found. Repeated verbose cached-job replay contributed roughly
483 MB of aggregate logs. The historical complete certificate above remains
historical and does not qualify this candidate or this new implementation.

The focused optimization adds `build-hamilton-batches.lean`, an audit-owned
orchestration driver using the public APIs of official Lean/Lake 4.29.0 at
[`98dc76e3c0a9b856c9b98726b713fb04fab16740`](https://github.com/leanprover/lean4/tree/98dc76e3c0a9b856c9b98726b713fb04fab16740).
It loads the official workspace once and calls `Workspace.runFetchM` once.
Within that call, it fetches only the current bounded chain batch, waits for
its official Lake job, and then advances. The same 347 two-chain batches, or
705 one-chain fallback batches, remain; only each chain's tip is requested,
since direct imports reach all earlier members. A persistent official
`BuildStore` retains completed jobs and graph work within this fresh build.
It does not import prior-run project objects, an upstream artifact cache, or
an alternate source closure. Every module still requires its own new observed
compiler invocation and object hash.

The official implementation establishes this store lifetime:
[`Workspace.startBuild` and `runFetchM`](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/lake/Lake/Build/Run.lean#L324-L359)
create one fresh store for the entire action;
[`FetchM`](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/lake/Lake/Build/Fetch.lean#L47-L103)
keeps its reference across sequential fetches.
[`buildSpecs` and target parsing](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/lake/Lake/CLI/Build.lean#L54-L55)
use the same target/facet machinery as the CLI;
[`Job.await`](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/lake/Lake/Build/Job/Monad.lean#L190-L193)
waits for actual job completion and throws on failure. Neither a hand-built
compiler command nor a reconstructed setup file is introduced.

### Quiet frontend, unchanged compiler boundary

`BuildConfig` explicitly uses quiet verbosity, warning output, error failure
threshold, and no ANSI. Official Lake still retains and reports failing jobs;
individual compiler logs remain lossless evidence independent of the frontend.
The driver does not spawn all 2,270 targets at once or rely on an undocumented
concurrency option. Only two chain tips are fetched at a time, and every later
chain member directly depends on its predecessor. The existing real-compiler
file locks remain a second independent worker bound. An atomic active-batch
permit rejects compilations outside the current planned batch and is hashed
into each compiler record; changing it during a compilation fails the audit.

The original persistent-plan frontend used the actual pinned compiler running the driver with
its official `libLake_shared.so` plugin. The complete frontend argv and plugin
hash are recorded; the plugin loads official Lake native functions and
initializers, as specified by
[Lean's loader](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/Lean/LoadDynlib.lean#L92-L103)
and [Lake's installation paths](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/lake/Lake/Config/InstallPath.lean#L151-L160).
This affects only orchestration. Each project compilation still invokes the
same actual compiler with unchanged Lake-generated argv, `LEAN_PATH`, original
options, and untouched `--setup` JSON through the existing observation shim.

`Env.compute ... (some true)` is exactly the official no-cache switch:
[`Env.compute`](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/lake/Lake/Config/Env.lean#L163-L175)
sets `noCache=true`, disabling automatic package release/cache retrieval.
`LAKE_ARTIFACT_CACHE=false` and empty `LAKE_CACHE_DIR` still disable root
artifact caching and the system artifact cache. The audited immutable TOML has
no package-level cache override. Workspace loading explicitly forbids
requested dependency/toolchain updates; the resolved manifest already exists
and is checked before the driver starts. Official pinned Mathlib dependency
objects retain the same separate permitted cache boundary.

### Lossless logs, actual resources, and cancellation

The observer sends actual compiler stdout/stderr directly into indexed files,
then forwards the same bytes to Lake using at most 1 MiB Python copy buffers.
Hashes are also calculated in bounded chunks. This removes Python's complete
per-compiler output capture and the parent audit's bulk frontend-log read/replay.
Lake's own internal job logging is unchanged. One lossless quiet frontend log
replaces repeated verbose batch logs; it is hashed and retained, while console
updates contain compact actual-success counts.

There remain at most two real compiler workers plus one persistent Lake
frontend, with small observation launchers. The second compiler still requires
8 GiB available memory; every launch still requires 1 GiB free disk, and smaller
machines still use one compiler. Launch observations record those quantities.
Linux reaped-child resource accounting records actual compiler user/system CPU
and maximum RSS. Periodic `/proc` snapshots record frontend CPU/thread count and
frontend/group RSS. Group RSS is a sum, so shared pages can be counted more than
once, and snapshots can miss short-lived peaks. These are observed resources
and enforced worker/launch-floor bounds, **not** hard CPU or resident-memory caps
or a wall-time guarantee. No compiler memory flag, VM cap, thread-count change,
runner upgrade, extra cache, or timeout extension is introduced.

Source compilation and the unchanged actual two-endpoint signature/axiom probe
both use the existing bounded process-group cancellation cleanup. Signals during
spawn remain deferred until the cleanup handle exists. Cleanup retains partial
files and refreshes records before propagating interruption. Waiting, running,
interrupted, missing-log, resource-blocked, or nonzero results remain
inconclusive or failed; they cannot become successful compiler exits.

### Acceptance gates and verification limits

A batch record contains `lake_job_success`, not an invented per-batch process
exit: all batches share one frontend process. Passing requires that actual
frontend process to exit zero, all indexed batch jobs to finish successfully,
and every expected module to have its own successful real compiler record
bound to the correct batch. Lake monitor failure remains decisive even if
batch job completion succeeded. The original source/setup/log/object hashes,
exact pins, source/trust scans, fresh-project-object checks, clean tracked
sources, complete module set, and both actual endpoint signatures and allowed
axioms are still required. Driver, plugin, and plan hashes must remain unchanged.

Thirty-four Python regressions pass without executing Lean or upstream code.
New coverage includes lossless multi-megabyte/binary mock-child output, bounded
log reads, missing stream logs, partial logs on interruption, active-batch
mutation, cancellation while waiting for a worker slot, per-batch completeness
and target/index tampering, adversarial dependency completion order, actual
frontend process-resource sampling, and invalid launch-resource evidence.
Existing actual SIGTERM/spawn-race/dead-owner descendant cleanup tests remain.
The static driver contract test is **not** an API typecheck or kernel certificate.

Those initial source-only checks did not establish runtime correctness. The
subsequent exact-toolchain driver elaboration and runtime failure are recorded
below. A fresh complete hosted run plus independent artifact review is still
required before this audit implementation can pass. A typecheck alone does not
establish runtime correctness, throughput, a complete source rebuild, or either endpoint.
Point 4 remains **OPEN**, with its canonical contract and missing semantic
bridge unchanged.

## Runtime failure and source-only native entry repair

The first persistent-driver candidate failed elaboration because `prefix` is a
reserved token in Lean 4.29. Renaming that local variable to `batchPrefix` did
not change scheduling or verification. The repaired exact candidate
`82d0a0e01a2a0669041c27f019205ca49b688665` passed its driver-only elaboration
but [run 37264715366](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37264715366)
then failed at runtime: the frontend exited **−11**, with **0 of 2,270** actual
source compiler successes, zero batch records, and an empty frontend log.
Neither endpoint probe ran. This is a failed orchestration run, not a
kernel-verified source closure. Artifact `11325608152` and all prior failure
reports retain their original identities and outcomes.

An independently fresh tiny TOML workspace with one local `lakefile.lean`
dependency reproduced the fault while stock native Lake loaded the same
fixture successfully. In that benign reproducer the immediate failure was a
null reference read of the configuration loader's builtin-initialized import
environment cache. Attribution of the untraced CI failure to the same mechanism
remains a strong inference. The official
[loader cache declaration](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/lake/Lake/Load/Lean/Elab.lean#L28-L38)
and [C initializer emission](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/Lean/Compiler/IR/EmitC.lean#L890-L938)
explain why initialization of the narrower `Lake` plugin root can leave an
additional loader module's builtin reference uninitialized. No manual access
to that private cache or unsafe initializer-flag workaround is introduced.

### Supported native bootstrap

The repair compiles only the audit-owned driver as a stable
`HamiltonAuditDriver` module. The exact official compiler emits C, and the
official `leanc` wrapper compiles and links it with the official static
`libLake.a`. The plugin is used only while elaborating the driver in the
compiler process; the resulting native frontend does not load that plugin.
The compiler-generated
[native main](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/Lean/Compiler/IR/EmitC.lean#L320-L352)
calls `initialize_HamiltonAuditDriver(1)` before ending initialization and
starting the task manager, recursively initializing the full explicit import
closure. Static checks reject generated C lacking that main, builtin argument,
startup order, or any driver-root import initializer.

The build uses the official
[leanc wrapper](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/Leanc.lean)
and its printed C/link flags. `-DLEAN_EXPORTING` follows the SDK's shipped
`share/lean/lean.mk`; `-rdynamic` is Lake's documented Linux
[supportInterpreter link mode](https://github.com/leanprover/lean4/blob/98dc76e3c0a9b856c9b98726b713fb04fab16740/src/lake/Lake/Config/LeanExe.lean#L79-L102),
needed to interpret ordinary dependency configurations. No linker-security
setting, plugin alias, injection, debugger, or signal/backtrace diagnostic is
part of this repair.

Because the native executable lives in the audit evidence directory,
`IO.appPath` no longer identifies an SDK installation. The driver requires
the observer-selected `LEAN_SYSROOT` and `LAKE_OVERRIDE_LEAN=true`, uses
`findLeanInstall?`, and constructs `LakeInstall.ofLean` from that selected
installation. The selected native application, compiler launcher, SDK root,
Lake library directory, shared-library path, and git revision are recorded and
checked. The actual source compiler identity remains separate from the native
bootstrap/executable identity, and every real compiler still passes through
the unchanged observer with its untouched Lake-generated argv/setup.

`native-bootstrap/bootstrap.json` retains version/revision metadata, the exact
elaboration, C compilation and linking argv, real exits/timing, lossless logs
and their hashes, generated C/object/native-executable hashes, source-copy
identity, official compiler/leanc/bundled-compiler/linker/static-library/plugin
identities, and the SDK import source/object/interpreter-IR graph. A complete
per-file `bin/include/lib/share/src` SDK catalog records **13,883** entries,
including shared-library variants, bundled LLVM/clang/C++/unwind libraries,
headers/support files and symlink targets. Escaping or cyclic links fail closed.
A path-independent catalog digest is pinned to the checksum-verified official
Linux release archive; bootstrap and verification require that exact digest. Source-only enumeration of
the checksum-verified SDK finds **1,068** modules reachable from implicit `Init`
and explicit `Lake`, `Lake.CLI.Build`, and `Lake.Load.Workspace` roots. Each
runtime bootstrap independently records and verifies its actual closure.
Only necessary nonsecret environment keys are recorded; the full environment
is never dumped. Caller compiler overrides and loader injection variables are
removed for the bootstrap. Historical diagnostic files remain preserved but
are never compiled, loaded, or invoked by the audit.

### Bounded native preflight and unchanged acceptance gates

The workflow first bootstraps the reviewed native driver, then runs it against
an isolated TOML-only toy root with **two distinct local Lean dependency
configurations with different import headers** and one benign project source.
The distinct headers force two import-cache misses rather than a second hit
on the first configuration's import environment. That run uses the same native
executable and the same real-compiler observer, starts from no project objects,
requires one fresh successful compiler record/object, complete setup/log
hashes, a completed Lake batch, the exact selected installation, and unchanged
fixture/plan/control/native identities. Its view is removed without touching
SDK files. Each bootstrap command has a 600-second bound; the toy frontend has
a 180-second bound. Timeout or cancellation retains inconclusive evidence and
uses the existing bounded process-group cleanup. A failed or missing preflight
prevents the expensive upstream rebuild.

The source launcher invokes only the verified native executable with the
plan and evidence paths. All original upstream and Mathlib pins, source/trust
scans, 2,270-module/64,667,615-byte closure, fresh project-object checks,
at-most-two compiler workers, 8 GiB second-worker launch floor, 1 GiB disk
floor, observer argv/setup/source/log/exit/object evidence, bounded
cancellation, disabled project/system caches, and both actual endpoint
signature/axiom gates remain required. Bootstrap/preflight success is not an
upstream kernel certificate or a semantic bridge.

**This repair is source-only and unverified by Lean, C compilation, linking,
or native execution.** Forty-five Python/static regressions pass, with all
new compile/link/native actions mocked. Two additional local admission-helper
regressions mock cancellation and verify detached-child cleanup. The admission
helper uses the same scoped SIGTERM-to-exception handler; its bounded owner
allows 45 seconds for the helper's 30+5-second cleanup, plus five seconds for
final owner reap. The original diagnostic owner is not reused. Fresh independent
source review must
precede separately admitted ordinary exact-SDK bootstrap and bounded toy
execution. Then exact-head full CI and independent artifact review remain
required before merging. Existing current-master geometry guards are not
waived. Point 4 remains **OPEN**.

## Running the audit

The workflow `Point-4 upstream Hamilton release audit` performs the pinned
checkout, source preflight, official Mathlib cache setup, bounded-chain
source compilation with one quiet persistent official Lake plan and real
compiler observation, and final signature/axiom probe. The local audit entry point
is `scripts/point4/audit-hamilton-release.py`; it requires a fresh exact upstream
checkout and the upstream pinned Lean/Mathlib environment. Its
`--bootstrap-only` and `--native-preflight-only` gates must pass on the same
driver/SDK/executable before an ordinary full invocation. It intentionally does
not invoke the upstream umbrella library target.
