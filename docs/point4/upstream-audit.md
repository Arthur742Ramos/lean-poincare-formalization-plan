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

The recovery rebuilds the entire immutable closure from fresh source, using at
most two dependency-ready workers on the same standard public Linux runner.
[GitHub's runner reference](https://docs.github.com/en/actions/reference/runners/github-hosted-runners)
lists that runner as free for public repositories, with four CPUs and 16 GB RAM.
Every project source module still uses the same `lake --no-cache build
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

## Running the audit

The workflow `Point-4 upstream Hamilton release audit` performs the pinned
checkout, source preflight, official Mathlib cache setup, dependency-ready
source compilation, and final signature/axiom probe. The local audit entry point
is `scripts/point4/audit-hamilton-release.py`; it requires a fresh exact upstream
checkout and the upstream pinned Lean/Mathlib environment. It intentionally does
not invoke the upstream umbrella library target.
