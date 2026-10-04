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

A static source review found substantive existence and uniqueness statements
with actual Ricci-flow differential equations. That is useful evidence for
selecting the candidate, but it is not a kernel rebuild of the full import
closure. The workflow result, exact source and audit commit, printed signatures,
and axiom output must all be checked before claiming verified upstream reuse.
Failure, resource exhaustion, or a timeout must remain a reported blocker.

Even a passing upstream audit leaves a semantic integration obligation. The
upstream existence endpoint assumes a smooth initial metric and a boundaryless,
positive-dimensional compact manifold. It returns a jointly smooth metric
family with a one-sided initial-time Ricci equation. Upstream forward uniqueness
uses its own jointly smooth candidate class and an inner-product model space.
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

## Running the audit

The workflow `Point-4 upstream Hamilton release audit` performs the pinned
checkout, source preflight, official Mathlib cache setup, topologically ordered
source compilation, and final signature/axiom probe. The local audit entry point
is `scripts/point4/audit-hamilton-release.py`; it requires a fresh exact upstream
checkout and the upstream pinned Lean/Mathlib environment. It intentionally does
not invoke the upstream umbrella library target.
