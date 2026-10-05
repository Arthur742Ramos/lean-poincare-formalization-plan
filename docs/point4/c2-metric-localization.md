# Literal C² initial metric localization

This is an authored supporting proof candidate. It has **not** yet passed exact
Lean 4.33 verification or independent mathematical review. It does not construct
the canonical Ricci-flow theorem. Point 4 remains **OPEN**.

## Intended theorem boundary

`AnalyticPDE/BoundarylessInitialMetricLocalization.lean` reads an actual
`Bundle.ContMDiffRiemannianMetric I 2 E TM` in the preferred tangent frame and
inverse chart. The endpoint `exists_initialMetricLocalizedHeatData` selects
`Module.finBasis ℝ E` internally. It does not receive a chart, cutoff, matrix jet,
derivative witness, positive-rank certificate, or positive initial Hölder
certificate from its caller.

The stronger in-basis and internally selected-basis constructions are local:
compactness of the whole manifold is unnecessary for this localization. The
final public signature explicitly retains its existing local geometric class
parameters. The probe has both an independent-universe bare-constant assignment
to that entire expected function type and a specialization under the complete
current compact-manifold contract context. A separate fixture attempts to
synthesize completeness, sigma compactness and tangent-bundle C² structure
from the minimal geometric context. These probes still need compilation.

The local model domain is the preimage of the actual preferred chart target
under `PreferredCoordinateFrame.toModel`. Openness comes from the already
published `BoundarylessChartTransport` theorem under the geometric hypothesis
`BoundarylessManifold I M`. No global `I.Boundaryless` instance is added. The
existing chosen-LC, curvature, frozen-heat, weak-Laplacian and gauge consumers
are unchanged.

The candidate proves local C² regularity by evaluating the actual metric on
actual local frames, composing through the inverse chart, and changing finite
basis. Positive definiteness at the localization point is the genuine Gram
positivity theorem. The matrix extension is symmetric, agrees with the actual
metric near the point, and equals that point's positive Gram matrix outside
the compact cutoff support.

## Actual derivative construction

`Analysis/CompactlySupportedC2Jet.lean` evaluates ordinary Fréchet derivatives
on `Pi.single k 1`. First and second coordinate rows are actual differentiated
functions. Their ordinary coordinate-curve `HasDerivAt` witnesses come from
`Function.update`; the second row is identified with the actual twice-Fréchet
derivative. Compact support propagates through each derivative. Continuous
compact support supplies boundedness and uniform continuity of every Hessian
entry. This does not assert an initial Hölder exponent or use a third derivative.

`AnalyticPDE/EuclideanC2Localization.lean` packages those functions into the
existing `EuclideanBoundedC2Data`, adds the frozen constant without changing
the derivatives, and instantiates the proved PR124 global zero-time C² heat
trace. The inherited right-initial heat generator remains a right derivative;
the candidate does not claim an ordinary time derivative for the constant
negative-time continuation.

## Uniform positivity on the entire model

`Analysis/FiniteCoordinateBilinear.lean` constructs the actual finite matrix
contraction as a continuous bilinear form. Its sup-norm bound has the explicit
factor `d²`. The coordinate basis change is never treated as an isometry.

`AnalyticPDE/PositiveFrozenC2Localization.lean` derives a positive coercivity
constant for the pointwise Gram form. Rank zero is handled internally. It
chooses an actual open neighborhood where the bilinear perturbation norm is
less than half that constant, then constructs a cutoff in `[0,1]`. The frozen
extension dominates half the original constant times the squared coordinate
norm everywhere, including outside the chart. This is stronger than a
positivity bound on a compact chart core alone.

## Dependency and verification discipline

The source-only constructor work started at exact PR124
`ba47fe1f4d8efad8bad68c61b4d25d0d8ff5387e`. The initial, historical endpoint
worktree combined that lineage with current master by a real uncommitted merge.
Its `aae38ed395ba2bdf141860b22b8ab9d4273433189648f337e25d3c8b2e263a19`
source archive was rejected for publication because an inherited source-union
release guard did not accept the additive localization scope. The mathematical
source review was positive; no compiler had checked those modules.

The coherent current unit is based directly on exact source-reviewed PR129
`fe921dbc34918d22389e87f30bdffb73ed7ebeb9`, which retains real current-master,
PR124 and PR127 ancestry. Its own exact Lean4.33 qualification is still pending.
Qualified mathematical source was not copied or rewritten. All five standalone
localization proof blobs and the full-signature probe are preserved exactly.

A single count-one, digest-pinned adapter is appended to PR129's combined
source guard. It expands only the explicit inherited/new source, import and
provenance union. Original geometry and weighted guard adapters, every inherited
workflow, all original9integration and13geometry fixture semantics,150 inherited
axiom occurrences, seven boundaryless type checks, and full canonical gates
remain in force. The focused workflow checks these alongside the ten new actual
localization axiom surfaces. No inherited workflow is changed.

Any development probe using restored Lean 4.35rc2 is development evidence only.
The pinned Lean 4.33 build, exact declaration/type/axiom probes, source audits,
and independent review are still required before this candidate is qualified.

The focused release guard locks all inherited files apart from the explicit
import/provenance/README integration surfaces, the five new proof-module hashes,
the full-signature probe, original toolchain/Mathlib manifest, and original
contract/auditor source. The one allowed inherited guard transformation is
reconstructed from the exact PR129 input; arbitrary guard or workflow drift is
rejected. Exact metadata bytes outside the provenance list are retained, even
when a changed spelling or numeric type would parse to an equal value.
It rejects duplicate YAML/provenance identities, tracked compiled caches,
unexpected imports and any canonical target. The original twenty plus nine
adapter/provenance/evidence tests distinguish the intentional missing-target
OPEN verdict from a bad newly introduced target or a failed/fast build.

The new focused workflow records exact HEAD/parents, an all-source SHA256
manifest, the actual Lean version and actual Mathlib checkout. It preserves
early derivative/metric build logs, axiom/type output, and the unchanged full
five-gate audit with an always-run evidence upload. The official metadata schema
is pinned to upstream commit
`99c678e569c7c4c0772db297c5ddd5e4c9b6322e`, `schema/v0.4.schema.json`, SHA256
`25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce`.

The first capped local rc2 probe aborted before checking its first Mathlib source
with exit 134 because its thread pool could not be created under the 3 GB virtual
memory guard. The log is preserved as inconclusive development evidence; no
source module was checked. Shared caches were unchanged. A later separately
admitted single-worker probe or exact hosted verification is still needed.

## Historical exact-toolchain failure and narrow repair

Exact source-reviewed draft `b29304efd90232b11b42fd7ab7d659e018a837dc`
failed focused Lean 4.33 CI run `37259615397` at the first two generic
modules. The compact-support constructor was incorrectly qualified, and
the finite-matrix adapter needed explicit Pi evaluation, projection types
and the actual finite-sum differentiability API. All later metric, signature,
axiom and canonical-audit steps were skipped. The failed source and logs
remain historical; the initial source review was not compiler certification.

The narrow repair uses the pinned Mathlib global `ofCompactSupport`, explicit
Pi add/sub evaluation and typed real projection maps, and `ContDiff.sum`.
No theorem statement, metric regularity, geometric hypothesis, derivative
meaning, inherited source/workflow or canonical gate changes. Updated new
proof-module hashes identify the repaired authored blobs; old b293 hashes
remain in its immutable history. The repaired source still needs independent
review and a new complete exact-head Lean 4.33 run before qualification.

## Historical nested-operator instance failure and proof-local candidate

Exact source-reviewed draft `e0231c3458c25115a0afabe7244a62e0716b204c`
failed focused Lean 4.33 CI run `37261014410`. The actual compact-support
constructor compiled, but `FiniteCoordinateBilinear` could not synthesize
`NormSMulClass` and `IsBoundedSMul` for the nested continuous-linear-map
codomain. A subsequent heartbeat timeout also occurred in the matrix norm
proof. The remaining metric modules, full signatures, ten new axiom surfaces,
150 inherited axiom occurrences and full canonical audit were not verified by
that failed run. The exact e023 source and failed result remain historical.

This proof-local candidate uses Mathlib's `opNorm_le_bound₂` directly on the
unchanged actual finite contraction. Its real-valued double sum is bounded
using two explicit `mul_le_mul` inequalities per entry, the finite Pi sup-norm
bounds and the same dimension-squared factor. No nested scalar-norm search or
heartbeat increase is needed for that estimate. The smoothness proof explicitly
supplies Mathlib's existing `ContinuousLinearMap.toNormedSpace` instances for
the inner real dual and outer real bilinear map, together with the derived
`IsBoundedSMul` instance.

It changes no theorem statement or hypothesis, matrix contraction,
dimension-squared sup-norm bound, inherited source, workflow, pin or canonical
gate. The new matrix-module hash identifies the authored candidate. A bounded
Lean 4.35.0-rc2 development run compiled this finite module without raising the
default heartbeat limit. That is development evidence only. No pinned Lean
4.33 compiler pass or independent review is claimed; all release gates remain
required.

## Remaining mathematical gaps

This local constructor does not discharge anisotropic inverse-Gram heat
transport, quantitative non-isometric model/basis norm factors for that
transport, compatible atlas overlap and assembly, weighted nonlinear PDE
closure from literal C² data, manifold realization, recovery-gauge regularity,
ordinary endpoint time derivatives, or uniqueness against the original weak
competitors on common closed intervals. No canonical Point-4 declaration is
added and no completion-auditor semantics are changed.
