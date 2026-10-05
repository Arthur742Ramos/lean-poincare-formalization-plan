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
default heartbeat limit. That is development evidence only; it did not establish
a pinned Lean 4.33 compiler pass or independent review. The subsequent exact-head
run is recorded below. All release gates remain required.

## Historical frozen-constant derivative failure and narrow repair

Exact source-reviewed draft `b20e28ddb995f40e79b6a7b4b4003958e18602f7`
failed focused Lean 4.33 CI run `37263905782`. Both generic modules compiled,
and the actual compiler and Mathlib checkout matched the unchanged pins. The
metric-localization build then failed at `EuclideanC2Localization.lean:46`:
unrestricted simplification reduced the target by the constant-add derivative
equivalence but left the source as a pointwise function sum. The remaining
three metric modules, full signatures, ten new axiom surfaces, 150 inherited
axiom occurrences and full canonical audit were not verified by that run.
The exact b20 source and failed result remain historical, alongside the earlier
b293 and e023 failures and all development logs.

The narrow proof repair explicitly changes the goal to the constant-plus-value
coordinate curve, then applies the pinned Mathlib `hasDerivAt_const_add_iff`
equivalence without simplification. The value, first and second fields, every
theorem signature and hypothesis, and the derivative meaning are unchanged.
Only the Euclidean module's new authored-source hash is updated. No inherited
source, workflow, contract, pin or canonical gate changes. This repaired source
has not been compiled; fresh independent review and a complete exact-head
Lean 4.33 run remain required before qualification.

## Historical positive-frozen elaboration failure and narrow repair

Exact source-reviewed draft `5af5630b3f3553d4b6afd9c4fd04adc4fa62d308`
failed focused Lean 4.33 CI run
[`37268699381`](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37268699381).
Both generic modules and `EuclideanC2Localization` compiled against the
unchanged compiler and Mathlib pins. `PositiveFrozenC2Localization` then failed
at its incorrectly qualified coercivity lemma, unresolved cutoff-field and
constant implicit arguments, and a redundant `rfl` after an already closed
matrix rewrite. The remaining metric module, complete signatures, ten new
axiom surfaces, 150 inherited axiom occurrences and full canonical audit were
not verified by that run. The exact failed source and logs remain historical.

This narrow proof candidate calls the existing
`Bundle.ContinuousLinearMap.exists_pos_mul_sq_le_of_pos` from the unchanged
owned `RiemannianSection` source, explicitly supplies the actual perturbation
`w := fun x => F x - F x₀` and `contDiffOn_const (c := F x₀)` to the cutoff
proof, and removes only the redundant final `rfl`. The pinned Mathlib
[`contDiffOn_const`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/ContDiff/Basic.lean#L107-L108)
and
[`ContDiffOn.sub`](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/ContDiff/Operations.lean#L318-L320)
declarations determine those explicit arguments. No theorem statement,
hypothesis, rank-zero handling, matrix or heat-data value, ordinary derivative
meaning, literal C² regularity, or positivity bound changes.

Only this module's authored-source digest is updated. Inherited source,
workflows, probes, pins, contract and canonical-gate semantics are unchanged.
The later nested-operator scalar-norm instance concern is source-only; this
candidate adds no instance or assumption. It has not been compiled. Independent
review and a complete new exact-head Lean 4.33 run remain required, including
the remaining metric module and all type, axiom and canonical-audit gates.
Point 4 remains **OPEN**.

## Development-only positive-frozen norm repair candidate

Source-reviewed `ff9d985eb81e8209df4e9c5838eeb24a3c98eed1` retains the three
preceding exact-error repairs. Two serial, separately admitted Lean 4.35.0-rc2
isolated diagnostics then terminated with exit code 1. The default generic
nested-operator `NormSMulClass` search failed; explicit standard proof-local
inner and outer `ContinuousLinearMap.toNormedSpace` instances and
`NormedSpace.toNormSMulClass` cleared that scalar-norm failure. Both diagnostics
still failed the untyped `add_sub_cancel_left` rewrite under the operator norm.
Those cached-development results do not establish the corresponding pinned
Lean 4.33 behavior, and all earlier source and terminal evidence is retained.

This additional source-only candidate supplies exactly those standard instances
inside the supported-point norm estimate. It first proves the fully typed
bilinear-map cancellation equality by evaluation on two vectors, definitional
pointwise operations and real polynomial arithmetic, then rewrites with that
local equality before applying `norm_smul`. No global instance or declaration,
new hypothesis, smoothness order, positive-rank premise, norm definition,
coercivity bound, F/V/P/D value definition or theorem signature is changed.
The rank-zero branch and the nonsupported-point proof are unchanged.

Only the PositiveFrozen authored-source digest is updated. Inherited sources,
workflows, existing probes, pins, contract and canonical-gate semantics remain
unchanged. The new patch and prepared isolated baseline/repair probes have not
been compiled. Independent source review, separate admission for any new
cached-development execution, and a complete new exact-head Lean 4.33 run
remain required. Merge only after every required verification and review gate
passes. Point 4 remains **OPEN**.

## Development-only operator-norm nonnegativity repair candidate

The source-reviewed candidate `d40aee088c67db3fada92ff36db079cddc96f9f8`
retains all prior source repairs. Its separately admitted corrected serial
Lean 4.35.0-rc2 diagnostic pair completed on 2026-10-05 at 07:43:49 UTC,
with both probes exiting 1 and both process groups absent after cleanup.
The repair probe cleared typed bilinear cancellation, the explicit standard
scalar-norm proof, operation coherence and rank-zero specialization. Its
single remaining error was the generic `norm_nonneg _` argument in the
coefficient bound: that argument selected `SeminormedAddGroup.toNorm`, while
the target used the actual `ContinuousLinearMap.hasOpNorm`. These are isolated
cached-development observations, not pinned Lean 4.33 qualification. Both
failed pairs, their owners, exact sources and terminal logs remain historical.

This source-only candidate changes exactly that argument to the pinned
`ContinuousLinearMap.opNorm_nonneg (F x - F x₀)`. The existing lemma proves
nonnegativity directly for the actual operator norm, without synthesizing
another norm on the map space. Every theorem signature, hypothesis, rank-zero
branch, local instance, bilinear cancellation, F/V/P/D value definition,
literal C² order and coercivity bound is unchanged. Only the authored
PositiveFrozen module digest is updated; inherited sources, existing probes,
workflows, pins, contract and canonical-gate semantics are unchanged.

The additional patch and one corrected control probe are source-only and
unexecuted. Fresh independent review and separate execution admission remain
required, followed by complete exact-head Lean 4.33 source, type, axiom, full
library and canonical-audit verification before merge. Point 4 remains **OPEN**.

## Historical b18 exact-toolchain failure and literal proof repair

The exact reviewed `b18aff42cc373124912a39cc32887f2545ef439b` candidate
failed the literal-metric job
[`111672366729`](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37282119161/job/111672366729)
of Lean 4.33 run `37282119161` on 2026-10-05. The job actually started at
09:54:35 UTC and ended with failure at 10:20:01 UTC. Both generic modules and
`EuclideanC2Localization` compiled. `PositiveFrozenC2Localization` had four
remaining elaboration failures at lines 88, 92, 98 and 115: the near-point
bilinear equality, frozen-exterior equality, preimage-to-ball norm estimate,
and exterior perturbation norm bound. Later metric, full-signature, axiom,
full-library and canonical-audit gates were not reached. The immutable b18
source and exact failure log remain historical.

Its previously admitted Lean 4.35.0-rc2 isolated operator-norm control had
exited 0 at 08:09:09 UTC, with the process group confirmed absent after cleanup.
That earlier fragment established only its cached-development cancellation,
scalar-norm, coefficient, coherence and rank-zero examples. It did not check
the four literal proof blocks now reported by the actual pinned compiler.

This source-only repair evaluates the two bilinear equalities on two vectors
and closes the resulting real polynomial identities. It explicitly types
`F x` as a member of the same existing operator-norm ball before rewriting
ball membership and distance. In the exterior estimate it proves that the
actual bilinear perturbation is the zero map by the same pointwise method,
then uses the pinned `ContinuousLinearMap.opNorm_zero` and the unchanged
positive half-radius. The supported-point scalar-norm, typed cancellation,
explicit nonnegativity and coefficient bound are preserved unchanged.

All four public theorem signatures and hypotheses, rank-zero branch,
F/V/P/D value definitions, derivative meaning, literal C² order, actual
operator norm and positivity bound are unchanged. Only the PositiveFrozen
module's authored digest changes in the source guard. Inherited source,
workflows, existing probes, pins, contract, metadata and canonical-gate
semantics remain unchanged. This new proof repair has not been compiled.
Fresh independent exact-byte review and complete exact-head Lean 4.33
verification are still required before merge. Point 4 remains **OPEN**.

## Historical 5cf distance rewrite failure and explicit-instance repair

The exact source-reviewed `5cf1da2517f3a907f506d31667559c9c7b56b606`
candidate failed the literal-metric job of Lean 4.33 run
[`37304828956`](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37304828956)
on 2026-10-05 at 12:24 UTC. Both generic modules and
`EuclideanC2Localization` compiled against the unchanged pins. The earlier
near-point, frozen-exterior and exterior-norm repairs passed their previous
error sites. `PositiveFrozenC2Localization` still failed at line 105: the
generic `dist_eq_norm` rewrite did not match the actual distance expression
after ball membership was exposed. The full module and every later metric,
signature, axiom, library and canonical-audit gate remain unverified. The
immutable 5cf source, source-only review and exact failed log remain historical;
the preceding review's predicted distance-rewrite elaboration did not hold.

This source-only repair replaces only that strict-radius proof. It explicitly
instantiates the pinned `dist_eq_norm` theorem with the actual bilinear-map
type and `ContinuousLinearMap.toSeminormedAddCommGroup`, using the standard
inner-dual `ContinuousLinearMap.toNormedSpace` instance within the proof.
A fully typed equality connects the same operator metric to the same genuine
operator norm; transporting `mem_ball.mp hball` across that equality avoids
the generic rewrite search. The pinned operator construction defines its norm
as the infimum of genuine operator bounds and preserves its existing topology
when constructing the pseudometric. No coordinate norm is substituted.

All public signatures and hypotheses, literal C² regularity, rank-zero branch,
F/V/P/D definitions, strict half-radius, positivity and coercivity constants,
and every other proof block remain byte-identical to 5cf. Only the module's
derived digest changes in the existing source guard. Inherited sources,
workflows, probes, toolchain and Mathlib pins, metadata, contract, fixtures and
canonical-gate semantics are unchanged. This candidate has not been compiled.
Fresh independent exact-source review and complete hosted exact-head Lean 4.33
verification remain required before qualification or merge. Point 4 remains
**OPEN**.

## Historical 880a tangent-bundle and atlas elaboration failure

The exact source-reviewed `880a8b7cd31c64d2076847cef7d61684959e3e27`
candidate failed the literal-metric job
[`111816126934`](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37325807619/job/111816126934)
of Lean 4.33 run `37325807619` on 2026-10-05 at 14:54 UTC.
Both generic modules, `EuclideanC2Localization`, and the complete
`PositiveFrozenC2Localization` module compiled against the unchanged pins.
`BoundarylessInitialMetricLocalization` then failed at the actual Gram
positivity call: the compiler could not synthesize its tangent `FiberBundle`
instance and left preferred-trivialization atlas goals. The coefficient
identity also retained the `frame` abbreviation, so `ring` did not recognize
the two Gram coefficients as the same atom. Every later full-signature,
axiom, full-library and canonical-audit gate remains unverified. The exact
880a source, review, distance repair and failed CI log remain historical.

This source-only candidate replaces only that existing positivity proof
block. It explicitly supplies Mathlib's canonical `TangentSpace.fiberBundle`
and `TangentSpace.vectorBundle` inside the proof. Those instances derive
from the existing smooth manifold assumption; they do not introduce a
new geometric premise. It installs canonical `MemTrivializationAtlas`
for the same `trivializationAt E TM p`, using the existing preferred
trivialization abbreviation. Finally it unfolds only the existing `frame`
abbreviation before the unchanged real coefficient identity is proved
by `ring`. The actual metric, chart, frame and finite contraction are
unchanged.

All public declaration headers and all bytes outside that one proof block
remain identical to 880a. Literal C² metric regularity, arbitrary models
under `BoundarylessManifold I M`, the rank-zero case, every definition and
data value, positivity and coercivity bounds remain unchanged. Only the
Boundaryless module's derived digest changes in the existing source guard.
All inherited proofs, fixtures, probes, workflows, pins, metadata, contract
and full canonical-gate semantics remain unchanged.

This new candidate is **SOURCE_ONLY_COMPILER_UNVERIFIED**. Independent
exact-source review and complete hosted exact-head Lean 4.33 verification
are required before qualification or merge. The separately reviewed
obstruction to the universal C² existence campaign remains in effect;
this localization is independently useful supporting work and does not
restart that stopped closure. Point 4 remains **OPEN**.

## Remaining mathematical gaps

This local constructor does not discharge anisotropic inverse-Gram heat
transport, quantitative non-isometric model/basis norm factors for that
transport, compatible atlas overlap and assembly, weighted nonlinear PDE
closure from literal C² data, manifold realization, recovery-gauge regularity,
ordinary endpoint time derivatives, or uniqueness against the original weak
competitors on common closed intervals. No canonical Point-4 declaration is
added and no completion-auditor semantics are changed.
