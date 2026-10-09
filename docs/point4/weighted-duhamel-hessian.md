# Weighted actual Gaussian Duhamel Hessian: reviewed source-only preparation

Status: independently source-reviewed mathematical bodies; narrow regularizer proof
repair pending fresh independent review and exact-head compilation.
Point 4 remains OPEN. The published historical head has only partial CI evidence.

## Concrete supporting source

The exact base is `3a8ed697d1f0366f8370efb2fa9e524b68d27e97`, targeting Lean
`leanprover/lean4:v4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. The nine admitted source modules are:

- `WeightedTimeKernel`: actual interval integrability and the interval-length-independent
  integral bound `1/a + 1/(1-a)` for `(t-s)^(a-1) * (s-t0)^(-a)`, under `t0<t` and `0<a<1`
- `WeightedHessianTimeEnvelope`: exact exponent equality at `a=alpha/2`
- `WeightedDuhamelIntegrand`: concrete Gaussian cancellation domination, unchanged theorem and proof
- `WeightedDuhamelHessianIntegral`: actual time integrability, bound, spatial continuity and BCF packaging
- `WeightedDuhamelHessianDerivative`: actual coordinate second differentiation of the raw Duhamel potential
- `WeightedDuhamelFrechet`: actual first/second Frechet derivative compatibility, fixed-time spatial C2 and bilinear Hessian bounds
- `WeightedDuhamelHessianTrace`: genuine little weighted forcing, direct uniform raw-entry vanishing and strong finite-BCF-entry/sup-norm right trace
- `WeightedDuhamelHessianFrechetTrace`: uniform-in-space right vanishing of the actual iterated Frechet derivative in its ordinary operator norm
- `EuclideanHeatRegularizerC2Trace`: genuine uniform C0/value, C1/gradient, Hessian-entry and BCF trace of `h*heat(h)q` for actual bounded uniformly continuous C0 data, with actual coordinate derivative witnesses

All new definitions, declaration headers, hypotheses and bounds are byte-identical
to their independently reviewed frozen sources. Proof bodies are unchanged except
for three exact count-one elaboration repairs in the regularizer, described below. The original frozen snapshots and their
digests remain unchanged. `source-transformations.json` retains the eight original
count-one repository import qualifications and records three additional exact
compatibility edits: the new Gaussian helper's modern/public import preamble and
public exposed noncomputable section, and the regularizer's replacement import
block. `WeightedTimeKernel` is entirely identical. The regularizer now imports
modern `EuclideanHeatFrechet`, modern `FiniteMomentApproximation`, and Mathlib's
`UniformConvergence` directly. It never used a declaration from the legacy
`EuclideanHeatInitialTrace` itself. The finite-coordinate bound is the existing
`FiniteMomentApproximation.norm_le_sum_abs_coord`. `EuclideanHeatFrechet` supplies
the existing gradient definition and publicly imports the actual Hessian/BCF
continuity closure; no C2 datum constructor or initial trace is used. No new mathematical primitive,
shadow declaration, hypothesis or weakened bound is introduced.

The actual integral/derivative hypotheses are explicit: `t0<t`, `0<alpha<1`,
continuous BCF-valued forcing, an actual global value bound, nonnegative `L`,
and weighted coordinate Holder control on the open positive-time interval.
They assume no interval integrability, inverse/solver norm, derivative witness
or initial-positive-Holder certificate. Rank zero is admitted; entry indices
are then vacuous, and full Frechet assembly also specializes to rank zero.

## Exact source and evidence release discipline

The inherited root imports, mathematical source, workflow semantic bodies, contracts, pins,
metadata, probes and completion auditor stay unchanged. The new modules are
not imported by the root library: a successful root build alone cannot verify
them. The dedicated workflow explicitly compiles every new module before its
actual theorem/type/axiom/rank-zero probe. It also preserves the inherited
manifold producer compile/probe, full library build, all 150 inherited axiom
occurrences, seven older boundaryless types plus the eleven PR131 axiom surfaces and four
additional full manifold-only theorem types, current closed contract, twelve kernel
negative fixtures and the complete OPEN audit.

Three inherited workflows gain only a digest-pinned count-one interpreter-startup
job environment setting. Their complete original YAML/byte remainders are checked.
Seven inherited source/fixture scripts have exact digest-pinned count-one
entrypoint/dispatch adapters. Original function and fixture bodies are retained
byte-for-byte and actually executed in a detached, exact-base source worktree.
That worktree's complete files, modes, Git index and HEAD are checked before
and after execution. Supplied current evidence is forwarded unchanged, without
mocking any inherited evidence checker. The full current tracked/untracked/
ignored/physical union is independently checked before and after each replay.
No hidden source, Python cache, target, unexpected workflow, or broad cache path
is accepted. Dependency source must match pinned heads and every blob/mode.
The one ProofWidgets lockfile sidecar is permitted only with its verified pinned
source and exact 16 bytes `179e66574f04806e`; the reviewed read-only inventory
fragment and adversarial fingerprint tests are retained.

Strict duplicate-free YAML, complete schema identity, structured provenance,
original/transformed module/adaptor bindings, source closure and exact evidence
inventory are required. A source-only traversal checks every project import
reachable from all nine new modules for modern module status, public imports,
cycles and membership in the exact source union. External Mathlib/Lean import
closure and elaboration remain exact-toolchain obligations. Synthetic fixture logs test rejection logic only and
are never compiler or theorem-verification evidence.

## Historical compiler failure and narrow replacement

PR133 head `90cc7ebed996f28acb57ef9948d37f114088bd4d` was published and checked by
[official Lean 4.33 run 37298223369, job 111724469033](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37298223369/job/111724469033).
The job failed at 2026-10-05 11:10:55 UTC after compiling the scalar time kernel,
scalar envelope and old Gaussian helper. It reported exactly two modern/legacy
import errors: `WeightedDuhamelHessianIntegral` imported the non-module
`WeightedDuhamelIntegrand`, and `EuclideanHeatRegularizerC2Trace` imported the
non-module `EuclideanHeatInitialTrace`. The retained downloaded job log has
SHA256 `bed3479ee5ffe3456478915966f8fb4805b0ed78d9b8dfa38c091f93d7c00a9c`.
There is no complete nine-module compile receipt, new actual theorem/type/axiom
probe, or full release certificate for that head. Its source, normalized import
pairs and favorable earlier source review remain historical evidence only.

The first replacement changed only the two new source preambles plus exact
transformation guards, source digests, adversarial fixtures and truthful dossier
text. Inherited legacy modules, all 74 mathematical declaration surfaces and
proofs, all inherited 161/155/11 evidence surfaces, workflows and evidence gates,
runtime/source closure, pins and canonical contracts remain unchanged. Fresh
exact-byte delta/integration review is required before any draft push; exact
Lean compilation is still required afterward. PR131's separately stopped
ready/merge action and all PR bases are outside this repair.

## Actual 24a0 elaboration failure and three proof-only repairs

The next published PR133 head `24a0b6532304116ff25f1c793a4dbc6696251b9e` was checked by
[official Lean 4.33 run 37306626807](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/37306626807).
It genuinely compiled the other eight mandatory new modules, including
`WeightedDuhamelHessianFrechetTrace`, but failed the ninth regularizer at
2026-10-05 12:30:02 UTC. The retained complete failed job log has SHA256
`7f8088506e81958ac20fb13e1374f3662c2cef67c1df9eb220fa43c11a092417`.
The new actual theorem/type/axiom/rank-zero probe, inherited full build and
later final audit gates were skipped. Eight successful units do not qualify
this head or the replacement as a complete verified release.

This second repair changes exactly three regularizer proof blocks:

1. Reduce the reflexive diagonal conditional before the existing sound
   Gaussian first/third moment, square-root and nonzero-denominator arithmetic
2. Give the positive first-moment pair an explicitly typed pointwise sum and
   volume measure, use the pinned `Integrable.fun_add` API, and transport it by
   actual almost-everywhere distributivity using `Integrable.congr`
3. Remove the redundant `ring` after the summed-moment rewrite already closes
   its goal, as the actual compiler reported

The original reviewed regularizer snapshot and the failed 24a0 input retain
SHA256 `ca8598bd4eddf118a7bf2afa097e232cd872e8ffc7f3b2b9fe76bdf913531f44` and
`177fdfdf992c95c77f8211f331379f92b58163764d91a8bd48678640715870b5` respectively.
The source guard reconstructs the three exact ordered count-one edits, then
reverses them to every original 24a0 byte before comparing the original frozen
mathematical source. Missing, duplicated, reordered, changed or extra proof
transformations are rejected. The other eight new modules, all 23 regularizer
public declarations, every data definition and hypothesis, all norm constants,
genuine actual Gaussian derivatives, rank-zero scope, inherited sources, pins,
probes, workflows, contract and compiler/evidence gates remain unchanged.
Fresh exact-byte source review is required before any draft push, and actual
exact-head Lean qualification is still required afterward.

## Honest remaining boundary

No Lean compiler, proof runtime, dependency installation, cache expansion,
publication or CI execution was performed for this local repair. Small read-only
official pinned API excerpts and retained immutable source snapshots support
the source review; they are not compiler evidence.
The two historical CI failures above are disclosed separately. Exact-toolchain
elaboration of the repaired bytes and final independent integrated release review remain pending.
The approved replacement trace is SHA64f8f5bc; original SHA065d29c1 was rejected
for seven unresolved initial-time applications and remains historical. The
replacement adds only seven explicit initial-time arguments before independent
delta review; the optional Frechet trace remains unchanged. Integration uses
only the approved final bytes. No exact-toolchain verification is implied.

The ninth leaf uses only existing exact-base project imports and does not
import pending two-sided-heat branch source. Its epsilon/delta argument assumes
bounded uniform continuity of the actual C0 datum, not C2 or positive-Holder
regularity. The quantitative Gaussian cancellation estimate is genuine; it
does not impose a fixed positive time-power decay rate. The resulting
Euclidean regularizer trace is not yet identified with a constructed global
metric endpoint family or its ordinary endpoint component derivative.

Assembly of value, first-derivative and Hessian traces in the full intended C2
topology is still OPEN. Positive-time BCF Hessian continuity, parabolic time regularity,
weighted derivative-graph inversion, literal-C2 compact-atlas gluing, nonlinear
invariance/contraction, positivity, geometric gauge recovery, ordinary endpoint
derivatives and uniqueness of the existing weak competitors remain OPEN.

The unchanged canonical contract remains arbitrary literal C2 metric, arbitrary
model `I`, only `BoundarylessManifold I M`, rank-zero-inclusive, common closed
intervals and ordinary endpoint component derivatives. This supporting result
makes no nonlinear, gauge, weak-uniqueness or canonical Point-4 completion claim.
