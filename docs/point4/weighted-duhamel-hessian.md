# Weighted actual Gaussian Duhamel Hessian: reviewed source-only preparation

Status: independently source-reviewed mathematical candidates; UNCOMPILED.
Point 4 remains OPEN. Publication and CI execution have not been performed.

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

All new definitions, hypotheses and proof bodies are byte-identical to their
independently reviewed frozen sources. `source-transformations.json` records
only eight count-one repository import qualifications. `WeightedTimeKernel` is
entirely identical, as is the ninth regularizer module. The legacy non-module Gaussian helper retains its original
visibility and `noncomputable section`; no exposure normalization was made.

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
inventory are required. Synthetic fixture logs test rejection logic only and
are never compiler or theorem-verification evidence.

## Honest remaining boundary

No Lean compiler, proof runtime, dependency installation, cache write, new
source download, publication or CI execution was performed here. Exact-toolchain
elaboration and final independent integrated release review remain pending.
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
