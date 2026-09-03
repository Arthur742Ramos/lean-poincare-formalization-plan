# Palomar Submission 04

## Ricci-DeTurck gauge reduction and curvature transport

This candidate replaces the earlier routine frozen affine ODE selection with
the geometric cancellation and transport identity that motivates the
Ricci-DeTurck method. The selected surface is an explicit fixed-tangent-model
version of the following argument:

1. pull a time-dependent metric and tangent data back along an anchored gauge;
2. evaluate the source Ricci-DeTurck equation at the gauge image;
3. subtract the Lie/gauge correction from the source velocity; and
4. obtain the intrinsic `-2 Ric` equation for the transformed metric.

The surface also proves preservation of the initial metric and invariance of
the finite-dimensional Ricci trace under tangent-map conjugation. It is a
geometric transport theorem, not a claim of the full nonlinear compact-
manifold local-existence theorem or of the Poincare Conjecture.

The exact selected declarations are:

- `PoincareCurvature.Palomar.pullbackBilinear_apply`;
- `PoincareCurvature.Palomar.gauge_corrected_velocity_eq_neg_two_pullbackRicci`;
- `PoincareCurvature.Palomar.gauge_reduction_has_derivAt`;
- `PoincareCurvature.Palomar.anchored_pullbackBilinear_eq_initial`;
- `PoincareCurvature.Palomar.ricciDeTurckGaugeReduction`;
- `PoincareCurvature.Palomar.trace_conjugation_invariant`; and
- `PoincareCurvature.Palomar.gauge_reduction_trace_readout`.

`Challenge.lean` imports only Mathlib and defines the ordinary pullback,
source-equation, and intrinsic-flow predicates needed to state the result in
a small auditable surface. `Solution.lean` proves the same declarations,
imports the checked Ricci-flow gauge-transport development, and records the
concrete implementation motivation in
`Geometry.Manifold.RicciFlow.ResearchTheorems`.

## Nested-project intake paths

The package lives at `curvature/` inside the roadmap repository. The intended
repository-relative intake fields are:

- repository: `Arthur742Ramos/lean-poincare-formalization-plan`;
- project directory: `curvature`;
- Comparator configuration: `curvature/comparator.json`;
- formalization metadata: `curvature/formalization.yaml`;
- license: the repository-root `LICENSE` file.

This is a new version of the existing Palomar result identity
`PALOMAR-2026-09-02-000007`, which already contains the earlier curvature
submissions. The submitted commit must be passed as `existing_id` for the
ordinary version intake.

## Local checks

Run from this directory:

```sh
bash scripts/verify-palomar.sh
```

For the independent Comparator plus NanoDa replay on this macOS development
machine, use:

```sh
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh
```

The replay pins Comparator, Lean4Export, Landrun, and NanoDa by full commit.
Linux runs use the pinned Landrun sandbox directly.

## External status

This document records local preparation only. A Palomar submission requires a
fresh action for the final public commit, with the exact repository, full SHA,
project directory, Comparator path, metadata path, and authorization
relationship verified at submission time. Local checks do not imply hosted
mechanical verification, renderability, editorial review, registration, or
public indexing.
