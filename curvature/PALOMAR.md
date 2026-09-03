# Palomar Submission 04

## Ricci–DeTurck pullback transport and metric-cone evolution

This revision replaces the previous assumption-assembly surface with a typed
coordinate theorem package that exposes the geometric objects it uses:

1. metrics are continuous bilinear forms;
2. the Ricci tensor is defined as the metric composed with a specified Ricci
   endomorphism;
3. the derivative of a gauge pullback is derived from independent Fréchet,
   gauge, and tangent-transport derivative data; and
4. a Ricci vector field on the space of bilinear forms has a
   Picard–Lindelöf evolution that remains in the cone of symmetric
   positive-definite metric forms, with uniqueness of Ricci-flow solutions.

The capstone combines the independently derived pullback derivative with the
Ricci–DeTurck source equation and the explicit Ricci-tensor transport identity.
It proves an intrinsic `-2 Ric` evolution law. The finite-dimensional scalar
trace transport lemma remains in the files as a proved supporting corollary,
but is not a standalone selected result.
The model is a finite-dimensional tangent-coordinate reduction of the
manifold-level gauge mechanism in the project source; it does not claim the
full nonlinear compact-manifold Ricci-flow existence theorem or a new
mathematical discovery.

The exact selected declarations are:

- `PoincareCurvature.Palomar.gauge_pullback_has_derivAt_of_C1_data`;
- `PoincareCurvature.Palomar.ricciTensor_pullback_transport`;
- `PoincareCurvature.Palomar.pullbackMetric_preserves_symmetricPositiveDefinite`;
- `PoincareCurvature.Palomar.ricciDeTurckGaugeReduction`;
- `PoincareCurvature.Palomar.metricCone_local_flow_exists`; and
- `PoincareCurvature.Palomar.metricCone_local_flow_unique`.

The Comparator definitions are `pullbackMetric`, `ricciTensorFamily`,
`RicciMetricCone`, `ricciFlowVectorField`, and `IsIntrinsicRicciFlow`. Their
formulas are visible in both `Challenge.lean` and `Solution.lean`; no
unconstrained scalar `ricci` family or arbitrary ODE field is hidden behind the
surface. `Challenge.lean` imports only Mathlib so the declarations are
independently auditable, while `Solution.lean` proves the same declarations
directly from the pinned Mathlib calculus and ODE results.

## Nested-project intake paths

The package lives at `curvature/` inside the roadmap repository. The intended
repository-relative intake fields are:

- repository: `Arthur742Ramos/lean-poincare-formalization-plan`;
- project directory: `curvature`;
- Comparator configuration: `curvature/comparator.json`;
- formalization metadata: `curvature/formalization.yaml`;
- license: the repository-root `LICENSE` file.

This is a corrected new submission following the review of
`PALOMAR-2026-09-02-000007`; the previous Palomar ID is not reused as the
registration field for this new submission.

## Local checks

Run from this directory:

```sh
bash scripts/verify-palomar.sh
```

For the independent Comparator plus NanoDa replay on the macOS development
machine, use:

```sh
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh
```

## External status

This document records local preparation only. A Palomar submission requires a
fresh action for the final public commit, with the exact public repository,
full SHA, project directory, Comparator path, metadata path, and authorization
relationship verified at submission time. Local checks do not imply hosted
mechanical verification, renderability, editorial review, registration, or
public indexing.
