# Palomar Submission 02

## Tensoriality and metric skew-adjointness of raw curvature

This candidate packages the next proof-bearing static curvature layer of the
`PoincareCurvature` development. The selected surface exposes the following
coherent theorem family:

- `PoincareCurvature.Palomar.raw_curvature_left_tensoriality`, pointwise
  scalar linearity in the left tangent-field slot;
- `PoincareCurvature.Palomar.raw_curvature_middle_tensoriality`, pointwise
  scalar linearity in the middle tangent-field slot;
- `PoincareCurvature.Palomar.raw_curvature_right_tensoriality`, pointwise
  scalar linearity in the bundle-section slot; and
- `PoincareCurvature.Palomar.raw_curvature_metric_skew_adjointness`, the
  metric-compatibility curvature commutator identity.

Together these results establish the core locality/tensoriality behavior of
the raw curvature commutator and its compatibility with a Riemannian inner
product. The selected statements retain the explicit regularity hypotheses
needed by the manifold proofs. The proved side imports the checked tensorial
curvature implementation; the statement side imports only Mathlib's
covariant-derivative, Lie-bracket, and Riemannian APIs and reconstructs the
small public vocabulary needed for Comparator replay.

These are standard differential-geometric identities, not claims of new
mathematics or priority. The contribution is the kernel-checked formalization
and its integration with the current Mathlib manifold/vector-bundle boundary.
The later bundled curvature and Ricci/scalar contraction definitions remain in
the implementation package but are not silently counted as selected results.

The complete automation and human-oversight record is in
`AGENT-CONTRIBUTION-02.md`.

## Nested-project intake paths

The package lives at `curvature/` inside the roadmap repository. The intended
repository-relative intake fields are:

- repository: `Arthur742Ramos/lean-poincare-formalization-plan`;
- branch: `dev/point4-campaign`;
- project directory: `curvature`;
- Comparator configuration: `curvature/comparator.json`;
- formalization metadata: `curvature/formalization.yaml`;
- license: the repository-root `LICENSE` file.

The accepted Submission 01 artifact remains reproducible at its own immutable
commit. This candidate uses a later immutable commit and a distinct
Comparator theorem surface.

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
