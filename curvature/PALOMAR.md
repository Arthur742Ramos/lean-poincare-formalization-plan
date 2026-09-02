# Palomar Submission 03

## Levi–Civita connections and metric-determined curvature invariants

This candidate packages the next proof-bearing static Riemannian layer of the
`PoincareCurvature` development. The selected surface exposes the following
coherent theorem family:

- `PoincareCurvature.Palomar.exists_contMDiffLeviCivitaConnection`, existence
  of a global C^1 Levi–Civita covariant derivative;
- `PoincareCurvature.Palomar.curvatureTensor_eq_of_isLeviCivita`, independence
  of the bundled curvature tensor from the chosen Levi–Civita realization;
- `PoincareCurvature.Palomar.ricciCurvature_symm_of_isLeviCivita`, symmetry of
  the Ricci contraction; and
- `PoincareCurvature.Palomar.ricciCurvature_eq_of_isLeviCivita` and
  `PoincareCurvature.Palomar.scalarCurvature_eq_of_isLeviCivita`, independence
  of the Ricci and scalar-curvature contractions from that realization.

Together these results connect the existence of the canonical connection to
the metric-determined curvature tensor and its two principal contractions.
They are standard consequences of the classical fundamental theorem of
Riemannian geometry and the usual curvature identities. The submission makes
no claim of a new theorem or priority; its contribution is the kernel-checked
formalization and integration of this theorem family at the current Mathlib
manifold/vector-bundle API boundary.

The Challenge imports only Mathlib and contains five deliberate theorem holes
plus three deliberate definition holes for the canonical bundled curvature
tensor, Ricci curvature, and scalar curvature. The exact source types of those
three definitions are exposed so that the Comparator can check the public
interface, while `Solution.lean` imports the actual package constructions and
proves all five selected statements. This definition-hole mechanism is
documented in `formalization.yaml` and `AGENT-CONTRIBUTION-03.md`.

The complete automation and human-oversight record is in
`AGENT-CONTRIBUTION-03.md`.

## Nested-project intake paths

The package lives at `curvature/` inside the roadmap repository. The intended
repository-relative intake fields are:

- repository: `Arthur742Ramos/lean-poincare-formalization-plan`;
- branch: `dev/point4-campaign`;
- project directory: `curvature`;
- Comparator configuration: `curvature/comparator.json`;
- formalization metadata: `curvature/formalization.yaml`;
- license: the repository-root `LICENSE` file.

The accepted Submission 01 and passed Submission 02 artifacts remain
reproducible at their own immutable commits. This candidate uses a later
immutable commit and a distinct Comparator theorem/definition surface.

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
