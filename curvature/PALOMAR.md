# Palomar Submission 01

## Static connection and curvature core

This candidate packages the first proof-bearing static layer of the
`PoincareCurvature` development. The selected surface exposes two results:

- `PoincareCurvature.Palomar.curvature_commutator_skew`, the alternating law
  for the raw curvature commutator;
- `PoincareCurvature.Palomar.levi_civita_uniqueness`, the uniqueness of a
  torsion-free, metric-compatible affine connection at the current manifold
  API boundary.

The proved side imports `PoincareCurvature.Basic`, which contains the static
connection, curvature, contraction, metric, and Levi-Civita layers. The
statement side imports only Mathlib's manifold and covariant-derivative APIs;
it deliberately does not import project-specific implementation modules.

This is a static geometry contribution. It does not claim a formalized
Poincare Conjecture, Ricci-flow local existence, surgery, or any result from
the internal point-4 scaffold.

## Nested-project intake paths

The package intentionally lives at `curvature/` inside the roadmap repository.
The current Palomar form supports this layout. For a future intake, the
repository-relative fields are:

- repository: `Arthur742Ramos/lean-poincare-formalization-plan`;
- project directory: `curvature`;
- Comparator configuration: `curvature/comparator.json`;
- formalization metadata: `curvature/formalization.yaml`;
- license: the repository-root `LICENSE` file.

These are recorded for reproducibility only. They are not an intake receipt,
submission identifier, or review result.

## Local checks

Run from this directory:

```sh
bash scripts/verify-palomar.sh
```

The check builds the complete pinned package and the two explicit Lake targets,
compiles both statement and solution files, checks the Challenge and Solution
import boundaries and size limits, validates the Comparator and metadata
shapes, and prints the kernel axiom declarations for the two selected
theorems. The public definitions are intentionally not listed as Comparator
definition holes: the stricter replay compares their bodies as well.

For the independent Comparator plus NanoDa replay, use:

```sh
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh
```

The environment flag is required only for this macOS development fallback;
Linux runs use the pinned Landrun sandbox. The script pins Comparator,
Lean4Export v4.29.1, Landrun, and NanoDa by full commit.

## External status

This candidate is locally prepared only. It has not been submitted to
Palomar. An external intake will require a fresh check of the current
Palomar contract, the exact public repository and immutable commit, the
Comparator configuration, and the authorized maintainer relationship.
