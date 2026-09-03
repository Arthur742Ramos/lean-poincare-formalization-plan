# Palomar Submission 04

## Frozen Ricci–DeTurck affine chart evolution

This corrected candidate replaces the rejected parabolic-infrastructure-only
surface with a connected frozen affine evolution result. The selected
definitions are the explicit block operator
`(v, s) ↦ (L v + s • b, 0)` and the first coordinate of its operator
exponential at `(y₀, 1)`. The selected theorem family proves scalar-coordinate
conservation, the initial value, the affine ODE, global uniqueness and
representation, exponential growth, and Lipschitz dependence on initial data.

The model is intentionally stated over an arbitrary complete normed real vector
space with bounded linear data `L` and `b`. It is the frozen affine analytic
core motivated by the Ricci–DeTurck chart, not a claim of the full nonlinear
Ricci-flow PDE, Schauder estimates, or short-time existence theorem. The
mathematical relationships are recorded in `formalization.yaml`: DeTurck is
background for the geometric motivation, while Hille–Phillips is the source
formalized/adapted for the operator-exponential affine evolution. These are
standard results; no originality or priority claim is made.

The exact selected surface is:

- `PoincareCurvature.Palomar.affineAugment_snd_orbit_eq_one`;
- `PoincareCurvature.Palomar.affineFundamentalSolution_initial`;
- `PoincareCurvature.Palomar.hasDerivAt_affineFundamentalSolution`;
- `PoincareCurvature.Palomar.affineODE_unique`;
- `PoincareCurvature.Palomar.eq_affineFundamentalSolution_of_hasDerivAt`;
- `PoincareCurvature.Palomar.norm_affineFundamentalSolution_le`; and
- `PoincareCurvature.Palomar.norm_affineFundamentalSolution_sub_le`.

`Challenge.lean` imports only Mathlib and exposes the actual block-operator and
operator-exponential formulas. It has seven deliberate theorem holes and no
definition holes. `Solution.lean` imports the checked proof-bearing
autonomous operator-exponential development and supplies all seven wrappers.
The repository's broader parabolic and coordinate modules remain library
material outside this Comparator selection; they are not claimed by the four
Palomar surface files to be part of this result.

## Nested-project intake paths

The package lives at `curvature/` inside the roadmap repository. The intended
repository-relative intake fields are:

- repository: `Arthur742Ramos/lean-poincare-formalization-plan`;
- branch: `dev/point4-campaign`;
- project directory: `curvature`;
- Comparator configuration: `curvature/comparator.json`;
- formalization metadata: `curvature/formalization.yaml`;
- license: the repository-root `LICENSE` file.

The accepted Submission 01, passed Submission 02, and accepted Submission 03
artifacts remain reproducible at their own immutable commits. The failed
Submission 04 artifact is not reused as the Palomar ID for this corrected
surface; the new intake must use the fresh final commit with the Palomar ID
field left blank unless the registry auto-detects an already-public record.

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
