# Palomar Submission 04

## Time-dependent Levi–Civita families and curvature invariants

This candidate isolates the explicit-time geometric interface already proved
in `PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TimeDependent.lean`.
The time variable is represented by an `ℝ`-indexed family, and all geometric
claims are made slice by slice. The selected surface is:

- `PoincareCurvature.Palomar.exists_contMDiffLeviCivitaConnection`, existence
  of a slicewise Levi–Civita family with C^1 slices;
- `PoincareCurvature.Palomar.leviCivitaConnection_isLeviCivita`, correctness of
  the canonical slicewise correction;
- `PoincareCurvature.Palomar.contMDiffCovariantDerivative_leviCivitaConnection`,
  preservation of slice regularity;
- `PoincareCurvature.Palomar.leviCivitaConnection_eq_leviCivitaConnection`,
  independence of the correction from the background family;
- `PoincareCurvature.Palomar.contMDiffCovariantDerivative_of_isLeviCivita`,
  regularity of every slicewise Levi–Civita family;
- `PoincareCurvature.Palomar.ricciCurvature_symm_of_isLeviCivita`, time-slice
  symmetry of Ricci curvature; and
- `PoincareCurvature.Palomar.ricciCurvature_eq_of_isLeviCivita` and
  `PoincareCurvature.Palomar.scalarCurvature_eq_of_isLeviCivita`, invariance
  of the two contractions under the choice of Levi–Civita family.

This is a standard formalization/adaptation of the classical slicewise
Levi–Civita and curvature theory, not a new theorem or priority claim. The
source module implements the time-dependent results by applying the static
constructions at each time; it does not assert time differentiability, a
Ricci-flow solution, or a parabolic existence theorem.

The Challenge imports only Mathlib and contains eight deliberate theorem holes
plus three deliberate definition holes for the time-dependent Levi–Civita
correction, Ricci curvature, and scalar curvature. The exact source types of
those definitions are exposed so the Comparator can check the public
interface, while `Solution.lean` imports the actual source module and proves
all eight selected statements. This mechanism is documented in
`formalization.yaml` and `AGENT-CONTRIBUTION-04.md`.

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
artifacts remain reproducible at their own immutable commits. This candidate
uses a distinct time-dependent Comparator theorem/definition surface.

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
