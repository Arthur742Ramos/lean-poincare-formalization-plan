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

These identify the exact intake surface. The first hosted attempt at commit
`22c21dd473fc77a5d93745df976fd27ec1e9ab4a` failed mechanical verification
because the repository license text did not have one unambiguous standard SPDX
match. The corrected attempt at commit
`7bf6cc5a17356c3cea71cc4c273434801b8ccd04` then failed because its Mathlib
revision was not an ancestor of canonical `master`. The current correction
pins Mathlib to canonical ancestor
`8a178386ffc0f5fef0b77738bb5449d50efeea95`, aligns the Lean/Comparator stack
to Lean 4.29.0, and adds local license and dependency-ancestry gates. A retry
must use the new immutable commit.

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
Lean4Export v4.29.0, Landrun, and NanoDa by full commit.

## External status

The first candidate was submitted to Palomar at the commit recorded above but
failed hosted mechanical verification on the license fingerprint alone. The
current correction is locally prepared; after the new commit is public, an
external retry still requires a fresh check of the current Palomar contract,
the exact immutable commit, the Comparator configuration, and the authorized
maintainer relationship.
