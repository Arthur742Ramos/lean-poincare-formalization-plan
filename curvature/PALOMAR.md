# Palomar Submission 01

## Raw Bianchi identities for torsion-free affine connections

This candidate packages the first proof-bearing static curvature-identity layer
of the `PoincareCurvature` development. The selected surface exposes the
following coherent theorem family:

- `PoincareCurvature.Palomar.first_bianchi_raw_of_torsion_free`, the pointwise
  cyclic first Bianchi identity for the raw curvature commutator;
- `PoincareCurvature.Palomar.second_bianchi_raw_of_torsion_free`, the pointwise
  cyclic raw differential second Bianchi identity.

The selected statements include the C^2/C^3 field regularity and manifold
smoothness assumptions used by the proofs. The proved side imports the checked
Bianchi implementation; the statement side imports only Mathlib's manifold,
covariant-derivative, torsion, and Lie-bracket APIs and reconstructs the small
public vocabulary needed for Comparator replay.

These are standard differential-geometric identities, not a claim of new
mathematics. The historical source relationship and the earlier Ricci/Padova
priority context are recorded in `formalization.yaml`. The former
`curvature_commutator_skew` and `levi_civita_uniqueness` wrappers remain
supporting library results and are deliberately not the research-interest
boundary of this candidate.

The automation role and human oversight record is pinned in
`AGENT-CONTRIBUTION.md`.

## Nested-project intake paths

The package intentionally lives at `curvature/` inside the roadmap repository.
The repository-relative intake fields are:

- repository: `Arthur742Ramos/lean-poincare-formalization-plan`;
- project directory: `curvature`;
- Comparator configuration: `curvature/comparator.json`;
- formalization metadata: `curvature/formalization.yaml`;
- license: the repository-root `LICENSE` file.

The earlier hosted artifact used the old two-theorem surface and was returned
for substantive research-interest and provenance clarification. This revision
uses Lean 4.33.0, Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d`, and matching Lean4Export revision
`15f6055e299ad5b89345e533cc2192f4cc00f659`.

## Local checks

Run from this directory:

```sh
bash scripts/verify-palomar.sh
```

The check builds the complete pinned package and the two explicit Lake targets,
compiles both statement and solution files, checks the Challenge and Solution
import boundaries and size limits, validates the Comparator and metadata shapes,
and prints the kernel axiom declarations for the two selected theorems. The
public `rawSecondBianchi` definition is intentionally not listed as a
Comparator definition hole: the stricter replay compares its body as well.

For the independent Comparator plus NanoDa replay, use:

```sh
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh
```

The environment flag is required only for this macOS development fallback;
Linux runs use the pinned Landrun sandbox. The script pins Comparator, Lean4Export
v4.33.0, Landrun, and NanoDa by full commit.

## External status

The previously submitted Lean 4.33.0 artifact is not this revised theorem
surface. After this revision is committed, pushed, and locally revalidated, a
new external Palomar action must be treated as a fresh artifact-specific
submission; local checks do not imply hosted verification, editorial review,
registration, or public indexing.
