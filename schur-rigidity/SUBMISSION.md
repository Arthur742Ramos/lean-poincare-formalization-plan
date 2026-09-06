# Submission handoff and historical receipts

## Current reviewed artifact

- Source commit: `3955dd0b8d1eaeaa7d7dd7675864352dddcf0ffb`.
- Intake: `58oc259e0tln` (identity supplied by the maintainer; private service
  state has not been independently retrieved for this handoff).
- This handoff supersedes the original preparation instructions below.
  The old commit and intake identify historical evidence only.
- Later documentation commits do not alter the source of this intake. They
  are not automatically submitted artifacts and cannot repair its immutable
  checkout in place.
- Readiness: **not cleared for another intake**. The selected mathematical
  package is classical; a distinct research-level mathematical contribution
  has not been established. See `RESEARCH-GATE.md`.

## Artifact fields

Title: **Schur rigidity and geometric contracted Bianchi**

- Repository: `https://github.com/Arthur742Ramos/lean-poincare-formalization-plan`
- Project directory: `schur-rigidity`
- Comparator: `schur-rigidity/comparator.json`
- Metadata: `schur-rigidity/formalization.yaml`
- Corrected artifact commit: `3955dd0b8d1eaeaa7d7dd7675864352dddcf0ffb`.
  Do not use a moving branch name or silently substitute a later commit.
- Existing entry ID: **leave blank**. This is never a v2 of another entry.
- Relationship: maintainer. The earlier "Let's submit it" authorization
  applied to the original artifact recorded below, not automatically to every
  later commit. Public registration remains a separate decision after review.

## Intake receipt

### Historical agent attempt for the corrected artifact: cooldown

On 2026-09-06 the corrected artifact above added the immutable inherited
`contracted-bianchi` formalization to structured provenance. All Lean sources,
Comparator configuration and Lean dependency pins are unchanged from the
original artifact. Metadata schema validation, the provenance regression check
(including three negative controls), comparison of all twelve inherited files
against their source commit, and the Mathlib-only Challenge dependency check
passed locally. CI for the corrected artifact was started separately.

The authorized new intake omitted `existing_id`. After consuming the access
proof, Palomar returned HTTP 429: "Please try again in 6 days."
No corrected submission was admitted by that attempt. This is not a statement
about the separate maintainer-reported intake `58oc259e0tln` above.
The temporary verification tag and
secret gist were deleted. Do not retry during that cooldown; a later authorized
attempt must start a fresh intake and use a fresh proof. No registration was
requested or performed.

### Original artifact receipt (historical)

- Submission ID: `l20vtgq7gct2`
- Created: 2026-09-06 at 16:21:03 UTC
- Exact source: `4317d35a3cf3bbf02859fcd811e8dacc83f51739`
- Existing ID omitted: new Schur entry, not a version update.
- Initial service status: `verifying` (preparation and mechanical verification
  queued). No editorial result or public registration is claimed.
- Used the documented GitHub CLI tag-and-secret-gist proof-of-access flow.
  Both temporary proof artifacts were deleted after verification of access.
- Registration consent: false.

The credential-bearing status link is deliberately not recorded in the
repository. Do not create another intake merely because the review is pending.

## Mathematical scope (not a submission-readiness claim)

Formalizes geometric contracted Bianchi for actual Ricci/scalar fields, the
divergence-free Einstein tensor, Schur constancy of a differentiable Einstein
factor on connected manifolds of dimension at least three, and the full
constant-curvature tensor formula for three-dimensional Einstein manifolds.
The Mathlib-only statement surface exposes the connection commutator,
orthonormal contractions and actual covariant divergence. Ricci/scalar
differentiation and extension independence are proved, not assumed.

The mathematics is classical. The contribution is a connected formalized
argument from connection calculus through trace differentiation to global
rigidity, for an audience in formalized Riemannian geometry and geometric
analysis. It extends the earlier double-contracted curvature-derivative result
by proving the missing geometric identifications and global consequences.
It does not claim space-form classification, Lorentzian results, Ricci flow
or Poincare.

## Intake gate

The original [Comparator configuration](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/blob/4317d35a3cf3bbf02859fcd811e8dacc83f51739/schur-rigidity/comparator.json)
belongs to the original artifact. Its [Linux verification run](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/34043491915)
is bound to that original commit. This handoff document may be updated later to
record receipts without changing that immutable artifact identity.

Independent Linux Comparator/NanoDa and isolated Challenge verification passed;
the original receipt is recorded as historical in `VERIFICATION.md`. The
current reviewed identity is the pair at the top of this document. Neither
historical success nor a documentation correction clears the research gate.
Show the private review and obtain
explicit registration authorization before publishing it.
If registry rules prevent a new independent entry, report the conflict
instead of using an existing ID or submitting a version update.
