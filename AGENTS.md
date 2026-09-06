# Project instructions

## Palomar submissions

- Every submission from this project is a **new entry**, never a v2 or later
  version of an existing entry. This is an explicit maintainer requirement.
- Give each result its own focused subproject, Comparator configuration,
  Challenge/Solution pair, and formalization metadata. Do not reuse another
  result's submission identity or supply its existing Palomar ID.
- A new entry must prove a genuinely distinct result; do not repackage an
  already submitted theorem merely to obtain another entry. If registry rules
  prevent a new entry, stop and report the conflict instead of silently making
  a version update.
- Preparing a submission does not authorize submitting or registering it.
  Keep mechanical verification, review approval, and public registration
  separate in status reports.

## Structured provenance preflight

- Before every intake, reconcile README/PROVENANCE attribution with
  `formalization.yaml`. Prose disclosure is not a substitute for structured
  `related_formalizations` entries.
- Record every reused earlier formalization there, including same-repository
  subprojects: immutable repository URL, full commit SHA, source project/path,
  an accurate schema-supported relationship (for example `builds-on`), and a
  note distinguishing inherited code/results from newly selected results.
- Compare vendored files with their stated source and preserve contributor
  notices. Do not leave `related_formalizations: []` when earlier formalized
  code is reused. Check both schema validity and factual completeness.
- Run the subproject's provenance regression check when provided; verify the
  metadata at the exact submitted SHA, not merely the working tree.

## Submission-link handoff

- Keep one explicit current artifact/intake pair. Label every older receipt
  historical, including its verification logs and old authorization. A
  documentation commit cannot change the checkout of an existing intake.
- Never carry an old "do not substitute" instruction into a new artifact's
  handoff without saying which historical artifact it protects. Mark
  maintainer-reported intake identities as such until independently checked.

- Treat the returned private status URL as a bearer credential. Keep it
  retrievable for the active session and give it directly to the requesting
  user with a warning that it can read the review and control registration.
- Do not commit it, put it in public logs, or retain only a redacted copy
  before handing it to the user. Submission IDs and public workflow URLs do
  not replace the private control link. Never create a duplicate intake to
  recover a link; use the current protocol's user-operated recovery flow.

## Proof and workspace discipline

- Do not call a candidate submission-ready on mechanical checks alone.
  Establish a substantive mathematical research-interest case from primary
  literature and the exact selected theorem, not code volume or proof effort.
- Do not repair a selection-level deficiency by promotional wording, routine
  corollaries, or assumed analytic bridges. A replacement research theorem
  requires an explicit scope decision, a proof, and renewed verification.

- Prove the advertised geometric statements using actual manifold curvature,
  Ricci, scalar curvature, and covariant derivatives. Do not assume the target
  differential identities or hide missing bridges inside hypotheses.
- Keep the Challenge independently auditable with Mathlib-only imports.
- Preserve unrelated edits and stage only explicit task paths.
