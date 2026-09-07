# Submission handoff

## Artifact identity

Title: **De Lellis--Topping almost-Schur inequality**

- Repository: `https://github.com/Arthur742Ramos/lean-poincare-formalization-plan`
- Project directory: `almost-schur`
- Comparator: `almost-schur/comparator.json`
- Metadata: `almost-schur/formalization.yaml`
- Existing Palomar ID: **blank**; this is a new result entry, not a version
  of `contracted-bianchi` or `schur-rigidity`.
- Relationship: maintainer of the substantive formalization.

The earlier artifact `8c8c0194519cb189931ae29147d1927e351b32ce` and its
documentation follow-up `539089aab6a9444ab401ef6136acd292f6490745` are
**superseded**: they selected only algebraic reductions for Comparator and
contained incorrect bibliographic metadata. Their successful builds do not
establish readiness of this repaired geometric entry.

The current revision selects `AlmostSchurEntry.Geometry.almostSchur` and all
nine geometric definitions. After committing and pushing this revision,
resolve `git rev-parse HEAD` and use that full 40-character SHA for intake.
The final handoff must name it explicitly; never submit a moving branch or
an uncommitted working tree. See [SEMANTIC-AUDIT.md](SEMANTIC-AUDIT.md).

## Delivery gates

The following states are intentionally separate:

1. local Lean/build, provenance, axiom, Challenge-closure and Comparator checks;
2. a pushed immutable GitHub commit;
3. hosted Linux mechanical verification at that exact commit;
4. Palomar editorial review;
5. explicit registration consent and public registry publication.

No gate is inferred from another. The private Palomar status URL, if an intake
is created, is a bearer credential and must not be committed or exposed in
public logs. The review remains private until an explicit registration action.

## Current record

- Source: the repaired geometric statement and proof in this revision.
- Verification evidence and exact scope: `VERIFICATION.md`.
- Delivery branch: `arthur742ramos-almost-schur-analysis`.
- Pull request: [#8](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/pull/8).
- Hosted verification: use the checks attached to the final pushed SHA;
  earlier runs at the superseded artifacts do not verify this revision.
- Palomar intake: none for this package; artifact-specific authorization is
  still required before `/api/submit` under the repository's submission instructions.
- Editorial review: none.
- Registration: none.

The older `schur-rigidity/` intake and its private status are historical and
must not be substituted for this artifact.
