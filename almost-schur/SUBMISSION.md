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

Exact source commit: `8c8c0194519cb189931ae29147d1927e351b32ce`. Do not submit
a moving branch or a working tree.

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

- Local source and package preparation: complete; the local checks listed in
  `VERIFICATION.md` passed at the exact commit above.
- Pushed commit: `8c8c0194519cb189931ae29147d1927e351b32ce` on
  `arthur742ramos-almost-schur-analysis`.
- Pull request: [#8](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/pull/8).
- Hosted verification: complete for this commit; see the two hosted workflow
  records in `VERIFICATION.md`.
- Palomar intake: none for this package; artifact-specific authorization is
  still required before `/api/submit`.
- Editorial review: none.
- Registration: none.

The older `schur-rigidity/` intake and its private status are historical and
must not be substituted for this artifact.
