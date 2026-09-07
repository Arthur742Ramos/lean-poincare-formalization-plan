# Verification record

## Local checks

The current geometric surface supersedes the algebra-only surface at
`8c8c0194519cb189931ae29147d1927e351b32ce`. The local package checks are:

- `lake build AlmostSchur Challenge Solution` for the complete development and
  both independent statement/proof modules;
- `lake env lean --src-deps Challenge.lean`, with the Challenge imported only
  from the pinned dependency closure;
- `python3 scripts/check-vendored.py`;
- `python3 scripts/check-curvature-provenance.py`;
- `python3 scripts/check-axioms.py`, which scans the public implementation
  declarations and rejects proof-hole tokens and unapproved axioms;
- `python3 scripts/validate-formalization.py`;
- `python3 scripts/check-entry-regressions.py`; and
- the pinned Linux Comparator/NanoDa replay, with the explicit unsandboxed
  fallback permitted only for local macOS development.

The revised development and Challenge/Solution modules build. The independent
Challenge compiles with the candidate library excluded from its import path.
The public implementation has 1,024 audited declarations; the axiom checker
also explicitly includes the selected Solution theorem and six vendored
endpoints. Provenance checks cover 36 Rellich--Kondrachov modules and eight
curvature modules. Structural metadata and four semantic-package negative
controls pass. Full validation against the official formalization.yaml JSON
schema was also run successfully during the audit.

The pinned Comparator replay passed on the repaired 137-line, 6,290-byte
Challenge. It compared the full geometric theorem and all nine definitions;
both NanoDa and Lean's default kernel accepted the selected Solution proof.
This local run used the explicit macOS fallback. Hosted Linux Landrun remains
the separate check of the sandboxed clean environment.

The Challenge intentionally contains one theorem `sorry` placeholder. It
is a statement-surface hole and is not included in the implementation axiom
audit. The Solution and all implementation modules must contain no `sorry`,
`admit`, custom `axiom`, `Lean.ofReduceBool` or `sorryAx` dependency.

## Historical hosted evidence

Hosted Linux CI is the authoritative clean-environment check for the pushed
snapshot. Record the exact workflow URL, run number, head SHA and completed
jobs here. A green workflow is mechanical evidence only; it does not imply
Palomar editorial review, registration or endorsement.

- Historical head SHA: `8c8c0194519cb189931ae29147d1927e351b32ce`
- [Almost-Schur development checks, run 34153158216](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/34153158216):
  `Almost-Schur package and Lean verification` passed in 11m49s, and
  `Almost-Schur Linux Comparator and NanoDa` passed in 13m24s.
- [Palomar Submission 01 audit, run 34153158227](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/34153158227):
  `Audit Submission 01 package and build Lean` passed in 54m8s, and
  `Run pinned Comparator and NanoDa` passed in 17m39s.

These runs checked the earlier algebraic Comparator surface. They are retained
as historical evidence and do not validate the repaired geometric selection.
Likewise, checks at `539089aab6a9444ab401ef6136acd292f6490745` predate the repair.
For the current artifact, inspect the run's full head SHA on PR #8 and compare
it with the exact source SHA in the final handoff.

## Palomar evidence

If an authorized intake is created, record only its public submission ID and
public mechanical workflow URL here. Keep the private status URL and bearer
access token outside the repository. Record editorial review and registration
as separate states, and never claim public registration without the
corresponding registry record.
