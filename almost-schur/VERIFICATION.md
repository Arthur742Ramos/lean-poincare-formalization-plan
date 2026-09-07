# Verification record

## Local checks

The final source commit is
`8c8c0194519cb189931ae29147d1927e351b32ce`. The local package checks are:

- `lake build` for the complete `AlmostSchur` development;
- `lake env lean --src-deps Challenge.lean`, with the Challenge imported only
  from the pinned dependency closure;
- `python3 scripts/check-vendored.py`;
- `python3 scripts/check-curvature-provenance.py`;
- `python3 scripts/check-axioms.py`, which scans the public implementation
  declarations and rejects proof-hole tokens and unapproved axioms;
- `python3 scripts/validate-formalization.py`; and
- the pinned Linux Comparator/NanoDa replay, with the explicit unsandboxed
  fallback permitted only for local macOS development.

The local checks passed at the exact source commit, including the complete
`AlmostSchur` build, the `Challenge`/`Solution` build, the dependency-only
Challenge boundary, the vendored-file and curvature-provenance checks, the
formalization metadata validator, and the exhaustive public axiom audit.

The Challenge intentionally contains two theorem `sorry` placeholders. They
are statement-surface holes and are not included in the implementation axiom
audit. The Solution and all implementation modules must contain no `sorry`,
`admit`, custom `axiom`, `Lean.ofReduceBool` or `sorryAx` dependency.

## Hosted evidence

Hosted Linux CI is the authoritative clean-environment check for the pushed
snapshot. Record the exact workflow URL, run number, head SHA and completed
jobs here. A green workflow is mechanical evidence only; it does not imply
Palomar editorial review, registration or endorsement.

- Head SHA: `8c8c0194519cb189931ae29147d1927e351b32ce`
- [Almost-Schur development checks, run 34153158216](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/34153158216):
  `Almost-Schur package and Lean verification` passed in 11m49s, and
  `Almost-Schur Linux Comparator and NanoDa` passed in 13m24s.
- [Palomar Submission 01 audit, run 34153158227](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/34153158227):
  `Audit Submission 01 package and build Lean` passed in 54m8s, and
  `Run pinned Comparator and NanoDa` passed in 17m39s.

The earlier push-triggered runs were canceled duplicate attempts; they are
not evidence for the current snapshot and are not part of this record.

## Palomar evidence

If an authorized intake is created, record only its public submission ID and
public mechanical workflow URL here. Keep the private status URL and bearer
access token outside the repository. Record editorial review and registration
as separate states, and never claim public registration without the
corresponding registry record.
