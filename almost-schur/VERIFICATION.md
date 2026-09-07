# Verification record

## Local checks

The final source commit and hosted run are recorded here after the package is
committed and pushed. The local package checks are:

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

The Challenge intentionally contains two theorem `sorry` placeholders. They
are statement-surface holes and are not included in the implementation axiom
audit. The Solution and all implementation modules must contain no `sorry`,
`admit`, custom `axiom`, `Lean.ofReduceBool` or `sorryAx` dependency.

## Hosted evidence

Hosted Linux CI is the authoritative clean-environment check for the pushed
snapshot. Record the exact workflow URL, run number, head SHA and completed
jobs here. A green workflow is mechanical evidence only; it does not imply
Palomar editorial review, registration or endorsement.

## Palomar evidence

If an authorized intake is created, record only its public submission ID and
public mechanical workflow URL here. Keep the private status URL and bearer
access token outside the repository. Record editorial review and registration
as separate states, and never claim public registration without the
corresponding registry record.
