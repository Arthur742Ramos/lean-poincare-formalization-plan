# Verification record

Selected theorem:
`EinsteinComparisonEntry.einsteinScalarComparisonAndSharpLifespan`.

Local renderability-repair replay on 2026-09-12 passed the full `lake build`
(3,030 jobs), dependency-only Challenge compile, package/schema validation,
vendored source verification, seven-result axiom audit, compiled closed-body
audit, Comparator theorem-and-definition comparison, NanoDa kernel replay, and
Lean default-kernel replay. The failed registry renderer's pinned
core-notation audit also accepted both selected signatures. This replay covers
the strengthened selected theorem, including its reciprocal scalar profile,
one-sided blow-up limit, and lifetime identity. The Comparator run used the
explicit macOS fallback described below.

The reproducible checks are:

```sh
lake build
lake env lean --src-deps Challenge.lean
python3 scripts/check-challenge-boundary.py
python3 scripts/check-vendored.py
python3 scripts/check-package.py
python3 scripts/check-axioms.py
lake env lean scripts/check-closed-statement.lean
bash scripts/verify-comparator.sh                 # Linux
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh  # macOS
```

The Challenge has exactly one intentional `sorry`; active implementation and
Solution sources have none.  The selected theorem and all six principal
implementation theorems use exactly `propext`, `Classical.choice`, and
`Quot.sound`.  The Challenge boundary check removes all candidate build paths,
proves that a local `PoincareCurvature` import is unavailable, and then compiles
the real Challenge from the pinned dependency closure.

The vendored-source check verifies nineteen files against their immutable Git
blobs at repository commit
`0cc7c31bf6e2dac5c0359a432f3d99803f563017`, plus exact reviewed hashes for two
narrow compatibility adaptations.  It also verifies both Apache-2.0 licence
copies.

Comparator pins:

- Comparator: `68a064109f01c08f47c8edc9f51d6a2bbffaa188`
- Lean4Export: `15f6055e299ad5b89345e533cc2192f4cc00f659`
- NanoDa: `68d5ca9db226849b41a6fff59d796ff19d0a8840`
- Landrun: `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`

The compiled closed-statement audit rejects any candidate-defined mathematical
data reachable from the selected definition body; proposition-valued compiler
proof helpers are the only permitted candidate constants. The actual pinned
Palomar renderer is replayed under Landrun by the dedicated hosted workflow.
The macOS Comparator replay explicitly substitutes an unsandboxed compatibility
wrapper because Landlock is Linux-only. Passing local checks does not imply a
hosted pass, editorial acceptance, intake, or registration.
