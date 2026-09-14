# Verification record

Selected theorem:
`SymmetricTensorHeatEntry.symmetricTensorHeatShortTimeWellPosed`.

The reproducible checks are:

```sh
lake build
lake env lean --src-deps TensorHeatChallenge.lean
python3 scripts/check-challenge-boundary.py
python3 scripts/check-provenance.py
uv run scripts/check-package.py
python3 scripts/check-axioms.py
lake env lean scripts/check-closed-statement.lean
bash scripts/verify-comparator.sh                 # Linux
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh  # macOS
```

The Challenge contains exactly one intentional `sorry`. The Solution does not
import the Challenge and active proof sources contain no `sorry`, `admit`, or
`axiom`. The selected theorem is expected to use exactly `propext`,
`Classical.choice`, and `Quot.sound`.

The closure audit checks the compiled `completeStatement` body and rejects
candidate proof-development references. Its only candidate-local dependencies
may be the statement's explicitly enumerated Mathlib-facing semantic helpers,
their structural bundle instances, and generated proposition proofs. All nine
semantic helper definitions are independently selected by Comparator in
addition to `completeStatement` itself.

Comparator pins:

- Comparator: `68a064109f01c08f47c8edc9f51d6a2bbffaa188`
- Lean4Export: `15f6055e299ad5b89345e533cc2192f4cc00f659`
- NanoDa: `68d5ca9db226849b41a6fff59d796ff19d0a8840`
- Landrun: `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`
- hosted renderer: `ef2fa1eadcb246c2346ddba39b52eaa53d4bb763`

The macOS Comparator replay explicitly substitutes an unsandboxed compatibility
wrapper because Landlock is Linux-only. The hosted GitHub workflow exercises
the pinned renderer and real Landrun. Passing these checks does not imply
Palomar editorial acceptance, intake, or registration.

## Recorded local result

On 2026-09-14, the prepared source passed all commands above. In particular:

- `lake build` completed 3,241 jobs;
- the dependency-only Challenge compile and local-import negative control
  passed;
- the package/schema, immutable provenance, and proof-hole checks passed;
- the selected theorem used exactly `propext`, `Classical.choice`, and
  `Quot.sound`;
- the compiled closure audit found 191 constants, no proof-development
  references, 11 canonical structural helpers, and 42 generated proofs; and
- Comparator reported that the solution is okay after both NanoDa and Lean's
  default kernel accepted the exported proof.

This local Comparator run used the explicitly labeled unsandboxed macOS
fallback. The exact candidate commit must also pass the hosted Linux renderer
workflow with real Landrun before the package is described as renderer-ready.
