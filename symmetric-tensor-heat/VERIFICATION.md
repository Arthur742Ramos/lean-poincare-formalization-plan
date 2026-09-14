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

- Comparator: `575674928e239f5bc452aab72d1dd7b0f1326494`
- Lean4Export: `15f6055e299ad5b89345e533cc2192f4cc00f659`
- NanoDa: `68d5ca9db226849b41a6fff59d796ff19d0a8840`
- Landrun: `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`
- hosted renderer: `a013555a88a0fc9ec910a09ea833dc9cc338db35`

The macOS Comparator replay explicitly substitutes an unsandboxed compatibility
wrapper because Landlock is Linux-only. The hosted GitHub workflow exercises
the pinned renderer and real Landrun. Passing these checks does not imply
Palomar editorial acceptance, intake, or registration.

## Historical intake and repaired topology

The intake for repository commit
`7f93a3dd648913bbe399af8cde59d30547e34a12` is historical. Its preparation,
metadata, provenance, Challenge compilation, and initial package builds passed,
but Comparator failed when Landrun denied a write beneath the nested path
package at `vendor/curvature/.lake/build/lib`. A later commit cannot alter that
immutable checkout.

The replacement candidate removes the path package. It compiles the unchanged
vendored sources as a root `PoincareCurvature` library, leaving the manifest
with zero path dependencies and putting all generated outputs beneath the one
root `.lake/build` directory Palomar permits. It requires a fresh intake
authorization after the exact replacement commit passes hosted verification.

## Recorded local result

On 2026-09-14, the repaired source passed every package-local command above
through the compiled closure audit. In particular:

- the repaired root-library topology completed a cold build of
  `TensorHeatSolution` with all 3,238 jobs successful;
- the subsequent complete default-target build finished all 3,240 jobs;
- the dependency-only Challenge compile and local-import negative control
  passed;
- the package/schema, immutable provenance, and proof-hole checks passed;
- the selected theorem used exactly `propext`, `Classical.choice`, and
  `Quot.sound`;
- the compiled closure audit found 191 constants, no proof-development
  references, 11 canonical structural helpers, and 42 generated proofs.

The prior package topology passed a local replay with the older Comparator pin,
but that is historical evidence, not validation of this replacement. On this
macOS host, the production Comparator revision's Lean 4.34.0-rc1 dependency
build terminates with `SIGTRAP` before reading the candidate, including from a
fresh checkout. Therefore no local current-Comparator pass is claimed. The
exact candidate commit must pass both hosted Linux workflows—the complete
Palomar verifier and the renderer—with real Landrun before the replacement is
described as mechanically ready.
