# Symmetric tensor heat equation

This focused Lean package prepares a new Palomar entry for short-time
well-posedness of the inhomogeneous heat equation on symmetric covariant
two-tensors over a closed smooth Riemannian manifold.

The selected theorem is
`SymmetricTensorHeatEntry.symmetricTensorHeatShortTimeWellPosed`. It constructs
a positive time interval and finite-atlas initial, source, and solution spaces.
For symmetric represented data it proves existence and uniqueness of a
coefficient witness whose geometric readout:

- is fiberwise symmetric;
- has the prescribed initial trace;
- satisfies `partial_t u - tr_g(nabla^2 u) = f`; and
- obeys a global finite-atlas `C^{2+alpha,1+alpha/2}` estimate.

The Mathlib-only [TensorHeatChallenge.lean](TensorHeatChallenge.lean) expands
the induced two- and three-tensor connections and takes the orthonormal trace
of the second covariant derivative. The independently compiled
[TensorHeatSolution.lean](TensorHeatSolution.lean) does not import the
Challenge; it bridges the statement to the unchanged implementation in the
repository's `curvature/` project.

## Scope boundary

The theorem is deliberately about the constructed finite-atlas Holder class.
It does not claim that every bare intrinsic tensor section has a coefficient
representation, nor uniqueness outside the represented classical class. It
constructs a short endpoint rather than solving to an arbitrary prescribed
final time. This is a formalization of classical mathematics, not a novelty or
priority claim.

## Verification

From this directory:

```sh
lake build
lake env lean --src-deps TensorHeatChallenge.lean
python3 scripts/check-challenge-boundary.py
python3 scripts/check-provenance.py
uv run scripts/check-package.py
python3 scripts/check-axioms.py
lake env lean scripts/check-closed-statement.lean
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh  # macOS
```

The hosted workflows run both the pinned renderer and the complete unmodified
Palomar mechanical verifier with real Linux Landrun. The package has no Lake
path dependencies: its unchanged vendored proof development is a library in
the root project, so all sandbox writes stay under the root build directory.
Preparation and verification do not authorize Palomar intake or registration.

See [PROVENANCE.md](PROVENANCE.md),
[RESEARCH_INTEREST.md](RESEARCH_INTEREST.md), and
[VERIFICATION.md](VERIFICATION.md) for the exact boundaries and evidence.
