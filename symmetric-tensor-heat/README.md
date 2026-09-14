# Symmetric tensor heat equation

This focused Lean package prepares a new Palomar entry for short-time
well-posedness of the inhomogeneous heat equation on symmetric covariant
two-tensors over a closed smooth Riemannian manifold.

The selected theorem is
`SymmetricTensorHeatEntry.symmetricTensorHeatShortTimeWellPosed`. It constructs
a positive time interval and finite-atlas initial, source, and solution spaces.
The compared proposition now exposes the analytic representation itself:

- a finite nonempty chart index;
- nonnegative chart weights summing to one, spanning local frames, normalized
  chart coordinates, positive source rescalings, and the normalized time map;
- exact finite-sum reconstruction of the global initial tensor, source,
  solution, and solution time derivative from their local tensors, together
  with equations identifying the local-frame coefficients with the displayed
  matrix representatives;
- injective initial, source, and solution coefficient readouts and witnesses
  for every atlas-wide family of constant matrices, which rule out singleton
  or all-zero coefficient carriers; and
- explicit spatial `C^{2,alpha}`, parabolic `C^{alpha,alpha/2}`, and solution
  `C^{2+alpha,1+alpha/2}` derivative and Hölder certificates controlled by the
  same sizes and norms used in the Schauder estimate.

For symmetric represented data it then proves existence and uniqueness of a
coefficient witness whose reconstructed geometric field:

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
lake env lean scripts/check-nonvacuity.lean
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

## Historical editorial correction

Commit `a210bc382e4f1e34f8e7de2384cf3b86cf561938` passed the pinned mechanical
pipeline but its selected statement left the existential coefficient spaces,
readouts, norms, and solution predicate underconstrained. In particular, the
proposition itself admitted a singleton/all-zero interpretation even though
the implementation behind the bridge used genuine atlas Banach spaces. That
candidate was therefore not a substantively adequate statement of record.

This replacement changes the Challenge and Solution together. The finite
atlas reconstruction laws, faithful coefficient readouts, nonzero constant
families, actual derivative identities, Hölder bounds, and norm control are
now premises of the selected proposition, not facts hidden only in the proof
development or claimed in metadata. A fresh intake would be required; the
historical intake and its private control link must not be reused.

See [PROVENANCE.md](PROVENANCE.md),
[RESEARCH_INTEREST.md](RESEARCH_INTEREST.md), and
[VERIFICATION.md](VERIFICATION.md) for the exact boundaries and evidence.
