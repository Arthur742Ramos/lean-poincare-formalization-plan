# Verification record

Selected theorem:
`SymmetricTensorHeatEntry.symmetricTensorHeatShortTimeWellPosed`.

## Current mathematical repair (working tree)

The chart geometry and frame constraints in the selected Challenge and Solution
compile. The separate `TensorHeatGeometricSymmetry` module proves the
unprojected transpose/PDE and initial-trace bridges and a conditional symmetry
lemma with geometric uniqueness stated explicitly. It also defines the
global-data `GeometricAtlasCauchySolution` class, proves transposition closure
for symmetric data, and obtains existence in that class from the strong atlas
construction. That module passes direct Lean elaboration and its Lake target
build. It also proves linearity of the intrinsic heat operator under
subtraction and reduces equal-data uniqueness to a zero-data problem. This
does not prove the zero-data uniqueness premise, which may need stronger
uniform regularity than the current classical-field interface records. The
selected theorem still uses a symmetrized readout; geometric
uniqueness has not been proved. This is not a candidate for intake.

Before the subsequent trace-estimate addition, `lake build` completed all 3,242 jobs;
`scripts/check-challenge-boundary.py` compiled the Challenge using only pinned
Mathlib dependencies; `scripts/check-axioms.py` accepted exactly the permitted
three axioms; `scripts/check-closed-statement.lean` found no proof-development
reference in the compiled selected body; and `scripts/check-package.py` passed
package, schema, pin, source-boundary and immutable vendored-provenance checks.
These checks do not replace the geometric proof or the exact-commit hosted
Linux renderer and mechanical replay.

The subsequent handoff adds two uniform initial-trace estimates in
`Parabolic/FiniteInitialTrace.lean`. Direct Lean elaboration of that file
passed. Its dependent curvature target is being rebuilt separately; the
earlier 3,242-job result predates this addition and must not be read as
verification of the handoff commit. No Palomar or Comparator result is
claimed for the handoff commit.

The reproducible checks are:

```sh
lake build
lake env lean --src-deps TensorHeatChallenge.lean
lake env lean scripts/check-nonvacuity.lean
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
their structural bundle instances, and generated proposition proofs. All
thirteen semantic helper definitions are independently selected by Comparator
in addition to `completeStatement` itself.

Comparator pins:

- Comparator: `575674928e239f5bc452aab72d1dd7b0f1326494`
- Lean4Export: `15f6055e299ad5b89345e533cc2192f4cc00f659`
- NanoDa: `68d5ca9db226849b41a6fff59d796ff19d0a8840`
- Landrun: `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`
- hosted renderer: `a013555a88a0fc9ec910a09ea833dc9cc338db35`

The macOS Comparator replay explicitly substitutes an unsandboxed compatibility
wrapper because Landlock is Linux-only. The hosted GitHub workflow exercises
the pinned renderer and real Landrun. Passing these checks does not imply
Palomar editorial acceptance, intake, or registration. The full verifier now
runs a bounded preflight that checks the package and provenance, restores the
official Mathlib cache, and compiles both the selected Challenge and the
anti-vacuity regression before starting the production replay. Exact tool
builds are cached by commit tuple. The production verifier still performs a
cold candidate build inside Landrun, so a successful full replay can remain
long; the preflight is intended to reject statement or package defects before
that expensive stage, not to bypass it.

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

## Historical mechanical result and editorial rejection

On 2026-09-14, merge commit
`a210bc382e4f1e34f8e7de2384cf3b86cf561938` passed the complete hosted Palomar
mechanical verifier and renderer after the package-topology repair. Its
selected proposition was nevertheless editorially rejected: it existentially
introduced coefficient carriers, readouts, norms, and `coordinateClass`
without constraining those objects enough to exclude singleton/all-zero
witnesses or to put the claimed Hölder/Schauder content into the statement of
record. That is a substantive statement defect; the mechanical pass does not
cure it.

The historical local evidence for that commit included:

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

Those counts and hashes apply only to the rejected historical statement.

## Strengthened replacement gate

The replacement proposition explicitly carries the finite nonempty atlas,
partition-of-unity weights, spanning frames, local-to-global data/solution/
time-derivative reconstruction equations, local-frame coefficient equations,
positive parabolic source rescaling, injective coefficient readouts, arbitrary
atlas-wide constant matrix families for all three carriers, genuine spatial
and parabolic derivative identities, explicit Hölder bounds, and the same norm
control used in the Schauder estimate. `scripts/check-nonvacuity.lean` proves
that the required constant-family contract cannot be implemented by a
singleton carrier, while `scripts/check-package.py` fails closed if any of the
semantic clauses disappear from the selected statement.

On 2026-09-14, this strengthened working tree passed every package-local gate
listed above. The complete default build finished all 3,240 jobs; the
dependency-only Challenge compile and local-import negative control passed;
the anti-vacuity regression compiled both generically and for the exact matrix
fiber used by the selected statement; and the selected theorem used exactly
`propext`, `Classical.choice`, and `Quot.sound`. The compiled closure audit
found 234 constants, 3 directly referenced selected semantic helpers, 11
canonical structural helpers, 46 generated proposition proofs, and no
proof-development references. These are working-tree results until attached
to an immutable commit and independently repeated by hosted Linux.

On this macOS host, the production Comparator revision's Lean 4.34.0-rc1
dependency build terminates with `SIGTRAP` before reading the candidate,
including from a fresh checkout. Therefore no local current-Comparator pass is
claimed. The exact strengthened candidate commit must pass all local gates and
both hosted Linux workflows—the complete Palomar verifier and the renderer
with real Landrun—before it is described as mechanically ready. A passing
replay still does not authorize intake or registration.
