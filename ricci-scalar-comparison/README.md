# Sharp Einstein scalar comparison and Ricci-flow lifespan

This standalone Lean project proves the exact shrinking Ricci-flow model for
positive Einstein initial data on a nonempty compact smooth manifold.  If

```text
Ric(g₀) = λ g₀,    λ > 0,
```

then the homothetic family

```text
g(t) = (1 - 2 λ (t - t₀)) g₀
```

is a genuine componentwise solution of `∂ₜg = -2 Ric(g)` while the factor is
positive.  Its scalar curvature is spatially constant and attains the standard
quadratic comparison profile exactly:

```text
R(t) = n λ / (1 - 2 λ (t - t₀))
     = R₀ / (1 - (2/n) R₀ (t - t₀)),    R₀ = n λ.
```

The positive-definite time set is exactly
`(-∞, t₀ + 1/(2λ))`, and at the endpoint the homothetic tensor is zero, so no
Riemannian metric can agree with it on a positive-dimensional nonempty
manifold.

The Comparator-selected declaration is
`EinsteinComparisonEntry.einsteinScalarComparisonAndSharpLifespan` in
`Solution.lean`.  Its exact statement is
`EinsteinComparisonEntry.completeStatement` in `Challenge.lean`.

## Auditable geometric surface

The Challenge imports Mathlib only.  It does not accept Ricci curvature,
scalar curvature, a Ricci-flow predicate, or a lifespan estimate as opaque
hypotheses.  Instead it defines:

- curvature by the corrected covariant-derivative commutator;
- Ricci and scalar curvature by explicit orthonormal contractions;
- metric compatibility by the manifold Leibniz rule;
- the Levi--Civita conditions as torsion-free plus metric-compatible; and
- Ricci flow by the componentwise real derivative of the metric tensor.

The Solution proves that these definitions agree with the bundled intrinsic
objects used by the implementation.  In particular, the smooth-extension
bridge is proved pointwise before taking the two curvature traces.

## Exact scope

The selected theorem assumes a nonzero finite-dimensional complete real model
space, a nonempty compact Hausdorff smooth manifold, a `C²` tangent bundle and
Riemannian metric, a `C¹` covariant derivative, and supplied global `C³` tangent
extensions anchored at their base points.  Compactness provides the
sigma-compact infrastructure used by the intrinsic Ricci-flow library; the
Einstein calculation itself is pointwise.

This result is the sharp positive-Einstein equality model for scalar
comparison.  It does **not** prove the general scalar evolution equation, a
maximum principle for arbitrary compact Ricci flows, uniqueness of Ricci flow,
or impossibility of a nonhomothetic continuation.  The endpoint conclusion is
precisely that a Riemannian metric cannot equal the collapsed homothetic tensor.

## Relationship to existing work

Hamilton's 1982 paper introduced Ricci flow and its curvature evolution
equations.  The exact Einstein homothety is classical; no mathematical novelty
or priority claim is made.

The independent `qinz1yang/differential-geometry` project already formalizes
the general scalar-curvature evolution and maximum-principle infrastructure.
This package deliberately does not duplicate that development.  Its narrower
contribution is an independently checkable equality case joining the actual
Ricci-flow equation, the scalar comparison profile, the exact positivity
interval, and the endpoint metric obstruction in one selected theorem.  See
`PROVENANCE.md` and `RESEARCH_INTEREST.md`.

## Reproduction

Lean 4.33.0 and Mathlib revision
`db584cd6d46c92f209a44c0f1c829460d327499d` are pinned.

```sh
lake exe cache get
lake build
lake env lean --src-deps Challenge.lean
python3 scripts/check-challenge-boundary.py
python3 scripts/check-vendored.py
python3 scripts/check-package.py
python3 scripts/check-axioms.py
PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1 bash scripts/verify-comparator.sh  # macOS
```

The macOS Comparator command is an explicit unsandboxed development replay.
The package intentionally has no automatic hosted build: its full pinned build
and audit suite is run from a populated local Mathlib cache.  A reviewer on
Linux can run `bash scripts/verify-comparator.sh` to replay Comparator with real
Landrun.  Local verification, editorial review, intake, and public registration
are separate states.  Preparing this package does not authorize submission.
