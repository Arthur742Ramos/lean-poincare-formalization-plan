# Provenance and attribution

## Direct mathematical source

Peter Topping, *Lectures on the Ricci Flow*, London Mathematical Society
Lecture Note Series 325, Cambridge University Press (2006), §1.2.1,
<https://doi.org/10.1017/CBO9780511721465>, explicitly gives the Einstein
homothetic solution `g(t) = (1 - 2 λ t) g₀` and its finite collapse time when
`λ > 0`.  This project adapts that classical equality model to an arbitrary
initial time and adds the explicit scalar-curvature barrier identity, exact
positive-factor time set, and endpoint Riemannian-metric obstruction.

## Historical background

Richard S. Hamilton, “Three-manifolds with positive Ricci curvature,”
*Journal of Differential Geometry* 17(2) (1982), 255--306,
<https://doi.org/10.4310/jdg/1214436922>, is the historical source for Ricci
flow and its curvature-evolution framework.  It is not presented here as the
direct source for the arbitrary-dimensional Einstein equality statement.
This project makes no claim of mathematical novelty, first formalization, or
source-author endorsement.

## Same-repository implementation source

The local dependency closure under `vendor/curvature/PoincareCurvature/` comes
from the Apache-2.0 `curvature/` project in this repository at immutable commit
`0cc7c31bf6e2dac5c0359a432f3d99803f563017`.

Nineteen Lean files are byte-for-byte copies of that snapshot.  Two additional
source files, `LocalExistence/EinsteinAux.lean` and
`LocalExistence/Einstein.lean`, are narrowly adapted for the package's exact
Lean 4.33.0 elaboration environment.  The adaptations replace a private
derivative bridge with public `mvfderiv` lemmas, make transported Riemannian
inner-product instances explicit, expose a real-derivative normalization, and
remove a redundant `congr`; they do not change theorem statements or add
axioms.  `scripts/check-vendored.py` verifies the exact file inventory, the
nineteen immutable Git blob identities, and the two reviewed adapted blob hashes.

The vendored library supplies general tangent connections, curvature tensors
and contractions, Ricci-flow structures, homothetic metric families, and the
Einstein intrinsic-solution construction.  The new
`RicciScalarComparison/EinsteinScalar.lean` derives the scalar trace formula,
its equality with the quadratic barrier, the exact positive time set, local
solutions before extinction, and the endpoint obstruction.  `Solution.lean`
adds the independent Mathlib-only Challenge bridges.

## Independent overlapping formalization

`qinz1yang/differential-geometry` at commit
`1b535dd102b94cc42b107cca27059687888f08b3` is an independent Lean geometry
library associated with Chow--Liao--Qin, “A Lean Formalization of Hamilton's
Three-Manifold Theorem,” arXiv:2608.21502.  It includes the general
scalar-curvature evolution equation and scalar maximum-principle consequences.
This package neither imports nor vendors that repository and does not claim
priority over it.  The selected result is intentionally the exact Einstein
equality model and endpoint obstruction, not a second general evolution or
maximum-principle theorem.

## Mathlib and verification tooling

Mathlib is pinned at
`db584cd6d46c92f209a44c0f1c829460d327499d`.  It supplies manifold calculus,
Riemannian metrics, finite-dimensional inner-product linear algebra, and real
derivatives.  Comparator, Lean4Export, Landrun, and NanoDa are pinned by the
verification script.  Kernel and replay checks are mechanical evidence, not
independent expert review.
