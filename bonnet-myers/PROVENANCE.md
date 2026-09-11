# Provenance and attribution

## Mathematical source

The selected result is the classical Bonnet--Myers theorem. The primary source
is Sumner Byron Myers, “Riemannian manifolds with positive mean curvature,”
*Duke Mathematical Journal* 8(2) (1941), 401--404,
<https://doi.org/10.1215/S0012-7094-41-00832-3>.

The formal statement assumes a complete connected smooth boundaryless
finite-dimensional real Riemannian manifold, dimension at least two, and the
pointwise lower bound `Ric >= (n-1) K g` for `K > 0`. It concludes compactness
and the sharp diameter bound `pi / sqrt K`. It does not include equality
rigidity, sphere classification, fundamental-group finiteness, or a novelty
claim.

## Same-repository infrastructure

Nineteen files under `vendor/curvature/PoincareCurvature/` are byte-for-byte
copies of their counterparts under `curvature/PoincareCurvature/` at immutable
repository commit `5db025e6d20d8aad714c3d116714545d1823fd8e`:

<https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/5db025e6d20d8aad714c3d116714545d1823fd8e/curvature>

They supply general smooth sections, covariant derivatives, Levi--Civita
existence, curvature contractions, and smooth-dependence infrastructure for
ordinary differential equations. They do not contain the selected theorem or
the local geodesic-distance, minimizing-segment, global parallel-frame,
second-variation, sine-index, Ricci contradiction, diameter, or compactness
proof developed in `BonnetMyers/`.

The files are compiled unchanged against this project's pinned Lean 4.33.0 and
Mathlib revision. The repository's Apache-2.0 licence is copied to the package
root and `vendor/curvature/LICENSE`. `scripts/check-vendored.py` recomputes Git
blob hashes and fails if the inventory or any byte differs from the immutable
source snapshot.

The three Comparator/Landrun shell helpers under `scripts/` derive from the
already attributed same-repository verification tooling at that commit. The
Comparator driver is updated to the current Palomar verifier pin; the helpers
are execution harnesses, not proof source.

## Superseded external wrapper

The branch originally contained a thin wrapper around
`qinz1yang/differential-geometry` at commit
`1b535dd102b94cc42b107cca27059687888f08b3`. That wrapper and its attribution
are preserved as noncompiled historical text in `superseded-upstream-wrapper/`.
The active Lakefile has no DifferentialGeometry dependency, and no active Lean
file imports, copies, translates, or adapts its Bonnet--Myers proof. The two
formalizations are related only as independent implementations of the same
classical theorem.

## Mathlib

The project builds on `leanprover-community/mathlib4` at immutable revision
`db584cd6d46c92f209a44c0f1c829460d327499d`. Mathlib supplies the underlying
manifold, Riemannian metric, calculus, ODE, integration, linear algebra,
topology, and extended-metric definitions. All new theorem proofs live in this
repository and are kernel checked.

## Automation and responsibility

Codex materially assisted with proof engineering, modular integration,
packaging, and verification under the maintainer's direction. Arthur Freitas
Ramos, David Barros Hulak, and Ruy J. G. B. de Queiroz are the human authors;
Arthur Freitas Ramos is the responsible maintainer. AI assistance is not listed
as authorship or mathematical priority. Kernel, Comparator, and NanoDa checks
are mechanical evidence rather than independent expert review or source-author
endorsement.
