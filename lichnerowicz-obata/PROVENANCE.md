# Provenance and attribution

## Mathematical sources and exact scope

The selected result is the classical Lichnerowicz--Obata first-eigenvalue
theorem, not a new mathematical theorem or a claimed first formalization.

- André Lichnerowicz, *Géométrie des groupes de transformations*, Dunod,
  Paris, 1958. This is the historical source of the sharp lower bound;
  it is also reference [2] in Obata's paper below.
- Morio Obata, *Certain conditions for a Riemannian manifold to be isometric
  with a sphere*, Journal of the Mathematical Society of Japan 14(3)
  (1962), 333--340, [DOI: 10.2969/jmsj/01430333](https://doi.org/10.2969/jmsj/01430333).
  Theorem A, Theorems 1--2, and the proof in Section 2 supply the geometric
  rigidity and eigenfunction source alignment. The source uses the
  nonnegative Laplacian; this development writes the equivalent equation
  `div grad f = -λ f`.

The selected Lean theorem is on **closed connected** smooth Riemannian
manifolds of dimension at least two with `Ric ≥ (n-1)K`, `K > 0`. It includes
attainment and minimality of a positive smooth eigenvalue, the lower bound,
and equality exactly for the radius-`1/sqrt K` round sphere. It does not claim
the noncompact complete version of Theorem A, the whole spectral resolution,
eigenspace multiplicities, or a new research theorem.

The sphere conclusion is a genuine diffeomorphism, smooth in both directions,
whose radius-scaled ambient inclusion preserves the tangent inner products
everywhere. It uses the standard unit-sphere manifold in Euclidean
`(n+1)`-space to express the induced metric of the required radius. It is not
merely a homeomorphism and is not an assertion about ambient chordal distance.

## Reused formalizations

1. The path dependency `../almost-schur` is inherited **without source changes**
   from this repository at
   [`3faf25aefc27842a77c37ca178e8a40a20bb20c7`](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/3faf25aefc27842a77c37ca178e8a40a20bb20c7/almost-schur).
   It supplies the actual Levi-Civita, curvature, Riemannian integration,
   Bochner, Sobolev compactness, variational PDE, and regularity infrastructure.
   Its selected almost-Schur theorem is not the new selected result here.
   Its named human authors are Arthur Freitas Ramos, David Barros Hulak, and
   Ruy J. G. B. de Queiroz. Existing notices and structured provenance remain
   in that unchanged subproject.
2. The inherited curvature implementation adapts the contracted-Bianchi core
   at [`12cebb809524d0cd185c6cd7bcb5b73d3562bce1`](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/12cebb809524d0cd185c6cd7bcb5b73d3562bce1/contracted-bianchi).
   Its inventory is `../almost-schur/AlmostSchur/CurvatureVendor/PROVENANCE.json`.
   The independent `extensionBump`, `extension`, and `curvature` definitions
   also adapt the explicitly attributed geometry vocabulary in the pinned
   almost-Schur source. The comparison theorems prove agreement with the
   implementation, rather than assuming a curvature bridge.
3. The inherited 36-file `RellichKondrachov/` adaptation originates from Adam
   Benenson's Apache-2.0 project at
   [`70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`](https://github.com/abenenson/rellich-kondrachov/tree/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23).
   Its exact inventory is `../almost-schur/dependencies/rellich-vendored.json`.
4. Mathlib is pinned to
   [`db584cd6d46c92f209a44c0f1c829460d327499d`](https://github.com/leanprover-community/mathlib4/tree/db584cd6d46c92f209a44c0f1c829460d327499d).
   The new subproject resolves this same immutable dependency via the pinned
   almost-Schur path dependency and its committed manifest.

`scripts/verify-comparator.sh`, `scripts/landrun-wrapper.sh`, and
`scripts/fake-landrun.sh` are exact copies from the same almost-Schur snapshot.
They retain its pinned verifier revisions and explicit distinction between
real Linux Landrun and the unsandboxed macOS development fallback.

## New contribution and independent boundary

The new source develops spectral attainment and smooth eigenfunctions,
global Obata rigidity with both pole extensions, the round-sphere converse,
and the assembled Lichnerowicz--Obata theorem. The source list and public
declaration audit distinguish this code from the unchanged path dependency.

`LichnerowiczObataChallenge.lean` imports only Mathlib. It constructs a
metric-compatible torsion-free connection before stating the Ricci-conditional
theorem. It independently specifies curvature, Ricci, gradient, Laplacian,
first-eigenvalue minimality, and the global round metric. All nine definitions
are selected for Comparator comparison. The only intentional proof hole is
the Challenge's selected theorem; neither the implementation nor the Solution
imports that hole. Distinct Challenge/Solution module names avoid collisions
with the inherited almost-Schur package.

## Authorship, automation, and release boundary

Arthur Freitas Ramos is the responsible maintainer of this candidate.
Codex materially generated and revised its Lean proofs, integration,
verification code, and documentation under the maintainer's direction.
Earlier contributors are credited for the inherited work above. No source
author endorsement or independent human mathematical review is claimed.

This is a **new entry candidate**, not an update to the earlier almost-Schur
entry. Local checks, independent verification, external review, intake, and
public registration are different states. Preparation does not authorize a
registry intake or public registration; no previous entry ID is reused.
