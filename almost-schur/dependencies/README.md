# Rellich–Kondrachov dependency experiment

Source: Adam Benenson,
[abenenson/rellich-kondrachov](https://github.com/abenenson/rellich-kondrachov/tree/70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23),
immutable commit `70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`.
Source code is Apache-2.0; see `RELLICH-LICENSE`.
Relationship: adapted build/proof compatibility, not independent authorship.

## Completed checks

- Original Lean `v4.29.1` / Mathlib
  `5e932f97dd25535344f80f9dd8da3aab83df0fe6` rebuilt successfully (2826 jobs).
- Applying `rellich-v4.33.patch` produces an experimentally migrated build on
  Lean `v4.33.0` / Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.
  Full `lake build RellichKondrachov` passed (3122 jobs).
- `git apply --check` passed against the original immutable checkout.
- Original and migrated axiom closures of volume finiteness, finite Riemannian chart
  existence and final manifold compactness contain only `propext`,
  `Classical.choice`, `Quot.sound`.

Migration changes strengthen elaboration of existing simplification proofs,
mark two tangent norm instances noncomputable in each chart module, replace
an unsynthesizable hypothesis-parameterized local instance by an explicitly
applied lemma, and expose subtype/composite coercions in two proofs. They also
update the pinned toolchain and dependency manifest. No intended mathematical
theorem statement is weakened; no axiom or proof hole is introduced.
The patch was developed with Codex and has not been upstreamed or endorsed.

The upstream measure is dimensional Hausdorff measure for the Riemannian
distance. Its finiteness and Sobolev compactness do not by themselves prove
the volume density formula, integration by parts, or Poisson regularity.

## Adopted volume and generic Sobolev subset

Thirty-six modules are now vendored in `RellichKondrachov/`: four chart/volume
modules, twenty-nine generic Sobolev, measure transport, and Euclidean
compactness modules, and three generalized density-transport modules.
The latter record `source_path` for the original Riemannian module they adapt.
Their original source
hashes, adapted hashes, author, license and immutable source identity are in
`rellich-vendored.json`. `scripts/check-vendored.py` checks the complete inventory.
Public module conversion is additional to the standalone migration patch.
Private helpers used in public declarations are exposed under unique
`vendor...` names so that this conversion preserves their defining expressions.
The copied Sobolev atlas hypotheses are generalized from analytic `ω`
(`⊤ : WithTop ℕ∞`) to smooth `∞` (`↑(⊤ : ℕ∞)`), with the proofs rebuilt under
the weaker hypothesis. This distinction is necessary for the advertised
smooth-manifold target and is not merely a notation change.
The new neighborhood/total-volume positivity arguments are separately authored
in `AlmostSchur/Volume.lean`; inherited finiteness is attributed to the source.

`AlmostSchur.DensityComparison` proves the two finite comparison constants
needed to transport the generic chart Sobolev construction to normalized
Riemannian density volume. `AlmostSchur.SobolevReconstruction` proves that its
assembled L2 projection represents the original C1 function. These are new
bridges; neither assumes equality with Hausdorff volume. The generalized
chartwise compactness proof is now adopted and instantiated for normalized
volume in `AlmostSchur.SobolevCompactness`. Energy localization and weak-limit
kernel rigidity remain separate obligations before Poincaré or Poisson
existence can be claimed.

## Reproduce the full-library experiment in an isolated checkout

```sh
git clone https://github.com/abenenson/rellich-kondrachov.git rellich-test
cd rellich-test
git checkout --detach 70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23
git apply /absolute/path/to/almost-schur/dependencies/rellich-v4.33.patch
lake exe cache get
lake build RellichKondrachov
```

The patch and these results are evidence for future dependency selection.
The almost-Schur project imports the recorded thirty-six-file subset, not
the Hausdorff-specialized global compactness theorem. Preserve these notices
and add structured
formalization provenance at the eventual submission boundary.
