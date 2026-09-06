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

## Reproduce in an isolated checkout

```sh
git clone https://github.com/abenenson/rellich-kondrachov.git rellich-test
cd rellich-test
git checkout --detach 70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23
git apply /absolute/path/to/almost-schur/dependencies/rellich-v4.33.patch
lake exe cache get
lake build RellichKondrachov
```

The patch and these results are evidence for future dependency selection.
The almost-Schur project does not yet import this library. Before adoption,
audit the relevant semantics, preserve these notices, and add structured
formalization provenance at the eventual submission boundary.
