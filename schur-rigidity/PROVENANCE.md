# Provenance and distinct contribution

The twelve `PoincareCurvature/**/*.lean` files are copied without modification
from `contracted-bianchi/PoincareCurvature/` at repository commit
`90d215d81d30a5f67922dce00dfa160b4878e1c5`:

https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/tree/90d215d81d30a5f67922dce00dfa160b4878e1c5/contracted-bianchi/PoincareCurvature

They retain original copyright and author notices. This dependency closure
supplies connection calculus, curvature tensoriality, metric symmetries and
the corrected differential Bianchi identity. The earlier entry's selected
double contraction is not selected again.

New root-level proof modules establish actual Ricci/scalar differentiation,
bilinear-derivative extension independence, geometric contracted Bianchi,
Einstein divergence, connected Einstein-factor constancy and three-dimensional
full-curvature rigidity. Challenge and Solution are new statement/proof
surfaces. Mathlib is the only external Lean dependency; no untracked sibling
build product is needed for reproduction.

Verification scripts adapt the earlier entry's pinned Comparator replay and
isolated Challenge test. A dedicated workflow uses Linux Landrun and NanoDa.
Local macOS replay is explicitly labeled unsandboxed development verification.

Mathematical attribution belongs to the classical literature and named sources
in `formalization.yaml`. Project authorship follows the existing maintainer
attribution; this does not assert that each author individually wrote or
reviewed every proof. See `AGENT-CONTRIBUTION.md`.
