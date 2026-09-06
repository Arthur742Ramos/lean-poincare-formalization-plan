# Almost-Schur: geometric-analysis development

Target: the De Lellis–Topping almost-Schur inequality and its Einstein equality
case on nonempty connected closed smooth Riemannian manifolds of dimension at
least three with nonnegative Ricci curvature.

**Incomplete development; not a Palomar submission artifact.** There is no
Challenge, Solution or Comparator in this directory yet. The full inequality
and equality rigidity are not proved. Do not submit these foundations as the
research theorem.

## Proved foundations

- `AlmostSchur.Gradient`: actual differential-to-gradient Riesz duality,
  uniqueness, zero-gradient characterization, and norm identities.
- `AlmostSchur.Hessian`: connection Hessian and Laplacian, with an
  orthonormal trace formula independent of basis/index type.
- `AlmostSchur.HilbertSchmidt`: intrinsic squared tensor norm, its full
  double-contraction formula, nonnegativity, and exact trace-free decomposition.
- `AlmostSchur.HessianNorm`: the pointwise trace-free norm identity for the
  actual covariant Hessian. This is not an integrated Bochner formula.

The Hessian is defined relative to a supplied connection; symmetry and smooth
regularity are not yet proved here. The final result must use Levi–Civita.
All definitions are total as in Mathlib; differentiability obligations must be
discharged when interpreting or differentiating them.

## Reproduction

Lean `v4.33.0`; Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

```sh
cd almost-schur
lake exe cache get
lake build
python3 scripts/check-axioms.py
```

Local development reused an ignored dependency-cache symlink; committed source
and manifest do not require a sibling project. The Linux workflow reconstructs
dependencies from the pinned manifest.

Local build passed (3479 jobs). All 23 public declarations' transitive axioms
are confined to `propext`, `Classical.choice`, `Quot.sound`. The check rejects
missing reports and three classes of unapproved axioms. Hosted CI is separate
evidence and must be checked at the exact source commit.

## Remaining work, in order

1. Intrinsic volume-density compatibility, finite positive total volume.
2. Smooth gradient/Hessian theory, manifold integration by parts.
3. Mean-zero coercivity, weak Poisson existence and smooth elliptic regularity.
4. Integrated Bochner and the geometric almost-Schur inequality.
5. Einstein equality rigidity, exact source/hypothesis audit.
6. Only then: independent Challenge/Solution packaging and kernel replay.

The external compactness library was rebuilt and migrated experimentally;
see [dependency evidence](dependencies/README.md). It is not yet a dependency
of this Lake project. Nothing here assumes its theorems to obtain the target.

## Sources and contribution

Mathematical source: De Lellis and Topping,
[Almost-Schur lemma](https://arxiv.org/abs/1003.3527v2), Theorem 0.1 (published
Theorem 1.1). This is source-based work, not a new mathematical discovery.
The pointwise trace decomposition is supporting linear algebra, not a
standalone research-interest claim.

The new modules were developed with Codex at the maintainer's request.
They currently import only Mathlib, not copied project-local geometry.
The existing `schur-rigidity/` proof library is planned integration material,
not yet imported. Its immutable provenance must be recorded if reused.
The separate migration patch preserves the external project's attribution and
license; it does not imply its author's endorsement or review.
