# De Lellis--Topping almost-Schur inequality

This project formalizes the sharp almost-Schur inequality for a nonempty
connected closed smooth Riemannian manifold of dimension at least three with
nonnegative Ricci curvature:

```text
∫ (R - average R)^2 ≤ 4 n (n - 1) / (n - 2)^2
  * ∫ |Ric - (R / n) g|^2.
```

It also proves the equality characterization: equality holds exactly when
the metric-raised trace-free Ricci operator vanishes everywhere, i.e. the
metric is Einstein. This is a formalization of the classical theorem of
Pierre De Lellis and Peter M. Topping, not a new mathematical result or a
priority claim.

## Main results

- `AlmostSchur.almostSchur_bound_complete` in
  `AlmostSchur/AlmostSchurFinal.lean` is the complete geometric inequality.
- `AlmostSchur.almostSchur_equality_iff` in
  `AlmostSchur/AlmostSchurEquality.lean` is the equality/rigidity theorem.
- `AlmostSchurEntry.almostSchur_from_identities` and
  `AlmostSchurEntry.almostSchur_equality_data` are the small,
  Mathlib-only Comparator surface in `Challenge.lean` and `Solution.lean`.

The implementation proves, rather than assumes, the normalized smooth
metric-density volume, global integration by parts, Poincare and weak Poisson
solvability, smooth local representatives of the Poisson solution, the
integrated Bochner identity, the actual contracted-Bianchi bridge, the sharp
finite-dimensional cancellation, and the equality rigidity argument.

The project does not identify this normalized density measure with dimensional
Hausdorff measure, prove optimality of the numerical constant, classify space
forms, or formalize Ricci flow.

## Submission surface

`Challenge.lean` imports only Mathlib and states the sharp cancellation and
equality-data endpoints. `Solution.lean` proves the same declarations from
the completed local development and exposes the concrete geometric endpoints.
`comparator.json` selects both Challenge/Solution declarations. The selected
project is the repository-relative `almost-schur` directory;
`formalization.yaml` records the source, attribution, adapted dependencies,
scope and AI-assisted development disclosure.

The result is source-based and distinct from the earlier `contracted-bianchi`
and `schur-rigidity` entries. The inherited curvature core and adapted
Rellich--Kondrachov files retain their immutable provenance and author notices.
See [PROVENANCE.md](PROVENANCE.md) and [SUBMISSION.md](SUBMISSION.md).

## Reproduction

Pinned Lean: **4.33.0**. Pinned Mathlib:
`db584cd6d46c92f209a44c0f1c829460d327499d`.

```sh
lake exe cache get
lake build
lake env lean --src-deps Challenge.lean
python3 scripts/check-vendored.py
python3 scripts/check-curvature-provenance.py
python3 scripts/check-axioms.py
python3 scripts/validate-formalization.py
bash scripts/verify-comparator.sh
```

The local Comparator replay explicitly opts into the unsandboxed macOS
fallback only when `PALOMAR_ALLOW_UNSANDBOXED_LOCAL=1` is set. Hosted Linux
verification must use real Landrun. Local checks, hosted mechanical
verification, editorial review and registry registration are separate states;
see [VERIFICATION.md](VERIFICATION.md) and [SUBMISSION.md](SUBMISSION.md).

## Sources and attribution

The mathematical source is De Lellis and Topping, [*Almost-Schur
lemma*](https://doi.org/10.1007/s00526-011-0413-z), Theorem 1.1. The
development also uses the immutable contracted-Bianchi curvature snapshot and
an adapted subset of Adam Benenson's Rellich--Kondrachov project. Neither
dependency's contributors are presented as endorsing this formalization.

The new modules were developed with Codex under the direction of the named
human authors. Automated Lean, Comparator, NanoDa and CI results are
mechanical evidence, not independent expert review.
