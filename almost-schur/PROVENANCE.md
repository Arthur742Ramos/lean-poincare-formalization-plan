# Provenance and attribution

## Mathematical source

The selected result is the classical De Lellis--Topping almost-Schur lemma:

> C. De Lellis and P. M. Topping, *Almost-Schur lemma*, Calc. Var. 43
> (2012), 347–354, Theorem 1.1, DOI [10.1007/s00526-011-0413-z](https://doi.org/10.1007/s00526-011-0413-z).

The Lean development is a source-based formalization of that theorem. It makes
no claim of mathematical originality, priority, optimality beyond the cited
coefficient, or endorsement by the source authors.

## Reused formalizations

`AlmostSchur/CurvatureVendor/` contains an explicitly recorded adaptation of
the contracted-Bianchi curvature core from
`Arthur742Ramos/lean-poincare-formalization-plan` at immutable commit
`12cebb809524d0cd185c6cd7bcb5b73d3562bce1`. The source paths, source blobs,
local hashes, adaptation hashes and permitted changes are recorded in
`AlmostSchur/CurvatureVendor/PROVENANCE.json`; the local provenance script
recomputes them. The inherited files retain their source notices and are
supporting infrastructure, not the selected almost-Schur result.

`AlmostSchur/GeometryStatements.lean` and the independent definitions in
`Challenge.lean` adapt the same source's canonical smooth-extension construction
to the tangent bundle. `AlmostSchurEntry.Geometry.curvature_eq` proves that the
explicit commutator agrees with the inherited bundled curvature. The new
Ricci contraction, tensor norm, volume and Einstein identifications connect
the independently stated theorem to the complete implementation.

`RellichKondrachov/` contains the 36-file adapted subset of Adam Benenson's
Apache-2.0 project at immutable commit
`70f85d4c1bf99c6e7d61e8be4daa6f3664d08d23`. The exact adapted inventory and
hashes are in `dependencies/rellich-vendored.json`, and
`scripts/check-vendored.py` checks the inventory and notices. The adapted
subset supplies generic compactness and chart measure infrastructure; it does
not supply the almost-Schur theorem, a Poisson solver, or the geometric
Bochner identity.

The project also depends on the pinned Mathlib revision in `lakefile.toml` and
`lake-manifest.json`. Mathlib is infrastructure, not a prior formalization of
the selected theorem.

## Authorship and automation

Arthur Freitas Ramos, David Barros Hulak and Ruy J. G. B. de Queiroz are the
listed human authors and Arthur Freitas Ramos is the responsible maintainer.
Codex materially generated and revised Lean proofs, integration modules,
documentation and verification scripts under the authors' direction. Human
review, mathematical responsibility, source selection and delivery decisions
remain with the named authors. No independent human peer review or source
author endorsement is recorded.
