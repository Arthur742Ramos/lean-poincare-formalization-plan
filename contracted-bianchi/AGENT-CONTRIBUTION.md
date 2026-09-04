# Agent contribution and human oversight

This record describes preparation of the separate `contracted-bianchi/`
surface in the public repository
`Arthur742Ramos/lean-poincare-formalization-plan`.

## Mathematical origin

The contracted second Bianchi identity and the divergence-free Einstein tensor
are classical results of Riemannian geometry and general relativity.  The
primary mathematical source for this presentation is:

- Arthur L. Besse, *Einstein Manifolds*, Springer, 1987,
  [doi:10.1007/978-3-540-74311-8](https://doi.org/10.1007/978-3-540-74311-8).

The relationship is `formalizes`: this repository gives a Lean
formalization/adaptation of the classical contraction argument.  The theorem
is not claimed as an original mathematical result or as a first presentation.
Mathlib provides general finite-dimensional linear algebra and basis-sum
infrastructure.  The parent `curvature/` package was audited as related
formal context and contains a raw manifold-level second-Bianchi identity, but
it is not a dependency of this standalone project.  Neither Mathlib nor the
parent package is being presented as the mathematical source.

## Agent contribution

GPT-5 Codex materially contributed to this preparation by:

- auditing the prior Palomar versions and the repository's proved curvature
  boundary;
- identifying the contracted second Bianchi identity as a separate theorem
  family rather than another transport or ODE wrapper;
- designing the explicit multilinear tensor interface and trace-contraction
  definitions in the Challenge surface;
- implementing and compiling the finite contraction proof and its
  divergence-free Einstein-tensor corollary;
- preparing the separate project path, pinned build files, Comparator,
  documentation, and metadata; and
- running Lean compilation and consistency checks on the selected modules.

The agent did not determine mathematical authorship, source priority,
originality, or the decision to publish.  It also did not silently turn the
tensor-level hypotheses into a manifold-level theorem: the selected fields
state exactly which derivative symmetries the contraction proof uses.

## Human authorship and oversight

The recorded authors are Arthur Freitas Ramos, David Barros Hulak, and Ruy J.
G. B. de Queiroz.  The human authors selected the result family, approved the
source relationship and limitations, reviewed the displayed definitions and
hypotheses, and retain responsibility for authorship, attribution, and any
external submission.  Arthur Freitas Ramos is the responsible maintainer.

Lean kernel checking and the pinned Comparator replay establish formal
elaboration and reproducibility; they do not establish novelty or research
priority.  The human review therefore remains the basis for the authorship and
mathematical-origin statements.

## Artifact boundary

`Challenge.lean` imports Mathlib only and exposes the tensor fields, their
symmetry and Bianchi hypotheses, the trace definitions, and the two selected
conclusions with proof holes.  `Solution.lean` independently repeats that
auditable interface and proves the same theorem statements using only the
pinned Mathlib dependency.  The contraction argument is explicit in
`Solution.lean`; neither divergence conclusion is assumed as a hypothesis.

This project has a distinct project path and Comparator identity from the
older `curvature/` surface.  A future Palomar intake for this directory must
be a new submission with a blank `existing_id`; it must not reuse the older
surface's Palomar lineage.
