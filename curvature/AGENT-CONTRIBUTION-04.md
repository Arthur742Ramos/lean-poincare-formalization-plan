# Submission 04 contribution and oversight record

This document records the preparation of the time-dependent Palomar surface
in the public repository
`Arthur742Ramos/lean-poincare-formalization-plan`, branch
`dev/point4-campaign`, project directory `curvature/`. The final
`formalization.yaml` pins this file to the immutable public commit containing
this record.

## Mathematical source and origin

The selected declarations are sourced from the repository module
`PoincareCurvature/Geometry/Manifold/VectorBundle/CovariantDerivative/TimeDependent.lean`.
That module defines an explicit `ℝ`-indexed family interface and proves the
selected statements by applying the static Levi–Civita, regularity, curvature,
Ricci, and scalar-curvature results at each time slice.

The underlying mathematics is classical differential geometry. The existence,
uniqueness, and curvature-contraction ingredients are the standard theory of
the Levi–Civita connection and Riemann curvature, represented in the metadata
by Kobayashi–Nomizu and by the Mathlib infrastructure on which the package
builds. Submission 04 is therefore an explicit time-indexed formalization and
adaptation of that source-based theorem family. It is not claimed as an
original theorem, independent discovery, or priority result. The selected
surface also deliberately stops short of time differentiability in the time
variable, Ricci-flow existence, and parabolic estimates.

## Agent contribution

GPT-5 Codex materially performed the following preparation work:

- audited the time-dependent source module and identified the coherent
  existence, regularity, background-independence, Ricci-symmetry, and
  contraction-invariance boundary;
- drafted the Submission 04 `Challenge.lean` and `Solution.lean` surfaces,
  including exact declaration alignment and the three Comparator definition
  holes;
- configured the eight selected theorem names and three definition names,
  updated the local Palomar verifier, and ran Lean/package checks and the
  independent Comparator/NanoDa replay;
- prepared this source/attribution/oversight record and the associated
  `PALOMAR.md`, metadata, and portfolio-plan entries; and
- preserved the accepted earlier artifacts while preparing and pushing the
  next public commit.

The agent did not decide authorship, source priority, or mathematical novelty.
It did not turn the time-indexed family into a claim about a time-dependent
PDE or Ricci-flow solution.

## Human authorship and oversight

The recorded human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. Human authors selected and approved the theorem
family, author list, source relationship, scope limits, and public artifact.
The responsible maintainer reviewed the source selection and repository diff,
authorized the public push, and retains responsibility for any Palomar
submission or later publication action. Human oversight is complemented by
Lean kernel elaboration, the repository's no-axiom/source audit, and the
independent pinned Comparator/NanoDa replay; those checks verify formal
consistency and reproducibility, not authorship or novelty.

## Artifact boundary

`Challenge.lean` imports only Mathlib and has eleven deliberate holes: eight
ordinary theorem statement holes and three definition holes for the
time-dependent Levi–Civita correction, Ricci curvature, and scalar curvature.
`Solution.lean` imports the actual PoincareCurvature source module and supplies
the eight proved wrappers. The exact final public commit and the external
Palomar status must be recorded separately; local preparation is not itself a
submission or an acceptance claim.
