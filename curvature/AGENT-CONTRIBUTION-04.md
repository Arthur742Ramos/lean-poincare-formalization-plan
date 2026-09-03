# Submission 04 contribution and oversight record

This document records preparation of the corrected Palomar surface in the
public repository `Arthur742Ramos/lean-poincare-formalization-plan`, project
directory `curvature/`. The metadata pins this record to an immutable public
commit containing the document.

## Mathematical source and origin

The mathematical motivation is Dennis M. DeTurck's Ricci-DeTurck gauge in
“Deforming metrics in the direction of their Ricci tensors,” *Journal of
Differential Geometry* 18 (1983), DOI `10.4310/jdg/1214509286`.

The selected surface formalizes the gauge pullback, source-equation
cancellation, initial-time anchoring, intrinsic Ricci-flow consequence, and
finite-dimensional curvature trace transport in an explicit fixed-tangent-
model setting. It does not claim DeTurck's full nonlinear parabolic theorem,
the general compact-manifold Ricci-flow existence theorem, or an original
mathematical discovery.

## Agent contribution

GPT-5 Codex materially performed the following preparation work:

- audited the prior Palomar review and identified that the frozen affine
  Banach-space ODE surface did not meet the research-interest gate;
- selected the geometric Ricci-DeTurck gauge-reduction boundary and wrote the
  compact Challenge/Solution statement surface;
- added the proof-bearing `ResearchTheorems` source module that exposes the
  concrete gauge-reduction and curvature-transport capstone;
- updated the Comparator surface, repository verifier, metadata, README,
  Palomar record, and this contribution/oversight record; and
- ran Lean builds, source-closure checks, metadata checks, and the independent
  Comparator/NanoDa replay needed for reproducible packaging.

The agent did not decide authorship, source priority, or mathematical novelty.
It did not convert the selected result into a claim about the full
time-dependent Ricci-flow PDE, Schauder estimates, or short-time existence.

## Human authorship and oversight

The recorded human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. Human authors selected and approved the author list,
external source relationship, theorem boundary, scope limits, and public
artifact. The responsible maintainer reviewed the mathematical boundary and
exact repository diff and retains responsibility for publication and the
Palomar submission. Lean kernel elaboration and the independent pinned
Comparator/NanoDa replay check formal consistency and reproducibility, not
authorship or novelty.

## Artifact boundary

`Challenge.lean` imports only Mathlib and states the pullback and
Ricci-DeTurck cancellation theorem family in a small fixed-tangent-model
surface. `Solution.lean` proves the seven compared declarations and imports
the checked Ricci-flow gauge-transport development, including
`ResearchTheorems.lean`. The selected statements are intentionally an
auditable abstraction of the larger geometric package; the source repository
does not claim that this submission closes arbitrary compact-manifold local
existence.

## External status

This document records local preparation only. A Palomar submission requires a
fresh action for the final public commit, with the exact public repository,
full SHA, project directory, Comparator path, metadata path, and authorization
relationship verified at submission time. Local checks do not imply hosted
mechanical verification, renderability, editorial review, registration, or
public indexing.
