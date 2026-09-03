# Submission 04 contribution and oversight record

This document records preparation of the corrected Palomar surface in the
public repository `Arthur742Ramos/lean-poincare-formalization-plan`, project
directory `curvature/`. The metadata pins this record to an immutable public
commit containing this document.

## Mathematical source and origin

The mathematical source relationship is to Dennis M. DeTurck's
“Deforming metrics in the direction of their Ricci tensors,” *Journal of
Differential Geometry* 18 (1983), DOI `10.4310/jdg/1214509286`. The paper is
the source of the Ricci–DeTurck gauge idea and the pullback reduction from the
gauge-fixed equation to Ricci flow.

The selected Lean result is an adaptation and formalized coordinate model of
that mechanism, not a claim to reproduce DeTurck's full nonlinear parabolic
short-time theorem. Its own formulas define continuous bilinear metric forms
and the Ricci tensor as metric composition with a specified Ricci
endomorphism. The derivative theorem is independently proved from Fréchet,
gauge, and tangent-transport derivative hypotheses. The selected metric-cone
existence and uniqueness declarations use the explicitly defined Ricci vector
field, while the finite-dimensional scalar-trace transport remains proved
supporting code rather than a selected standalone claim. These results are
standard consequences/adaptations in the stated model, not an original
theorem or a first mathematical presentation.

## Agent contribution

GPT-5 Codex materially performed the following preparation work:

- audited the Palomar rejection and traced each complaint to the selected
  declarations, README, Comparator, and verifier;
- redesigned the Challenge boundary so the metric, Ricci tensor, scalar trace,
  derivative data, and positive-definite metric cone are explicit and typed;
- removed the theorem whose hypothesis was exactly its advertised derivative
  conclusion and replaced it with a chain-rule theorem from independent data;
- implemented the corresponding proof-bearing Solution declarations,
  including Ricci-tensor transport, trace transport, and metric-cone ODE
  existence/uniqueness;
- synchronized the Comparator, local verifier, README, Palomar record,
  metadata, and this oversight record; and
- ran Lean builds, source-closure checks, metadata checks, and the independent
  Comparator/NanoDa replay needed for reproducible packaging.

The agent did not decide authorship, source priority, or mathematical
novelty. It did not claim that the coordinate model proves the general
compact-manifold Ricci-flow PDE, Schauder estimates, or short-time existence.

## Human authorship and oversight

The recorded human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. The human authors selected and approved the author
list, external source relationship, theorem boundary, scope limitations, and
publication decision. Arthur Freitas Ramos, as responsible maintainer,
reviewed the mathematical boundary and exact repository diff and retains
responsibility for attribution, release, and the Palomar submission. Lean
kernel elaboration and the pinned Comparator/NanoDa replay check formal
consistency and reproducibility; they do not establish authorship or novelty.

## Artifact boundary

`Challenge.lean` imports only Mathlib and exposes the exact formulas and
hypotheses compared by Palomar. `Solution.lean` proves the same declarations
without importing the project-specific Ricci-flow source, so the compared
proofs do not hide an assumption in a local helper module. The larger
manifold-level source package remains implementation context and is described
as such in the README; it is not silently substituted for the Challenge
surface.

## External status

This document records local preparation only. A Palomar submission requires a
fresh action for the final public commit, with the exact public repository,
full SHA, project directory, Comparator path, metadata path, and authorization
relationship verified at submission time. Local checks do not imply hosted
mechanical verification, renderability, editorial review, registration, or
public indexing.
