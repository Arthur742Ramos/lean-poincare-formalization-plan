# Submission 04 contribution and oversight record

This document records preparation of the corrected Palomar surface in the
public repository `Arthur742Ramos/lean-poincare-formalization-plan`, branch
`dev/point4-campaign`, project directory `curvature/`. The metadata pins this
record to an immutable public commit containing the document.

## Mathematical source and origin

The geometric motivation is Dennis M. DeTurck's Ricci–DeTurck gauge in
“Deforming metrics in the direction of their Ricci tensors,” *Journal of
Differential Geometry* 18 (1983), DOI `10.4310/jdg/1214509286`. It is cited as
background for the frozen-chart interpretation; this submission does not
claim to formalize DeTurck's full nonlinear parabolic theorem.

The selected theorem family is the standard operator-exponential treatment of
the affine autonomous equation `y' = L y + b` on a complete normed real vector
space. Its mathematical source is Einar Hille and Ralph S. Phillips,
*Functional Analysis and Semi-Groups*, AMS Colloquium Publications 31. The
seven declarations are a formalization/adaptation of that standard result
family using the block-operator augmentation; they are not claimed as original
proofs or as a first presentation. The repository's parabolic and coordinate
modules are broader supporting library material and are not part of this
Palomar selection.

## Agent contribution

GPT-5 Codex materially performed the following preparation work:

- audited the failed parabolic-only selection and traced the Palomar review
  defects in provenance, README scope, and research-interest evidence;
- selected the stronger frozen affine evolution boundary and aligned its
  Challenge/Solution statements with the existing proof-bearing development;
- authored the corrected Challenge/Solution declarations and updated the
  Comparator surface, repository verifier, metadata, README, Palomar record,
  and this contribution/oversight record;
- removed the auxiliary coordinate target from the selected surface after the
  independent Comparator exposed a definition-target mismatch, preserving the
  stronger affine family as the auditable result; and
- ran Lean 4.33 builds, source-closure checks, metadata checks, and the
  independent Comparator/NanoDa replay needed for reproducible packaging.

The agent did not decide authorship, source priority, or mathematical novelty.
It did not convert the selected analytic core into a claim about a full
time-dependent Ricci-flow PDE, Schauder estimates, or first discovery.

## Human authorship and oversight

The recorded human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. Human authors selected and approved the author list,
external source relationships, corrected theorem family, scope limits, and
public artifact. The responsible maintainer reviewed the mathematical
boundary and exact repository diff and retains responsibility for publication
and the Palomar submission. Human oversight covers attribution, the decision
to replace the weak selection, and authorization of the public push and new
submission. Lean kernel elaboration and the independent pinned
Comparator/NanoDa replay check formal consistency and reproducibility, not
authorship or novelty.

## Artifact boundary

`Challenge.lean` imports only Mathlib, exposes actual bodies for the block
operator and operator-exponential solution, and has seven deliberate theorem
holes with no definition holes. `Solution.lean` imports the checked
autonomous operator-exponential development and supplies seven proved
wrappers. The final public commit and external Palomar status are recorded
separately; local preparation is not itself an acceptance or registration
claim.
