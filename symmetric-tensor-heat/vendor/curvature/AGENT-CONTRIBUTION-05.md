# Submission 05 contribution and oversight record

This document records preparation of the geometric transport surface in the
public repository `Arthur742Ramos/lean-poincare-formalization-plan`, project
directory `curvature/`. The metadata pins this record to an immutable public
commit containing this document.

## Mathematical source and origin

The mathematical provenance is the classical theory of affine connections and
Riemannian geometry in:

- S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, Vol. I,
  Wiley-Interscience, 1963, especially the chapters on affine connections and
  curvature; and
- J. M. Lee, *Riemannian Manifolds: An Introduction to Curvature*, 2nd ed.,
  Graduate Texts in Mathematics 176, Springer, 2018, especially the treatment
  of pullback metrics and Levi-Civita connections.

The selected statements are standard naturality consequences: a smooth
diffeomorphism transports tangent vectors, affine connections, curvature, and
torsion, and the pullback of a metric-compatible torsion-free connection is
the Levi-Civita connection for the pulled-back metric. This submission is a
formalization/adaptation of that established theory, not an original theorem
and not a first mathematical presentation. The repository source
`PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeTransport` is the Lean
implementation source for the proved Solution declarations; it is not being
offered as the mathematical provenance.

## Agent contribution

GPT-5 Codex materially performed the following preparation work:

- audited the rejected coordinate, affine-ODE, and gauge-reduction surfaces
  against the repository's actual proved theorem boundary;
- identified the fixed-diffeomorphism connection-transport family already
  proved in `GaugeTransport.lean`;
- rebuilt the Mathlib-only Challenge boundary around actual tangent spaces,
  bundled `C^2` self-diffeomorphisms, covariant derivatives, the raw curvature
  commutator, torsion, and explicit metric pullback equations;
- aligned `Solution.lean` with the corresponding proved source theorems;
- updated the Comparator, local verifier, metadata, README, portfolio plan,
  and Palomar preparation record; and
- ran Lean compilation, source-closure, metadata, proof-hole, and Comparator/
  NanoDa checks before submission.

The agent did not decide authorship, source priority, mathematical novelty,
or whether the classical results should be described as original. It did not
claim that this surface proves Ricci-flow PDE local existence, Schauder
estimates, or the Poincare Conjecture.

## Human authorship and oversight

The recorded human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. The human authors selected and approved the theorem
family, author list, classical source relationship, scope limitations, and
submission decision. Arthur Freitas Ramos, as responsible maintainer, reviewed
the exact repository diff and retains responsibility for attribution, release,
and the Palomar submission. Lean kernel elaboration and the pinned
Comparator/NanoDa replay check formal consistency and reproducibility; they do
not establish authorship, priority, or research novelty.

## Artifact boundary

`Challenge.lean` imports only Mathlib. It exposes the formulas for `along`,
the raw curvature commutator, tangent transport, the pulled-back connection,
torsion-free structure, metric compatibility, and the Levi-Civita predicate.
`Solution.lean` imports the repository's proved `GaugeTransport` module and
provides the aligned proofs. The selected declarations therefore have an
auditable statement/formula boundary while the implementation proof remains
traceable to the pinned source module.

The one construction proof obligation in the Challenge is recorded honestly
in `formalization.yaml` as a definition hole; it is not an axiom and does not
appear in `Solution.lean`. The six selected Challenge theorem holes are all
filled by the corresponding source-backed Solution proofs.

## External status

This document records preparation and the submission action only. A successful
Palomar mechanical check, renderability check, editorial review, registration,
and public indexing are separate states and must not be conflated.
