# Agent contribution and human oversight — Submission 02

This document records the automation and human-oversight roles for the
immutable Palomar artifact selecting the raw curvature tensoriality and metric
skew-adjointness theorems. It is kept beside the Challenge/Solution surface so
that the disclosure is inspectable with the exact repository snapshot.

## Agent role

GPT-5 Codex performed material proof-engineering work under the direction of
the human author/maintainer. In this submission cycle the agent:

- audited the accepted Submission 01 boundary and the next available
  curvature APIs;
- selected and drafted the new Challenge/Solution statement boundary for
  pointwise scalar tensoriality in the left, middle, and bundle-section slots;
- added the metric-compatibility curvature skew-adjointness statement;
- aligned the Challenge vocabulary with the implementation's public
  covariant-derivative and raw-curvature declarations;
- updated the Comparator configuration, repository verifier, metadata, and
  submission documentation; and
- ran the Lean builds, axiom checks, repository checks, and independent
  Comparator/NanoDa replay used as evidence for the artifact.

The agent is not an author, does not receive mathematical priority, and does
not independently establish novelty. The standard differential-geometric
identities and the existing implementation remain attributed to their
original sources and repository authors.

## Human role and oversight

The declared human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. The human author team owns the mathematical
objective, authorship, source relationships, research-interest framing, and
responsibility for the final artifact.

Arthur Freitas Ramos, as responsible maintainer, directed the move to the
next submission, approved the tensoriality/skew-adjointness boundary and its
non-originality language, reviewed the generated Lean and metadata changes,
and authorizes any later repository or Palomar action. The repository records
David Barros Hulak and Ruy J. G. B. de Queiroz as coauthors; it does not claim
that either coauthor personally operated the agent. Their coauthorship carries
the usual responsibility for confirming the mathematical content and final
public artifact.

Human review is distinct from automated verification. The Lean kernel checks
the proof terms, while the pinned repository checks and Comparator/NanoDa
replay check compilation, import boundaries, declaration equality, permitted
axioms, and reproducibility. Those checks are evidence about formal
correctness and packaging, not substitutes for human mathematical or editorial
review.

## Scope and attribution decision

The selected identities are standard consequences of the covariant-derivative
definition of curvature and metric compatibility. The contribution claimed
here is their explicit kernel-checked formalization at the stated Mathlib
manifold/vector-bundle API boundary. No new mathematical discovery,
exclusive priority, or independent novelty claim is made.
