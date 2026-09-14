# Agent contribution and human oversight

This document is the contribution record for the Palomar artifact whose
immutable commit contains this file. It is part of the repository so that the
automation disclosure is inspectable alongside the Lean sources and metadata.

## Agent role

GPT-5 Codex performed material proof-engineering work under the direction of
the human author/maintainer. In this submission cycle that work included:

- auditing the existing curvature and Bianchi APIs and the hosted renderability
  and mechanical-verification failures;
- migrating and checking the package at the pinned Lean 4.33/Mathlib boundary;
- drafting and revising the `Challenge.lean` and `Solution.lean` declarations
  and proofs, including the Palomar surface for the first and raw differential
  second Bianchi identities;
- maintaining the exact Challenge/Solution declaration equality needed by the
  Comparator, and updating its theorem surface and verification scripts;
- drafting the source, scope, authorship, and automation metadata and this
  contribution record; and
- running the Lean builds, kernel checks, repository verifier, and independent
  Comparator/NanoDa replay used as evidence for the artifact.

The agent is not an author, does not receive mathematical priority, and does
not independently establish novelty. Existing Mathlib and repository results
remain attributed to their original sources.

## Human role and oversight

The declared human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. The human author team owns the mathematical objective,
authorship, source relationships, research-interest framing, and responsibility
for the final artifact.

For this revision, Arthur Freitas Ramos, as responsible maintainer, directed
the response to review, selected the first/second Bianchi theorem family as the
stronger submission boundary, approved the provenance and non-originality
language, reviewed the generated Lean and metadata changes, and authorized the
repository and submission actions. The repository records David Barros Hulak
and Ruy J. G. B. de Queiroz as coauthors; it does not claim that either
coauthor personally operated the agent. Their coauthorship carries the usual
responsibility for confirming the mathematical content and final public
artifact.

Human review is distinct from automated verification. The Lean kernel checks
the proof terms, while the pinned repository checks and Comparator/NanoDa
replay check compilation, import boundaries, declaration equality, permitted
axioms, and reproducibility. These checks are evidence about formal correctness
and packaging, not substitutes for human mathematical or editorial review.

## Scope and attribution decision

The selected Bianchi identities are standard mathematics. The contribution is
their explicit, kernel-checked formalization for the stated smooth manifold and
covariant-derivative API boundary. The former Palomar wrappers for commutator
skew and Levi-Civita uniqueness are supporting library results only; neither is
claimed as an original discovery or selected as the research-interest boundary
of this artifact.
