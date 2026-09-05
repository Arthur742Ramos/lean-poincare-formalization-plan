# Agent contribution and human oversight — Submission 03

This document records the automation and human-oversight roles for the
Palomar artifact selecting the static Levi–Civita and curvature-invariant
theorem family. It is kept beside the Challenge/Solution surface so that the
disclosure can be inspected with the exact repository snapshot.

## Agent role

GPT-5 Codex performed material proof-engineering work under the direction of
the human author/maintainer. In this submission cycle the agent:

- preserved and audited the accepted Submission 02 baseline and the next
  available static Riemannian APIs;
- selected and drafted the Submission 03 Challenge/Solution boundary for
  Levi–Civita existence, curvature-tensor independence, Ricci symmetry, and
  Ricci/scalar-curvature invariance;
- aligned the five theorem statements with the source declarations in the
  package's Levi–Civita, curvature-tensor, and contraction modules;
- exposed the exact source types of the canonical bundled curvature tensor,
  Ricci-curvature, and scalar-curvature definitions as three explicit
  Comparator definition holes, while keeping the actual constructions in the
  proved package;
- updated the Comparator configuration, repository verifier, metadata,
  portfolio plan, and Palomar intake documentation; and
- ran Lean 4.33 elaboration/builds, repository checks, axiom checks, and the
  independent pinned Comparator/NanoDa replay used as evidence for the
  artifact.

The agent did not determine authorship, source priority, or mathematical
novelty. The selected theorem family is standard classical Riemannian
geometry; the repository's source modules contain the formal constructions and
proofs used by `Solution.lean`.

## Human role and oversight

The declared human authors are Arthur Freitas Ramos, David Barros Hulak, and
Ruy J. G. B. de Queiroz. The human author team owns the mathematical objective,
authorship, source relationships, research-interest framing, and
responsibility for the final artifact.

Arthur Freitas Ramos, as responsible maintainer, directed the move to
Submission 03, approved the stronger static Riemannian theorem boundary and
its source-based non-originality language, reviewed the generated Lean and
metadata changes, and authorizes any later repository or Palomar action. The
repository records David Barros Hulak and Ruy J. G. B. de Queiroz as
coauthors; it does not claim that either coauthor personally operated the
agent. Their coauthorship carries the usual responsibility for confirming the
mathematical content and final public artifact.

Human review is distinct from automated verification. The human review basis
is inspection of the source theorem declarations, the Challenge/Solution
interface, the metadata and attribution record, and the final repository
diff. The Lean kernel checks the proof terms, while the pinned repository
checks and Comparator/NanoDa replay check compilation, import boundaries,
declaration equality, permitted axioms, and reproducibility. Those checks are
evidence about formal correctness and packaging, not substitutes for human
mathematical or editorial review.

## Scope, source relationship, and definition holes

The selected existence, curvature-independence, Ricci-symmetry, and
trace-invariance results are standard consequences of the fundamental theorem
of Riemannian geometry and the usual curvature contraction identities. The
submission claims an explicit kernel-checked Lean formalization/adaptation at
the stated Mathlib manifold/vector-bundle API boundary, not a new mathematical
discovery or exclusive priority.

`Challenge.lean` contains five ordinary theorem statement holes and three
explicit definition holes. The latter are the public types of
`CovariantDerivative.curvatureTensor`, `CovariantDerivative.ricciCurvature`,
and `CovariantDerivative.scalarCurvature`; `Solution.lean` imports and uses
the actual definitions from the checked `PoincareCurvature` source package.
The Comparator configuration lists those three names in `definition_names`, so
their bodies may differ between statement and solution while their public
types and safety remain checked. This mechanism is disclosed rather than
counted as a proved theorem.
