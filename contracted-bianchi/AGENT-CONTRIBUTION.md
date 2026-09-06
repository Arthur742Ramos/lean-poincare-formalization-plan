# Agent contribution and human oversight

## Authorship and oversight evidence

The authors named at the user's direction are Arthur Freitas Ramos,
David Barros Hulak, and Ruy J. G. B. de Queiroz. Arthur Freitas Ramos is the
responsible maintainer. In this conversation Arthur selected the
contracted-Bianchi target, requested the authorship list, supplied reviewer
objections, and authorized repair of the submission.

There is no recorded independent line-by-line proof review by each named
author. Do not infer that all authors inspected every definition or verified
the completed replacement. Lean/Comparator checking checks formal proofs,
not author consent, mathematical originality, or editorial suitability.

## Agent work

GPT-5 Codex prepared the earlier independent-tensor abstraction, metadata,
and Comparator. That abstraction compiled but did not connect its derivative
to the metric connection.

GPT-6 Codex audited those shortcomings and implemented the replacement:
regularity of the curvature section; first-pair skew symmetry of its
covariant derivative; differentiation of curvature skew-adjointness using
metric compatibility; differentiation of the first Bianchi identity;
derivative pair interchange; and contraction of the actual second Bianchi
identity for a torsion-free connection. It also prepared the Challenge and
Solution wrappers, vendored dependency closure, source mapping, disclosure,
metadata, and verification.

The agent removed the separate Einstein-divergence claim because a
trace/differentiation bridge for that field is not part of this result.
Human oversight consists of the recorded target selection, review feedback,
and requested changes; no additional human audit is invented here.

For the renderability repair, GPT-6 Codex removed the candidate-local
`PoincareCurvature` import from `Challenge.lean`, exposed the corrected
commutator and anchored smooth-extension hypotheses directly in the Challenge,
and added the corresponding generic section-level bridge theorem to the
Solution-side dependency closure. The canonical-style direct Lean compile and
Comparator replay were rerun after that change. This repair preserves the
pointwise orthonormal contraction while making the Challenge compile from the
allowlisted Mathlib/core-facing search path.

## Origin and implementation provenance

This is a formal adaptation of the classical contraction identity, not
original mathematics. The directly checked source is Sean M. Carroll,
*Lecture Notes on General Relativity*, section 3, equations (3.87)–(3.94),
https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll3.html.
Besse's *Einstein Manifolds* is background. The mathematical provenance is
distinct from the implementation provenance in VENDORED-SOURCES.md.

The dependency closure comes from the repository's committed curvature
library, with the new bridge included explicitly. Existing unrelated
uncommitted source changes are not part of that copied closure.
