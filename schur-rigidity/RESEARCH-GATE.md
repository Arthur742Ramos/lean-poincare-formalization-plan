# Mathematical research gate

Status: unresolved. This is a development assessment, not a reproduction of
any private review, a claim of novelty, or a clearance to submit.

The four selected theorems are geometric contracted Bianchi, Einstein
divergence, Schur constancy, and three-dimensional Einstein constant-curvature
rigidity. They are classical identities and consequences. The newly proved
Lean differentiation bridges improve the formal library but do not by
themselves establish a distinct mathematical extension. No amount of receipt
repair establishes that missing mathematical contribution.

## Authorized research direction; implementation not yet complete

The maintainer has authorized pursuing almost-Schur, starting with feasibility.
See [the completed initial audit](ALMOST-SCHUR-AUDIT.md) for source mapping,
dependency evidence, semantic pitfalls and ordered implementation gates.

De Lellis and Topping's *Almost-Schur lemma*, Theorem 1.1, gives a quantitative
extension: on a closed connected Riemannian manifold of dimension n >= 3 with
nonnegative Ricci curvature, scalar-curvature variance is bounded by
`4*n*(n-1)/(n-2)^2` times the squared L2 norm of traceless Ricci, with equality
exactly in the Einstein case.

Primary source: https://arxiv.org/abs/1003.3527v2
Published paper: https://doi.org/10.1007/s00526-011-0413-z

This is an existing research theorem, not an original result of this project.
It is a candidate for a substantive source-based formalization, not a promise
that a registry will find a future artifact eligible.

## Missing proof obligations

The present selected package does not establish this quantitative theorem.
A genuine implementation must supply Riemannian volume and integration,
mean-zero Poisson solvability with regularity, integration by parts, the
integrated Bochner/Hessian estimate, the sharp quantitative inequality, and
the equality-case argument. These cannot be supplied as hypotheses replacing
the mathematical work. Availability of these dependencies in the wider
repository and pinned Mathlib still needs a dedicated feasibility audit.

Before changing the selected result, discharge the audit's implementation
gates. Map the exact source theorem and all hypotheses, audit prior
formalizations and attribution, prove the geometric and analytic obligations,
and independently verify the resulting immutable Challenge/Solution boundary.
Do not replace the current Comparator with an unproved or conditional stand-in.
