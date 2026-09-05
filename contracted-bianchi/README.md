# Double-contracted second Bianchi identity

This directory is a standalone Lean project. Its selected result is
`ContractedBianchi.contractedSecondBianchi`: the orthonormal double contraction
of the **actual curvature derivative of a torsion-free metric-compatible
tangent connection** on a finite-dimensional smooth Hausdorff real manifold.
The Challenge makes the smooth extension used to evaluate tangent vectors an
explicit argument, so the selected formula is auditable without importing the
candidate's local curvature library.

Write
```text
D_ext(p,a,b,c,d;x) = g(∇P(R(A,B)C) − R(∇P A,B)C
                              − R(A,∇P B)C − R(A,B)∇P C, D),
where `P,A,B,C,D` are the supplied smooth extensions at `x` and are anchored
by `P(x)=p`, ..., `D(x)=d`.
```
For an orthonormal basis b at x, the selected conclusion is
```text
Σᵢ Σₖ D(w,bₖ,bᵢ,bᵢ,bₖ) = 2 Σᵢ Σₖ D(bᵢ,bₖ,bᵢ,w,bₖ).
```

The derivative is constructed from the supplied connection. Its first-pair
skew symmetry, last-pair skew symmetry, pair interchange, and differentiated
first Bianchi identity are proved. The cyclic second Bianchi identity follows
from torsion-freeness. None of these equations is a premise of the selected
theorem, and there is no independent curvature/derivative tensor parameter.
The proof side instantiates the explicit extension argument with the
repository's canonical smooth extension.

## Exact scope

The statement exposes the smoothness and bundle assumptions: a smooth
Hausdorff manifold, finite-dimensional complete real model space, tangent
bundle smoothness through order three, connection smoothness through order
two, and Riemannian bundle smoothness through order two (with the order-one
instance also explicit). At the selected point it requires a supplied
extension for every tangent vector, anchored at that point and of class
`C^3`. It requires neither compactness nor sigma-compactness.

This is the connection-curvature contraction form of the classical identity.
It does **not** separately identify the sums with derivatives of the
repository's Ricci or scalar-curvature fields, prove extension independence
of the displayed derivative as a bundled tensor, or state an Einstein-tensor
divergence theorem. The previous abstract tensor selection and its advertised
Einstein-divergence corollary are superseded.

## Mathematical provenance

The result adapts the classical twice-contracted Bianchi calculation in
Sean M. Carroll, *Lecture Notes on General Relativity*, section 3,
equations (3.87)–(3.94):
[accessible source](https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll3.html).
The current statement uses a positive-definite Riemannian metric and an explicit
orthonormal contraction. Carroll's subsequent Einstein-tensor reformulation
is motivation, not another selected theorem. Besse's *Einstein Manifolds*
(DOI 10.1007/978-3-540-74311-8) is the previously cited background source.
No mathematical originality or first-formalization claim is made.

The research context is differential curvature constraints in Riemannian
geometry and the contracted Bianchi identity used in geometric field
equations. The submitted mathematical content includes deriving the
derivative symmetries from a connection and its metric Leibniz rule, rather
than assuming a tensor satisfying all the required identities. This context
does not guarantee Palomar's editorial assessment.

## Reproducibility and status

Run `lake build` from this directory. Lean 4.33.0 and Mathlib are pinned.
`Challenge.lean` has one intentional proof hole; `Solution.lean` proves it.
The Comparator includes the definitions of the connection-derived curvature
derivative and its raw commutator. The Challenge imports only Mathlib/core-facing
manifold interfaces. The Solution imports the committed local dependency
closure to instantiate the explicit extension interface; it has no path
dependency on the parent project.
See [VENDORED-SOURCES.md](VENDORED-SOURCES.md) and
[AGENT-CONTRIBUTION.md](AGENT-CONTRIBUTION.md).

An earlier abstract version reached intake but failed mechanical verification.
This replacement is unregistered. Any fresh intake must leave `existing_id`
blank; it must not update a different registered result.
