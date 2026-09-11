# Research-interest case

Positive Einstein metrics are the exact shrinking models against which the
scalar-curvature maximum-principle estimate for Ricci flow is calibrated.  For
`Ric(g₀) = λg₀`, the geometric PDE closes to one scalar ODE: the metric shrinks
linearly, while scalar curvature follows the quadratic reaction profile and
blows up at the reciprocal-curvature time.  This is simultaneously a sanity
check on sign conventions, dimensional constants, curvature contractions,
metric scaling, and singular-time normalization.

The selected Lean theorem keeps those interfaces geometric.  Its Challenge
defines the corrected curvature commutator, takes two explicit orthonormal
traces to obtain Ricci and scalar curvature, spells out the Levi--Civita
conditions, and states the Ricci-flow equation through componentwise time
derivatives.  The proof then establishes one coherent certificate:

- the homothetic family solves the actual Ricci-flow equation;
- its scalar curvature equals the sharp quadratic comparison barrier;
- the positive-definite factor set is exactly the half-line before
  `t₀ + 1/(2λ)`; and
- the collapsed endpoint tensor cannot be a Riemannian metric.

The result is deliberately narrower than a general compact-flow comparison
theorem.  The latter, including scalar evolution and maximum-principle
infrastructure, already exists in the independent
`qinz1yang/differential-geometry` development.  The value here is the
fully linked equality benchmark and reusable bridge from an explicit
Mathlib-only geometric statement to the repository's intrinsic Ricci-flow
objects.  It advances the local Poincare formalization roadmap without making
a novelty or priority claim.  Palomar editorial interest remains for editors
to assess.
