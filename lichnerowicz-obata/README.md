# Lichnerowicz--Obata (in progress)

Target: on a closed connected smooth Riemannian manifold of dimension
`n ≥ 2`, with `Ric ≥ (n - 1) K g` and `K > 0`, prove attainment of the first
positive Laplace eigenvalue, its bound `λ₁ ≥ n K`, and equality if and only if
the manifold is globally Riemannian-isometric to the round sphere of radius
`1 / sqrt K`.

**The full target is not proved. This project is not submission-ready.**

## Checked analytic step

`LichnerowiczObata/BochnerBound.lean` proves:

- the dimension-weighted integrated Ricci bound;
- `n K ∫ |grad f|² ≤ ∫ (Δf)²` for every C³ function;
- positive energy for nonconstant C¹ functions on the connected manifold;
- `μ ≥ n K` for every nonconstant C³ eigenfunction `Δf = -μ f`;
- everywhere vanishing of the trace-free Hessian when the integrated bound
  is saturated;
- the genuine Hessian equation `Hess f(v,w) = -K f ⟪v,w⟫` for an extremal
  eigenfunction `Δf = -n K f`.

The Laplacian uses the `div grad` sign convention. Ricci, Hessian, gradient,
and volume are the existing constructed geometric objects. Bochner and Green
identities are proved imports, not extra hypotheses. The intermediate estimates
hold without assuming `K > 0`; positivity is required for the full sphere target.

## Checked spectral step

`CompactEnergy.lean` factors the completed mean-zero Dirichlet energy space
through the actual chart H¹ graph and proves compactness of its L² realization.
`NontrivialEnergy.lean` derives a nonzero element from positive dimension and
smooth separation; no eigenfunction or nonzero test function is assumed.
`CompactSpectral.lean` proves largest-positive-eigenvalue attainment for a
nonzero compact positive symmetric Hilbert-space operator.

`EnergySpectrum.lean` applies this to the actual energy Gram operator. It proves
attainment and minimality of the first positive **variational** eigenvalue, and
existence of a nonzero mean-zero L² eigenfunction satisfying the actual
Laplace--Beltrami eigen-equation against every C² test function.
`ReactionBootstrap.lean` adapts the elliptic induction to `div(A grad u) = F u`,
where only the potential `F` is assumed smooth. `ManifoldReactionJets.lean`
and `SmoothEigenfunction.lean` apply this to the eigen-equation and construct
a global smooth representative satisfying the pointwise geometric equation.

`ClassicalSpectrum.lean` proves attainment and minimality of the first positive
classical smooth eigenvalue, and its sharp lower bound `λ₁ ≥ n K`. These results
no longer assume spectral existence or smoothness of a weak eigenfunction.

## Remaining proof obligations

1. Global Obata rigidity from the Hessian equation: complete geodesics and
   minimizing segments, the polar description with unique extrema, and the
   smooth metric-preserving sphere identification, including both poles.
2. The round-sphere converse, the independently auditable Mathlib-only
   Challenge, and final theorem/axiom/provenance verification.

Do not replace any of these obligations by an assumed analytic or geometric
bridge, and do not call the checked eigenfunction estimate the full theorem.

## Checked rigidity step

`ObataEnergy.lean` differentiates the squared gradient norm using the actual
Levi–Civita connection's metric compatibility. From the Hessian equation it
proves that `|grad f|² + K f²` is constant on a connected manifold. This is a
local-to-global conserved-energy identity, not yet the sphere-isometry theorem.

`ObataExtrema.lean` proves Fermat's theorem for the actual manifold gradient,
obtains extrema by compactness, and shows that a nonconstant Obata function
has maximum `a > 0`, minimum `-a`, and `|grad f|² = K (a² - f²)`.
Its only critical values are `a` and `-a`. Uniqueness of the critical points
and the global sphere isometry remain unproved.

`ObataRadial.lean` constructs the radial candidate
`r = arccos(f/a) / sqrt K`, proves its range and the reconstruction
`f = a cos(sqrt K * r)`, and proves `|grad r| = 1` at every noncritical
point. The theorem derives the needed energy identity from the Obata equation.
It does not assume or yet prove that `r` is geodesic distance.

## Sources and reuse

The classical argument is due to Lichnerowicz and Obata, not a new mathematical
result. The global rigidity reference is M. Obata, *Certain conditions for a
Riemannian manifold to be isometric with a sphere*, J. Math. Soc. Japan 14
(1962), 333--340, especially Theorem A and section 2:
<https://doi.org/10.2969/jmsj/01430333>.

The local path dependency `../almost-schur` inherits the existing geometric
and analytic formalization from this repository at commit
`3faf25aefc27842a77c37ca178e8a40a20bb20c7`. Its original provenance and contributor
notices remain authoritative. This project adds the sharp positive-Ricci
eigenfunction estimate, its equality-to-Hessian argument, spectral attainment,
and weak-eigenfunction regularity. The adapted bootstrap and chart assembly
retain explicit immutable source attribution in their module headers. Structured
submission metadata must disclose all inherited formalizations before any
intake; no intake or registration has been requested by this project.

## Build

Lean `v4.33.0`, Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

```sh
lake update
lake build
lake env lean Audit.lean
```

The audit prints transitive axioms for the principal analytic and spectral statements.
