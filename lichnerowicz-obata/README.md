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

1. Global Obata rigidity from the Hessian equation: construct the polar map,
   identify its angular metric with the unit round metric, and prove the
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
is supplied by `ObataUniquePoles.lean`; the global sphere isometry remains unproved.

`ObataRadial.lean` constructs the radial candidate
`r = arccos(f/a) / sqrt K`, proves its range and the reconstruction
`f = a cos(sqrt K * r)`, and proves `|grad r| = 1` at every noncritical
point. The theorem derives the needed energy identity from the Obata equation.
It does not itself identify `r` with distance; `RadialDistance.lean` proves that
identification without an assumed minimizing property.

`EikonalConnection.lean` proves radial regularity between the extrema and
derives `∇_(grad r) grad r = 0` from the unit-gradient identity and symmetry
of the actual Levi–Civita Hessian. The resulting radial gradient is unit and
autoparallel on this open region; global flow existence, minimizing properties,
and the polar-coordinate isometry are not supplied by this pointwise result.

`RadialCurves.lean` constructs actual local integral curves of the radial
gradient at every regular point and proves the exact local parameterization
`r(γ(t)) = r(γ(0)) + t`. Its scalar chain rule is adapted from the inherited
Almost-Schur proof with immutable attribution in the module header. Full-interval
existence and endpoint convergence are supplied by the later modules below.

`UniformChartODE.lean` and `UniformManifoldODE.lean` prove uniform local
existence in a chart, a finite-cover time bound on compact manifolds, and
completeness of C1 vector fields on compact boundaryless Hausdorff manifolds.
`GlobalGradientCurves.lean` applies this to the original Obata gradient:
through every point there is a curve defined for all real times, and its
scalar value satisfies `d(f ∘ γ)/dt = K (a² - (f ∘ γ)²)`.
These are curves of `grad f`, not yet a complete radial coordinate system;
the behavior at the poles and the global isometry still require proof.

`ObataScalarLimits.lean` proves monotonicity, convergence of the scalar values
to `a` and `-a` in opposite time directions, and crossing of every intermediate
level. `GlobalGradientCurves.lean` applies these results to the constructed
Obata curves starting at regular points. Convergence of scalar values is not
yet convergence of the manifold-valued curves to unique poles.

`RegularGradientCurves.lean` uses global ODE uniqueness to rule out reaching
a critical point at finite time from a regular initial point. The function
value is strictly increasing along such a curve, and every intermediate
level has a unique crossing time. The following modules provide the radial
reparameterization; the global metric/isometry argument remains open.

`ObataClock.lean` proves the explicit logarithmic clock and its inverse-level
identity. `RadialParameterization.lean` uses it to construct, through every
regular point, a differentiable curve on the full open radial interval with
`r(η(s)) = s`. `RadialVelocity.lean` proves that the same construction follows
the actual radial gradient and has intrinsic velocity of norm one over the
full open interval.

`UniformManifoldODE.lean` also proves C1 regularity of integral curves of C1
fields. `UnitCurveDistance.lean` uses this to bound the canonical Riemannian
extended distance by elapsed time along the actual unit radial gradient flow.
`RadialEndpoints.lean` equips the compact manifold with the canonical
Riemannian extended metric (preserving its original topology), proves Cauchy
convergence at both radial endpoints, and identifies their eigenfunction
values as `a` and `-a`. Its combined theorem constructs such a full unit-speed
curve through every regular point directly from the Obata equation. It does
not itself prove that different curves have the same poles; this is now proved
by `ObataUniquePoles.lean`. The global round-sphere isometry remains unproved.

`RadialEndpointDistance.lean` passes the intrinsic Lipschitz estimates to the
endpoint limits. Every regular point has a maximum and minimum endpoint at
distance at most `r` and `pi / sqrt K - r`, respectively. These are proved
upper bounds, not an assertion that the radial curves minimize distance.
The matching lower bounds and radial minimality are proved subsequently in
`RadialDistance.lean`.

`ObataCriticalIsolation.lean` derives the ordinary derivative of the coordinate
gradient at a critical point from the covariant Hessian equation. It is the
nonzero scalar `-K * f(x)` times the identity. The inverse function theorem
then isolates each critical point; continuity and compactness prove that the
critical set is finite. Uniqueness of both extrema is proved below.

`ContinuousGlobalFlow.lean` proves joint continuous dependence on initial
point and time for complete C1 flows on compact manifolds. It uses the retained
joint continuity of the local chart flow, uniqueness, a compactness-based
uniform time interval, and iteration. `RadialFlowFamily.lean` applies this to
the actual gradient and the explicit clock, giving one jointly continuous
family of full unit radial curves through every regular point, with extremal
endpoint limits. Independence of those endpoints from the starting point
is established by the connectedness argument below.

`ContinuousPoleMaps.lean` proves uniform convergence of radial slices to
their endpoints using the intrinsic distance bounds. It constructs continuous
maximum and minimum endpoint maps on the regular region, retaining both
extremal values and the distance bounds.

`DenseRegionConnected.lean` and `PuncturedManifoldConnected.lean` prove that
removing a finite set from a connected boundaryless manifold of dimension at
least two leaves a dense preconnected region. `ObataRegularConnected.lean`
identifies the regular region with the complement of the finite critical set.
`ObataUniquePoles.lean` consequently proves constancy of both continuous endpoint
maps, uniqueness of the maximum and minimum, and radial distance upper bounds
at every point by density. It does not assume pole uniqueness or distance
minimality. The global metric-preserving identification with a sphere is still
required.

`ScalarDistanceBound.lean` proves that a C1 scalar function with gradient norm
at most one contracts intrinsic distances, directly from the infimum over C1
path lengths. `RegularizedRadial.lean` applies this to the enlarged-amplitude
arccosine coordinates and passes to the original amplitude by continuity.
This proves global nonexpansion even at both nonsmooth radial endpoints.
`RadialDistance.lean` then identifies the radial and complementary coordinates
with the exact distances to the two poles and proves that radially parameterized
gradient curves realize distance on every subsegment.

`HessianChainRule.lean` derives the scalar covariant chain rule from the actual
connection's Leibniz rule. `RadialShapeOperator.lean` applies the cosine
reconstruction to prove the full radial Hessian and shape operator, with
factor `sqrt K * cos(sqrt K * r) / sin(sqrt K * r)`. Thus directions tangent
to a radial level have exactly the spherical infinitesimal scaling.
`AngularMetricEvolution.lean` uses torsion freeness and metric compatibility
to derive and integrate the metric evolution for commuting angular fields:
their inner product divided by `sin(sqrt K * r)^2` is constant along a radial
curve. This is conditional on the supplied differentiable, commuting angular
fields; constructing them as polar coordinate directions and identifying the
remaining angular metric with the round metric are not yet proved. The smooth
round-sphere isometry and its extension over the poles remain unproved.

To construct differentiable radial transport, `DifferentiableFixedPoint.lean`
proves strict differentiability and higher regularity of a continuous selection
of fixed points from the actual operator's derivative and smoothness.
`ContinuousMapCalculus.lean` proves smooth superposition on compact-domain
path spaces, deriving a uniform derivative remainder by compactness and the
mean-value inequality. `PathPrimitive.lean` constructs integration on unit
paths as a bounded linear operator of norm at most one.
`SmoothPicardOperator.lean` combines them for the scaled Picard equation
`alpha(s) = x + tau * integral(0..s, v(alpha(t)))`: any continuous local
solution inherits the vector field's finite smoothness at time zero. This
does not yet establish differentiable dependence for the previously constructed
manifold flow: its ODE curves must be assembled into these continuous path-space
solutions, localized in charts, and transported to nonzero times.

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

`ScaledFlowPaths` constructs continuous unit-interval paths from a continuous
local ODE flow, derives their Picard equation by the fundamental theorem of
calculus, and proves finite-order smooth path dependence at zero elapsed time
for globally smooth vector fields; endpoint evaluation recovers smoothness of
the actual flow. `LocalVectorFieldExtension` constructs a smooth cutoff
extension agreeing near the initial point. `SmoothLocalFlow` removes the
global-field hypothesis and constructs a jointly finite-order smooth flow on
a product neighborhood. `SmoothManifoldFlow` lifts this result to smooth
boundaryless manifolds whose model space admits smooth bump functions.
`SmoothGlobalFlow` uses uniqueness, compactness, and the flow composition law
to prove joint smooth dependence for complete flows, including infinite
smoothness. `SmoothRadialFlow` constructs the smooth complete intrinsic
gradient flow and proves smoothness of its explicit radial time change on
the regular region. Constructing the angular variations and proving the
global round-sphere isometry remain unfinished.
The constructed smooth radial family now simultaneously satisfies the radial
ODE, unit-speed and radial-coordinate identities, extremal endpoint limits,
and a reset identity identifying curves started at intermediate points.
`RadialProduct` uses these identities to construct a homeomorphism from the
regular region to any one radial level times the full open radial interval.
This is a topological product theorem, not yet a round-metric identification.
`RadialVariation` differentiates the attained-level and reset identities:
the actual initial-point derivatives are orthogonal to the radial gradient
and satisfy the tangent-transport composition law. Metric evolution for these
variations and normalization at a pole remain to be established.
Differentiating the starting-point identity also gives the spatial/time
derivative splitting. Transport at the starting level fixes angular vectors,
and transport to any interior level has trivial kernel on angular vectors.
`FlowVariationEquation` derives the linearized ODE for initial-point
derivatives of a jointly C2 Euclidean flow from its actual ODE and symmetry
of second derivatives. Connecting this equation to the manifold metric
evolution remains a separate step.
`CoordinateMetricVariation` derives the chart derivative of the actual metric
paired with arbitrary fixed coordinate vectors from metric compatibility.
The varying-vector terms still need to be combined with the flow variational ODE.
The fixed-vector derivative is also expressed through the actual frame
connection coefficients, by proving that constant coordinate sections have
zero ordinary coordinate derivative.
The actual coordinate metric is now packaged as a continuous bilinear form.
`MetricPairingCalculus` proves the three-term moving-pairing derivative rule
and its algebraic conversion to covariant evolution. Applying that rule still
requires regularity of the bilinear-valued coordinate metric and the geometric
shape identities for the constructed variations; the generic calculus lemma
does not discharge those obligations.
