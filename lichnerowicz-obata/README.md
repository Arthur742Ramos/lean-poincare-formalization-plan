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
requires the geometric shape identities for the constructed variations; the
generic calculus lemma does not discharge those obligations.
`MetricBilinearRegularity` supplies C1 operator-norm regularity of the actual
bilinear-valued coordinate metric by reconstructing it from its smooth finite
basis pairings. Its differentiability holds at every point of the open chart
target. The bundled derivative agrees with fixed-pair differentiation and
satisfies the genuine connection-coefficient compatibility formula.
`hasDerivAt_coordinateMetric_pairing_connection` now derives the moving-pairing
formula for the actual metric along a differentiable coordinate curve.
`CoordinateRadialShape` derives the coordinate radial shape identity from
torsion freeness and the radial Hessian theorem. It gives spherical metric
scaling for a radial coordinate solution and angular solutions of its
linearized equation. For C2 families of genuine radial coordinate solutions,
`hasDerivAt_radial_flow_metric` derives the spatial variational equations and
radial-field differentiability, leaving no separate linearized-ODE assumption.
Applying these local results to the constructed global manifold radial flow,
and establishing the pole normalization, remains pending.
`ManifoldFlowCoordinates` expresses actual manifold families in fixed input
and output charts. It constructs their natural open coordinate domain,
transfers joint smoothness, and derives the coordinate time ODE directly
from the manifold integral-curve equation.
`CoordinateAngularVariation` derives angularity by differentiating the radial
level identity, then proves spherical metric evolution for the actual chart
representation of a smooth manifold radial family. The theorem requires its
integral-curve and level identities, but no separate angularity or variational
ODE hypothesis.
`ConstructedRadialMetric` instantiates the metric equation with the same
constructed global radial family. The strengthened existence theorem retains
the original gradient-norm identity, smoothness, reset law, integral-curve
equation, level identity, unit speed, and endpoint limits, and adds metric
evolution in every valid chart pair. Pole normalization remains to be completed.
`IntrinsicFlowMetric` identifies coordinate spatial derivatives with the
actual tangent maps of the fixed-time manifold slices. Their coordinate
metric pairing equals the intrinsic inner product, independently of the
output chart. The local ODE now transfers to this intrinsic pairing and
integrates over the entire open radial interval. The chart-free
`radialVariationMetric_sine_squared_normalized_eq` proves that the actual
tangent-map metric divided by the spherical sine-square factor is constant,
for arbitrary initial tangent vectors. Identification of the normalized
metric at a pole with the round angular metric remains pending.
`RadialMetricNormalization` fixes the integration constant at the actual
starting level. Angular transport has exactly the initial inner product
multiplied by the ratio of sine-squared radial factors, derived from the
initial-point identity. This is an initial-level normalization, not yet the
identification of the pole's angular metric with the round sphere.
`SmoothConnectionCoordinates` derives finite-order smoothness of the actual
metric torsion-free connection coefficients and the associated position–velocity
geodesic equation. The existing smooth local-flow construction now supplies
local geodesic solution families near any chart position and velocity, without
an extra coefficient-regularity or bump-function assumption.
`GeodesicLinearization` proves that the actual geodesic vector field at zero
velocity has derivative `(δposition, δvelocity) ↦ (δvelocity, 0)`. ODE
uniqueness proves local stationarity of a solution starting at rest, and
spatial derivatives of a smooth solution family satisfy the resulting linear
system along it. Integration of this linear system on a connected open time
domain proves constant velocity variation and affine position variation.
The initial-value identity determines the spatial derivative at time zero;
along the stationary orbit the flow derivative is therefore
`(u, v) ↦ (u + t • v, v)`.
Restricting to initial velocities and projecting to position proves that the
endpoint map `v ↦ (α ((z, v), t)).1` has derivative `t • id` at zero.
The inverse function theorem now constructs a local endpoint homeomorphism at
a positive time, with a C² inverse at the base point. The existence theorem
constructs its own C² geodesic flow on an open product neighborhood and proves
stationarity by uniqueness; neither the flow nor stationarity is an extra
hypothesis. Using this local normal map to identify the pole's angular metric
with the round metric remains pending.
`GeodesicEnergy` proves that the actual coordinate metric's squared speed has
zero derivative along a geodesic, hence is constant on each connected open
time domain. The proof derives conservation from metric compatibility and
the geodesic equation, without assuming a speed identity.
It also proves that simultaneous time and velocity rescaling preserves the
coordinate geodesic equation, using the bilinearity of its acceleration term.
`SmoothODEUniqueness` derives uniqueness on connected open time domains from
local C¹ regularity along a solution. `GeodesicScaling` uses it to prove the
actual flow-scaling identity on common solution domains, not just invariance
of the differential equation.
For a C¹ family on an open product solution domain, nearby scalings stay in
a common time domain. Differentiating their identity proves that the endpoint
derivative in its initial-velocity direction is time times terminal velocity.
`GeodesicHessian` derives the value derivative and Hessian evolution along
these geodesics. Under the Obata Hessian equation, the scalar restriction
satisfies `f″ = -K · speed² · f`, with the constant speed evaluated at any
fixed reference time. `ScalarOscillator` proves the cosine solution by energy
uniqueness, including zero frequency. Applied to geodesics from a critical
point, this gives the cosine profile with frequency equal to the square root
of curvature times initial squared metric speed. Identification with the
existing radial curves and the round angular metric remains pending.
`GeodesicRadial` recovers the radial parameter as initial metric speed times
elapsed time before the antipodal phase, and proves that strictly intermediate
positive phases lie in the regular region. Differentiating this identity
locally gives the radial-gradient/velocity pairing. On a connected manifold,
the existing Obata energy theorem supplies unit radial-gradient norm, which
together with conserved speed proves that geodesic velocity equals the
speed-scaled radial gradient. Identification of the angular metric with the
round tangent-sphere metric remains pending.
`GeodesicNormalRadial` combines the endpoint derivative and the proved
geodesic-velocity identity: intrinsically, the endpoint map's radial derivative
is the radial gradient multiplied by time and initial metric speed.
On a neighborhood of a regular positive-phase initial velocity, it also
proves that squared endpoint radius equals time squared times the initial
quadratic metric energy. The symmetric quadratic-metric derivative is checked
separately. `GeodesicGauss` differentiates this identity and combines it with
the intrinsic radial derivative to prove the Gauss lemma: the pullback metric
pairs a radial initial vector with any variation as time squared times the
initial metric pairing. Thus angular initial directions remain orthogonal to
the endpoint's radial direction. The full angular metric formula remains pending.
`NormalMetricLimit` proves continuity of the pullback metric and its limiting
value at zero initial velocity. For the actual geodesic endpoint map this limit
is time squared times the base-point metric, derived from its checked derivative
at zero. This supplies the pole normalization for the angular evolution argument.
The variation equation now also covers initial-parameter-dependent speeds.
Its derivative is derived from the actual flow equation and includes the
longitudinal speed-variation term, which must be accounted for in angular
metric evolution.
`ScaledRadialMetric` proves the corresponding angular metric equation for C²
scaled radial flows. Metric compatibility and the actual radial shape operator
give the speed-scaled spherical coefficient; angular orthogonality cancels the
longitudinal terms. Application to the normal-map rays remains pending.
`NormalRays` supplies the chain-rule bridge for a family `F(s • u)`: its
time derivative, spatial variations, the squared-parameter metric factor,
and cancellation of a nonzero radial parameter to obtain the ray equation.
`GeodesicNormalRays` specializes this to the actual geodesic endpoint map:
positive-parameter rays satisfy the scaled radial gradient equation, and
initial angular directions give spatial ray variations orthogonal to that
gradient. Both facts follow from the geodesic family and the checked Gauss
lemma, rather than being additional flow assumptions.
`NormalRayMetric` combines these results to prove the actual angular metric
differential equation at every positive-phase ray point. Its open ray domain,
smoothness, differentiable speed, and angular orthogonality are derived, and
the geodesic radius identity gives the explicit sine-square evolution
coefficient. Its sine-square-normalized metric is now proved constant on every
connected open positive-phase ray interval. This uses local integration and
does not require one normal coordinate chart to cover the whole radial range.
`SineMetricLimit` proves the scalar limit step: a quadratic center limit fixes
a constant sine-square normalization on a short positive interval.
`NormalRayNormalization` applies this to the actual geodesic metric. The
normalized angular pairing is the initial pairing divided by curvature times
initial squared speed. Its constant is derived from the endpoint derivative
at zero, with the endpoint-time factors cancelled. A valid short positive-phase
ray interval is constructed from the open initial-data domain for every
positive-energy initial ray. The resulting interval supports the formula for
all angular vector pairs. Global sphere rigidity is not yet established.
`RadialAngularDecomposition` reconstructs a symmetric bilinear metric from
its radial and angular restrictions. Applying it to the actual geodesic map
now gives the full local pullback metric for arbitrary vector pairs, including
radial and mixed directions, using the Gauss lemma and pole normalization.
The full formula now holds on one constructed punctured velocity ball for all
directions and vector pairs simultaneously; its radius is not selected
separately for each ray. Coordinate-metric positivity is derived from the
invertible tangent trivialization.
`RoundPolarCurves` begins the explicit round-sphere comparison: its meridians
lie on the actual radius-R metric sphere, have unit speed, and join a common
pole to its antipode at parameter `π R`. The sphere chart metric comparison
and global Riemannian isometry are not yet established.
`RoundPolarMetric` computes actual angular derivatives of this parametrization,
proves their tangency to the sphere and orthogonality to radial velocity, and
derives the full polar pairing: unit radial coefficient and radius-squared
sine-square angular coefficient. Constructing the global comparison map is
still pending.
`RoundPolarCoordinates` constructs a continuous, injective map from unit
directions perpendicular to a pole and the open radial interval into the
actual sphere. Height determines the radial parameter, and the remaining
component determines the angular direction.
`RoundPolarInverse` constructs polar coordinates for every sphere point other
than the two poles: arccosine of its normalized height gives the angle, and
the normalized perpendicular component gives the unit angular direction.
Surjectivity away from the poles and exclusion of both poles from the open
polar range are proved. The parametrization is packaged as a continuous
bijection onto the punctured sphere. `RoundPolarHomeomorph` proves explicit
inverse formulas and their continuity, upgrading this to a homeomorphism
between the punctured sphere and angular directions times the radial interval.
The global Riemannian comparison with the manifold remains pending.
`SmallRadialLevels` proves that any neighborhood of the unique Obata maximum
contains every sufficiently small radial level. Thus a normal-chart image
containing the pole captures entire small levels, not only local pieces.
`NormalLevelHomeomorph` constructs whole-level homeomorphisms by restricting
an actual chart and its inverse. For a radial chart with a scaled-norm identity,
compactness supplies sphere-to-level homeomorphisms for every sufficiently
small positive radius.
The actual Obata endpoint map now has the scaled-norm radial identity on a
neighborhood including zero velocity, both in coordinate and intrinsic tangent
variables.
`IntrinsicNormalChart` now constructs and restricts the actual chart from the
intrinsic tangent space to the manifold. It sends zero to the maximum and
has the scaled-norm radial identity on its entire source. The geodesic family
and positive endpoint time are constructed, not required as extra hypotheses.
Applying this chart to the whole-level construction now identifies every
sufficiently small positive Obata radial level with an actual intrinsic
tangent-space sphere. The scale, chart, and uniform range of small radii are
constructed. The global radial product now also uses a whole ambient level,
with a proved homeomorphism removing the nested regular-region subtype; this
allows direct composition with the normal-sphere identification. The retained
energy identity now forces its amplitude to agree with any positive critical
value. Combining these results at the unique maximum identifies the entire
regular region with an actual intrinsic tangent sphere of constructed positive
radius times the full open radial interval. This is a homeomorphism; comparison
of the angular metric, smooth extension at the poles, and the global
Riemannian isometry remain pending.
`ObataRegularSphere` now derives the poles, coordinate basis, and sphere radius
from the smooth nonconstant Obata equation in dimension at least two. It also
proves that the regular region is exactly the manifold minus those two poles,
so the resulting tangent-sphere product omits no other manifold points.
