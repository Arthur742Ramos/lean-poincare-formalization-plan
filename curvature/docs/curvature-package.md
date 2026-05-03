# Curvature package status

This package now contains the connection-theoretic layer together with the
bundled curvature tensor and its Ricci/scalar contractions.

## Completion standard

Within this package, a roadmap point counts as complete only when the target
result is actually proved in Lean. Interfaces, theorem boundaries, axioms,
`sorry`, or other scaffolding do not count as completion.

## Landed in code

- a Lean package with a pinned toolchain and a mathlib dependency
- `CovariantDerivative.along`, packaging the section `∇_X σ`
- algebraic lemmas for the vector-field slot of `∇_X σ`
- pointwise Leibniz/additivity lemmas in the section slot
- a smoothness theorem showing that `∇_X σ` has the expected regularity
- `CovariantDerivative.curvatureAux`, the raw curvature commutator
- alternating identities `R_aux(X, Y) = -R_aux(Y, X)` and `R_aux(X, X) = 0`
- `CovariantDerivative.curvatureTensor`, packaging curvature fibrewise as a
  multilinear map
- `CovariantDerivative.ricciCurvature` and `CovariantDerivative.scalarCurvature`
  on the tangent bundle
- `CovariantDerivative.IsMetricCompatible`, phrased for Riemannian vector bundles
- tangent-bundle predicates `CovariantDerivative.IsTorsionFree` and
  `CovariantDerivative.IsLeviCivita`
- skew-adjointness of the difference of two metric-compatible affine connections
- symmetry of the difference of two torsion-free affine connections
- uniqueness of Levi-Civita connections in the current representation, packaged
  as `cov.difference cov' = 0`

## Point 2: curvature identities and existence

- Levi-Civita existence via `leviCivitaConnection_nonempty` and
  `exists_leviCivitaConnection`
- local-frame Gram determinant nonvanishing, inverse Gram/Riesz-map regularity,
  and a compact-domain positive lower bound for the Gram determinant on
  trivialization bases
- sectional curvature via `sectionalCurvature`, `sectionalCurvatureNumerator`,
  and `sectionalCurvatureDenominator`
- first-Bianchi identities for `curvatureAux` and `curvatureTensor`
- a raw second-Bianchi identity package on smooth tangent vector fields

## Point 3: time-dependent geometric structures

- `TimeFamily`, `TimeDependentSection`, and `TimeDependentCovariantDerivative`
- evaluation-at-time and constant-family interfaces
- a per-time smoothness predicate `ContMDiffInSpace`
- a time-lifted `along` construction
- `TimeDependentRiemannianMetric` for families of smooth tangent-bundle metrics
- family-level metric compatibility and Levi-Civita predicates
- slicewise Levi-Civita construction and existence for time-dependent metrics
- tangent-bundle curvature, Ricci, scalar, and sectional constructions defined
  pointwise in time using the metric and connection at each slice

## Current boundary

The package now closes roadmap points 1 through 3 under the repository's
proof-only standard. Point 4 remains open. There is draft Ricci-flow scaffold
code in the repository, but it is not part of the public package boundary and
does not count toward completion. The next follow-on work is therefore still the
actual Lean proof of roadmap point 4. In the meantime the package has gained a
real proof-bearing section-smoothing layer: local-to-global convex gluing,
trivial-bundle and open-set smoothing, local smoothing in bundle
trivializations, and a global smoothing theorem for continuous bundle sections
that stay inside open fiberwise convex subsets of the total space, together
with an intrinsic fiberwise-`ε` approximation theorem for continuous sections
of smooth Riemannian vector bundles. The package also now contains a
proof-bearing `C^0` coordinate layer for continuous sections: local-frame
continuity criteria, compact coordinate-map packaging in a trivialization,
compact overlap coordinate-change identities in `C(K, F)`, and cover-level
compatible compact coordinate families that recover the section on the covered
union. On finite compact covers, the compatible families form a closed complete
compatibility kernel inside the ambient product of compact `ContinuousMap`
spaces, the gluing lemmas reconstruct continuous sections from those compatible
families to produce a genuine finite-cover equivalence, and that equivalence
now transfers the induced additive, module, normed, and complete structure to a
dedicated continuous-section wrapper. Continuous and smooth Riemannian metrics
are also now packaged as honest sections of the bilinear-form hom bundle, with
extensionality lemmas reducing equality of metrics to pointwise equality of
their fiberwise bilinear forms. That same public layer now also proves
finite-dimensional coercivity and operator-norm openness lemmas for
positive-definite continuous bilinear forms, giving the first honest fiberwise
open-neighborhood result needed for a section-space model of metrics, and lifts
that result to compact `ContinuousMap` and `BoundedContinuousFunction`
families, and from there to the preferred finite-cover `ContinuousSectionSpace`
model, where actual positive-definite bilinear-form sections form an open
subset, the symmetric locus is now closed, and continuous Riemannian metrics
land inside the refined symmetric positive-definite locus there, now packaged as
an open subset of the closed symmetric section subtype. The
repository's internal
`RicciFlow.LocalExistence` scaffold has also gained a proof-bearing stationary
Ricci-flat special case with the corresponding restricted metric/connection
uniqueness statement, plus zero-velocity and Ricci-tensor-zero interval
constancy theorems for local solutions at both the metric and Levi-Civita
connection levels. It also now proves that the Ricci tensor, Ricci-flow
right-hand side, and Ricci-flow equation do not depend on which Levi-Civita
family is chosen for a fixed metric family, and it now also packages intrinsic
metric-only `IntrinsicSolution`, `IntrinsicLocalSolution`, and
`IntrinsicLocalExistenceUniqueness` wrappers with conversions to and from the
older connection-parametrized scaffold. The general compact-manifold local
existence/uniqueness theorem is still unproved and therefore point 4 remains
open. The analytic evolution layer now also exposes shorter-terminal
restriction constructors for Banach local solutions, with direct interval
equation, continuity, state-membership, and uniqueness readouts for state-preserving
solutions. The analytic PDE side has started with proof-bearing parabolic Hölder
primitives in `RicciFlow/AnalyticPDE/ParabolicHolder.lean`: parabolic distance,
balls/cylinders, `C^{0,α}` control, product-topology local-base compatibility
for parabolic balls and product cylinders, exact standard ball/cylinder
identifications, closed-to-open shrink inclusions for balls/cylinders,
open-to-closed closure containment, proper-space compactness for closed
balls/cylinders, finite open/closed parabolic ball and cylinder covers of
compact sets, finite center-dependent open ball/cylinder subcovers subordinate
to any ambient open set containing a compact set, with matching closed
balls/cylinders still contained in that open set, uniform positive closed
ball/cylinder radii inside such open neighborhoods,
continuity/uniform-continuity consequences, explicit
closed-ball/cylinder oscillation bounds, estimate monotonicity in the
controlling constants, constant-preserving localization of open-domain Hölder
and `C^{0,α}` estimates to uniform closed parabolic patches around compact
subsets, a bounded local-to-global Hölder estimate from parabolic ball covers
and doubled closed patches, plus its compact uniform-local corollary, and
finite-cover Holder patching with automatic local-constant selection,
matching local-to-global `C^{0,α}` patching theorems,
finite-cover `C^{0,α}` patching with automatic local-constant selection,
variable-radius finite-cover Holder and `C^{0,α}` patching plus compact
point-dependent- and existential-radius corollaries, finite-sum closure for
explicit Holder, bounded, and `C^{0,α}` controls, finite-sum closure for
existential Holder and `C^{0,α}` controls, finite-product closure for
existential normed-comm-ring-valued `C^{0,α}` controls, finite `Pi` packaging
across bounded, Holder, and `C^{0,α}` controls from componentwise estimates
and same-constant projection back to components,
continuous-linear, curried-bilinear-map, curried-bilinear difference,
operator-application closure, and operator-application difference with
operator-norm constants,
product-valued pairing closure,
integer-scalar closure,
additive/subtractive closure estimates, plus the
bounded product estimate for
normed-ring-valued `C^{0,α}` functions, two-factor and finite-sum
product-difference `C^{0,α}` estimates, and the corresponding bounded
scalar-action estimate for normed-space-valued functions, reciprocal and
division closure for normed-field-valued functions bounded away from zero, and
an explicit bounded finite-product `C^{0,α}` estimate,
plus closure under taking norms, Lipschitz composition on the controlled range,
direct parabolic Hölder/`C^{0,α}` lifts of time-independent spatial
Hölder/Lipschitz functions on the spatial projection, and bounded `C^{0,α}`
composition under range or explicit closed-sup-ball bounds. This is
groundwork for the future Schauder and Ricci-DeTurck Banach-chart layer, now
also including exponent lowering on unit parabolic-diameter domains with
closed-ball and closed-cylinder specializations across the Holder and
`C^{0,α}` interfaces, closed-ball diameter control, product ball/closed-ball
compatibility in both directions for parabolic balls and product cylinders,
pointwise finite-product Lipschitz estimates and finite-sum Lipschitz estimates
for two-factor products on factorwise bounded sets, plus
basepoint-to-sup bounds and Holder-to-`C^{0,α}` packaging on compact domains,
with direct proper-space closed-ball/cylinder corollaries, not the
local-existence theorem itself.
The separate `RicciFlow/AnalyticPDE/Parabolic/MatrixC0Alpha.lean` module proves
explicit bounded `C^{0,α}` determinant, adjugate-entry, and inverse-entry
estimates plus a whole inverse-matrix estimate, and parabolic `C^{0,α}` closure
for finite matrix determinants, adjugate entries, and inverse entries under a
determinant lower bound from entrywise control, plus pointwise determinant
Lipschitz control in the elementwise matrix norm, named adjugate-entry,
inverse-entry, summed whole inverse-matrix, function-level
determinant/inverse/matrix-product bounded-difference,
inverse-principal entry Lipschitz, bounded Holder entry/matrix estimates, and
inverse-principal contraction bounded-difference control with a compact-domain
determinant-lower-bound variant,
inverse-Christoffel derivative/metric-side and
array-level Lipschitz constants, inverse-Christoffel function-level
bounded-difference control with a compact-domain determinant-lower-bound
variant, inverse-Christoffel bounded Holder entry/array estimates, and
quadratic-Christoffel matrix-norm Lipschitz and bounded Holder
entry/matrix estimates, supplied-Christoffel schematic bounded Holder
entry/matrix estimates, primitive-input schematic bounded Holder entry/matrix
estimates, plus supplied-Christoffel and primitive-input schematic RHS entry
and whole-matrix Lipschitz constants and a named function-level
bounded-difference package for the primitive schematic matrix RHS, with a
compact-domain variant selecting a common determinant lower bound, on entrywise bounded
finite matrices, using a determinant lower bound for inverse estimates,
including a compactness bridge from nonvanishing determinants to a uniform
determinant lower bound and compact-domain inverse-entry, inverse-action,
inverse-bilinear, and schematic matrix-valued RHS variants, as well as
entrywise and whole-valued closure for
finite matrix transpose, pointwise symmetrization, matrix products,
explicit entrywise/whole-matrix product-difference estimates,
matrix-vector and vector-matrix products, explicit bounded matrix-vector/vector-matrix estimates,
matrix-vector/vector-matrix product-difference
estimates, and inverse-matrix vector products on
both sides under the same determinant lower bound, plus
whole finite vector/matrix and inverse-matrix packages, finite vector dot
products, dot-product difference estimates, finite bilinear-contraction
difference estimates, and bilinear contractions
through matrices or inverse matrices,
including explicit bounded Holder entry and whole-array estimates for
Christoffel-symbol type inverse-metric contractions and their entrywise/whole-array
closure, explicit bounded Holder entry/matrix estimates and whole matrix-valued
principal-part closure for `g^{ab} H_abij`,
whole matrix-valued Ricci-coordinate quadratic Christoffel contractions with
explicit bounded Holder entry/matrix estimates and product-difference bounded
Holder estimates, and supplied-Christoffel
schematic local Ricci-DeTurck RHS entry/matrix bounded Holder estimates and
primitive-input schematic RHS entry/matrix bounded Holder estimates and whole
matrix-valued closure, using the finite-product, integer-scalar, reciprocal,
and division
closure layer. The companion
`RicciFlow/AnalyticPDE/Parabolic/LocalFrameGram.lean` module bridges compact
time-space local-frame Gram determinant nonvanishing to parabolic inverse
Gram-matrix control and inverse-Gram Christoffel/schematic Ricci-DeTurck
closure, including spatial-Hölder entry-control variants and compact
quantitative inverse Gram, inverse-Gram Christoffel, and schematic RHS bridges
exposing the determinant lower-bound constant, all with matching spatial-Hölder
Gram-entry input forms.
