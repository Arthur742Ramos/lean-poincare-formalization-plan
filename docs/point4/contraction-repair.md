# Conventional DeTurck contraction repair

The fixed-background Hamilton--DeTurck route needs the conventional vector

`W^k = sum_{i,j} g^{ij} (Gamma^k_{ij} - GammaBar^k_{ij})`.

The legacy `intrinsicDeTurckOneForm` instead takes the ordinary trace of
`u ↦ connectionDifference(u,w)` and raises that covector. Its proved local-frame
formula gives

`V^k = sum_j g^{kj} sum_i (Gamma^i_{ij} - GammaBar^i_{ij})`.

These are different contractions. In dimension two, the conformal symbol with
Euclidean metric value and conformal differential `(1,0)` gives `W = 0` while
the first component of `V` is `2`. This is a slot-contraction difference, not
merely a sign convention. The positive conventional field, the equation
`-2 Ric + Lie_W g`, and the negative recovery gauge are mutually consistent.

## Existing standard route and new supporting construction

`RicciFlow/StandardDeTurck.lean` already defines the conventional two-input
contraction, and `StandardDeTurckRegularity.lean` proves spatial C¹ regularity
from the C² metric and C¹ background connection. The new generic adapter is
proved equal to that existing standard field. It is not a second geometric
model or a claim that no correct field existed before this milestone.

The equality also permits reuse of the existing standard-field derivative and
Koszul-expansion infrastructure when the remaining analytic bridge is proved.

`Analysis/MetricBilinearContraction.lean` contracts a vector-valued bilinear
map with `InnerProductSpace.canonicalCovariantTensor`. It proves:

- the diagonal formula in any orthonormal basis
- the arbitrary-frame formula using the metric-dual basis
- the actual inverse-Gram-matrix formula, with invertibility derived from the
  frame's linear independence
- an explicit two-dimensional conformal-symbol regression distinguishing the
  two contractions

`RicciFlow/MetricContractedDeTurckField.lean` applies this construction to the
actual `CovariantDerivative.difference`, proves its conventional local-frame
coefficient formula, identifies it with the existing standard field, and defines
the metric-contracted vector and negative
gauge fields. Equal Levi-Civita connections have zero contraction, so the
evolving-Levi-Civita special case still reduces to zero gauge.

The legacy field and its conditional results are preserved. They must not be
identified with this conventional field without a valid theorem. This is an
additive repair of the field-definition/frame-identification layer; it does not
claim a completed migration of the existing gauge/PDE interfaces.

## Joint regularity follow-up

The candidate supporting module
`GaugeReduction/MetricContractedDeTurckJointRegularity.lean` uses the new
conventional field throughout. Its proof route is:

1. identify its actual chosen/background connection difference with
   `explicitLeviCivitaCorrection`
2. derive the local-frame vector formula using the inverse Gram matrix of the
   defining metric, or an explicitly agreeing smooth metric representative
3. prove inverse-Gram and bilinear-section contraction regularity in
   `Analysis/TimeDependentMetricContraction.lean`, with Gram nonsingularity
   discharged by positive definiteness
4. globalize that local section and prove joint smoothness of the positive
   conventional vector and its negative recovery gauge
5. feed that same negative field to the existing coherent compact-flow theorem

The correction-functional corollary uses the existing genuine Gram/Riesz
reconstruction of the actual correction tensor. It therefore exposes joint
metric regularity and local-frame correction-functional section regularity as
analytic inputs; it does not assume regularity of the final contracted field.
The compact-flow conclusion is conditional on those smooth geometric data and
on the existing compact, boundaryless manifold hypotheses. It constructs no
Ricci--DeTurck PDE solution and supplies no variational recovery theorem.

The generic regularity and parameterized-negation lemmas have a development-only
Lean-4.35.0-rc2 prototype check. The new geometric adapter and the inherited
contraction adapter have not yet passed exact Lean-4.33 hosted compilation.
The exact-head workflow now explicitly compiles the follow-up and checks its
axiom surfaces before running the unchanged full completion audit. Prototype
checks are not final verification.

## Remaining obligations

The conventional field still needs the joint geometric regularity hypotheses
of the supporting bridge to be discharged, the associated fixed-background
parabolic operator and nonlinear construction, intrinsic curvature
identification, gauge flow/variational recovery, and uniqueness. A supporting
smooth closed-manifold endpoint also needs a precise bridge to the canonical
target's C² initial metrics, weaker candidate regularity, ordinary initial-time
derivative, model-space assumptions, and interval convention.

Point 4 remains **OPEN**. The canonical target, its solution predicates, and the
completion auditor are unchanged. The exact-head workflow separately compiles
the contraction, frame bridge, regression and axiom probe, then runs the unchanged
full completion audit. Prototype typechecks with a different toolchain are not
accepted as final verification of this Lean-4.33-pinned package.
