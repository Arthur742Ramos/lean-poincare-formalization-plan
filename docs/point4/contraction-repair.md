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

## Remaining obligations

The conventional field still needs its joint regularity, the associated fixed-
background parabolic operator and nonlinear construction, intrinsic curvature
identification, gauge flow/variational recovery, and uniqueness. A supporting
smooth closed-manifold endpoint also needs a precise bridge to the canonical
target's C² initial metrics, weaker candidate regularity, ordinary initial-time
derivative, model-space assumptions, and interval convention.

Point 4 remains **OPEN**. The canonical target, its solution predicates, and the
completion auditor are unchanged. The exact-head workflow separately compiles
the contraction, frame bridge, regression and axiom probe, then runs the unchanged
full completion audit. Prototype typechecks with a different toolchain are not
accepted as final verification of this Lean-4.33-pinned package.
