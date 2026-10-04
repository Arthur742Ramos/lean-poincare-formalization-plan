# Vanishing weighted initial Hessian Hölder certificates

This supporting source candidate builds on immutable PR124 head
`591c25914c80366d619ece00da204997ee2a65d7`, an explicit unmerged stack dependency.
The actual Gaussian, its normalization and semigroup law, coordinate derivative
commutation, compatible bounded-C² heat producer, and arbitrary-modulus initial
trace are inherited byte-for-byte. Structured builds-on attribution is recorded
in `curvature/formalization.yaml`; all existing attribution and license notices
remain. No registry submission or new registry identity is part of this work.

## Actual theorem and quantitative certificate

`AnalyticPDE/EuclideanHeatWeightedInitialHolder.lean` constructs
`heatEvolvedWeightedC2AlphaData D ht hα0 hα1`. Its base is exactly the existing
`heatEvolvedBoundedC2Data D ht`: the actual heat-evolved value, first derivatives,
Hessian entries and their genuine coordinate derivative witnesses are unchanged.

For an initial Hessian entry `f = D.second j k`, define the actual error

`E_f(t) = ‖f - heatFlowPathBcf f (√t)‖`.

At positive time, the path in that formula is exactly `S_{√t} f`. The producer's
Hessian Hölder constant is the finite sum of the explicit scalar constants

`K_f(t) = 2(πt)^(-α/2) E_f(t) + 2(π√t)^(-α/2) ‖f‖`.

There is no chosen continuity-modulus oracle or supplied weighted-bound premise.
The proved Gaussian split is

`S_t f = S_t(f - S_{√t} f) + S_{t+√t} f`.

The first term uses the existing bounded-data smoothing estimate with the small
actual error norm. The second uses the genuine Gaussian semigroup and
`t + √t ≥ √t`, giving its Hölder estimate at the fixed larger smoothing scale.
The resulting scalar certificate is summed over all Hessian entries, matching
the established coordinate-sum Hölder convention.

The exact weight identity is

`t^(α/2) K_f(t) = 2π^(-α/2) E_f(t) + 2π^(-α/2)t^(α/4) ‖f‖`.

For uniformly continuous bounded `f`, the inherited genuine sup-norm initial
trace makes `E_f(t) → 0`. For `α > 0`, `t^(α/4) → 0` as well. Finite summation
therefore proves the headline
`EuclideanBoundedC2Data.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero`
for the constructed datum's own actual Hessian Hölder constant.

The certificate is valid for `0 ≤ α ≤ 1`; the vanishing conclusion is for
`0 < α ≤ 1`, and in particular the intended `0 < α < 1` range. Only uniform
continuity of the initial Hessian entries is assumed for the global trace.
No positive-exponent initial Hessian Hölder certificate is assumed, and no
positive-dimension/rank assumption is added. Dimension zero is explicitly
covered by the compiled-type probe, with Hessian constant identically zero.

## Verification boundary

The inherited PR124 actual trace/generator type and axiom checks reportedly
passed at its exact Lean-4.33 head; its complete build remains a separate
pending inherited gate. This candidate has had no local Lean compiler run.
Exact Lean-4.33 verification and independent review are pending.

The new pinned read-only workflow builds the actual weighted module, checks
all eleven selected axiom surfaces and exact headline types, and runs the
unchanged full Point-4 audit. The inherited initial-trace workflow is unchanged
and also triggers on the new candidate's `curvature/**` changes.

The source preflight
`curvature/scripts/point4_weighted_initial_heat_guard.py` checks all 385 inherited
Lean proof files against the exact base, preserves the canonical contracts,
initial-data meaning, full completion audit, inherited workflow and toolchain
pins, and checks the new headline source signature. The compiled type/axiom
probe is an independent required gate, not replaced by that source check.
With the cached complete official v0.4 schema supplied, full metadata validation
and exact stack provenance validation pass. The forbidden-term scan is zero.

## Remaining endpoint plan

This proves an initial-face heat Hölder-weight smallness estimate, rather than
repackaging the already proved crude boundedness of `t^(α/2) O(t^(-α/2))`.
It does not prove weighted spacetime Schauder estimates, temporal Hölder control,
a nonlinear weighted contraction or an actual Ricci–DeTurck evolution.

The next analytic work must establish the weighted forcing/Duhamel and
coefficient estimates needed to consume this vanishing initial face in a
quasilinear fixed-point construction. Compact C² metric localization still
needs actual derivative support, boundedness, ambient uniform continuity and
geometric overlap producers. Metric positivity, ordinary endpoint metric
derivatives, recovery gauge regularity, competing-candidate encoding and the
canonical existence/uniqueness theorem remain independent open obligations.
The general manifold scope, C² initial data and weak competing-candidate
contracts are unchanged. Point 4 remains **OPEN** until all canonical gates close.
