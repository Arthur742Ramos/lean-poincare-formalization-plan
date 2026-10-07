# Vanishing weighted initial Hessian Hölder certificates

This supporting source candidate now builds on immutable integrated PR124 head
`ba47fe1f4d8efad8bad68c61b4d25d0d8ff5387e`, an explicit unmerged stack dependency.
That head merges historical heat-trace source
`591c25914c80366d619ece00da204997ee2a65d7` with exact current master
`60b6f8ef9d37d1fc5fac1f6113584e1b16370016` by ancestry.
This weighted integration has real parents: the one-file API repair
`f908454fac787a720239e04feee6d61a9f9ab202` and the integrated PR124 head.
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

Historical PR124 head `591c25914c80366d619ece00da204997ee2a65d7`
passed its actual Lean-4.33 helpers, trace/generator type and twelve axiom
surfaces, G1 and full G2 build in run `37231132865`, with Point4 OPEN.
Its separate current closed-contract run `37231132971` failed source identity
before Lean, because that branch lacked the subsequently merged contract.
Both outcomes are preserved; neither verifies the new integrated head.

Historical weighted head `633ec144d7f1fb1b04737f309942b73b7a63d083`
failed actual Lean-4.33 compilation at four API/proof points: the unavailable
`abs_add` name, the square-root/heat-path limit composition, the untyped
constant in the norm-error limit, and the final conditional-holder-constant
simplification. The minimal one-file repair at
`f908454fac787a720239e04feee6d61a9f9ab202` received independent source
approval before this integration but was not Lean-compiled or published.
That exact repaired proof is retained byte-for-byte, with SHA256
`a1ca6c80dabcc0f9df8d788870869bc0a5eff453752e8fef1379cc8a2d0dca23`.
The failed head and its evidence remain historical rather than being relabeled
successful. The original author/development history remains unchanged.

The current integrated weighted head is **UNVERIFIED**. Fresh actual Lean-4.33
closed-contract, inherited initial-trace and weighted workflows must pass all
compile/type/axiom/kernel-regression and full-build gates, followed by new
independent exact-head review, before any merge. No local Lean compiler,
dependency install, toolchain change or cache download was used for integration.

The new pinned read-only workflow builds the actual weighted module, checks
all eleven selected axiom surfaces and exact headline types, and runs the
unchanged full Point-4 audit. The inherited initial-trace workflow is unchanged
and also triggers on the new candidate's `curvature/**` changes.

The source preflight
`curvature/scripts/point4_weighted_initial_heat_guard.py` checks the exact immutable parent union of all inherited
repository Lean proof files and rejects unknown proof files. It retains the
390-file integrated library plus the exact repaired weighted file, preserves
the current canonical closed contract, all eight interface fingerprints and
negative kernel fixtures, the current full auditor,
initial-data meaning, all inherited workflows and toolchain
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
