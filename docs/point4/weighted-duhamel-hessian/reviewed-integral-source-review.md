# Weighted integrated Gaussian Hessian: independent source-only review

Review date: 2026-10-05 UTC

## Verdict

**Favorable mathematical and pinned-API static review. Explicit source-only
approval is granted for clearly labeled reviewed draft integration of the
frozen candidate. The candidate remains UNCOMPILED.** This is not exact-toolchain
verification, merge approval, a new required gate, or a Point 4 completion claim.

The independently inspected declaration signatures match the new applications.
No mathematical defect, hidden solution-bound/integrability oracle, or concrete
call-signature mismatch was found. Exact imports, elaboration, notation, typeclass
inference, and kernel checking still require the target toolchain.

## Exact inputs and provenance

Frozen input directory:
`/workspace/shared/poincare-weighted-hessian-integral-source-20261005`.

New source `WeightedDuhamelHessianIntegral.lean`, 9963 bytes, 201 lines:
`84ff76aeee604c8824d2daa226f2b876d6146b14e5a292f37f18693c4c9fd8f2`.
Its Git blob identity is `247aa25922dfef687d81a4943949d5991df08522`.

All four candidate SHA256 values agree with the frozen manifest. The three
inherited candidates were also compared byte-for-byte with the prior frozen
time-kernel artifact:

- `WeightedTimeKernel.lean`:
  `20ceba4efe5d3c2d0d302220e94db8394496be16ee336382c4d1049b470fc3a5`
- `WeightedHessianTimeEnvelope.lean`:
  `4283e582912f8556266e2944e9453a2ed475522e8d4e95a5cba19ec39deb070d`
- `WeightedDuhamelIntegrand.lean`:
  `77da0c8aaad5fc44aae5dfd9bb9958da90528112d93eedba7082647f64d4a577`

The README, remaining-bridge document, manifest, and both receipt files were
read. All seven inherited db584 Mathlib snapshots independently reproduce
their recorded Git blob SHA and SHA256. All five project source snapshots were
compared directly with the exact local Git objects at project commit
`3a8ed697d1f0366f8370efb2fa9e524b68d27e97`, including independent blob identity
checks. The project toolchain and Lake manifest snapshots also agree with that
commit's `curvature/lean-toolchain` and `curvature/lake-manifest.json`.

Target Lean: `leanprover/lean4:v4.33.0`.
Target Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.

The prior scalar review was read from
`/workspace/shared/poincare-weighted-time-kernel-review-20261005/REVIEW.md`.
Its favorable verdict is preserved for the unchanged scalar argument; the
present review independently covers the new integral/continuity/BCF file and
its inherited concrete Gaussian domination.

The new review manifest binds every frozen input and every review output by
byte length and SHA256. No `sorry`, `admit`, `axiom`, or `unsafe` token occurs in
the four candidate Lean files.

## Mathematical review

Write `a = α/2`, `M = heatHessianEntryHolderMoment n α j k`, and
`A = L*M`. The theorem hypotheses are explicit actual data:

- `t₀ < t` and `0 < α < 1`
- `q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ`, with `Continuous q`
- `∀ s y, ‖q s y‖ ≤ C`
- `0 ≤ L`, and the stated weighted spatial coordinate-Hölder inequality only
  for `t₀ < s < t`

There is no assumed envelope integrability, integrated estimate, solution
bound, inverse, solver, uniform unweighted source-Hölder constant, source
Hölder hypothesis at `t₀`, or selected trace/modulus certificate.

1. **Concrete Gaussian input.** The inherited helper invokes the existing
   `abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale`, whose
   actual integral and hypotheses are visible in the pinned project snapshot
   `EuclideanHeatHessian.lean:249–258`. The coefficient
   `L*(s-t₀)^(-a)` is nonnegative because `s>t₀` and `L≥0`. Its product with
   the Gaussian factor `(t-s)^(a-1)` is algebraically the claimed envelope.
   The helper merely reassociates factors by `ring`; it does not posit a
   Gaussian operator norm.
2. **Endpoint treatment.** New source lines 41–49 discard precisely the
   terminal singleton `{t}` using volume-nullity. Membership in `Ioc t₀ t`
   already gives `t₀<s`; combining `s≤t` with `s≠t` gives `s<t`. Thus the
   positive-time cancellation theorem and the interior Hölder assumption
   apply almost everywhere. This does not discard any neighborhood of either
   singular endpoint or substitute endpoint totalization for integrability.
3. **Actual integrability.** Lines 66–77 derive interval integrability of
   `A*weightedHessianTimeEnvelope` from the scalar theorem, obtain actual
   time measurability from the existing Gaussian convolution theorem, and
   apply `Integrable.mono'` on volume restricted to `Ioc t₀ t`. All three
   required premises are provided. The scalar proof genuinely controls both
   endpoint singularities; it is not an integrability hypothesis.
4. **Raw integral and signs.** The existing definition in
   `EuclideanDuhamelHessian.lean:139–143` is exactly
   `∫ s in t₀..t, heatHessianEntryConvolutionND (t-s) (q s) j k x`.
   Lines 100–101 establish actual integrability before estimating this
   totalized integral. The local `hGi` proof is not subsequently consumed by
   the majorant API, which does not require it; its presence still establishes
   the genuine integrability claim. The factor `A` is nonnegative by the
   existing moment theorem `EuclideanHeatHessian.lean:237–244`, and pulling it
   outside the integral and multiplying the scalar inequality preserve order.
   The final multiplication order `M*L` is a harmless commutative reassociation.
5. **Constant and exponent range.** The actual majorant is
   `(t-s)^(a-1)*(s-t₀)^(-a)`. The scalar proof requires `0<a<1`, equivalent
   to `0<α<2`, and the new file's stronger explicit `α<1` provides this.
   The bound is `M*L*(1/a+1/(1-a))`; both denominators are positive, there is
   no omitted interval-length factor, and the two midpoint powers cancel
   scale exactly. `α=0` and `α=1` are outside the new theorem's declared
   strict range. No assertion at those boundary values is smuggled in.
6. **Spatial continuity.** Lines 127–158 use the same actual integrable
   majorant, restricted time measurability for every `x`, and continuity of
   the positive-time spatial Gaussian convolution almost everywhere in time.
   `continuous_of_dominated` is applied with its exact declared argument
   order. The finite real coordinate space has the required first-countable
   topology, including rank zero. Lines 159–164 identify the restricted
   integral with the actual oriented interval integral using `t₀≤t`.
7. **BCF packaging.** Lines 168–186 package the raw integral using the
   proved spatial continuity and pointwise uniform bound. The constructor
   does not assume an independently supplied boundedness certificate or
   derivative identity. The application theorem at lines 188–198 is genuinely
   definitional (`rfl`) for the inspected constructor.

The conclusions are spatial continuity and boundedness at each fixed positive
final time. They do not establish time continuity of the BCF-valued Hessian,
an actual second derivative of the Duhamel potential, strong C² trace, time
Hölder forcing, or the parabolic equation.

No `n>0` premise appears. With `n=0`, the coordinate entry indices `j k : Fin 0`
are empty, so the entry family is vacuous; this does not resolve the separate
rank-zero geometric obligation by fiat.

## Independent pinned Mathlib API checks

The initially absent source declarations were independently retrieved through
the authorized read-only GitHub connector from official
`leanprover-community/mathlib4` at the exact db584 commit. Full retained files
reproduce their returned Git blob SHA after normalizing only the extra newline
introduced by the local patch transport. `retrieved-source-receipts.json`
records source URLs, exact blob/SHA256, byte lengths, and inspected line ranges.

- [Bochner.Basic:415–450](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Integral/Bochner/Basic.lean#L415-L450)
  declares `continuous_of_dominated` with measurable slices, a uniform a.e.
  norm bound, an integrable real bound, and a.e. continuous spatial slices,
  in exactly that order. Its ambient assumptions impose no missing analytic
  premise for the real-valued finite-coordinate application
- [L1Space.Integrable:101–103](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/L1Space/Integrable.lean#L101-L103)
  declares `Integrable.mono'` with an integrable real majorant, a.e. strong
  measurability of the target, and `‖f‖≤g` a.e. No extra nonnegativity
  premise is required; the supplied norm domination implies it where needed
- [AEStronglyMeasurable:220–223](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Function/StronglyMeasurable/AEStronglyMeasurable.lean#L220-L223)
  declares `.restrict` with the implicit restriction set inferred from the
  expected type, matching lines 74 and 138 of the candidate
- [Measure.Restrict:627–629](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Measure/Restrict.lean#L627-L629)
  gives exactly the a.e. restricted-measure/ambient-implication equivalence
  used with `measurableSet_Ioc`
- [Bounded.Normed:118–125](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Topology/ContinuousMap/Bounded/Normed.lean#L118-L125)
  declares `ofNormedAddCommGroup f Continuous_f C bound`, and its coercion
  equality is `rfl`. This matches the packaging and application theorem
- [NullSingletonClass:29–40](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/MeasureTheory/Measure/Typeclasses/NullSingletonClass.lean#L29-L40)
  exports `measure_singleton`. The old NoAtoms file is now a deprecated-module
  stub; the actual current pinned declaration was retrieved and inspected

The already retained pinned `IntervalIntegral.Basic` also directly matches:
`intervalIntegrable_iff_integrableOn_Ioc_of_le` at lines 131–133;
`integral_of_le` at lines 677–681;
`norm_integral_le_of_norm_le` at lines 756–760; and
`integral_const_mul` at lines 817–819. In particular, the norm-majorant theorem
takes `a≤b`, the ambient a.e. implication on `Ioc a b`, and interval
integrability of the majorant, matching the candidate's line 104.

The full BCF Basic and DominatedConvergence files were retained as context.
The dominated-continuity declaration used here is in Bochner.Basic, not a
guessed Bochner/Continuous path. One initial read of that nonexistent path
returned 404; ordinary directory inspection identified the correct pinned
source. No access restriction was bypassed.

These checks close the concrete previously stated source gaps for dominated
continuity, the BCF constructor, and `Integrable.mono'`. They do not claim
complete inspection of every transitive import or successful compiled-module
availability. No concrete replacement assumption is needed or recommended.

## Remaining obligations and canonical contract

The current remaining-bridge document is accurate. In particular, the existing
`hasDerivAt_heatDuhamelGradientCoordND_entry` at pinned project lines 278–355
requires a global unweighted Hölder constant, so it cannot simply be reused
for the new weighted forcing. The following remain **OPEN**:

- Weighted actual second-differentiation compatibility, assembly into full
  Fréchet C², and strong BCF Hessian time continuity
- Strong C² zero trace from the genuine vanishing weighted Hölder condition,
  together with value/gradient traces
- Time-slab Hölder estimates and the actual parabolic time derivative identity
- Coordinate-seminorm reconciliation and the weighted derivative-graph solver
- Literal-C² compact-atlas encoding and overlap compatibility
- Weighted nonlinear invariance/contraction, positivity, geometric readout,
  gauge recovery, ordinary endpoint derivatives, and uniqueness for the
  existing weak competitors on common closed intervals

The arbitrary-C² initial-data, arbitrary model `I`, manifold-only
`BoundarylessManifold I M`, rank-zero-inclusive, common-closed-interval,
ordinary-endpoint-component-derivative contract is unchanged. No C³,
initial-positive-Hölder, positive-dimension, or global `I.Boundaryless` premise
was added. **Point 4 remains OPEN.**

## Execution and mutation boundary

No Lean compiler/proof runtime was executed. No package/runtime/compiler/cache
was installed, downloaded, rebuilt, or modified. No frozen input, shared
candidate tree, repository source, branch, PR, CI configuration, verification
gate, or publication was changed. New public source snapshots were retrieved
only for this independent static review; the frozen author-stage manifest's
`downloaded_any_new_source=false` remains a statement about that earlier stage.
The only output writes are in this new review directory.
