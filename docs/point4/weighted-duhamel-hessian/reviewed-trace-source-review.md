# Weighted Hessian trace: independent source-only review

Review date: 2026-10-05 UTC.

## Verdict: APPROVE, source only

**APPROVE the exact replacement bytes below for clearly labeled reviewed draft integration. They remain SOURCE ONLY, UNCOMPILED.** No further concrete mathematical defect, hidden solution-bound assumption, or pinned-API signature mismatch was found after the narrow initial-time repair.

This is not Lean elaboration, kernel verification, merge approval, release admission, or Point 4 completion. Exact Lean 4.33.0 / Mathlib db584 verification remains mandatory.

## Exact reviewed identities and historical rejection

- `WeightedDuhamelHessianTrace.lean`: 13872 bytes, 277 lines; SHA256 `64f8f5bc8cfd468fe9b46b60be39c5686dec4b870b481b766403d9e52cda9d33`; Git blob `e1508795061348414a5226ce552db65751e6cec3`
- `WeightedDuhamelHessianFrechetTrace.lean`: 4019 bytes, 93 lines; SHA256 `3af628927dd651ea247f07159243a8dd100267bdabcaabb06fb9263882ff7b08`; Git blob `a404a133ef2f70a0ee56208f5d43ab7fbe3c0cb6`

The original trace SHA256 `065d29c14f3f6c2c966939d968f0ac93c5ed90de723f518d81cae5a7c97e2384` is **REJECTED**. Its canonical BCF constructor had an implicit initial time not determined by visible argument types or its result type; seven applications omitted its named argument. The author flagged this issue, and this reviewer independently confirmed it. The parent authorized the narrow correction.

An independent byte diff confirms that the replacement adds only `(t₀ := t₀)` at the seven direct BCF applications, unchanged source lines 159, 170, 185, 211, 232, 253, and 268. There is no definition, hypothesis, constant, proof-body, import, or conclusion change. The optional Fréchet trace leaf remains byte-for-byte unchanged. The original source, original manifest/docs, and the explicit historical REJECT report are retained in `historical-original/`.

The exact author repair patch has SHA256 `6514089db5eaa198f7e4500671ecfc33ef9218335c86745717dfc1ede28bd8d2`. This review is a full mathematical/API inspection of the originals followed by a delta-only inspection of the named-argument repair.

## Inputs and provenance inspected

The README, UNPROVED_BRIDGES document, author manifest, and provenance receipts were read. All six inherited candidate Lean files were compared byte-for-byte with their previously reviewed integral/derivative artifacts. The prior independent integral and derivative reviews were read.

The seven retained project source snapshots and the toolchain/Lake manifest snapshots were independently compared to their exact local Git objects at project commit `3a8ed697d1f0366f8370efb2fa9e524b68d27e97`. Their SHA256 and Git blob identities match the retained receipts. The project specifies:

- Lean `leanprover/lean4:v4.33.0`
- Mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`

The relevant retained official db584 Mathlib files were independently rehashed against the official retrieval receipts and their declarations inspected. Three additional full official source files were independently fetched read-only and reproduce their returned Git blob SHA exactly: Operator.Basic, Operator.NormedSpace, and Group.Defs. The independent API receipt file records exact URLs, snapshot identities, and inspected ranges.

No `sorry`, `admit`, `axiom`, or `unsafe` token occurs in any of the eight candidate Lean files.

## Mathematical review

### 1. Actual forcing condition and quantifiers

Trace lines 32–46 define the actual spatial coordinate-Hölder domination on strictly interior source times. The little condition is:

For every ε > 0, there is δ > 0 such that the actual forcing satisfies the weighted spatial inequality with coefficient ε on Ioo t₀ (t₀ + δ), for every spatial x and y.

There is no assumed solution trace, fixed positive small-time decay power, initial-face positive-Hölder regularity, derivative witness, operator estimate, inverse/solver bound, or integrability oracle. The BCF-valued forcing is continuous in time and has the stated actual uniform pointwise bound ∀ s y, ‖q s y‖ ≤ C. These are explicit hypotheses, not derived from an unspecified solver.

The mono-right lemma correctly restricts source intervals: s < t ≤ T implies s < T. On every t ∈ Ioo t₀ (t₀ + δ), the same forcing coefficient and δ apply uniformly to every entry and spatial point.

### 2. Constants, signs, and singular powers

Write a = α/2, Mjk = heatHessianEntryHolderMoment n α j k, and Kjk = Mjk (1/a + 1/(1-a)). Under 0 < α < 1, both denominators are strictly positive and Kjk ≥ 0. The existing moment is a genuine derived Gaussian constant, with its nonnegative declaration and actual Gaussian cancellation estimate visible in the project source.

The inherited envelope is (t-s)^(a-1) (s-t₀)^(-a). Here a-1 and -a both lie strictly between -1 and 0. The inherited scalar proof establishes genuine integrability near both endpoints and an interval-length-independent bound. Its two midpoint powers cancel the interval scale exactly; no missing small-time factor is implicitly assumed.

The inherited integral proof establishes actual interval integrability of the Hessian convolution before estimating its raw integral. It uses Ioc t₀ t, excludes the initial endpoint by the carrier, and discards only the terminal singleton by volume-nullity. No neighborhood of either singular endpoint is discarded and no Hölder value at s=t₀ or s=t is assumed.

### 3. Direct strict raw-integral vanishing

Trace lines 71–107 derive |raw Hjk(t,x)| ≤ Kjk ε using the actual Gaussian-integral estimate and interval restriction.

Lines 112–131 then use ε = η/(Kjk+1). Since Kjk ≥ 0, Kjk+1 > 0 and ε > 0. The identity ε(Kjk+1)=η yields Kjk ε = η-ε < η, including the Kjk=0 case. The returned δ is positive and the conclusion holds for all x and all t in the punctured interval.

This proof precedes and is independent of BCF construction. It cannot obtain vanishing merely from a zero value assigned at t=t₀.

### 4. Canonical BCF equality and its initial value

Trace lines 138–148 define a global field by the actual raw-integral BCF constructor whenever t₀<t and a nonnegative weighted coefficient exists. The fallback is zero elsewhere. The little condition supplies a qualifying coefficient at every time in its punctured initial interval, so the fallback is not used to prove positive-time decay.

The application equality at lines 152–164 is genuinely coefficient-independent: whichever witness the constructor chooses, its underlying function is the same raw Gaussian interval integral. A later arbitrarily smaller coefficient can therefore estimate that same field. The constructor's continuity and boundedness are proved in the inherited integral leaf.

The named t₀ arguments now explicitly identify the initial time. At t=t₀ the qualifying branch is impossible by lt_irrefl, and the field is zero. This initial-value theorem is separate from the right-neighborhood proof; no raw-integral or derivative endpoint convention is substituted for the estimates.

### 5. BCF norm and right trace

Lines 179–200 first establish the nonnegative bound Kjk L, then use BCF.norm_le to convert uniform pointwise domination of the actual identified raw integral into a genuine BCF norm estimate. Strict norm decay again uses η/(Kjk+1).

Lines 227–243 apply the exact metric nhdsWithin characterization. Membership in Ioi t₀ supplies t₀<t. The distance condition gives |t-t₀|<δ and therefore t<t₀+δ. Thus the strict bound applies to the correct one-sided neighborhood. dist_zero_right converts the target distance to the actual BCF norm.

This is strong right convergence in the spatial sup norm, not merely pointwise convergence. It does not prove BCF-valued time continuity at every positive time.

### 6. Finite-family sup norm and rank zero

Lines 247–258 use tendsto_pi_nhds twice, for the two finite coordinate indices. The topology is the ordinary finite-product topology, and the pinned normed structure is its sup norm. Lines 262–274 compose the family limit with continuous_norm; the resulting scalar norm limit is genuinely a strong finite-entry sup-norm trace.

No positive-dimension premise is added. At n=0 the entry family is empty, the finite sup norm is zero, and the Pi construction remains valid. The optional operator coefficient is an empty sum and is zero. The inherited actual Fréchet bridge explicitly treats the singleton rank-zero domain using the zero map, rather than excluding it.

### 7. Actual iterated Fréchet derivative and ordinary operator norm

The optional leaf defines Kop = Σj Σk Kjk and proves Kop ≥ 0 by finite sums. Its norm estimate is derived from the existing coordinate-matrix operator bound and the actual Gaussian entry estimates. Factoring L out of the two finite sums is correct.

For η>0 it chooses ε=η/(Kop+1), obtains the forcing's δ independent of x, and restricts the weighted condition to the positive final time. It then rewrites the actual iterated fderiv of the raw Duhamel potential by the retained proved derivative identity before applying the operator estimate.

The retained identity was assembled from genuine first-derivative existence, equality of the global fderiv function to the Gaussian gradient, and actual differentiation of that gradient. No derivative or solver identity is a new hypothesis.

The norm is the ordinary curried continuous-linear-map operator norm. The independently inspected pinned Operator.Basic declares hasOpNorm using the infimum of all nonnegative bounds ‖A v‖ ≤ c‖v‖. Operator.NormedSpace supplies its normed-group structure, and the inherited local structures use that same declaration. The finite coordinate projections have operator norm at most one, yielding the l¹ entry majorant. No custom replacement norm or asserted derivative bound is used.

## Exact pinned API checks

The following inspected declarations match the applications and are bound to exact source/blob receipts:

- Metric.tendsto_nhdsWithin_nhds: Pseudo.Defs lines 864–868, with ∀ ε>0, ∃ δ>0, membership plus source-distance implication
- tendsto_pi_nhds: Topology.Constructions lines 807–809, used twice
- BoundedContinuousFunction.norm_le: Bounded.Normed lines 87–89, requiring nonnegative C and equivalent to pointwise norm domination
- BCF.ofNormedAddCommGroup and its definitional coercion: Bounded.Normed lines 116–129
- Finite Pi sup seminorm and normed instances: Group.Constructions lines 293–350 and 409–426, with no Nonempty index requirement for the normed structure
- continuous_norm: generated additive declaration at Group.Continuity lines 127–130
- dist_zero_right and norm_zero: generated additive declarations at Group.Basic lines 51–52 and 134–135
- Ordinary CLM opNorm and opNorm_le_bound: Operator.Basic lines 172–201
- Global CLM normed-group structure: Operator.NormedSpace lines 154–167

The inherited raw-integral and fderiv theorem signatures were also compared directly with the new call sites. Complete transitive import availability, typeclass search, simplifier behavior, and tactic elaboration are not claimed verified.

## Scope and execution boundary

The README and remaining-bridge document accurately keep the full C0/C1/C2 trace assembly, positive-time BCF time regularity, time/slab Hölder estimates, parabolic evolution identity, literal-C² atlas localization, full weighted derivative-graph Banach carrier, nonlinear closure, positivity, manifold geometry, gauge recovery, and weak-competitor uniqueness OPEN. The little forcing condition itself does not establish that the full nonlinear geometric forcing satisfies it.

The arbitrary literal-C² initial-data, arbitrary-model I, manifold-only BoundarylessManifold I M, rank-zero-inclusive, common-closed-interval, ordinary-endpoint-component-derivative contract remains unchanged. No C³, initial positive-Hölder, positive-dimension, global I.Boundaryless, or stronger competitor premise was introduced.

This reviewer ran no Lean compiler, proof runtime, verification toolchain, build, or test. No dependency/toolchain/cache was installed or downloaded. No candidate source, repository tree, branch, PR, CI configuration, verification gate, or publication was changed by the reviewer. Output writes are confined to this isolated review directory; the author separately made the authorized seven named-argument additions. Read-only official source retrieval and exact-byte hashing were used solely for static inspection.

**Point 4 remains OPEN. Exact4.33 verification remains mandatory before any verified or merge-ready claim.**
