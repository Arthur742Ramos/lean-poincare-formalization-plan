# Independent review: UC weighted Gaussian Hessian trace

## Verdict

**APPROVE — SOURCE ONLY, UNCOMPILED.** No blocking mathematical or static source/API defect was found in the exact Lean bytes identified below. This approves the supporting Euclidean leaf for subsequent isolated exact-toolchain verification. It is not a Lean elaboration result, kernel check, CI result, merge approval, or completion of canonical Point 4.

- Reviewed file: `EuclideanHeatRegularizerC2Trace.lean`
- SHA-256: `ca8598bd4eddf118a7bf2afa097e232cd872e8ffc7f3b2b9fe76bdf913531f44`
- Exact size: 23,557 UTF-8 bytes, 457 lines
- Project baseline: `3a8ed697d1f0366f8370efb2fa9e524b68d27e97`
- PR132 context, not an import: `c72c7e35282f6697e5911464a8c043e0e3c26d11`
- Mathlib baseline: `db584cd6d46c92f209a44c0f1c829460d327499d`
- Declared toolchain, not executed: `leanprover/lean4:v4.33.0`
- Review date: 2026-10-05 UTC

The source hash was checked before and after review. The candidate was not edited. The completed producer `SOURCE-REPORT.md` and `REVIEW-HANDOFF.md` were also read; their mathematical account and explicit scope limits agree with the Lean statements.

## 1. Exact input provenance

`INPUT-HASH-AUDIT.json` independently recomputes SHA-256, Git's SHA-1 over `blob <byte-length>\0<exact-bytes>`, and sizes for all supplied dependency snapshots. All 19 source snapshots match their receipt hashes: 13 project receipts and six Mathlib receipts. All entries in the completed producer manifest match their recorded hashes and sizes.

The 12 project-baseline snapshots were additionally compared byte-for-byte with read-only exact-commit Git reads. The c72 tree independently names blob `437d77b93fe712ccfedaf528cd172693eda81047`. The c72 source blob was not initially available for a local no-lazy-fetch content read; an independent read-only official GitHub connector read at the exact c72 commit supplied the complete source. Its exact bytes and recomputed blob hash match the retained context snapshot. The unavailable local content read is recorded, not represented as a successful local read.

For all six supplied Mathlib snapshots, fresh independent official GitHub reads at db584 confirm the full-file blob SHA reported by the producer receipts. The reviewer also retrieved exact official db584 sources for the missing pseudometric, integration-translation, integrability-sum, and square-root APIs. These exact source files and receipts are retained under `official-api-source/`. No package or executable dependency was downloaded.

## 2. Kernel identity, signs, and domination (lines 34–65)

The actual imported Hessian kernel is

`K_h(z) * (z_j*z_k/(4*h^2) - if j=k then 1/(2*h) else 0)`.

Its diagonal has the negative constant term required by twice differentiating the Gaussian. The first derivative kernel used later is `K_h(z) * (-z_k/(2*h))`; the second derivative witness has the correct positive quadratic term and negative diagonal term. All convolutions use the same displacement `x-y`, with derivatives taken in x, so no unintended reflection sign is introduced.

The positive majorant is `M_k = K_h * (z_k^2/(4*h^2) + 1/(2*h))`. Nonnegativity and integrability require and receive `0<h`. Its imported mass is exactly `1/h`. For diagonal entries, the triangle bound gives `|K_jj|≤M_j`; the subsequent pair estimate safely uses `M_j+M_j`. For off-diagonal entries, the imported mixed-entry bound gives `|K_jk|≤M_j+M_k`. This factor-two domination is intentionally non-sharp but valid for every j,k.

The imported zero-mass/cancellation theorem applies to the actual signed kernel, with q's continuity supplying measurability and its BCF norm supplying the uniform bound. There is no assumed zero trace or substituted abstract solver estimate.

## 3. Actual first moments and real powers (lines 67–115)

Let `G_r = gaussianAbsMoment r`, the actual absolute moment of the time-one one-dimensional heat kernel. The candidate's fixed coefficient is

`c(ell,k) = if ell=k then G_3/4 + G_1/2 else G_1`.

For ell=k, the imported integral is

`(1/(4*h^2)) * ((sqrt h)^(1+2)*G_3) + (1/(2*h)) * ((sqrt h)^1*G_1)`.

Multiplication by h gives `sqrt h * (G_3/4 + G_1/2)`. The explicit real-power-to-natural-power step uses the exact db584 `Real.rpow_natCast`; the cube reduction uses `(sqrt h)^2=h` under `h≥0`. All division cancellations have `h≠0` derived from `0<h`.

For ell≠k, independence of Gaussian product coordinates gives `(sqrt h*G_1)*(1/h)`, hence `h*moment = sqrt h*G_1`. This is the first absolute coordinate moment times the majorant's exact mass, rather than an incorrectly scaled third moment. The candidate uses r=1 in both imported moment theorems and proves their `0≤r` prerequisites. The Gaussian moments are integrable at orders one and three; their use is a property of the kernel, not a Holder premise on q.

Consequently `C(j,k)=sum_ell (c(ell,j)+c(ell,k))` is a finite, time-independent actual Gaussian constant, including when j=k. No unproved positive-rank restriction or dimension-dependent change of norm enters this calculation.

## 4. UC-derived affine increment bound (lines 117–149)

For a fixed positive delta and nonnegative epsilon, near points use the supplied modulus. Far points use `|q(y)-q(x)|≤2*norm q` and `delta≤norm(y-x)`. The coefficient `L=2*norm q/delta` is nonnegative and satisfies `L*delta=2*norm q`. The finite Pi sup norm obeys `norm(x-y)≤sum_ell |(x-y)_ell|`, including dimension zero.

This proves exactly

`|q(y)-q(x)| ≤ epsilon + L*sum_ell |(x-y)_ell|`.

The argument does not assert that q is Lipschitz, C1, C2, or Holder with a positive exponent. The additive epsilon is essential. The source's local bound is correctly parameterized; the global uniform-continuity quantifier is introduced only in the later uniform trace theorem.

## 5. Integrability, translation, and quantitative estimate (lines 151–244)

For `M=M_j+M_k`, the candidate explicitly constructs integrability of M and each `|z_ell|*M(z)`. Addition, finite sums, translation/reflection `y↦x-y`, and multiplication by the fixed constants epsilon and L preserve the stated integrability. The dominating integrand is exactly

`M(x-y)*epsilon + L*sum_ell (|(x-y)_ell|*M(x-y))`.

`norm_integral_le_of_norm_le` is applied with this integrable majorant and a pointwise, hence almost-everywhere, bound. The actual convolution is first replaced by its increment form using genuine signed-kernel cancellation. Integral sums and additions receive the required individual integrability proofs. The Lebesgue measure on the finite Cartesian power is invariant under translations and negation; the exact db584 additive translation APIs have the required `x-y` orientation.

The mass and moment calculations are

- `h * integral M = 2`
- `h * sum_ell integral (|z_ell|*M(z)) = sqrt h * C(j,k)`

The resulting estimate is therefore exactly

`|h * heatHessianEntryConvolutionND h q j k x| ≤ 2*epsilon + (2*norm q/delta)*sqrt h*C(j,k)`.

There is no missing h, inverse h, factor two, absolute value, or reversed inequality in the argument. The final multiplication by h uses its positivity. No fixed positive power rate is claimed for the UC-only result: the coefficient L depends on the chosen modulus delta.

## 6. Genuine BCF and its norm trace (lines 246–368)

The separate bounded-data estimate uses actual kernel-pair domination without cancellation and gives `|h*HessianEntry|≤2*norm q`. This needs no uniform continuity. The BCF constructor uses the imported continuity theorem for the actual convolution and this finite bound. Its positive-time apply theorem is literally the Gaussian integral, by definition; it does not use a Holder constructor.

The globally defined path returns this actual BCF whenever `h>0`, and zero otherwise. Its right-limit proof uses only the positive branch, so the zero extension does not manufacture the claimed positive-time convergence.

For each eta>0 the uniform proof first chooses delta from the global UC modulus with epsilon=eta/4. Delta is independent of x and h. The subsequent scalar tail coefficient A depends only on q, delta, j,k. Continuity of `A*sqrt h` supplies a positive-time neighborhood with its value below eta/2. The kernel estimate is then at most eta/2 plus a strictly smaller eta/2 term, uniformly in every x. The order of these quantifiers is correct.

The exact db584 `Metric.tendstoUniformly_iff` uses `dist(limit x, value h x)`. Thus the proof's `zero_sub`/`abs_neg` rewrites have the correct orientation. The BCF proof uses the eta/2 uniform tail and the exact `BoundedContinuousFunction.norm_le` API to obtain `norm(path h)≤eta/2<eta`. Its statement is genuine Tendsto in the BCF norm topology at `nhdsWithin 0 (Ioi 0)`.

## 7. Lower jets and actual derivative witnesses (lines 370–454)

The value trace follows from the actual Gaussian contraction: `|h*H_h q|≤h*norm q`. The first coordinate jet uses the actual gradient L1 bound `norm q/sqrt(pi*h)`. For `h>0`, `sqrt(pi*h)=sqrt pi*sqrt h`; nonzero square roots and `(sqrt h)^2=h` yield the exact bound `(norm q/sqrt pi)*sqrt h`. The division and square-root prerequisites are provided. Both lower traces require bounded C0 data only.

The conjunction at lines 421–434 quantifies over every first coordinate and every ordered pair j,k. It is full entrywise Hessian coverage, not merely a diagonal or Laplacian trace. There are finitely many entries at each n; the declaration states the individual entrywise uniform limits, rather than adding a finite-product/operator-norm theorem not present in the file.

The first final witness differentiates `a↦h*H_h q(update x k a)` at `x_k` and produces the actual h-weighted Gaussian gradient. The base-point update is reduced by `Function.update_eq_self`. The second witness differentiates the actual h-weighted k-gradient along coordinate j at `x_j` and produces the actual h-weighted Hessian entry. The imported base theorem handles both j=k and j≠k; the candidate imposes no distinctness premise. Constant-scalar differentiation uses the db584 `[to_fun]` generated `HasDerivAt.fun_const_smul` API and the real scalar multiplication-to-multiplication simplification. No derivative of q occurs in the hypotheses.

The exact project baseline separately contains the actual Frechet gradient/Hessian identification and `contDiff_two_heatSemigroupND` for bounded continuous q at positive time. The new leaf does not replace those witnesses by a desired estimate.

## 8. Finite/rank-zero case and contract boundaries

No theorem assumes `n>0`. The space `Fin 0→R` is a singleton. The value trace remains valid there; first-coordinate and Hessian-entry statements are vacuous because there are no coordinate indices. The imported norm/sum estimate expressly handles dimension zero. No witness is extracted from an empty index set, and there is no division by n.

For the c72 negative slice `f+t*H_{-t}(q)`, write `h=-t>0`. Its perturbation is `-h*H_h(q)`, so the new h-weighted spatial traces have the correct magnitude; the sign must still be carried through an explicit future package identification. The source does not already prove that branch/package corollary. q may be the stored initial Laplacian, whose UC is derived in c72 from UC of the initial Hessian entries, without differentiability of q.

Canonical Point 4 remains **OPEN**, with literal C2, M-only Boundaryless, and ordinary closed-time endpoint requirements unchanged. This leaf supplies no finite-atlas positivity, localization/transition compatibility, ordinary manifold endpoint family, nonlinear existence, gauge completion, or weak uniqueness. It does not solve backward heat evolution. No PR132 package integration, finite-entry product-norm assembly, or manifold endpoint theorem is claimed by this review.

## 9. Static API findings and required next gate

Blocking mathematical findings: none.

Blocking static exact-API findings: none found. Exact project declaration signatures and retained official db584 sources were inspected for the main kernel, moment, cancellation, continuity, norm, metric-convergence, integration, power, square-root, and derivative-scaling calls. The `integral_finset_sum` and `integrable_finset_sum` names are deprecated aliases in db584 but remain available; their use is a warning-level maintenance issue, not a missing API.

No `sorry`, `admit`, or `axiom` token occurs in the candidate. This lexical observation is not theorem verification. Elaboration, inference, tactic execution, heartbeat sufficiency, imports' compiled availability, and kernel acceptance cannot be established by this review. The exact frozen source must still pass the pinned Lean/toolchain verification and required review gates before any verified or merge-ready claim.

## Actions not performed

No Lean, lake, elan, compiler, proof runtime, toolchain probe, package setup, dependency/cache download, candidate mutation, repository write, CI mutation, publication, or merge was performed. Python was used only for exact byte/hash/JSON bookkeeping; Git and GitHub connector usage was read-only source inspection. All reviewer files are newly created in this review directory.
