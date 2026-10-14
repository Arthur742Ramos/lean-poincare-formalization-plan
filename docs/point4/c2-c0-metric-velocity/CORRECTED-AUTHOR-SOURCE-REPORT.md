# C² metric endpoint extension with continuous prescribed velocity

Status: independently source-reviewed construction-shaped Lean candidate, not compiled or kernel-verified. Frozen-001 was independently source-rejected for two composition-basepoint proof defects, with no mathematical obstruction found. Frozen-003 changes only those two proof blocks, with an explicit inner-function argument in the derivative composition, and has received separate exact-byte SOURCE-ONLY APPROVE. The sealed replacement report is copied into source-only-review-frozen-003. Its SHA-256 is `07c9bce974d0fe9b4bf4d7044263bdf520dfeecc018873078674c4481ee4c5fa`. Frozen-002 also received SOURCE-ONLY APPROVE and is preserved as a source-approved, superseded intermediate snapshot; frozen-003 is the final source-approved identity. All three remain exact4.33-unverified. This is an endpoint extension only; it is not a Ricci-flow solution and does not close Point 4.

## Exact intended result

For arbitrary finite-dimensional complete real model E, arbitrary model with corners I, a compact Hausdorff smooth manifold M with `BoundarylessManifold I M`, any literal `Bundle.ContMDiffRiemannianMetric I 2 E TM` g₀, any real t₀, and any continuous symmetric section v of the actual covariant-two-tensor bundle, construct g : `RicciFlow.MetricFamily` with g(t₀) = g₀ and ordinary `HasDerivAt` of every fixed component equal to v(x)(u,w) at t₀.

The velocity regularity is explicit in `ContinuousSymmetricVelocity`:
- tensor : ∀ x, TM x →L[ℝ] TM x →L[ℝ] ℝ
- continuous : Continuous (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (tensor x))
- symmetric : ∀ x u w, tensor x u w = tensor x w u

The background norm is selected from the literal g₀ in the exported statement. There is no supplied regularizer, density theorem, solver, atlas witness, positivity witness, positive dimension, or global `I.Boundaryless` hypothesis. No spatial derivative of v is assumed.

## Actual construction

1. Choose the existing finite smooth preferred tangent trivializing cover, subordinate simultaneously to original preferred chart sources and frame domains. Choose `Module.finBasis ℝ E` internally.
2. Transport each compact partition support to finite real coordinates. Manifold boundarylessness proves openness of the genuine preferred coordinate domain.
3. Construct a compact C² coordinate buffer equal to one near the transported support from Mathlib's compact-between and smooth manifold cutoff facts. Multiply the actual continuous tensor/frame coefficients by that buffer. This yields actual bounded uniformly continuous scalar functions, with no regularization witness hypothesis.
4. Apply the existing Gaussian semigroup at τ(h) = sqrt(abs h). Symmetrize coefficient matrices and reconstruct actual tangent bilinear forms through `localTensorOfMatrix`, then sum with the fixed finite partition. Call this A(h).
5. Establish A(0) = v and continuity at zero of every fixed component. The ordinary two-sided derivative of h A(h) at zero is v. C² regularity of each nonzero-parameter slice comes from the actual Gaussian ContDiff theorem and smooth reconstruction. No differentiated heat-time coefficient is required.
6. Read g₀ in each fixed model frame on its compact partition support. Existing finite-dimensional metric-cone openness gives a positive radius εᵢ. Actual Gaussian contraction gives finite matrix bounds Bᵢ. A single positive δ, chosen from the finite sum Σᵢ Bᵢ/εᵢ, satisfies δ Bᵢ < εᵢ for every i, including the empty index case.
7. Clamp the signed amplitude a(h) = max(-δ, min(δ,h)). Define the actual tensor g₀ + a(h) A(h). Convex partition synthesis and the compact radii prove positivity for every real h. Reify the bounded-unit-ball field using the existing finite-dimensional positive bilinear-form theorem. At h = 0 return g₀ literally; at h ≠ 0 use the reconstructed C² metric. Finally shift h = t − t₀.

Rank-zero and empty-manifold cases are covered by the same construction: the positivity-radius helper explicitly removes a Nontrivial model premise, and the common-amplitude helper has no nonempty index premise.

## Source files

- C0GaussianEndpoint.lean: genuine Gaussian path, uniform bound, C² nonzero slices, ordinary signed endpoint derivative
- C0FiniteAtlasGaussian.lean: actual C⁰ velocity type, constructed atlas/buffers/coefficients, symmetric reconstruction, exact A(0) = v and ordinary component jets
- C0EndpointCompactPositivity.lean: compact model metric-cone radii and a derived all-parameter positivity reserve
- C2MetricVelocityExtension.lean: clamped all-real-time positive C² metric family and the exported endpoint statement

The current source identity is frozen-003; source-overlay contains those exact four source files at their intended integration paths. Frozen-001 and its rejection are historical and preserved. The optional primitive-buffer refinement is isolated and is not part of frozen-003. Frozen snapshots are source-review identities, not verified artifacts.

## Provenance and qualification

The canonical contract is exact project commit `3a8ed697d1f0366f8370efb2fa9e524b68d27e97`. The inspected LocalExistence and TimeDependent bytes at source baseline `90cc7ebed996f28acb57ef9948d37f114088bd4d` agree with that exact contract. Project/API Gitblob SHA1 and SHA-256 receipts are under pinned-sources, and complete reachable immutable project import graphs are saved separately.

Mathlib API files were retrieved read-only from the official repository at `db584cd6d46c92f209a44c0f1c829460d327499d`. Their local bytes match the returned Gitblob receipts. They support source review only. No complete authenticated local db584 tree is present; the unexpanded external import frontier is explicitly recorded. No compatible4.33 or kernel pass has occurred.

New files intentionally use legacy headers to consume existing legacy analytic leaves. The complete reachable project graph has no modern-module-to-legacy-file edge. Do not add a modern aggregate import of these legacy candidate files without a coherent source/header compatibility pass. Inherited modules are unchanged by this task.

## Still unestablished

- Elaboration, instance synthesis, simplifier behavior and theorem application under actual pinned Lean4.33/db584
- Full inherited external dependency/header graph and package build
- Any strong C²-in-time trace; it is unnecessary for this endpoint result and is not claimed
- Positive-time Ricci–DeTurck or pure Ricci existence, fixed-original-atlas gauge reconstruction, or uniqueness against the canonical weak competitors

There is no presently identified mathematical obstruction to this endpoint-only construction. The displayed Lean theorem is a candidate, not evidence that its source checks.

## Actions deliberately outside this task

No Lean/compiler/toolchain/cache/dependency downloads, Lean execution, changes to existing project trees, publication, CI edits, registry submission, credential actions, or security changes were performed by this worker.
