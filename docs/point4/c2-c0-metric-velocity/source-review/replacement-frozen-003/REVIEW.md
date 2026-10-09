# Independent bounded replacement review: frozen-003

**SOURCE-ONLY APPROVE for frozen-003.** Both established frozen-001 defects are repaired, and the derivative composition now explicitly fixes its inner function. No additional concrete mathematical or exact-pin API blocker was found. Lean 4.33 elaboration, exported-signature checks, and compiled axiom verification remain pending.

## Binding and preservation

This approval binds only the four files in `REVIEWED-SOURCE-MANIFEST.json`:

- C0EndpointCompactPositivity: `45261b684e7add6c9e83eca9266777b8d12b6c7c598084d1d9e10b74f7867274`
- C0FiniteAtlasGaussian: `474af52d61a6a90197d92ee24517952863cc834b66c3158c98182e78de21771f`
- C0GaussianEndpoint: `dd5dcbe309cc2e41eb60c7ed6e95a4e87161272abdc207658ff249f1cb077fa8`
- C2MetricVelocityExtension: `0c6c921536d3cade268948431dd254dd7c602cc04f2d8d4aa7365ab6c39793b7`

Compared with frozen-001, exactly the two previously identified proof blocks change. All declaration statements, hypotheses, imports, mathematical data definitions, atlas/buffer construction, reconstruction, symmetry, C² regularity, positivity, and other bytes are preserved. Compared with source-approved frozen-002, only the derivative composition call gains `(h := fun t : ℝ => t - t₀)`.

## API review

1. `ContinuousAt (heatFlowPathBcf f) (smoothingTime 0)` is now established by rewriting `smoothingTime_zero` before `.comp ht`. This supplies the actual outer continuity point required by exact db584 `ContinuousAt.comp`.
2. `HasDerivAt (...) (v.tensor x u w) (t₀ - t₀)` is now established by rewriting `sub_self` before composing with `hshift`. The call is `hcenterAt.comp t₀ (h := fun t : ℝ => t - t₀) hshift`. Exact db584 `HasDerivAt.comp` has the implicit inner function parameter named `h`, so the named argument is valid and avoids inference from the repeated-variable expression `t₀ - t₀`. The result derivative is the supplied velocity times one, which the final `mul_one` simplification removes.

The full mathematical findings, 63-module immutable project graph audit, source/API byte receipts, and external-transitive limitations are inherited from the sealed frozen-001 report. No graph edge, import, or module header changed. The export's explicit omission of an ambient RiemannianBundle instance and its exact elaborated signature remain a precaution for the compiler gate, not an established blocker in this bounded source review.

## Exact reverse proof bytes

The forward patch was applied with zero fuzz only to fresh review copies of frozen-001. Every resulting file matches frozen-003 byte-for-byte. The reverse patch was applied with zero fuzz only to fresh review copies of frozen-003. Every resulting file matches frozen-001 byte-for-byte. Original rejected proof bytes are retained in `reverse-reconstruction/`.

- Forward patch SHA-256: `15351558b7c673db8542f791b67c8753931c6045f3547ff19f33d3edff8118b5`
- Reverse patch SHA-256: `c097b685fedc8ed6ad16d063723b78201d4b4951276e847d9a27a36f591d64a8`

Historical verdicts are preserved: frozen-001 is source-rejected; frozen-002 is source-approved but superseded by this explicit-inner-function precaution. No theorem statement was weakened and no mathematical assumption was added. No protected source edits, Lean compiler/runtime execution, builds, installations, cache operations, or publication occurred.
