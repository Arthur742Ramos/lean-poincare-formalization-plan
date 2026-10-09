# Independent bounded replacement review: frozen-002

## Verdict

**SOURCE-ONLY APPROVE for frozen-002.** The two established frozen-001 composition-basepoint defects are repaired. No additional concrete mathematical or pinned-API blocker was found. This does not assert successful Lean elaboration, exact-toolchain verification, a compiled axiom audit, or readiness to merge.

Frozen-001 remains **SOURCE-ONLY REJECT** under its separate sealed report and manifest. This approval applies only to the four exact frozen-002 source hashes listed in `REVIEWED-SOURCE-MANIFEST.json`.

## Exact scope and review

- `C0GaussianEndpoint.lean` now first constructs `houter : ContinuousAt (heatFlowPathBcf f) (smoothingTime 0)` using `smoothingTime_zero`, then composes `houter.comp ht`. The outer and inner point arguments now agree with exact db584 `ContinuousAt.comp`.
- `C2MetricVelocityExtension.lean` now first constructs `hcenterAt : HasDerivAt (...) (v.tensor x u w) (t₀ - t₀)` using `sub_self`, then composes it with `hshift` at `t₀`. The required outer derivative point is supplied before the composition call. The resulting scalar derivative is multiplied by `1`, and the final `simpa only [mul_one]` has the appropriate result type.
- Exactly those two proof blocks changed. Every declaration statement, hypothesis, import, data definition, compact-buffer argument, reconstruction proof, C² proof, positivity proof, and other source byte is preserved. The two other files are byte-identical to frozen-001.
- The already checked 63-project-module graph and exact immutable baseline bindings remain applicable: no project import or module header changed. The mathematical checks and external-transitive audit limitations in the frozen-001 report are inherited unchanged.
- Higher-order inference from the derivative point `t₀ - t₀` has not been exercised by a compiler. Explicitly naming `(h := fun t : ℝ => t - t₀)` in that composition is an optional precaution discussed with the author, not an established defect in this source-only review. Any such further edit must have a separately frozen identity.

## Reversible exact-byte evidence

The supplied forward patch was applied with zero fuzz only to fresh review copies of frozen-001; all four resulting files compare byte-for-byte with frozen-002. The supplied reverse patch was applied with zero fuzz only to fresh review copies of frozen-002; all four resulting files compare byte-for-byte with frozen-001. The rejected original proof bytes are retained under `reverse-reconstruction/` rather than overwritten or discarded.

- Forward patch SHA-256: `7aba4400f67623dfcd952692ea7e7830d5ad78cc83fe11595781298af0ee1455`
- Reverse patch SHA-256: `6e3137ecb7aec5f454f95858802d21c859d64e09ab813b8942c3048fce37ac3c`
- Unchanged positivity source SHA-256: `45261b684e7add6c9e83eca9266777b8d12b6c7c598084d1d9e10b74f7867274`
- Unchanged finite-atlas source SHA-256: `474af52d61a6a90197d92ee24517952863cc834b66c3158c98182e78de21771f`
- Repaired Gaussian endpoint source SHA-256: `dd5dcbe309cc2e41eb60c7ed6e95a4e87161272abdc207658ff249f1cb077fa8`
- Repaired metric extension source SHA-256: `31dbda60b3c654061973de61557cb4dcabe2ab22f32361ba76937f697d84159c`

No protected source was edited. No Lean compiler/runtime, build, cache operation, installation, or publication was performed. Exact Lean 4.33 verification and exported-signature/compiled-axiom checks remain pending.
