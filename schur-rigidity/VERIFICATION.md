# Verification record

Status during preparation, 2026-09-06:

- All new geometric modules and `Solution.lean` compile with Lean 4.33.0.
- Challenge compiles with Mathlib-only paths. The negative control confirms
  that the local `PoincareCurvature` library is inaccessible.
- Exactly four Challenge theorem placeholders; no definition placeholders or
  proof holes in the new Solution/proof modules were found in the source scan.
- Full `lake build` passed (3539 jobs).
- Pinned Comparator replay passed for all four selected theorems and all eight
  definitions. NanoDa and Lean's default kernel both accepted the Solution.
  This local replay used the explicitly opted-in unsandboxed macOS fallback.
- Hosted Linux verification has not yet been recorded for this candidate.
- Lean's `#print axioms` reports exactly `propext`, `Classical.choice` and
  `Quot.sound` for each selected theorem and definition; no `sorryAx`.
- All twelve inherited Lean files are byte-identical to their documented
  source commit. Metadata validates against the live formalization.yaml
  schema (v0.4).

No submission, editorial approval or registration has been performed for this
new entry. The Linux receipt will be added after the hosted check completes.
