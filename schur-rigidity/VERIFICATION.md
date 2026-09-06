# Verification record

Verified artifact: `4317d35a3cf3bbf02859fcd811e8dacc83f51739`, 2026-09-06.
This receipt was recorded after that immutable source commit; later receipt
edits do not change the selected submission artifact.

- All new geometric modules and `Solution.lean` compile with Lean 4.33.0.
- Challenge compiles with Mathlib-only paths. The negative control confirms
  that the local `PoincareCurvature` library is inaccessible.
- Exactly four Challenge theorem placeholders; no definition placeholders or
  proof holes in the new Solution/proof modules were found in the source scan.
- Full `lake build` passed (3539 jobs).
- Pinned Comparator replay passed for all four selected theorems and all eight
  definitions. NanoDa and Lean's default kernel both accepted the Solution.
  This local replay used the explicitly opted-in unsandboxed macOS fallback.
- Hosted Linux verification **passed**, using real Landrun rather than the
  macOS fallback. The Solution build completed successfully (3536 jobs).
  Comparator, NanoDa, Lean's default kernel and the isolated Challenge test
  all passed.
- Lean's `#print axioms` reports exactly `propext`, `Classical.choice` and
  `Quot.sound` for each selected theorem and definition; no `sorryAx`.
- All twelve inherited Lean files are byte-identical to their documented
  source commit. Metadata validates against the live formalization.yaml
  schema (v0.4).

## Hosted receipt

- [Run 34043491915](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/34043491915)
- [Job 101514321502](https://github.com/Arthur742Ramos/lean-poincare-formalization-plan/actions/runs/34043491915/job/101514321502)
- Reported head SHA: `4317d35a3cf3bbf02859fcd811e8dacc83f51739`
- Result: `success`, completed 2026-09-06 at 16:08:12 UTC (19m 5s).
- Log at 16:07:57 UTC: NanoDa accepted, Lean's default kernel accepted,
  Comparator reported that the Solution is okay, and replay passed.
- Log at 16:08:10 UTC: Challenge compiled with dependency libraries only;
  the local-library import negative control passed.

Pinned verifier revisions, also recorded in `scripts/verify-comparator.sh`:

| Tool | Revision |
| --- | --- |
| Comparator | `68a064109f01c08f47c8edc9f51d6a2bbffaa188` |
| Lean4Export | `15f6055e299ad5b89345e533cc2192f4cc00f659` |
| NanoDa | `68d5ca9db226849b41a6fff59d796ff19d0a8840` |
| Landrun | `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4` |

Builds retain non-fatal style, deprecated-API and unused-section-variable
warnings. The four intentional Challenge theorem placeholders are separate
from the verified Solution, whose axiom closure contains no `sorryAx`.

The artifact passed these independent mechanical checks. Palomar intake
`l20vtgq7gct2` was subsequently created on 2026-09-06 at 16:21:03 UTC and queued
its own hosted verification. No Palomar editorial result or public registration
is claimed; see `SUBMISSION.md` for the distinct intake receipt.
