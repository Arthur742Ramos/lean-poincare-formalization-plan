# Weighted time kernel: independent source-only review

Review date: 2026-10-05 UTC

Review verdict: favorable mathematical and pinned-API static review. Source-only
approval is granted for clearly labeled, reviewed draft integration. These
remain uncompiled source candidates; this is not exact-toolchain verification,
approval to merge, a new required gate, or a Point 4 completion claim.

## Exact reviewer inputs

Frozen source directory:
`/workspace/shared/poincare-weighted-time-kernel-source-20261005`.

All five supplied frozen hashes were checked and match:

- `WeightedTimeKernel.lean`:
  `20ceba4efe5d3c2d0d302220e94db8394496be16ee336382c4d1049b470fc3a5`
- `WeightedHessianTimeEnvelope.lean`:
  `4283e582912f8556266e2944e9453a2ed475522e8d4e95a5cba19ec39deb070d`
- `WeightedDuhamelIntegrand.lean`:
  `77da0c8aaad5fc44aae5dfd9bb9958da90528112d93eedba7082647f64d4a577`
- `pinned-source-receipts.json`:
  `7e9177adcb875a6982a3ca9273198ab42265d53e91b20ee19371919215845544`
- `source-only-manifest.json`:
  `cabb6f0c12179eb2ab0bbfa451ca48a707f14fd6f5aeea501061a3e521e7c16e`

The accompanying review manifest binds every preserved input file by exact byte
length and SHA256, as well as this report. All seven dependency snapshots
independently reproduce their recorded Git blob SHA and SHA256. The retained
Gaussian theorem suffix is byte-identical to the original. No `sorry`, `admit`,
`axiom`, or `unsafe` token occurs in the three authored Lean files.

Target toolchain: `leanprover/lean4:v4.33.0`.
Target Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.
Inspected project base: `3a8ed697d1f0366f8370efb2fa9e524b68d27e97`.

## Reviewed scope and proof semantics

The independent mathematical and source-API review covers the scalar theorem
and its wrappers in `WeightedTimeKernel.lean`, and the exact exponent bridge
and scalar wrappers in `WeightedHessianTimeEnvelope.lean`. The separate
Gaussian helper was checked for theorem-suffix identity and separation from
the scalar argument, not independently compiler-verified or promoted to an
integrated Gaussian theorem.

The scalar theorem has precisely the hypotheses `t₀ < t`, `0 < a`, `a < 1`.
It concludes actual real interval integrability of
`(t - s) ^ (a - 1) * (s - t₀) ^ (-a)` and an integral bound of
`1 / a + 1 / (1 - a)`. It assumes no integrability, solver, inverse, Gaussian
operator estimate, or operator norm bound.

- `WeightedTimeKernel.lean:43–68` establishes actual product integrability.
  Each singular factor uses `intervalIntegrable_rpow'`; only the nonsingular
  factor is required continuous on the relevant compact closed half interval
- Both substitutions have correct orientation. `comp_sub_left` first gives
  the reversed interval; `.symm` restores `m..t`. `integral_comp_sub_left`
  itself produces `0..t−m` without a missing sign
- The pinned `comp_sub_*` declarations have default endpoint-finiteness
  arguments. For real-valued functions these are automatic, not additional
  analytic hypotheses
- `integral_mono_on` requires domination on `Icc`; the candidate supplies it,
  including endpoints. `Real.rpow_nonneg` permits the singular factor's zero
  base, while every negatively powered factor being bounded below has a
  strictly positive base
- The exact integrals use exponents `−a` and `a−1`, both greater than `−1`.
  The primitive exponents `1−a` and `a` are nonzero
- Scale cancellation correctly uses `rpow_add` only after proving `h>0`
- `IntervalIntegrable.trans` and adjacent-integral addition join the actual
  integrability proofs and bounds
- `WeightedHessianTimeEnvelope.lean:23–42` gives exact function equality at
  `a=α/2`, then derives precisely `0<α/2<1` from `0<α<2`

The inspected db584 declaration signatures match every application, including
the continuous-factor multiplication order and the monotonicity arguments.
Additional pinned public-import headers confirm availability of the
power-continuity and interval-integral APIs. In particular:

- `Integrals.Basic` publicly imports `Pow.Deriv`, which publicly imports
  `Pow.Continuity`; its public chain continues through `Pow.Asymptotics`,
  `Pow.NNReal`, and `Pow.Real`
- `Integrals.Basic` publicly imports `NonIntegrable`, which publicly imports
  `IntervalIntegral.FundThmCalculus`; that publicly imports
  `Integral.DominatedConvergence`, which publicly imports
  `IntervalIntegral.Basic`

No mathematical defect, hidden solver/operator hypothesis, or concrete
source-level API mismatch was found. This review does not assert successful
Lean elaboration or complete compiled-import availability. Lean's totalized
real powers have finite endpoint values; those values do not replace the
singular integrability proof. All bases used in domination are nonnegative,
and the bounded negatively powered bases are strictly positive, so the
negative-base convention introduces no change to the claimed integral.

## Optional cached development probe: blocked and not admitted

No development probe is admitted or needed for this handoff.

The existing development runtime is Lean `4.35.0-rc2` at
`/workspace/shared/higher-cell-tools/lean-4.35.0-rc2-linux/bin/lean`.
Its existing Mathlib checkout is
`/workspace/shared/higher-cell-attachment-lean/.lake/packages/mathlib`,
commit `065356127b1dc0016f66b7283ce0ce2c4055aa55`.

`Mathlib/Tactic/Linarith.olean` and `Mathlib/Tactic/Ring.olean` exist there.
However, the direct required compiled import
`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.olean` and its private/server
companions are absent. Therefore the unchanged scalar cannot currently be
admitted under the no-download/no-cache-write constraint. Nothing was rebuilt
or downloaded to overcome this blocker.

The conditional minimal plan, only for a later explicit coordinator admission:

1. Recheck frozen hashes and require all three direct compiled imports already
   present; otherwise stop before launching Lean
2. Use the absolute cached Lean binary directly, with existing package build
   directories in `LEAN_PATH`. Do not use Lake, elan, cache retrieval, or
   dependency builds
3. To avoid generating a scalar `.olean`, submit one in-memory combined input:
   the complete scalar source followed by the envelope source after removing
   only its module/import header. Preserve all definitions, theorem statements,
   and proofs verbatim
4. Invoke `lean --stdin -j1 -M3000` with no output, incremental-save,
   profiler-output, or compilation-output options
5. Enforce a total wall limit of 180 seconds and monitor aggregate owned-process
   RSS against 3 GiB. Terminate only the probe's process group on either limit;
   clean only owned temporary material
6. Label any success "4.35 development combined-body elaboration," not exact
   4.33/db584 verification or original-module verification

CLI and frontend behavior for stdin, thread and memory limits, and optional
output emission was checked from the existing 4.35 source, without executing
the Lean binary. The current missing-import blocker stops this plan before any
proof runtime action. Neither successful parsing nor API elaboration is
assumed.

## Actual remaining bridges and contract

This supplies the scalar time-envelope leaf only. The following remain open:

- Time measurability and domination-based integrability of the actual Gaussian
  Hessian convolution, and its integrated bound
- Actual Duhamel second-differentiation compatibility and BCF Hessian packaging
- Strong C² zero trace at the initial time
- Parabolic-time Hölder estimates and the nonlinear estimates
- Global flow construction, gauge recovery, and weak uniqueness

The canonical arbitrary-C², arbitrary-model manifold-only boundaryless,
rank-zero-inclusive, common-closed-interval, ordinary-endpoint-time contract
is unchanged. No C³, initial Hölder, positive-dimension, or global
`I.Boundaryless` premise has been added. **Point 4 remains OPEN.**

## Execution and mutation boundary

No compiler or Lean proof runtime was executed. No compiler, runtime, or cache
was installed or downloaded. No cache or frozen source file was modified.
No candidate source was published or merged, and no required verification gate
was changed. The only output writes for this handoff are this new review
directory's `REVIEW.md` and `review-manifest.json`.
