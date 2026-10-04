# Genuine bounded-C² initial heat traces

This supporting source candidate builds on immutable master
`1d1f97fe481e0899a0cd54889b0f99ba159ba3fa`. The actual Gaussian,
its normalization and coordinate first moments, positive-time kernel
calculus and actual initial derivative witnesses are inherited unchanged.
Structured builds-on attribution is recorded in `curvature/formalization.yaml`.
No registry submission or new registry identity is part of this milestone.

## Exact mathematical boundary

`EuclideanBoundedC2Data n` retains its original meaning: bounded continuous
value, first derivatives and all mixed Hessian entries, together with actual
coordinate derivative witnesses. No positive-exponent Hessian modulus is
added, and `n = 0` is not excluded.

`Analysis/CompactUniformModulus.lean` obtains a common ambient continuity
radius near an arbitrary compact set from ordinary continuity. Only the
comparison center must belong to the compact set; the second point may be
outside it. Compact-uniform continuity restricted to the set would not
suffice for a Gaussian convolution.

`Analysis/FiniteMomentApproximation.lean` proves the normalized nonnegative
kernel estimate using finite first moments. Its explicit generic kernel
hypotheses are discharged by the actual Gaussian in
`AnalyticPDE/EuclideanHeatInitialTrace.lean`. If `δ > 0`, `ε ≥ 0` and
`|f(y) - f(x)| ≤ ε` for `‖y - x‖ < δ`, the actual heat convolution obeys

`|S_t f(x) - f(x)| ≤ ε + (2‖f‖/δ)n(2/√π)√t`, for `t > 0`.

The near part uses the stated continuity modulus; the complementary part
uses `2‖f‖ ≤ (2‖f‖/δ)‖z‖` and the actual Gaussian coordinate first moments.
No heat convergence estimate is assumed as an oracle.

The scalar consequence is `TendstoUniformlyOn` on every compact spatial
set. The existing proved derivative commutation identities then yield the
same locally uniform trace for the actual homogeneous gradient and every
mixed Hessian entry. Finite-dimensionality makes these entrywise local
traces a genuine local C² trace.

For global convergence, bounded continuous Hessians on noncompact Euclidean
space need not be uniformly continuous. The theorem
`EuclideanBoundedC2Data.continuousAt_heatC2Trace_zero` therefore assumes
uniform continuity only of each initial Hessian entry. Value and first
uniform continuity are derived by the actual coordinate-to-Fréchet
calculus and bounded successive derivatives. Its conclusion is continuity
in the finite product of bounded-continuous component spaces, so it controls
the global supremum norms of value, all first derivatives and all Hessian
entries together.

Finally, `hasDerivWithinAt_heatFlowPathBcf_apply_zero` proves the right initial
generator `Σ_k D.second k k x` for every bounded-C² datum. It uses the
positive-time heat equation, local-compact Hessian convergence on `{x}`, and
Mathlib's derivative-limit extension theorem. This requires neither a
Hessian Hölder certificate nor global Hessian uniform continuity.

## Verification status

The compact ambient-modulus helper passed a bounded, read-only Lean
4.35.0-rc2 **development-only** probe. The finite-moment helper's first bounded development probe hit its enforced
3GB memory guard at 28.42 seconds while loading the overly broad Mathlib
import. That resource-inconclusive run produced no Lean proof result. The
helper now uses narrow Mathlib imports; this exact source has not had a local
compiler check. The actual Gaussian and C² assembly
have not been compiled locally against the incompatible rc2 baseline.
Exact Lean-4.33 verification remains pending.

The dedicated exact-head read-only workflow builds both Mathlib-only helpers,
then the actual trace/generator module, checks exact elaborated theorem types
and all twelve headline axiom surfaces, and runs the unchanged full Point-4
audit. Dimension-zero examples are included. All actions are pinned and
checkout credentials are not persisted. The full official cached v0.4
metadata schema passes; the inherited unsupported method label is minimally
normalized to the supported `agent` label while preserving its attribution.

## What remains open

This advances the flat initial-face analysis rather than repackaging the
already-existing positive-time C²-to-C²,α smoothing result. It does not
construct localization of an arbitrary compact C² metric into Euclidean
bounded-C² data; in particular, derivative support, boundedness, ambient
uniform continuity and geometric overlap still need actual producers.

The existing constant negative-time heat path is used only for continuity.
Its ordinary derivative at zero generally is not the right generator.
A separate reflected continuation (`2f - S_{-t}f` for negative time) is
needed to turn this right derivative into an ordinary initial derivative
while retaining C² spatial slices; it is not a backward heat solution.
Metric positivity is another independent obligation.

The unweighted Hölder solver still requires a uniform positive-exponent
initial Hessian modulus and cannot consume arbitrary C² data merely because
positive-time smoothing has been proved. Weighted parabolic estimates,
nonlinear closure, coefficient localization at the actual regularity,
compact-manifold realization, recovery gauge regularity and canonical
existence/uniqueness remain open. The canonical target, completion auditor
and approved manifold scope are unchanged. Point 4 is **OPEN**.
