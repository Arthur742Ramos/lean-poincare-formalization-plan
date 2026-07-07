import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.SmoothDependenceCk
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The autonomous fundamental solution is the operator exponential

For a **time-independent** (autonomous) linear generator `A₀ : E →L[ℝ] E`, the campaign's resolvent
`fundamentalSolution` (built abstractly from any flow family `Φ` of the linear variational field via
Picard–Lindelöf / Grönwall uniqueness) coincides with Mathlib's analytic operator exponential:

`fundamentalSolution hA hΦ h0 t = NormedSpace.exp ((t - t₀) • A₀)`.

This is the bridge from the `IsIntegralCurve`-based resolvent used throughout the smooth-dependence
layer to the analytic `NormedSpace.exp`.  It matters because `NormedSpace.exp` is analytic in its
argument, so this identity transports the exponential's analytic dependence on the operator to the
autonomous resolvent — precisely the smooth-dependence structure needed for the **frozen** (autonomous,
bounded-linear) geometric Ricci–DeTurck chart generator, whose fibre generator depends on the spatial
point.  Everything is proved from Mathlib's `hasDerivAt_exp_smul_const'` and the campaign's global
integral-curve uniqueness `eq_of_isIntegralCurve_of_eq_at`; no PDE or manifold content is used.
-/

@[expose] public noncomputable section

open Set
open scoped Topology NNReal

namespace RicciFlow
namespace AnalyticPDE
namespace SmoothDependenceCk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **The operator-exponential curve solves the autonomous linear ODE.**  For a fixed generator
`A₀ : E →L[ℝ] E` and initial point `x`, the path `t ↦ exp ((t - t₀) • A₀) x` is a global integral
curve of the (time-independent) vector variational field `variationalFieldVec (fun _ => A₀)`, i.e. it
obeys `γ'(t) = A₀ (γ t)` everywhere.  Proved from Mathlib's `hasDerivAt_exp_smul_const'`
(`d/du exp (u • A₀) = A₀ * exp (u • A₀)`) precomposed with the shift `t ↦ t - t₀` and evaluated at the
fixed direction `x` via `HasDerivAt.clm_apply`. -/
theorem isIntegralCurve_exp_smul_const (A₀ : E →L[ℝ] E) (t₀ : ℝ) (x : E) :
    IsIntegralCurve (fun t => NormedSpace.exp ((t - t₀) • A₀) x)
      (variationalFieldVec (fun _ => A₀)) := by
  intro t
  have hbase : HasDerivAt (fun u : ℝ => NormedSpace.exp (u • A₀))
      (A₀ * NormedSpace.exp ((t - t₀) • A₀)) (t - t₀) :=
    hasDerivAt_exp_smul_const' A₀ (t - t₀)
  have hshift : HasDerivAt (fun t : ℝ => t - t₀) (1 : ℝ) t :=
    (hasDerivAt_id t).sub_const t₀
  have hcomp : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t - t₀) • A₀))
      (A₀ * NormedSpace.exp ((t - t₀) • A₀)) t := by
    have := HasDerivAt.scomp t hbase hshift
    simpa using this
  have hpt : HasDerivAt (fun t : ℝ => NormedSpace.exp ((t - t₀) • A₀) x)
      ((A₀ * NormedSpace.exp ((t - t₀) • A₀)) x) t := by
    have := HasDerivAt.clm_apply hcomp (hasDerivAt_const t x)
    simpa using this
  simpa [variationalFieldVec, ContinuousLinearMap.mul_apply] using hpt

variable {Φ : E → ℝ → E} {t₀ : ℝ}

/-- **The autonomous fundamental solution is the operator exponential.**  For a *time-independent*
generator `A₀ : E →L[ℝ] E` the campaign resolvent (built from any flow family `Φ` of the linear
variational field anchored at `t₀`) equals `NormedSpace.exp ((t - t₀) • A₀)`.

Both sides are integral curves (at each fixed direction `x`) of the same globally
`‖A₀‖`-Lipschitz autonomous field `variationalFieldVec (fun _ => A₀)`, and both send `t₀ ↦ x`
(`Φ x t₀ = x` and `exp (0 • A₀) x = x`); global integral-curve uniqueness
(`eq_of_isIntegralCurve_of_eq_at`) forces them to agree at every time and every direction. -/
theorem fundamentalSolution_const_eq_exp {A₀ : E →L[ℝ] E} {K : ℝ≥0}
    (hA : ∀ t, ‖(fun _ : ℝ => A₀) t‖₊ ≤ K)
    (hΦ : ∀ x, IsIntegralCurve (Φ x) (variationalFieldVec (fun _ => A₀)))
    (h0 : ∀ x, Φ x t₀ = x) (t : ℝ) :
    fundamentalSolution hA hΦ h0 t = NormedSpace.exp ((t - t₀) • A₀) := by
  ext x
  rw [fundamentalSolution_apply]
  refine eq_of_isIntegralCurve_of_eq_at (K := K) (t₁ := t₀)
    (fun s => lipschitzWith_variationalFieldVec hA s) (hΦ x)
    (isIntegralCurve_exp_smul_const A₀ t₀ x) ?_ t
  rw [h0]
  simp [NormedSpace.exp_zero]

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
