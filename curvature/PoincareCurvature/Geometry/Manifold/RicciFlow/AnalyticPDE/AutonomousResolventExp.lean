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

/-- **The operator-exponential map is smooth.**  For a fixed scalar `s`, the map
`A₀ ↦ exp (s • A₀)` on `E →L[ℝ] E` is `ContDiff ℝ n` for every `n`.  Immediate from the analyticity of
`NormedSpace.exp` on the (complete) operator Banach algebra (`NormedSpace.exp_analytic`, whose power
series has infinite radius) composed with the smooth scalar rescaling `A₀ ↦ s • A₀`. -/
theorem contDiff_exp_smul_const (s : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun A₀ : E →L[ℝ] E => NormedSpace.exp (s • A₀)) := by
  have hana : AnalyticOnNhd ℝ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  exact ContDiff.comp hana.contDiff (contDiff_const_smul s)

/-- **Smooth dependence of the autonomous resolvent on a parameter.**  If a family of autonomous
generators `A : X → (E →L[ℝ] E)` over a normed parameter space `X` is `C^n`, then the autonomous
resolvent `x ↦ exp (s • A x)` is `C^n`.  This transports smooth dependence of the generator to smooth
dependence of the resolvent — the parameter-smoothness form that, via `fundamentalSolution_const_eq_exp`,
turns spatial (`x`-dependent) smoothness of a frozen bounded-linear generator into spatial smoothness of
its Banach evolution, with no `IsIntegralCurve` bookkeeping. -/
theorem contDiff_exp_smul_of_contDiff
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : X → (E →L[ℝ] E)} {n : WithTop ℕ∞} (hA : ContDiff ℝ n A) (s : ℝ) :
    ContDiff ℝ n (fun x => NormedSpace.exp (s • A x)) := by
  have hana : AnalyticOnNhd ℝ (NormedSpace.exp : (E →L[ℝ] E) → (E →L[ℝ] E)) Set.univ :=
    fun x _ => NormedSpace.exp_analytic x
  exact ContDiff.comp hana.contDiff (ContDiff.const_smul s hA)

end SmoothDependenceCk
end AnalyticPDE
end RicciFlow
