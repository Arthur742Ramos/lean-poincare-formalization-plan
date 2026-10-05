module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanDuhamelHessian
public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.WeightedHessianTimeEnvelope

/-!
Source-only research helper. Not compiled, not part of a candidate tree or CI gate.

This retains only the inherited Gaussian integrand domination. The separate
scalar files propose the time integrability and bound, still source-only. The
integrated Gaussian estimate, derivative compatibility, and strong zero trace
still have to be proved. No solver or solver norm is an input.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory Metric
open scoped Real BigOperators

namespace RicciFlow
namespace AnalyticPDE

/-- Actual Gaussian Hessian cancellation with a positive-time weighted
spatial Hölder forcing bound. This is not an assumed operator estimate. -/
theorem abs_heatHessianEntryConvolutionND_le_weighted_envelope
    {n : ℕ} {t₀ s t α L C : ℝ}
    (hα : 0 ≤ α) (hs : t₀ < s) (hst : s < t) (hL : 0 ≤ L)
    (q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hqb : ∀ y, ‖q s y‖ ≤ C)
    (hqholder : ∀ x y, |q s y - q s x| ≤
      (L * (s - t₀) ^ (-(α / 2))) *
        ∑ ell : Fin n, |(x - y) ell| ^ α)
    (x : Fin n → ℝ) (j k : Fin n) :
    |heatHessianEntryConvolutionND (t - s) (q s) j k x| ≤
      (L * heatHessianEntryHolderMoment n α j k) *
        weightedHessianTimeEnvelope t₀ t α s := by
  have hH : 0 ≤ L * (s - t₀) ^ (-(α / 2)) :=
    mul_nonneg hL (Real.rpow_nonneg (sub_pos.mpr hs).le _)
  have h := abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
    (sub_pos.mpr hst) hα hH x j k
    (q s).continuous.aestronglyMeasurable hqb (hqholder x)
  change |heatHessianEntryConvolutionND (t - s) (q s) j k x| ≤
    (L * (s - t₀) ^ (-(α / 2))) * (t - s) ^ (-1 + α / 2) *
      heatHessianEntryHolderMoment n α j k at h
  exact h.trans_eq (by unfold weightedHessianTimeEnvelope; ring)

end AnalyticPDE
end RicciFlow
