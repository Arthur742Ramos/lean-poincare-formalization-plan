module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanMildSchauder

/-!
# Quantitative Hessian control for Euclidean tensor heat flow

The scalar full-Hessian Schauder estimate is lifted to every coefficient of
the finite symmetric-matrix model for a covariant two-tensor.
-/

@[expose] public noncomputable section

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

/-- Every coefficient of the actual matrix-valued parabolic second jet obeys
the explicit full mixed-Hessian Schauder bound, uniformly under common Holder
constants for the initial tensor and forcing. -/
theorem norm_matrixHeatMildParabolicSecondJetND_entry_spaceSecondDeriv_le
    {n d : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ))
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hu₀holder : ∀ x y i j, |u₀ i j y - u₀ i j x| ≤
      H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → Matrix (Fin d) (Fin d)
      (BoundedContinuousFunction (Fin n → ℝ) ℝ)}
    (hq : ∀ i j, Continuous (fun s ↦ q s i j))
    {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y i j, ‖q s i j y‖ ≤ C)
    (hqholder : ∀ s x y i j, |q s i j y - q s i j x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) (i j : Fin d) :
    ‖(heatMildParabolicSecondJetND (t₀ := t₀) hr0 (u₀ i j) (hq i j) hH
      (fun s y ↦ hqb s y i j)
      (fun s y z ↦ hqholder s y z i j)).spaceSecondDeriv (t, x)‖ ≤
      (∑ a : Fin n, ∑ b : Fin n,
        H₀ * (t - t₀) ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r a b) +
      ∑ a : Fin n, ∑ b : Fin n,
        H * heatHessianEntryHolderMoment n r a b *
          ((t - t₀) ^ (r / 2) / (r / 2)) := by
  simpa [heatMildParabolicSecondJetND, heatMildSpaceHessianND, ht] using
    (norm_heatMildSpatialHessianCLM_le_explicit ht hr0 (u₀ i j) hH₀
      (fun y z ↦ hu₀holder y z i j) (hq i j) hH
      (fun s y ↦ hqb s y i j) (fun s y z ↦ hqholder s y z i j) x)

end AnalyticPDE
end RicciFlow
