module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.TensorHeatSecondJet

/-!
# Quantitative Hessian control for the Euclidean mild heat solution

This file proves the full mixed-Hessian operator-norm component of the
Euclidean Schauder estimate.  The homogeneous term uses heat-kernel
cancellation against the spatial Holder modulus of the initial datum; the
inhomogeneous term uses the time-integrated Duhamel Hessian estimate.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 800000

open Real Set MeasureTheory Metric
open scoped Real BigOperators Interval Topology

namespace RicciFlow
namespace AnalyticPDE

section HessianNorms

local instance mildSchauderCoordinateDualNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildSchauderCoordinateBilinearNormedAddCommGroup {n : ℕ} :
    NormedAddCommGroup ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance mildSchauderCoordinateBilinearContinuousAdd {n : ℕ} :
    ContinuousAdd ((Fin n → ℝ) →L[ℝ] ((Fin n → ℝ) →L[ℝ] ℝ)) :=
  IsTopologicalAddGroup.toContinuousAdd

/-- Full operator-norm form of the homogeneous spatial Hessian Schauder
estimate.  Every mixed Hessian entry is controlled, then the finite entries
are summed to bound the curried bilinear operator norm. -/
theorem norm_heatSemigroupHessianCLM_le_of_coordHolder
    {n : ℕ} {t r : ℝ} (ht : 0 < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hu₀holder : ∀ x y, |u₀ y - u₀ x| ≤
      H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ‖heatSemigroupHessianCLM t u₀ x‖ ≤
      ∑ j : Fin n, ∑ k : Fin n,
        H₀ * t ^ (-1 + r / 2) * heatHessianEntryHolderMoment n r j k := by
  unfold heatSemigroupHessianCLM
  refine (norm_coordinateHessianCLM_le _).trans ?_
  gcongr with j k
  exact abs_heatHessianKernelEntryND_convolution_le_of_coordHolder_scale
    ht hr0.le hH₀ x j k u₀.continuous.aestronglyMeasurable
      (fun y ↦ u₀.norm_coe_le_norm y) (hu₀holder x)

/-- The explicit bound stored by a bundled Duhamel Hessian entry is also a
bound for its `C_b` norm. -/
theorem norm_heatDuhamelHessianEntryNDbcf_le
    {n : ℕ} {t₀ t r : ℝ} (hT : t₀ ≤ t) (hr0 : 0 < r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ} (hq : Continuous q)
    {C H : ℝ} (hH : 0 ≤ H) (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (j k : Fin n) :
    ‖heatDuhamelHessianEntryNDbcf hT hr0 hq hH hqb hqholder j k‖ ≤
      H * heatHessianEntryHolderMoment n r j k *
        ((t - t₀) ^ (r / 2) / (r / 2)) := by
  unfold heatDuhamelHessianEntryNDbcf
  apply BoundedContinuousFunction.norm_ofNormedAddCommGroup_le
  exact mul_nonneg
    (mul_nonneg hH (heatHessianEntryHolderMoment_nonneg n r j k))
    (div_nonneg (Real.rpow_nonneg (sub_nonneg.mpr hT) _)
      (by positivity))

/-- **Full mixed-Hessian Schauder bound for the actual mild solution.**
At every positive time the genuine Frechet Hessian of
`H_(t-t₀) u₀ + ∫ H_(t-s) q(s) ds` is bounded by the sum of the
homogeneous cancellation constant and the time-integrated Duhamel constants.
This controls the complete bilinear Hessian, not only its diagonal trace. -/
theorem norm_heatMildSpatialHessianCLM_le
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hu₀holder : ∀ x y, |u₀ y - u₀ x| ≤
      H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ‖heatMildSpatialHessianCLM ht.le hr0 u₀ hq hH hqb hqholder x‖ ≤
      (∑ j : Fin n, ∑ k : Fin n,
        H₀ * (t - t₀) ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r j k) +
      ∑ j : Fin n, ∑ k : Fin n,
        ‖heatDuhamelHessianEntryNDbcf ht.le hr0 hq hH hqb hqholder j k‖ := by
  unfold heatMildSpatialHessianCLM
  calc
    ‖heatSemigroupHessianCLM (t - t₀) u₀ x +
        heatDuhamelHessianCLM ht.le hr0 hq hH hqb hqholder x‖ ≤
        ‖heatSemigroupHessianCLM (t - t₀) u₀ x‖ +
          ‖heatDuhamelHessianCLM ht.le hr0 hq hH hqb hqholder x‖ :=
      norm_add_le _ _
    _ ≤ (∑ j : Fin n, ∑ k : Fin n,
          H₀ * (t - t₀) ^ (-1 + r / 2) *
            heatHessianEntryHolderMoment n r j k) +
        ∑ j : Fin n, ∑ k : Fin n,
          ‖heatDuhamelHessianEntryNDbcf ht.le hr0 hq hH hqb hqholder j k‖ :=
      add_le_add
        (norm_heatSemigroupHessianCLM_le_of_coordHolder
          (sub_pos.mpr ht) hr0 u₀ hH₀ hu₀holder x)
        (norm_heatDuhamelHessianCLM_le ht.le hr0 hq hH hqb hqholder x)

/-- Explicit-constant form of `norm_heatMildSpatialHessianCLM_le`.
The source contribution is the finite sum of the time-integrated Holder
moments `H (t-t₀)^(r/2)/(r/2)`. -/
theorem norm_heatMildSpatialHessianCLM_le_explicit
    {n : ℕ} {t₀ t r : ℝ} (ht : t₀ < t) (hr0 : 0 < r)
    (u₀ : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    {H₀ : ℝ} (hH₀ : 0 ≤ H₀)
    (hu₀holder : ∀ x y, |u₀ y - u₀ x| ≤
      H₀ * ∑ ell : Fin n, |(x - y) ell| ^ r)
    {q : ℝ → BoundedContinuousFunction (Fin n → ℝ) ℝ}
    (hq : Continuous q) {C H : ℝ} (hH : 0 ≤ H)
    (hqb : ∀ s y, ‖q s y‖ ≤ C)
    (hqholder : ∀ s x y, |q s y - q s x| ≤
      H * ∑ ell : Fin n, |(x - y) ell| ^ r)
    (x : Fin n → ℝ) :
    ‖heatMildSpatialHessianCLM ht.le hr0 u₀ hq hH hqb hqholder x‖ ≤
      (∑ j : Fin n, ∑ k : Fin n,
        H₀ * (t - t₀) ^ (-1 + r / 2) *
          heatHessianEntryHolderMoment n r j k) +
      ∑ j : Fin n, ∑ k : Fin n,
        H * heatHessianEntryHolderMoment n r j k *
          ((t - t₀) ^ (r / 2) / (r / 2)) := by
  refine (norm_heatMildSpatialHessianCLM_le ht hr0 u₀ hH₀ hu₀holder
    hq hH hqb hqholder x).trans ?_
  gcongr with j k
  exact norm_heatDuhamelHessianEntryNDbcf_le ht.le hr0 hq hH hqb hqholder j k

end HessianNorms

end AnalyticPDE
end RicciFlow
