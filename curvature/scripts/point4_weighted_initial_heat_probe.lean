import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatWeightedInitialHolder

set_option pp.proofs false

open RicciFlow.AnalyticPDE Filter
open scoped Topology BigOperators

#print initialHeatHolderConstant
#print heatEvolvedWeightedC2AlphaData
#print abs_heatSemigroupNDbcf_spatial_holder_le
#print heatSemigroupNDbcf_split_initial_error
#print abs_heatSemigroupNDbcf_sub_le_initialHeatHolderConstant
#print initialHeatHolderConstant_weight_identity
#print tendsto_weighted_initialHeatHolderConstant_zero
#print heatEvolvedWeightedC2AlphaData_base_eq
#print heatEvolvedWeightedC2AlphaData_holderConstant_eq
#print EuclideanBoundedC2Data.tendsto_weighted_initialHessianHolderConstant_zero
#print EuclideanBoundedC2Data.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero

#print axioms abs_heatSemigroupNDbcf_spatial_holder_le
#print axioms heatSemigroupNDbcf_split_initial_error
#print axioms initialHeatHolderConstant_nonneg
#print axioms abs_heatSemigroupNDbcf_sub_le_initialHeatHolderConstant
#print axioms initialHeatHolderConstant_weight_identity
#print axioms tendsto_weighted_initialHeatHolderConstant_zero
#print axioms heatEvolvedWeightedC2AlphaData
#print axioms heatEvolvedWeightedC2AlphaData_base_eq
#print axioms heatEvolvedWeightedC2AlphaData_holderConstant_eq
#print axioms EuclideanBoundedC2Data.tendsto_weighted_initialHessianHolderConstant_zero
#print axioms EuclideanBoundedC2Data.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero

-- The producer carries the original actual value, first and Hessian derivatives.
example {n : ℕ} (D : EuclideanBoundedC2Data n) {t α : ℝ}
    (ht : 0 < t) (hα : 0 < α) (hα1 : α < 1) :
    (heatEvolvedWeightedC2AlphaData D ht hα.le hα1.le).base =
      heatEvolvedBoundedC2Data D ht := rfl

-- No initial positive-exponent Hölder hypothesis is added to the headline.
example {n : ℕ} (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ))
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    Tendsto (fun t : ℝ => t ^ (α / 2) *
      (if ht : 0 < t then
        (heatEvolvedWeightedC2AlphaData D ht hα.le hα1.le).hessianHolderConstant
      else 0)) (𝓝[>] 0) (𝓝 0) :=
  D.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero hsecond hα hα1.le

-- Dimension zero remains valid, without an added positive-rank assumption.
example (D : EuclideanBoundedC2Data 0) {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Tendsto (fun t : ℝ => t ^ (α / 2) *
      (if ht : 0 < t then
        (heatEvolvedWeightedC2AlphaData D ht hα.le hα1).hessianHolderConstant
      else 0)) (𝓝[>] 0) (𝓝 0) :=
  D.tendsto_weighted_heatEvolvedWeightedC2AlphaData_zero (fun j => Fin.elim0 j) hα hα1

example (D : EuclideanBoundedC2Data 0) (α t : ℝ) :
    D.initialHessianHolderConstant α t = 0 := by
  simp [EuclideanBoundedC2Data.initialHessianHolderConstant]
