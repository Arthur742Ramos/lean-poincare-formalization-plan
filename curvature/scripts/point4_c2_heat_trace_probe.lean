import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace

set_option pp.proofs false

open RicciFlow.AnalyticPDE
open scoped Topology BigOperators

#print PoincareCurvature.CompactUniformModulus.exists_pos_norm_modulus_boundedContinuous
#print PoincareCurvature.FiniteMomentApproximation.abs_integral_sub_self_le_of_local_modulus
#print abs_heatSemigroupND_sub_self_le_of_local_modulus
#print norm_heatSemigroupNDbcf_sub_self_le_of_modulus
#print continuousAt_heatFlowPathBcf_zero_of_uniformContinuous
#print tendstoUniformlyOn_heatSemigroupND_zero
#print EuclideanBoundedC2Data.uniformContinuous_value
#print EuclideanBoundedC2Data.uniformContinuous_first
#print EuclideanBoundedC2Data.tendstoUniformlyOn_heatGradient_zero
#print EuclideanBoundedC2Data.tendstoUniformlyOn_heatHessian_zero
#print EuclideanBoundedC2Data.continuousAt_heatC2Trace_zero
#print EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_apply_zero

#print axioms PoincareCurvature.CompactUniformModulus.exists_pos_norm_modulus_boundedContinuous
#print axioms PoincareCurvature.FiniteMomentApproximation.abs_integral_sub_self_le_of_local_modulus
#print axioms abs_heatSemigroupND_sub_self_le_of_local_modulus
#print axioms norm_heatSemigroupNDbcf_sub_self_le_of_modulus
#print axioms continuousAt_heatFlowPathBcf_zero_of_uniformContinuous
#print axioms tendstoUniformlyOn_heatSemigroupND_zero
#print axioms EuclideanBoundedC2Data.uniformContinuous_value
#print axioms EuclideanBoundedC2Data.uniformContinuous_first
#print axioms EuclideanBoundedC2Data.tendstoUniformlyOn_heatGradient_zero
#print axioms EuclideanBoundedC2Data.tendstoUniformlyOn_heatHessian_zero
#print axioms EuclideanBoundedC2Data.continuousAt_heatC2Trace_zero
#print axioms EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_apply_zero

-- Dimension zero is not excluded from the global endpoint trace or generator.
example (D : EuclideanBoundedC2Data 0) :
    ContinuousAt (fun t : ℝ =>
      (heatFlowPathBcf D.value t,
        (fun k => heatFlowPathBcf (D.first k) t),
        (fun j k => heatFlowPathBcf (D.second j k) t))) 0 :=
  D.continuousAt_heatC2Trace_zero (fun j => Fin.elim0 j)

example (D : EuclideanBoundedC2Data 0) (x : Fin 0 → ℝ) :
    HasDerivWithinAt (fun t => heatFlowPathBcf D.value t x)
      (∑ k : Fin 0, D.second k k x) (Set.Ici 0) 0 :=
  D.hasDerivWithinAt_heatFlowPathBcf_apply_zero x
