import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatStrongInitialGenerator

-- Source-only exact BCF-valued types; neither target is merely pointwise in space.
open scoped BigOperators Topology
open Set Filter MeasureTheory RicciFlow.AnalyticPDE

abbrev ExpectedActualHeatBanachIncrement :=
  ∀ {n : ℕ} (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ))
    {t : ℝ}, 0 ≤ t →
    heatFlowPathBcf D.value t = D.value +
      ∫ s in (0 : ℝ)..t, ∑ k : Fin n, heatFlowPathBcf (D.second k k) s

def actualHeatBanachIncrementFullSignatureAssignment : ExpectedActualHeatBanachIncrement :=
  @EuclideanBoundedC2Data.heatFlowPathBcf_eq_value_add_integral_actualTrace

abbrev ExpectedActualHeatStrongRightInitialDerivative :=
  ∀ {n : ℕ} (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ)),
    HasDerivWithinAt (heatFlowPathBcf D.value) (∑ k : Fin n, D.second k k) (Ici 0) 0

def actualHeatStrongRightInitialDerivativeFullSignatureAssignment : ExpectedActualHeatStrongRightInitialDerivative :=
  @EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_strong_zero

-- Empty dimension requires no selected Hessian index or positive rank.
example (D : EuclideanBoundedC2Data 0) :
    HasDerivWithinAt (heatFlowPathBcf D.value)
      (0 : BoundedContinuousFunction (Fin 0 → ℝ) ℝ) (Ici 0) 0 := by
  simpa using D.hasDerivWithinAt_heatFlowPathBcf_strong_zero (fun j => Fin.elim0 j)

example (D : EuclideanBoundedC2Data 0) {t : ℝ} (ht : 0 ≤ t) :
    heatFlowPathBcf D.value t = D.value := by
  simpa using D.heatFlowPathBcf_eq_value_add_integral_actualTrace (fun j => Fin.elim0 j) ht

set_option pp.universes false
set_option format.width 200
#check @EuclideanBoundedC2Data.heatFlowPathBcf_eq_value_add_integral_actualTrace
#check @EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_strong_zero

#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.heatFlowPathBcf_eq_value_add_integral_actualTrace
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_strong_zero
