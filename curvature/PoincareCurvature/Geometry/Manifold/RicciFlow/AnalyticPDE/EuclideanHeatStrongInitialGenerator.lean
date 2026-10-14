import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatInitialTrace
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Strong BCF right initial derivative of actual bounded C2 heat

Source candidate, uncompiled. The initial Hessian uniform-continuity witnesses
are retained. The actual scalar Gaussian time derivatives give the Banach
increment identity by evaluation and scalar FTC. Banach FTC then gives a
genuine derivative in the bounded-continuous-function norm from the right.

No Banach differentiability, generator or integral equation is supplied as a
premise. No ordinary initial derivative of the constant negative-time branch,
joint regularity, generator-domain characterization or nonlinear solution is
asserted.
-/

noncomputable section

open scoped BigOperators Topology
open Set Filter MeasureTheory

namespace RicciFlow.AnalyticPDE

private theorem continuous_closedHeatPath_of_uniformContinuous {n : ℕ}
    (f : BoundedContinuousFunction (Fin n → ℝ) ℝ)
    (hf : UniformContinuous (f : (Fin n → ℝ) → ℝ)) : Continuous (heatFlowPathBcf f) := by
  apply continuous_iff_continuousAt.2
  intro t
  by_cases ht : 0 < t
  · exact continuousAt_heatFlowPathBcf f ht
  by_cases ht0 : t = 0
  · subst t
    exact continuousAt_heatFlowPathBcf_zero_of_uniformContinuous f hf
  have hneg : t < 0 := by
    rcases lt_trichotomy t 0 with hneg | heq | hpos
    · exact hneg
    · exact False.elim (ht0 heq)
    · exact False.elim (ht hpos)
  apply (continuousAt_const : ContinuousAt (fun _ : ℝ => f) t).congr_of_eventuallyEq
  filter_upwards [Iio_mem_nhds hneg] with s hs
  exact dif_neg (not_lt.mpr hs.le)

private def actualHeatHessianTraceBcf {n : ℕ} (D : EuclideanBoundedC2Data n) (t : ℝ) :
    BoundedContinuousFunction (Fin n → ℝ) ℝ :=
  ∑ k : Fin n, heatFlowPathBcf (D.second k k) t

private theorem actualHeatHessianTraceBcf_apply {n : ℕ}
    (D : EuclideanBoundedC2Data n) (t : ℝ) (x : Fin n → ℝ) :
    actualHeatHessianTraceBcf D t x = ∑ k : Fin n, heatFlowPathBcf (D.second k k) t x := by
  classical
  change BoundedContinuousFunction.evalCLM ℝ x (∑ k : Fin n, heatFlowPathBcf (D.second k k) t) = _
  simp only [map_sum, BoundedContinuousFunction.evalCLM_apply]

private theorem continuous_actualHeatHessianTraceBcf {n : ℕ}
    (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ)) :
    Continuous (actualHeatHessianTraceBcf D) := by
  classical
  unfold actualHeatHessianTraceBcf
  apply continuous_finsetSum
  intro k _
  exact continuous_closedHeatPath_of_uniformContinuous (D.second k k) (hsecond k k)

private theorem hasDerivAt_heatValue_eq_actualTrace {n : ℕ}
    (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    HasDerivAt (fun s => heatFlowPathBcf D.value s x) (actualHeatHessianTraceBcf D t x) t := by
  have htime : HasDerivAt (fun s => heatFlowPathBcf D.value s x)
      (heatSemigroupLaplacianND t D.value x) t := by
    apply (hasDerivAt_heatSemigroupND_time_eq_laplacian ht D.value x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    simpa only [heatFlowPathBcf_of_pos D.value hs] using heatSemigroupNDbcf_apply hs D.value x
  have htrace : heatSemigroupLaplacianND t D.value x = actualHeatHessianTraceBcf D t x := by
    rw [actualHeatHessianTraceBcf_apply]
    unfold heatSemigroupLaplacianND
    apply Finset.sum_congr rfl
    intro k _
    rw [heatFlowPathBcf_of_pos (D.second k k) ht, heatSemigroupNDbcf_apply]
    simpa only [heatHessianCoordConvolutionND, heatHessianEntryConvolutionND,
      heatHessianKernelEntryND_diag] using D.heatHessianEntryConvolutionND_eq ht k k x
  exact htime.congr_deriv htrace

namespace EuclideanBoundedC2Data

/-- Genuine Bochner increment identity for the actual heat path at nonnegative
time. Its integrand is the heat evolution of the stored Hessian diagonal. -/
theorem heatFlowPathBcf_eq_value_add_integral_actualTrace {n : ℕ}
    (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ))
    {t : ℝ} (ht : 0 ≤ t) :
    heatFlowPathBcf D.value t = D.value +
      ∫ s in (0 : ℝ)..t, ∑ k : Fin n, heatFlowPathBcf (D.second k k) s := by
  classical
  let G := actualHeatHessianTraceBcf D
  have hG : Continuous G := continuous_actualHeatHessianTraceBcf D hsecond
  have hintG : IntervalIntegrable G volume 0 t := hG.intervalIntegrable 0 t
  have hF : Continuous (heatFlowPathBcf D.value) :=
    continuous_closedHeatPath_of_uniformContinuous D.value D.uniformContinuous_value
  have hzero : heatFlowPathBcf D.value 0 = D.value := dif_neg (lt_irrefl 0)
  ext x
  have hFTC : (∫ s in (0 : ℝ)..t, G s x) = heatFlowPathBcf D.value t x - D.value x := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
      ((continuous_eval_const x).comp hF).continuousOn
      (fun s hs => hasDerivAt_heatValue_eq_actualTrace D hs.1 x)
      (((continuous_eval_const x).comp hG).intervalIntegrable 0 t)
    simpa only [Function.comp_apply, G, hzero] using h
  have heval : (∫ s in (0 : ℝ)..t, G s) x = ∫ s in (0 : ℝ)..t, G s x := by
    change BoundedContinuousFunction.evalCLM ℝ x (∫ s in (0 : ℝ)..t, G s) = _
    exact ((BoundedContinuousFunction.evalCLM ℝ x).intervalIntegral_comp_comm hintG).symm
  change heatFlowPathBcf D.value t x = D.value x + (∫ s in (0 : ℝ)..t, G s) x
  rw [heval, hFTC]
  ring

/-- The actual closed heat path has a strong right initial derivative in BCF
norm. The derivative is the stored actual Hessian trace, not an oracle. -/
theorem hasDerivWithinAt_heatFlowPathBcf_strong_zero {n : ℕ}
    (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ)) :
    HasDerivWithinAt (heatFlowPathBcf D.value) (∑ k : Fin n, D.second k k) (Ici 0) 0 := by
  classical
  let G := actualHeatHessianTraceBcf D
  have hG : Continuous G := continuous_actualHeatHessianTraceBcf D hsecond
  have hInt : HasDerivAt (fun t : ℝ => ∫ s in (0 : ℝ)..t, G s) (G 0) 0 :=
    intervalIntegral.integral_hasDerivAt_right
      (hG.intervalIntegrable 0 0) hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt
  have hzero : G 0 = ∑ k : Fin n, D.second k k := by
    change (∑ k : Fin n, heatFlowPathBcf (D.second k k) 0) = _
    apply Finset.sum_congr rfl
    intro k _
    exact dif_neg (lt_irrefl 0)
  have hprimitive : HasDerivAt (fun t : ℝ => D.value + ∫ s in (0 : ℝ)..t, G s)
      (∑ k : Fin n, D.second k k) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) D.value).add hInt using 1 <;>
      simp only [Pi.add_apply, zero_add, hzero]
  apply hprimitive.hasDerivWithinAt.congr
  · intro t ht
    exact D.heatFlowPathBcf_eq_value_add_integral_actualTrace hsecond ht
  · exact D.heatFlowPathBcf_eq_value_add_integral_actualTrace hsecond (le_refl 0)

end EuclideanBoundedC2Data

end RicciFlow.AnalyticPDE
