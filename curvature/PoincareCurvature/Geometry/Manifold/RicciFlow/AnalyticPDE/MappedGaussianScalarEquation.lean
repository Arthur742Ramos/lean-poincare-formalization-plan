import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2MappedAffineGenerator
import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.RicciDeTurckHolderSmoothing

/-!
# Actual positive-time scalar equation of mapped Gaussian heat

Source candidate, uncompiled. The positive-time Gaussian evolution of the
certified affine pullback is pulled back once more by the inverse affine map.
This produces actual bounded C2 data in the original coordinates. Its stored
Hessian is the actual spatial Hessian, and the genuine Gaussian time derivative
is its contraction with the structurally defined L L-transpose coefficients.

Both dimensions are retained. No supplied derivative, heat equation, generator
or coefficient-closeness oracle is used. No higher C2alpha assumption replaces
the literal C2 witnesses. This is a scalar constant-coefficient equation only.
-/

noncomputable section

open scoped BigOperators Topology
open Set Filter

namespace RicciFlow.AnalyticPDE

private theorem inverse_affine_point {n m : ℕ} (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ) :
    -L.symm a + L.symm z = L.symm (z - a) := by
  rw [map_sub]
  abel

private theorem inverse_affine_roundTrip {n m : ℕ} (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (x : Fin m → ℝ) :
    -L.symm a + L.symm (a + L x) = x := by
  rw [map_add, L.symm_apply_apply]
  abel

private theorem forward_affine_point {n m : ℕ} (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ) :
    a + L (L.symm (z - a)) = z := by
  rw [L.apply_symm_apply]
  abel

/-- Actual positive-time mapped Gaussian data, with both coordinate derivative
certificates inherited from the genuine heat evolution and affine constructor. -/
def mappedGaussianBoundedC2Data {n m : ℕ} (D : EuclideanBoundedC2Data n)
    (a : Fin n → ℝ) (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ}
    (ht : 0 < t) : EuclideanBoundedC2Data n :=
  (heatEvolvedBoundedC2Data (D.precompAffine a L.toContinuousLinearMap) ht).precompAffine
    (-L.symm a) L.symm.toContinuousLinearMap

/-- The certified mapped value is the actual mapped Gaussian path. -/
theorem mappedGaussianBoundedC2Data_value_eq_path {n m : ℕ}
    (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ} (ht : 0 < t) (z : Fin n → ℝ) :
    (mappedGaussianBoundedC2Data D a L ht).value z = mappedAffineHeatFlowPath D a L t z := by
  unfold mappedGaussianBoundedC2Data mappedAffineHeatFlowPath
  rw [EuclideanBoundedC2Data.precompAffine_value_apply]
  change heatSemigroupNDbcf ht (D.precompAffine a L.toContinuousLinearMap).value
      (-L.symm a + L.symm z) =
    heatFlowPathBcf (D.precompAffine a L.toContinuousLinearMap).value t (L.symm (z - a))
  rw [inverse_affine_point, heatFlowPathBcf_of_pos _ ht]

/-- The stored mapped gradient differentiates the actual scalar path value. -/
theorem hasDerivAt_mappedAffineHeatFlowPath_coordinate {n m : ℕ}
    (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (p : Fin n) (z : Fin n → ℝ) :
    HasDerivAt (fun r => mappedAffineHeatFlowPath D a L t (Function.update z p r))
      ((mappedGaussianBoundedC2Data D a L ht).first p z) (z p) := by
  have h := (mappedGaussianBoundedC2Data D a L ht).hasDeriv_value p z
  have hfun : (fun r => (mappedGaussianBoundedC2Data D a L ht).value (Function.update z p r)) =
      (fun r => mappedAffineHeatFlowPath D a L t (Function.update z p r)) := by
    funext r
    exact mappedGaussianBoundedC2Data_value_eq_path D a L ht (Function.update z p r)
  rw [hfun] at h
  exact h

/-- Explicit genuine Hessian slots in the original coordinates. The first
source index differentiates the second source first-derivative index. -/
theorem mappedGaussianBoundedC2Data_second_apply {n m : ℕ}
    (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (p q : Fin n) (z : Fin n → ℝ) :
    (mappedGaussianBoundedC2Data D a L ht).second p q z =
      ∑ k : Fin m, ∑ l : Fin m,
        (L.symm (Pi.single p 1) k * L.symm (Pi.single q 1) l) *
          heatSemigroupND t ((D.precompAffine a L.toContinuousLinearMap).second k l)
            (L.symm (z - a)) := by
  unfold mappedGaussianBoundedC2Data
  rw [EuclideanBoundedC2Data.precompAffine_second_apply]
  simp only [heatEvolvedBoundedC2Data_second_eq, heatSemigroupNDbcf_apply]
  change (∑ k : Fin m, ∑ l : Fin m,
      (L.symm (Pi.single p 1) k * L.symm (Pi.single q 1) l) *
        heatSemigroupND t ((D.precompAffine a L.toContinuousLinearMap).second k l)
          (-L.symm a + L.symm z)) = _
  rw [inverse_affine_point]

private theorem second_affine_inverse_roundTrip {n m : ℕ}
    (E : EuclideanBoundedC2Data m) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (k l : Fin m) (x : Fin m → ℝ) :
    ((E.precompAffine (-L.symm a) L.symm.toContinuousLinearMap).precompAffine
      a L.toContinuousLinearMap).second k l x = E.second k l x := by
  let R := (E.precompAffine (-L.symm a) L.symm.toContinuousLinearMap).precompAffine
    a L.toContinuousLinearMap
  have hvalue (y : Fin m → ℝ) : R.value y = E.value y := by
    change ((E.precompAffine (-L.symm a) L.symm.toContinuousLinearMap).precompAffine
      a L.toContinuousLinearMap).value y = E.value y
    rw [EuclideanBoundedC2Data.precompAffine_value_apply,
      EuclideanBoundedC2Data.precompAffine_value_apply]
    change E.value (-L.symm a + L.symm (a + L y)) = E.value y
    rw [inverse_affine_roundTrip]
  have hfirst (s : Fin m) (y : Fin m → ℝ) : R.first s y = E.first s y := by
    have hR := R.hasDeriv_value s y
    have hfun : (fun r => R.value (Function.update y s r)) =
        (fun r => E.value (Function.update y s r)) := by
      funext r
      exact hvalue (Function.update y s r)
    rw [hfun] at hR
    exact hR.unique (E.hasDeriv_value s y)
  have hR := R.hasDeriv_first k l x
  have hfun : (fun r => R.first l (Function.update x k r)) =
      (fun r => E.first l (Function.update x k r)) := by
    funext r
    exact hfirst l (Function.update x k r)
  rw [hfun] at hR
  exact hR.unique (E.hasDeriv_first k l x)

private theorem scalar_trace_coefficients {n m : ℕ}
    (F : EuclideanBoundedC2Data n) (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ) :
    (∑ k : Fin m, ∑ p : Fin n, ∑ q : Fin n,
      (L (Pi.single k 1) p * L (Pi.single k 1) q) * F.second p q z) =
      ∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q * F.second p q z := by
  classical
  calc
    _ = ∑ p : Fin n, ∑ k : Fin m, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single k 1) q) * F.second p q z :=
      Finset.sum_comm
    _ = ∑ p : Fin n, ∑ q : Fin n, ∑ k : Fin m,
        (L (Pi.single k 1) p * L (Pi.single k 1) q) * F.second p q z := by
      apply Finset.sum_congr rfl
      intro p _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro q _
      rw [affineSpatialGramCoefficient, Finset.sum_mul]

private theorem hessian_trace_inverse_affine {n m : ℕ}
    (E : EuclideanBoundedC2Data m) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ) :
    (∑ k : Fin m, E.second k k (L.symm (z - a))) =
      ∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q *
        (E.precompAffine (-L.symm a) L.symm.toContinuousLinearMap).second p q z := by
  classical
  let F := E.precompAffine (-L.symm a) L.symm.toContinuousLinearMap
  calc
    _ = ∑ k : Fin m, (F.precompAffine a L.toContinuousLinearMap).second k k
        (L.symm (z - a)) := by
      apply Finset.sum_congr rfl
      intro k _
      exact (second_affine_inverse_roundTrip E a L k k (L.symm (z - a))).symm
    _ = ∑ k : Fin m, ∑ p : Fin n, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single k 1) q) * F.second p q z := by
      simp only [EuclideanBoundedC2Data.precompAffine_second_apply]
      change (∑ k : Fin m, ∑ p : Fin n, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single k 1) q) *
          F.second p q (a + L (L.symm (z - a)))) = _
      rw [forward_affine_point]
    _ = _ := scalar_trace_coefficients F L z

/-- The actual mapped Gaussian path solves its scalar frozen-coefficient
equation at every positive time, with its genuine original-coordinate Hessian. -/
theorem hasDerivAt_mappedAffineHeatFlowPath_eq_coefficientHessian {n m : ℕ}
    (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ} (ht : 0 < t) (z : Fin n → ℝ) :
    HasDerivAt (fun s => mappedAffineHeatFlowPath D a L s z)
      (∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q *
        (mappedGaussianBoundedC2Data D a L ht).second p q z) t := by
  classical
  let P := D.precompAffine a L.toContinuousLinearMap
  let E := heatEvolvedBoundedC2Data P ht
  let x := L.symm (z - a)
  have htime : HasDerivAt (fun s => mappedAffineHeatFlowPath D a L s z)
      (heatSemigroupLaplacianND t P.value x) t := by
    apply (hasDerivAt_heatSemigroupND_time_eq_laplacian ht P.value x).congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds ht] with s hs
    change heatFlowPathBcf P.value s x = heatSemigroupND s P.value x
    rw [heatFlowPathBcf_of_pos P.value hs]
    exact heatSemigroupNDbcf_apply hs P.value x
  have htrace : heatSemigroupLaplacianND t P.value x = ∑ k : Fin m, E.second k k x := by
    unfold heatSemigroupLaplacianND
    apply Finset.sum_congr rfl
    intro k _
    simpa only [E, heatEvolvedBoundedC2Data_second_eq, heatSemigroupNDbcf_apply,
      heatHessianCoordConvolutionND, heatHessianEntryConvolutionND,
      heatHessianKernelEntryND_diag] using P.heatHessianEntryConvolutionND_eq ht k k x
  have hcoeff : heatSemigroupLaplacianND t P.value x =
      ∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q *
        (mappedGaussianBoundedC2Data D a L ht).second p q z :=
    htrace.trans (hessian_trace_inverse_affine E a L z)
  exact htime.congr_deriv hcoeff

end RicciFlow.AnalyticPDE
