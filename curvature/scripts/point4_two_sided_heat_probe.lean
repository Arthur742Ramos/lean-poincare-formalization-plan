import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanHeatTwoSidedInitial

set_option pp.proofs false

open RicciFlow.AnalyticPDE
open scoped Topology BigOperators

#print boundedContinuous_zero_coordHolder
#print heatSmoothedBoundedC2Data
#print EuclideanBoundedC2Data.initialLaplacianBcf_apply
#print EuclideanBoundedC2Data.uniformContinuous_initialLaplacianBcf
#print EuclideanBoundedC2Data.twoSidedHeatPathBcf_of_nonneg
#print EuclideanBoundedC2Data.twoSidedHeatPathBcf_of_neg
#print EuclideanBoundedC2Data.norm_twoSidedHeatPathBcf_sub_value_of_neg
#print EuclideanBoundedC2Data.continuousAt_twoSidedHeatPathBcf_zero
#print EuclideanBoundedC2Data.negativeHeatC2Data
#print EuclideanBoundedC2Data.twoSidedHeatC2Data_value_eq
#print EuclideanBoundedC2Data.hasDerivAt_twoSidedHeatPathBcf_apply_zero
#print EuclideanBoundedC2Data.hasDerivAt_twoSidedHeatPathBcf_apply_of_pos

#print axioms boundedContinuous_zero_coordHolder
#print axioms heatSmoothedBoundedC2Data
#print axioms EuclideanBoundedC2Data.initialLaplacianBcf_apply
#print axioms EuclideanBoundedC2Data.uniformContinuous_initialLaplacianBcf
#print axioms EuclideanBoundedC2Data.twoSidedHeatPathBcf_of_nonneg
#print axioms EuclideanBoundedC2Data.twoSidedHeatPathBcf_of_neg
#print axioms EuclideanBoundedC2Data.norm_twoSidedHeatPathBcf_sub_value_of_neg
#print axioms EuclideanBoundedC2Data.continuousAt_twoSidedHeatPathBcf_zero
#print axioms EuclideanBoundedC2Data.negativeHeatC2Data
#print axioms EuclideanBoundedC2Data.twoSidedHeatC2Data_value_eq
#print axioms EuclideanBoundedC2Data.hasDerivAt_twoSidedHeatPathBcf_apply_zero
#print axioms EuclideanBoundedC2Data.hasDerivAt_twoSidedHeatPathBcf_apply_of_pos

-- The ordinary initial derivative is an actual theorem, with no assumed PDE,
-- assumed target derivative, C3 data, or positive initial Holder exponent.
example {n : ℕ} (D : EuclideanBoundedC2Data n) (x : Fin n → ℝ) :
    HasDerivAt (fun t => D.twoSidedHeatPathBcf t x)
      (∑ k : Fin n, D.second k k x) 0 :=
  D.hasDerivAt_twoSidedHeatPathBcf_apply_zero x

-- The literal initial value and genuine positive-time heat evolution stay.
example {n : ℕ} (D : EuclideanBoundedC2Data n) :
    D.twoSidedHeatPathBcf 0 = D.value := D.twoSidedHeatPathBcf_zero

example {n : ℕ} (D : EuclideanBoundedC2Data n) {t : ℝ} (ht : 0 < t)
    (x : Fin n → ℝ) :
    D.twoSidedHeatPathBcf t x = heatSemigroupND t D.value x :=
  D.twoSidedHeatPathBcf_of_pos_apply ht x

-- Every slice is represented by bounded continuous actual C2 derivatives.
example {n : ℕ} (D : EuclideanBoundedC2Data n) (t : ℝ) :
    ∃ S : EuclideanBoundedC2Data n, S.value = D.twoSidedHeatPathBcf t :=
  ⟨D.twoSidedHeatC2Data t, D.twoSidedHeatC2Data_value_eq t⟩

-- Actual UC Hessians imply UC of the literal actual generator.
example {n : ℕ} (D : EuclideanBoundedC2Data n)
    (hsecond : ∀ j k, UniformContinuous (D.second j k : (Fin n → ℝ) → ℝ)) :
    UniformContinuous (D.initialLaplacianBcf : (Fin n → ℝ) → ℝ) :=
  D.uniformContinuous_initialLaplacianBcf hsecond

-- Rank zero has an empty Hessian trace and ordinary derivative zero.
example (D : EuclideanBoundedC2Data 0) (x : Fin 0 → ℝ) :
    HasDerivAt (fun t => D.twoSidedHeatPathBcf t x) 0 0 := by
  simpa using D.hasDerivAt_twoSidedHeatPathBcf_apply_zero x

example (D : EuclideanBoundedC2Data 0) {t : ℝ} (ht : t < 0) :
    (D.negativeHeatC2Data ht).value = D.twoSidedHeatPathBcf t :=
  D.negativeHeatC2Data_value_eq ht

example (f : BoundedContinuousFunction (Fin 0 → ℝ) ℝ) {s : ℝ} (hs : 0 < s) :
    (heatSmoothedBoundedC2Data hs f).value = heatSemigroupNDbcf hs f := rfl
