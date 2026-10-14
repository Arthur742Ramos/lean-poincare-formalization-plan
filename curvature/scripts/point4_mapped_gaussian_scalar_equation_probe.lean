import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.MappedGaussianScalarEquation

noncomputable section

-- Source-only whole types, actual spatial certificates and empty-dimension probes.
open scoped BigOperators Topology
open Set Filter RicciFlow.AnalyticPDE

abbrev ExpectedMappedGaussianC2Data :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ}, 0 < t → EuclideanBoundedC2Data n

def mappedGaussianC2DataFullSignatureAssignment : ExpectedMappedGaussianC2Data :=
  @mappedGaussianBoundedC2Data

abbrev ExpectedMappedGaussianValueIdentity :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ} (ht : 0 < t) (z : Fin n → ℝ),
    (mappedGaussianBoundedC2Data D a L ht).value z = mappedAffineHeatFlowPath D a L t z

def mappedGaussianValueIdentityFullSignatureAssignment : ExpectedMappedGaussianValueIdentity :=
  @mappedGaussianBoundedC2Data_value_eq_path

abbrev ExpectedMappedGaussianActualSpatialDerivative :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (p : Fin n) (z : Fin n → ℝ),
    HasDerivAt (fun r => mappedAffineHeatFlowPath D a L t (Function.update z p r))
      ((mappedGaussianBoundedC2Data D a L ht).first p z) (z p)

def mappedGaussianActualSpatialDerivativeFullSignatureAssignment : ExpectedMappedGaussianActualSpatialDerivative :=
  @hasDerivAt_mappedAffineHeatFlowPath_coordinate

abbrev ExpectedMappedGaussianActualHessian :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (p q : Fin n) (z : Fin n → ℝ),
    (mappedGaussianBoundedC2Data D a L ht).second p q z =
      ∑ k : Fin m, ∑ l : Fin m,
        (L.symm (Pi.single p 1) k * L.symm (Pi.single q 1) l) *
          heatSemigroupND t ((D.precompAffine a L.toContinuousLinearMap).second k l)
            (L.symm (z - a))

def mappedGaussianActualHessianFullSignatureAssignment : ExpectedMappedGaussianActualHessian :=
  @mappedGaussianBoundedC2Data_second_apply

abbrev ExpectedMappedGaussianActualScalarEquation :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ} (ht : 0 < t) (z : Fin n → ℝ),
    HasDerivAt (fun s => mappedAffineHeatFlowPath D a L s z)
      (∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q *
        (mappedGaussianBoundedC2Data D a L ht).second p q z) t

def mappedGaussianActualScalarEquationFullSignatureAssignment : ExpectedMappedGaussianActualScalarEquation :=
  @hasDerivAt_mappedAffineHeatFlowPath_eq_coefficientHessian

-- Actual second certificates differentiate first_q in original direction p.
example {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ} (ht : 0 < t)
    (p q : Fin n) (z : Fin n → ℝ) :
    HasDerivAt (fun r => (mappedGaussianBoundedC2Data D a L ht).first q (Function.update z p r))
      ((mappedGaussianBoundedC2Data D a L ht).second p q z) (z p) :=
  (mappedGaussianBoundedC2Data D a L ht).hasDeriv_first p q z

example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin 0 → ℝ)) {t : ℝ} (ht : 0 < t) :
    EuclideanBoundedC2Data 0 := mappedGaussianBoundedC2Data D a L ht

example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin 0 → ℝ)) {t : ℝ} (ht : 0 < t) (z : Fin 0 → ℝ) :
    HasDerivAt (fun s => mappedAffineHeatFlowPath D a L s z) 0 t := by
  simpa using hasDerivAt_mappedAffineHeatFlowPath_eq_coefficientHessian D a L ht z

example {n : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin 0 → ℝ) ≃L[ℝ] (Fin n → ℝ)) {t : ℝ} (ht : 0 < t) (z : Fin n → ℝ) :
    HasDerivAt (fun s => mappedAffineHeatFlowPath D a L s z) 0 t := by
  simpa [affineSpatialGramCoefficient] using
    hasDerivAt_mappedAffineHeatFlowPath_eq_coefficientHessian D a L ht z

set_option pp.universes false
set_option format.width 200
#check @mappedGaussianBoundedC2Data
#check @mappedGaussianBoundedC2Data_value_eq_path
#check @hasDerivAt_mappedAffineHeatFlowPath_coordinate
#check @mappedGaussianBoundedC2Data_second_apply
#check @hasDerivAt_mappedAffineHeatFlowPath_eq_coefficientHessian

#print axioms RicciFlow.AnalyticPDE.mappedGaussianBoundedC2Data
#print axioms RicciFlow.AnalyticPDE.mappedGaussianBoundedC2Data_value_eq_path
#print axioms RicciFlow.AnalyticPDE.hasDerivAt_mappedAffineHeatFlowPath_coordinate
#print axioms RicciFlow.AnalyticPDE.mappedGaussianBoundedC2Data_second_apply
#print axioms RicciFlow.AnalyticPDE.hasDerivAt_mappedAffineHeatFlowPath_eq_coefficientHessian
