import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.MappedHeatStrongInitialGenerator

noncomputable section

-- Source-only original-coordinate BCF-valued derivative, retaining initial hsecond.
open scoped BigOperators Topology
open Set Filter RicciFlow.AnalyticPDE

abbrev ExpectedActualMappedHeatBcf :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (t : ℝ),
    BoundedContinuousFunction (Fin n → ℝ) ℝ

def actualMappedHeatBcfFullSignatureAssignment : ExpectedActualMappedHeatBcf :=
  @mappedAffineHeatFlowBcf

abbrev ExpectedActualMappedHeatBcfValue :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (t : ℝ) (z : Fin n → ℝ),
    mappedAffineHeatFlowBcf D a L t z = mappedAffineHeatFlowPath D a L t z

def actualMappedHeatBcfValueFullSignatureAssignment : ExpectedActualMappedHeatBcfValue :=
  @mappedAffineHeatFlowBcf_apply

abbrev ExpectedActualMappedHeatStrongRightInitialDerivative :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hsecond : ∀ p q, UniformContinuous (D.second p q : (Fin n → ℝ) → ℝ)),
    HasDerivWithinAt (mappedAffineHeatFlowBcf D a L)
      (∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q • D.second p q)
      (Ici 0) 0

def actualMappedHeatStrongRightInitialDerivativeFullSignatureAssignment : ExpectedActualMappedHeatStrongRightInitialDerivative :=
  @hasDerivWithinAt_mappedAffineHeatFlowBcf_strong_zero

example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin 0 → ℝ)) :
    HasDerivWithinAt (mappedAffineHeatFlowBcf D a L)
      (0 : BoundedContinuousFunction (Fin 0 → ℝ) ℝ) (Ici 0) 0 := by
  simpa using hasDerivWithinAt_mappedAffineHeatFlowBcf_strong_zero D a L (fun p => Fin.elim0 p)

example {n : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin 0 → ℝ) ≃L[ℝ] (Fin n → ℝ))
    (hsecond : ∀ p q, UniformContinuous (D.second p q : (Fin n → ℝ) → ℝ)) :
    HasDerivWithinAt (mappedAffineHeatFlowBcf D a L)
      (0 : BoundedContinuousFunction (Fin n → ℝ) ℝ) (Ici 0) 0 := by
  simpa [affineSpatialGramCoefficient] using
    hasDerivWithinAt_mappedAffineHeatFlowBcf_strong_zero D a L hsecond

set_option pp.universes false
set_option format.width 200
#check @mappedAffineHeatFlowBcf
#check @mappedAffineHeatFlowBcf_apply
#check @hasDerivWithinAt_mappedAffineHeatFlowBcf_strong_zero

#print axioms RicciFlow.AnalyticPDE.mappedAffineHeatFlowBcf
#print axioms RicciFlow.AnalyticPDE.mappedAffineHeatFlowBcf_apply
#print axioms RicciFlow.AnalyticPDE.hasDerivWithinAt_mappedAffineHeatFlowBcf_strong_zero
