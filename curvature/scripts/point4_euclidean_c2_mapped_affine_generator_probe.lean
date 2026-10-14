import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2MappedAffineGenerator

-- Source-only full statements and empty-dimension actual right-derivative probes.
open scoped BigOperators Topology
open Set Filter RicciFlow.AnalyticPDE

abbrev ExpectedMappedAffineInitialValue :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ),
    mappedAffineHeatFlowPath D a L 0 z = D.value z

def mappedAffineInitialValueFullSignatureAssignment : ExpectedMappedAffineInitialValue :=
  @mappedAffineHeatFlowPath_zero

abbrev ExpectedMappedAffineActualInitialGenerator :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ),
    HasDerivWithinAt (fun t => mappedAffineHeatFlowPath D a L t z)
      (∑ p : Fin n, ∑ q : Fin n, affineSpatialGramCoefficient L p q * D.second p q z)
      (Ici 0) 0

def mappedAffineActualInitialGeneratorFullSignatureAssignment : ExpectedMappedAffineActualInitialGenerator :=
  @hasDerivWithinAt_mappedAffineHeatFlowPath_zero

-- Source and original coordinate dimensions are never identified by a cast.
example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin 0 → ℝ)) (z : Fin 0 → ℝ) :
    mappedAffineHeatFlowPath D a L 0 z = D.value z :=
  mappedAffineHeatFlowPath_zero D a L z

example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) ≃L[ℝ] (Fin 0 → ℝ)) (z : Fin 0 → ℝ) :
    HasDerivWithinAt (fun t => mappedAffineHeatFlowPath D a L t z) 0 (Ici 0) 0 := by
  simpa using hasDerivWithinAt_mappedAffineHeatFlowPath_zero D a L z

example {n : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin 0 → ℝ) ≃L[ℝ] (Fin n → ℝ)) (z : Fin n → ℝ) :
    HasDerivWithinAt (fun t => mappedAffineHeatFlowPath D a L t z) 0 (Ici 0) 0 := by
  simpa [affineSpatialGramCoefficient] using hasDerivWithinAt_mappedAffineHeatFlowPath_zero D a L z

set_option pp.universes false
set_option format.width 200
#check @mappedAffineHeatFlowPath_zero
#check @hasDerivWithinAt_mappedAffineHeatFlowPath_zero

#print axioms RicciFlow.AnalyticPDE.mappedAffineHeatFlowPath_zero
#print axioms RicciFlow.AnalyticPDE.hasDerivWithinAt_mappedAffineHeatFlowPath_zero
