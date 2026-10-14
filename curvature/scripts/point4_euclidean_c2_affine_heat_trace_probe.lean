import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.EuclideanC2AffineHeatTrace

-- Source-only exact signatures, empty dimensions and four semantic AX records.
open scoped BigOperators Topology
open Set Filter RicciFlow.AnalyticPDE

abbrev ExpectedAffineSecondUniformContinuity :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (hsecond : ∀ p q, UniformContinuous (D.second p q : (Fin n → ℝ) → ℝ))
    (k l : Fin m),
    UniformContinuous ((D.precompAffine a L).second k l : (Fin m → ℝ) → ℝ)

def affineSecondUniformContinuityFullSignatureAssignment : ExpectedAffineSecondUniformContinuity :=
  @EuclideanBoundedC2Data.uniformContinuous_precompAffine_second

abbrev ExpectedAffineInitialHeatC2Trace :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ))
    (hsecond : ∀ p q, UniformContinuous (D.second p q : (Fin n → ℝ) → ℝ)),
    ContinuousAt (fun t : ℝ =>
      (heatFlowPathBcf (D.precompAffine a L).value t,
        (fun k => heatFlowPathBcf ((D.precompAffine a L).first k) t),
        (fun k l => heatFlowPathBcf ((D.precompAffine a L).second k l) t))) 0

def affineInitialHeatC2TraceFullSignatureAssignment : ExpectedAffineInitialHeatC2Trace :=
  @EuclideanBoundedC2Data.continuousAt_heatC2Trace_precompAffine_zero

abbrev ExpectedAffineActualHeatHessianTrace :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (k l : Fin m)
    {K : Set (Fin m → ℝ)} (hK : IsCompact K),
    TendstoUniformlyOn
      (fun t x => heatHessianEntryConvolutionND t (D.precompAffine a L).value k l x)
      (fun x => ∑ p : Fin n, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single l 1) q) * D.second p q (a + L x))
      (𝓝[>] 0) K

def affineActualHeatHessianTraceFullSignatureAssignment : ExpectedAffineActualHeatHessianTrace :=
  @EuclideanBoundedC2Data.tendstoUniformlyOn_heatHessian_precompAffine_zero

abbrev ExpectedAffineActualInitialHeatGenerator :=
  ∀ {n m : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin n → ℝ)) (x : Fin m → ℝ),
    HasDerivWithinAt (fun t => heatFlowPathBcf (D.precompAffine a L).value t x)
      (∑ k : Fin m, ∑ p : Fin n, ∑ q : Fin n,
        (L (Pi.single k 1) p * L (Pi.single k 1) q) * D.second p q (a + L x))
      (Ici 0) 0

def affineActualInitialHeatGeneratorFullSignatureAssignment : ExpectedAffineActualInitialHeatGenerator :=
  @EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_precompAffine_apply_zero

-- No source second-slot UC hypothesis is needed when the original dimension is empty.
example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin 0 → ℝ)) (k l : Fin m) :
    UniformContinuous ((D.precompAffine a L).second k l : (Fin m → ℝ) → ℝ) :=
  D.uniformContinuous_precompAffine_second a L (fun p => Fin.elim0 p) k l

example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin 0 → ℝ)) :
    ContinuousAt (fun t : ℝ =>
      (heatFlowPathBcf (D.precompAffine a L).value t,
        (fun k => heatFlowPathBcf ((D.precompAffine a L).first k) t),
        (fun k l => heatFlowPathBcf ((D.precompAffine a L).second k l) t))) 0 :=
  D.continuousAt_heatC2Trace_precompAffine_zero a L (fun p => Fin.elim0 p)

-- Empty pulled dimension gives an actual zero right generator.
example {n : ℕ} (D : EuclideanBoundedC2Data n) (a : Fin n → ℝ)
    (L : (Fin 0 → ℝ) →L[ℝ] (Fin n → ℝ)) (x : Fin 0 → ℝ) :
    HasDerivWithinAt (fun t => heatFlowPathBcf (D.precompAffine a L).value t x) 0 (Ici 0) 0 := by
  simpa using D.hasDerivWithinAt_heatFlowPathBcf_precompAffine_apply_zero a L x

example {m : ℕ} (D : EuclideanBoundedC2Data 0) (a : Fin 0 → ℝ)
    (L : (Fin m → ℝ) →L[ℝ] (Fin 0 → ℝ)) (x : Fin m → ℝ) :
    HasDerivWithinAt (fun t => heatFlowPathBcf (D.precompAffine a L).value t x) 0 (Ici 0) 0 := by
  simpa using D.hasDerivWithinAt_heatFlowPathBcf_precompAffine_apply_zero a L x

set_option pp.universes false
set_option format.width 200
#check @EuclideanBoundedC2Data.uniformContinuous_precompAffine_second
#check @EuclideanBoundedC2Data.continuousAt_heatC2Trace_precompAffine_zero
#check @EuclideanBoundedC2Data.tendstoUniformlyOn_heatHessian_precompAffine_zero
#check @EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_precompAffine_apply_zero

#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.uniformContinuous_precompAffine_second
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.continuousAt_heatC2Trace_precompAffine_zero
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.tendstoUniformlyOn_heatHessian_precompAffine_zero
#print axioms RicciFlow.AnalyticPDE.EuclideanBoundedC2Data.hasDerivWithinAt_heatFlowPathBcf_precompAffine_apply_zero
