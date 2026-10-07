import PoincareCurvature.Geometry.Manifold.RicciFlow.AnalyticPDE.ChosenLCFrozenTensorHeat

#print axioms PoincareCurvature.second_fderiv_linear_readout
#print axioms RicciFlow.AnalyticPDE.localFrameInChart_preferred_eq_basis
#print axioms RicciFlow.AnalyticPDE.chosenLC_localFrameInverseGramMatrix_eq_inverse
#print axioms RicciFlow.AnalyticPDE.chosenLCFrozenTensorHeatPrincipalCoefficient_apply
#print axioms RicciFlow.AnalyticPDE.second_finiteCylinderTensorReadout
#print axioms RicciFlow.AnalyticPDE.deriv_finiteCylinderTensorReadout
#print axioms RicciFlow.AnalyticPDE.evalCLM_chosenLCFrozenTensorHeatCauchyL
#print axioms RicciFlow.AnalyticPDE.evalCLM_chosenLCFrozenTensorHeatCauchyL_eq_actual_derivatives

-- Full elaborated types expose geometric assumptions and the actual derivatives.
#check @RicciFlow.AnalyticPDE.chosenLCFrozenTensorHeatPrincipalCoefficient_apply
#check @RicciFlow.AnalyticPDE.evalCLM_chosenLCFrozenTensorHeatCauchyL_eq_actual_derivatives

noncomputable section
open scoped Manifold ContDiff BigOperators
open RicciFlow.AnalyticPDE PoincareCurvature.PreferredCoordinateFrame

section GenuineReadout
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {d : ℕ} {t₀ T α : ℝ}

-- The output reversal is definitional and does not assume tensor symmetry.
example (b : Module.Basis (Fin d) ℝ E)
    (u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    (s : ℝ) (ξ : Fin d → ℝ) (i j : Fin d) :
    finiteCylinderTensorReadout b u s ξ i j =
      FiniteParabolicC2AlphaBanach.value u (s, toModel b ξ) (j, i) := rfl

-- No positive alpha, time nonemptiness, or separately supplied C2 certificate.
example (b : Module.Basis (Fin d) ℝ E)
    (u : FiniteParabolicC2AlphaBanach E (Fin d × Fin d → ℝ) t₀ T α)
    {s : ℝ} (hs : s ∈ Set.Ioc t₀ T) (ξ : Fin d → ℝ) (a c i j : Fin d) :
    PoincareCurvature.CoordinateMatrixJet.second (finiteCylinderTensorReadout b u s) ξ a c i j =
      FiniteParabolicC2AlphaBanach.spaceSecondDeriv u (s, toModel b ξ)
        (b a) (b c) (j, i) :=
  second_finiteCylinderTensorReadout b u hs ξ a c i j
end GenuineReadout

section ActualMetric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I] [SigmaCompactSpace M]
  {d : ℕ} {t₀ T α : ℝ}

-- No ambient Riemannian-bundle instance is supplied: the actual g slice selects it.
example (g : RicciFlow.MetricFamily (I := I) (M := M)) (tStar : ℝ)
    (p : M) (b : Module.Basis (Fin d) ℝ E) {x₀ : M}
    (hx₀ : x₀ ∈ (extChartAt I p).source)
    (Q : E →L[ℝ] E →L[ℝ] (Fin d × Fin d → ℝ)) (out : Fin d × Fin d) :
    chosenLCFrozenTensorHeatPrincipalCoefficient g tStar p b x₀ Q out =
      ∑ a : Fin d, ∑ c : Fin d,
        PoincareCurvature.CoordinateMatrixJet.inverse (RicciFlow.chosenLCMetricCoordinates g tStar p b)
          (RicciFlow.chosenLCCoordinatePoint (I := I) p b x₀) a c * Q (b a) (b c) out :=
  chosenLCFrozenTensorHeatPrincipalCoefficient_apply g tStar p b hx₀ Q out
end ActualMetric
