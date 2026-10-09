import ChartPort.ChosenChartRicciTrace

noncomputable section
open Bundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace ChartPort.ChosenChartRicciTraceEvidence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

section WithBoundaryless
variable [BoundarylessManifold I M]
theorem rankZero (hzero : Module.finrank ℝ E = 0)
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∀ i k : Fin (Module.finrank ℝ E),
      chartRicciTensor (I := I) (g t) α i k (extChartAt I α x) =
        letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
          ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
        letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
        CovariantDerivative.ricciCurvature (cov := timeFamilyChosen g t) x
          (chartLocalFrame (I := I) α k x) (chartLocalFrame (I := I) α i x) := by
  intro i k
  have _rankIsZero := hzero
  exact chartRicciTensor_eq_timeFamilyChosen_ricciCurvature_transposed g t α i k hx

theorem rankZeroTrace (hzero : Module.finrank ℝ E = 0)
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) (u w : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
    letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
    CovariantDerivative.ricciCurvature (cov := timeFamilyChosen g t) x u w = 0 := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
  letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
  letI : IsEmpty (Fin (Module.finrank ℝ E)) := by rw [hzero]; infer_instance
  rw [SourceLocalRicciTrace.ricciCurvature_eq_sum_localFrameCoeff (cov := timeFamilyChosen g t)
    (chartModelBasis E) α (chartLeviCivitaGoodSet_mem_baseSet hx)]
  exact Finset.sum_eq_zero (fun j _ => isEmptyElim j)
end WithBoundaryless

theorem empty [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    (i k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartRicciTensor (I := I) (g t) α i k (extChartAt I α x) =
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
      letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
      CovariantDerivative.ricciCurvature (cov := timeFamilyChosen g t) x
        (chartLocalFrame (I := I) α k x) (chartLocalFrame (I := I) α i x) :=
  chartRicciTensor_eq_timeFamilyChosen_ricciCurvature_transposed g t α i k hx
end ChartPort.ChosenChartRicciTraceEvidence

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
#print ChartPort.SourceLocalRicciTrace.repr_basisAt_eq_localFrameCoeff
#print ChartPort.SourceLocalRicciTrace.ricciCurvature_eq_sum_localFrameCoeff
#print ChartPort.chartRicciTensor_eq_timeFamilyChosen_ricciCurvature_transposed
#print ChartPort.ChosenChartRicciTraceEvidence.rankZero
#print ChartPort.ChosenChartRicciTraceEvidence.rankZeroTrace
#print ChartPort.ChosenChartRicciTraceEvidence.empty
#print CovariantDerivative.ricciCurvature
#print CovariantDerivative.ricciCurvature_apply
#print CovariantDerivative.ricciEndomorphism
#print CovariantDerivative.ricciEndomorphism_apply
#print CovariantDerivative.curvatureTensor
#print DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor
#print DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor
#print Bundle.Trivialization.localFrameCoeff
#print LinearMap.trace
#print LinearMap.trace_eq_matrix_trace
#print RicciFlow.SmoothForward.toC2
#print ChartPort.timeFamilyChosen_contMDiffCovariantDerivative_one
#print ChartPort.timeFamilyChosenChartCurvatureComponent
#print ChartPort.timeFamilyChosenChartCurvatureComponent_eq_chartRiemannTensor

#print axioms ChartPort.SourceLocalRicciTrace.repr_basisAt_eq_localFrameCoeff
#print axioms ChartPort.SourceLocalRicciTrace.ricciCurvature_eq_sum_localFrameCoeff
#print axioms ChartPort.chartRicciTensor_eq_timeFamilyChosen_ricciCurvature_transposed
#print axioms ChartPort.ChosenChartRicciTraceEvidence.rankZero
#print axioms ChartPort.ChosenChartRicciTraceEvidence.rankZeroTrace
#print axioms ChartPort.ChosenChartRicciTraceEvidence.empty
#print axioms CovariantDerivative.ricciCurvature
#print axioms CovariantDerivative.ricciEndomorphism
#print axioms CovariantDerivative.curvatureTensor
#print axioms DifferentialGeometry.Integral.DivergenceTheorem.chartRicciTensor
#print axioms DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor
#print axioms Bundle.Trivialization.localFrameCoeff
#print axioms LinearMap.trace
#print axioms LinearMap.trace_eq_matrix_trace
#print axioms RicciFlow.SmoothForward.toC2
#print axioms ChartPort.timeFamilyChosen_contMDiffCovariantDerivative_one
#print axioms ChartPort.timeFamilyChosenChartCurvatureComponent_eq_chartRiemannTensor

set_option pp.explicit false
#check ChartPort.SourceLocalRicciTrace.repr_basisAt_eq_localFrameCoeff
#check ChartPort.SourceLocalRicciTrace.ricciCurvature_eq_sum_localFrameCoeff
#check ChartPort.chartRicciTensor_eq_timeFamilyChosen_ricciCurvature_transposed
#check ChartPort.ChosenChartRicciTraceEvidence.rankZero
#check ChartPort.ChosenChartRicciTraceEvidence.rankZeroTrace
#check ChartPort.ChosenChartRicciTraceEvidence.empty
