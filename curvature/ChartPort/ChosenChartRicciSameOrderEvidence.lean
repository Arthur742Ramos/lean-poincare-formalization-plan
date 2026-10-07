import ChartPort.ChosenChartRicciSameOrder

noncomputable section
open Bundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace ChartPort.ChosenChartRicciSameOrderEvidence
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
          (chartLocalFrame (I := I) α i x) (chartLocalFrame (I := I) α k x) := by
  intro i k
  have _rankIsZero := hzero
  exact chartRicciTensor_eq_timeFamilyChosen_ricciCurvature g t α i k hx

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
        (chartLocalFrame (I := I) α i x) (chartLocalFrame (I := I) α k x) :=
  chartRicciTensor_eq_timeFamilyChosen_ricciCurvature g t α i k hx
theorem metricRegularity (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(RicciFlow.SmoothForward.toC2 g).toRiemannianMetric⟩
    letI : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
      Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
        (E := (TangentSpace I : M → Type _)) y
    letI : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) := fun y =>
      Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) y
    IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(RicciFlow.SmoothForward.toC2 g).toRiemannianMetric⟩
  letI : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := (TangentSpace I : M → Type _)) y
  letI : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) := fun y =>
    Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) y
  infer_instance

theorem chosenLeviCivita
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
    (timeFamilyChosen g t).IsLeviCivita := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
  exact (downgradedC2Family g).someContMDiffLeviCivitaConnection_isLeviCivita t

end ChartPort.ChosenChartRicciSameOrderEvidence

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
#print ChartPort.timeFamilyChosen_ricciCurvature_symm
#print ChartPort.chartRicciTensor_eq_timeFamilyChosen_ricciCurvature
#print ChartPort.ChosenChartRicciSameOrderEvidence.rankZero
#print ChartPort.ChosenChartRicciSameOrderEvidence.rankZeroTrace
#print ChartPort.ChosenChartRicciSameOrderEvidence.empty
#print ChartPort.ChosenChartRicciSameOrderEvidence.metricRegularity
#print ChartPort.ChosenChartRicciSameOrderEvidence.chosenLeviCivita
#print CovariantDerivative.ricciCurvature_symm_of_isLeviCivita
#print CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
#print CovariantDerivative.ricciCurvature
#print RicciFlow.SmoothForward.toC2
#print ChartPort.timeFamilyChosen_contMDiffCovariantDerivative_one
#print ChartPort.chartRicciTensor_eq_timeFamilyChosen_ricciCurvature_transposed
#print Bundle.ContMDiffRiemannianMetric.toRiemannianMetric
#print ChartPort.timeFamilyChosen
#print ChartPort.downgradedC2Family
#print axioms ChartPort.timeFamilyChosen_ricciCurvature_symm
#print axioms ChartPort.chartRicciTensor_eq_timeFamilyChosen_ricciCurvature
#print axioms ChartPort.ChosenChartRicciSameOrderEvidence.rankZero
#print axioms ChartPort.ChosenChartRicciSameOrderEvidence.rankZeroTrace
#print axioms ChartPort.ChosenChartRicciSameOrderEvidence.empty
#print axioms ChartPort.ChosenChartRicciSameOrderEvidence.metricRegularity
#print axioms ChartPort.ChosenChartRicciSameOrderEvidence.chosenLeviCivita
#print axioms CovariantDerivative.ricciCurvature_symm_of_isLeviCivita
#print axioms CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
#print axioms CovariantDerivative.ricciCurvature
#print axioms RicciFlow.SmoothForward.toC2
#print axioms ChartPort.timeFamilyChosen_contMDiffCovariantDerivative_one
#print axioms ChartPort.chartRicciTensor_eq_timeFamilyChosen_ricciCurvature_transposed
set_option pp.explicit false
#check ChartPort.timeFamilyChosen_ricciCurvature_symm
#check ChartPort.chartRicciTensor_eq_timeFamilyChosen_ricciCurvature
#check ChartPort.ChosenChartRicciSameOrderEvidence.rankZero
#check ChartPort.ChosenChartRicciSameOrderEvidence.rankZeroTrace
#check ChartPort.ChosenChartRicciSameOrderEvidence.empty
#check ChartPort.ChosenChartRicciSameOrderEvidence.metricRegularity
#check ChartPort.ChosenChartRicciSameOrderEvidence.chosenLeviCivita
