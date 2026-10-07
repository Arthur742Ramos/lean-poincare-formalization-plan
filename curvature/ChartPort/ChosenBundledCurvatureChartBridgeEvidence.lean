import ChartPort.ChosenBundledCurvatureChartBridge

noncomputable section
open Bundle
open scoped Manifold ContDiff Topology

namespace ChartPort.ChosenBundledCurvatureChartBridgeEvidence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- The transplanted local tensor result needs no boundarylessness hypothesis. -/
theorem localRawTensor_noBoundaryless
    [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
    {cov : CovariantDerivative I E (TangentSpace I : M → Type _)}
    [CovariantDerivative.ContMDiffCovariantDerivative cov 1]
    {X Y σ : Π y : M, TangentSpace I y} {u : Set M} (hu : IsOpen u) {x : M} (hx : x ∈ u)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% X) u)
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% Y) u)
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) 2 (T% σ) u) :
    cov.curvatureAux X Y σ x = CovariantDerivative.curvatureTensor (cov := cov) x (X x) (Y x) (σ x) :=
  SourceLocalCurvature.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame hu hx hX hY hσ

section WithBoundaryless
variable [BoundarylessManifold I M]

theorem rankZero (hzero : Module.finrank ℝ E = 0)
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {X Y σ : Π y : M, TangentSpace I y} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% X)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)) :
    letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
    CovariantDerivative.curvatureTensor (cov := timeFamilyChosen g t) x (X x) (Y x) (σ x) =
      chartCurvatureCommutator (g t) α X Y σ x := by
  have _rankIsZero := hzero
  exact timeFamilyChosen_curvatureTensor_eq_chartCommutator g t α hx hX hY hσ

end WithBoundaryless

theorem empty [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {X Y σ : Π y : M, TangentSpace I y} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% X)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)) :
    letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
    CovariantDerivative.curvatureTensor (cov := timeFamilyChosen g t) x (X x) (Y x) (σ x) =
      chartCurvatureCommutator (g t) α X Y σ x :=
  timeFamilyChosen_curvatureTensor_eq_chartCommutator g t α hx hX hY hσ

end ChartPort.ChosenBundledCurvatureChartBridgeEvidence

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true

#print ChartPort.SourceLocalCurvature.curvatureAux_apply_eq_of_eventuallyEq_fields
#print ChartPort.SourceLocalCurvature.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
#print ChartPort.timeFamilyChosen_curvatureTensor_eq_chartCommutator
#print ChartPort.ChosenBundledCurvatureChartBridgeEvidence.localRawTensor_noBoundaryless
#print ChartPort.ChosenBundledCurvatureChartBridgeEvidence.rankZero
#print ChartPort.ChosenBundledCurvatureChartBridgeEvidence.empty
#print ChartPort.timeFamilyChosen_contMDiffCovariantDerivative_one
#print ChartPort.timeFamilyChosen_curvatureAux_eq_chartCommutator
#print CovariantDerivative.curvatureTensor
#print ChartPort.chartCurvatureCommutator
#print ChartPort.chartAlong
#print RicciFlow.SmoothForward.toC2

#print axioms ChartPort.SourceLocalCurvature.curvatureAux_apply_eq_of_eventuallyEq_fields
#print axioms ChartPort.SourceLocalCurvature.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
#print axioms ChartPort.timeFamilyChosen_curvatureTensor_eq_chartCommutator
#print axioms ChartPort.ChosenBundledCurvatureChartBridgeEvidence.localRawTensor_noBoundaryless
#print axioms ChartPort.ChosenBundledCurvatureChartBridgeEvidence.rankZero
#print axioms ChartPort.ChosenBundledCurvatureChartBridgeEvidence.empty
#print axioms ChartPort.timeFamilyChosen_contMDiffCovariantDerivative_one
#print axioms ChartPort.timeFamilyChosen_curvatureAux_eq_chartCommutator
#print axioms CovariantDerivative.curvatureTensor
#print axioms RicciFlow.SmoothForward.toC2

set_option pp.explicit false
#check ChartPort.SourceLocalCurvature.curvatureAux_apply_eq_of_eventuallyEq_fields
#check ChartPort.SourceLocalCurvature.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
#check ChartPort.timeFamilyChosen_curvatureTensor_eq_chartCommutator
#check ChartPort.ChosenBundledCurvatureChartBridgeEvidence.localRawTensor_noBoundaryless
#check ChartPort.ChosenBundledCurvatureChartBridgeEvidence.rankZero
#check ChartPort.ChosenBundledCurvatureChartBridgeEvidence.empty
