import ChartPort.ChosenChartRiemannComponents

noncomputable section
open Bundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace ChartPort.ChosenChartRiemannComponentsEvidence
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem localBracket (α : M) (a b : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    VectorField.mlieBracket I (chartLocalFrame (I := I) α a) (chartLocalFrame (I := I) α b) x = 0 :=
  chartLocalFrame_mlieBracket_zero α a b hx

section WithBoundaryless
variable [BoundarylessManifold I M]
theorem rankZero (hzero : Module.finrank ℝ E = 0)
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    ∀ a b c k : Fin (Module.finrank ℝ E),
      timeFamilyChosenChartCurvatureComponent g t α a b c k x =
        chartRiemannTensor (I := I) (g t) α c a b k (extChartAt I α x) := by
  intro a b c k
  have _rankIsZero := hzero
  exact timeFamilyChosenChartCurvatureComponent_eq_chartRiemannTensor g t α a b c k hx
end WithBoundaryless

theorem empty [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    (a b c k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    timeFamilyChosenChartCurvatureComponent g t α a b c k x =
      chartRiemannTensor (I := I) (g t) α c a b k (extChartAt I α x) :=
  timeFamilyChosenChartCurvatureComponent_eq_chartRiemannTensor g t α a b c k hx
end ChartPort.ChosenChartRiemannComponentsEvidence

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
#print ChartPort.chartLocalFrame_contMDiffOn_goodSet
#print ChartPort.chartLocalFrame_mlieBracket_zero
#print ChartPort.christoffelCorrection_frameDirection_component
#print ChartPort.chartLeviCivita_frameDirection_component
#print ChartPort.chartLeviCivita_frame_repr_component
#print ChartPort.eventually_chartLeviCivita_frame_pullback_component
#print ChartPort.chartLeviCivita_frame_pullback_partialDeriv
#print ChartPort.chartAlong_nested_frame_component
#print ChartPort.chartCurvatureCommutator_frame_component_eq_chartRiemannTensor
#print ChartPort.timeFamilyChosenChartCurvatureComponent
#print ChartPort.timeFamilyChosenChartCurvatureComponent_eq_chartRiemannTensor
#print ChartPort.ChosenChartRiemannComponentsEvidence.localBracket
#print ChartPort.ChosenChartRiemannComponentsEvidence.rankZero
#print ChartPort.ChosenChartRiemannComponentsEvidence.empty
#print DifferentialGeometry.Geometry.Operator.chartChristoffel
#print DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor
#print DifferentialGeometry.Geometry.Operator.chartChristoffel_symm
#print DifferentialGeometry.Integral.DivergenceTheorem.partialDeriv
#print CovariantDerivative.curvatureTensor
#print CovariantDerivative.curvatureAux
#print ChartPort.chartCurvatureCommutator
#print DifferentialGeometry.Geometry.Connection.chartLeviCivita
#print DifferentialGeometry.Geometry.Connection.chartLeviCivita_apply
#print Bundle.Trivialization.localFrameCoeff
#print RicciFlow.SmoothForward.toC2
#print ChartPort.timeFamilyChosen_eq_chartLeviCivita
#print ChartPort.timeFamilyChosen_curvatureTensor_eq_chartCommutator
#print ChartPort.timeFamilyChosenChartCoefficient_eq_chartChristoffel

#print axioms ChartPort.chartLocalFrame_contMDiffOn_goodSet
#print axioms ChartPort.chartLocalFrame_mlieBracket_zero
#print axioms ChartPort.christoffelCorrection_frameDirection_component
#print axioms ChartPort.chartLeviCivita_frameDirection_component
#print axioms ChartPort.chartLeviCivita_frame_repr_component
#print axioms ChartPort.eventually_chartLeviCivita_frame_pullback_component
#print axioms ChartPort.chartLeviCivita_frame_pullback_partialDeriv
#print axioms ChartPort.chartAlong_nested_frame_component
#print axioms ChartPort.chartCurvatureCommutator_frame_component_eq_chartRiemannTensor
#print axioms ChartPort.timeFamilyChosenChartCurvatureComponent
#print axioms ChartPort.timeFamilyChosenChartCurvatureComponent_eq_chartRiemannTensor
#print axioms ChartPort.ChosenChartRiemannComponentsEvidence.localBracket
#print axioms ChartPort.ChosenChartRiemannComponentsEvidence.rankZero
#print axioms ChartPort.ChosenChartRiemannComponentsEvidence.empty
#print axioms DifferentialGeometry.Geometry.Operator.chartChristoffel
#print axioms DifferentialGeometry.Integral.DivergenceTheorem.chartRiemannTensor
#print axioms CovariantDerivative.curvatureTensor
#print axioms CovariantDerivative.curvatureAux
#print axioms DifferentialGeometry.Geometry.Connection.chartLeviCivita
#print axioms Bundle.Trivialization.localFrameCoeff
#print axioms RicciFlow.SmoothForward.toC2
#print axioms ChartPort.timeFamilyChosen_eq_chartLeviCivita
#print axioms ChartPort.timeFamilyChosen_curvatureTensor_eq_chartCommutator
#print axioms ChartPort.timeFamilyChosenChartCoefficient_eq_chartChristoffel

set_option pp.explicit false
#check ChartPort.chartLocalFrame_mlieBracket_zero
#check ChartPort.chartLeviCivita_frameDirection_component
#check ChartPort.chartLeviCivita_frame_pullback_partialDeriv
#check ChartPort.timeFamilyChosenChartCurvatureComponent
#check ChartPort.timeFamilyChosenChartCurvatureComponent_eq_chartRiemannTensor
#check ChartPort.ChosenChartRiemannComponentsEvidence.localBracket
#check ChartPort.ChosenChartRiemannComponentsEvidence.rankZero
#check ChartPort.ChosenChartRiemannComponentsEvidence.empty
