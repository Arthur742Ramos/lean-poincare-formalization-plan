import ChartPort.ChosenChartConnectionCoefficients

noncomputable section
open Bundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace ChartPort.ChosenChartConnectionCoefficientsEvidence
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
    ∀ i j k : Fin (Module.finrank ℝ E),
      timeFamilyChosenChartCoefficient g t α i j k x =
        chartChristoffel (I := I) (g t) α i j k (extChartAt I α x) := by
  intro i j k
  have _rankIsZero := hzero
  exact timeFamilyChosenChartCoefficient_eq_chartChristoffel g t α i j k hx

end WithBoundaryless

theorem empty [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    (i j k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    timeFamilyChosenChartCoefficient g t α i j k x =
      chartChristoffel (I := I) (g t) α i j k (extChartAt I α x) :=
  timeFamilyChosenChartCoefficient_eq_chartChristoffel g t α i j k hx

end ChartPort.ChosenChartConnectionCoefficientsEvidence

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true
#print ChartPort.chartLocalFrame
#print ChartPort.chartLocalFrame_eq_chartBasisVecFiber
#print ChartPort.chartLocalFrame_contMDiffOn_baseSet
#print ChartPort.chartLocalFrame_repr_of_mem
#print ChartPort.eventually_chartLocalFrame_pullback_constant
#print ChartPort.chartLocalFrame_pullback_fderiv_zero
#print ChartPort.christoffelCorrection_chartLocalFrame
#print ChartPort.chartLeviCivita_chartLocalFrame_apply
#print ChartPort.chartLocalFrameCoeff_eq_modelRepr
#print ChartPort.timeFamilyChosen_chartLocalFrame_apply
#print ChartPort.timeFamilyChosenChartCoefficient
#print ChartPort.timeFamilyChosenChartCoefficient_eq_chartChristoffel
#print ChartPort.ChosenChartConnectionCoefficientsEvidence.rankZero
#print ChartPort.ChosenChartConnectionCoefficientsEvidence.empty
#print DifferentialGeometry.Geometry.Operator.chartChristoffel
#print DifferentialGeometry.Geometry.Connection.chartLeviCivita
#print DifferentialGeometry.Geometry.Connection.chartLeviCivita_apply
#print Bundle.Trivialization.localFrameCoeff
#print RicciFlow.SmoothForward.toC2
#print ChartPort.timeFamilyChosen_eq_chartLeviCivita

#print axioms ChartPort.chartLocalFrame
#print axioms ChartPort.chartLocalFrame_eq_chartBasisVecFiber
#print axioms ChartPort.chartLocalFrame_contMDiffOn_baseSet
#print axioms ChartPort.chartLocalFrame_repr_of_mem
#print axioms ChartPort.eventually_chartLocalFrame_pullback_constant
#print axioms ChartPort.chartLocalFrame_pullback_fderiv_zero
#print axioms ChartPort.christoffelCorrection_chartLocalFrame
#print axioms ChartPort.chartLeviCivita_chartLocalFrame_apply
#print axioms ChartPort.chartLocalFrameCoeff_eq_modelRepr
#print axioms ChartPort.timeFamilyChosen_chartLocalFrame_apply
#print axioms ChartPort.timeFamilyChosenChartCoefficient
#print axioms ChartPort.timeFamilyChosenChartCoefficient_eq_chartChristoffel
#print axioms ChartPort.ChosenChartConnectionCoefficientsEvidence.rankZero
#print axioms ChartPort.ChosenChartConnectionCoefficientsEvidence.empty
#print axioms DifferentialGeometry.Geometry.Operator.chartChristoffel
#print axioms DifferentialGeometry.Geometry.Connection.chartLeviCivita
#print axioms Bundle.Trivialization.localFrameCoeff
#print axioms RicciFlow.SmoothForward.toC2
#print axioms ChartPort.timeFamilyChosen_eq_chartLeviCivita

set_option pp.explicit false
#check ChartPort.chartLocalFrame_pullback_fderiv_zero
#check ChartPort.timeFamilyChosenChartCoefficient
#check ChartPort.timeFamilyChosenChartCoefficient_eq_chartChristoffel
#check ChartPort.ChosenChartConnectionCoefficientsEvidence.rankZero
#check ChartPort.ChosenChartConnectionCoefficientsEvidence.empty
