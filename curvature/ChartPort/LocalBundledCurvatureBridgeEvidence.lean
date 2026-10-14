import ChartPort.LocalBundledCurvatureBridge

noncomputable section
open Bundle
open scoped Manifold Topology ContDiff

namespace ChartPort.LocalBundledCurvatureBridgeEvidence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

theorem rankZero_one (hzero : Module.finrank ℝ E = 0)
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative (ChartPort.timeFamilyChosen g t) 1 := by
  have _rankIsZero := hzero
  exact ChartPort.timeFamilyChosen_contMDiffCovariantDerivative_one g t

omit [BoundarylessManifold I M] in
theorem empty_one [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative (ChartPort.timeFamilyChosen g t) 1 :=
  ChartPort.timeFamilyChosen_contMDiffCovariantDerivative_one g t

example : ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I := inferInstance

end ChartPort.LocalBundledCurvatureBridgeEvidence

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true

#print ChartPort.timeFamilyChosen_contMDiffCovariantDerivativeOn_infinity
#print ChartPort.timeFamilyChosen_contMDiffCovariantDerivative_one
#print ChartPort.LocalBundledCurvatureBridgeEvidence.rankZero_one
#print ChartPort.LocalBundledCurvatureBridgeEvidence.empty_one
#print ChartPort.timeFamilyChosen_contMDiffCovariantDerivative
#print ChartPort.timeFamilyChosen_curvatureAux_eq_chartCommutator
#print CovariantDerivative.curvatureTensor
#print ChartPort.timeFamilyChosen
#print RicciFlow.SmoothForward.toC2

#print axioms ChartPort.timeFamilyChosen_contMDiffCovariantDerivativeOn_infinity
#print axioms ChartPort.timeFamilyChosen_contMDiffCovariantDerivative_one
#print axioms ChartPort.LocalBundledCurvatureBridgeEvidence.rankZero_one
#print axioms ChartPort.LocalBundledCurvatureBridgeEvidence.empty_one
#print axioms ChartPort.timeFamilyChosen_contMDiffCovariantDerivative
#print axioms ChartPort.timeFamilyChosen_curvatureAux_eq_chartCommutator
#print axioms CovariantDerivative.curvatureTensor
#print axioms RicciFlow.SmoothForward.toC2
