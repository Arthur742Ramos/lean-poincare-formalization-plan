import ChartPort.LocalRawCurvatureBridge

noncomputable section
open Bundle
open scoped Manifold Topology ContDiff

namespace ChartPort.LocalRawCurvatureBridgeEvidence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

/-- The genuine bridge specializes to model rank zero without a positive-rank instance. -/
theorem rankZero_bridge (hzero : Module.finrank ℝ E = 0)
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {X Y σ : Π y : M, TangentSpace I y} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% X)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)) :
    (ChartPort.timeFamilyChosen g t).curvatureAux X Y σ x =
      ChartPort.chartCurvatureCommutator (g t) α X Y σ x := by
  have _rankIsZero := hzero
  exact ChartPort.timeFamilyChosen_curvatureAux_eq_chartCommutator g t α hx hX hY hσ

omit [BoundarylessManifold I M] in
/-- An empty base provides its own M-only boundaryless instance for the actual bridge. -/
theorem empty_bridge [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {X Y σ : Π y : M, TangentSpace I y} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% X)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)) :
    (ChartPort.timeFamilyChosen g t).curvatureAux X Y σ x =
      ChartPort.chartCurvatureCommutator (g t) α X Y σ x :=
  ChartPort.timeFamilyChosen_curvatureAux_eq_chartCommutator g t α hx hX hY hσ

/-- Verify the project's raw operator has exactly the advertised nested definition. -/
theorem actual_curvatureAux_definition
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    (X Y σ : Π y : M, TangentSpace I y) (x : M) :
    (ChartPort.timeFamilyChosen g t).curvatureAux X Y σ x =
      (ChartPort.timeFamilyChosen g t).along X ((ChartPort.timeFamilyChosen g t).along Y σ) x -
      (ChartPort.timeFamilyChosen g t).along Y ((ChartPort.timeFamilyChosen g t).along X σ) x -
      (ChartPort.timeFamilyChosen g t).along (VectorField.mlieBracket I X Y) σ x := rfl

end ChartPort.LocalRawCurvatureBridgeEvidence

set_option pp.universes true
set_option pp.fullNames true
set_option pp.explicit true

#print CovariantDerivative.curvatureAux
#print ChartPort.chartAlong
#print ChartPort.chartCurvatureCommutator
#print ChartPort.timeFamilyChosen_along_contMDiff
#print ChartPort.chartAlong_contMDiffOn_goodSet
#print ChartPort.eventually_timeFamilyChosen_along_eq_chartAlong
#print ChartPort.timeFamilyChosen_nestedAlong_eq_chartAlong
#print ChartPort.timeFamilyChosen_curvatureAux_eq_chartCommutator
#print ChartPort.LocalRawCurvatureBridgeEvidence.rankZero_bridge
#print ChartPort.LocalRawCurvatureBridgeEvidence.empty_bridge
#print ChartPort.LocalRawCurvatureBridgeEvidence.actual_curvatureAux_definition
#print IsCovariantDerivativeOn.congr_of_eventuallyEq
#print ChartPort.timeFamilyChosen_contMDiffCovariantDerivative
#print DifferentialGeometry.Geometry.Connection.chartLeviCivita_contMDiffCovariantDerivativeOn
#print ChartPort.timeFamilyChosen
#print ChartPort.downgradedC2Family
#print RicciFlow.SmoothForward.toC2

#print axioms ChartPort.chartAlong
#print axioms ChartPort.chartCurvatureCommutator
#print axioms ChartPort.timeFamilyChosen_along_contMDiff
#print axioms ChartPort.chartAlong_contMDiffOn_goodSet
#print axioms ChartPort.eventually_timeFamilyChosen_along_eq_chartAlong
#print axioms ChartPort.timeFamilyChosen_nestedAlong_eq_chartAlong
#print axioms ChartPort.timeFamilyChosen_curvatureAux_eq_chartCommutator
#print axioms ChartPort.LocalRawCurvatureBridgeEvidence.rankZero_bridge
#print axioms ChartPort.LocalRawCurvatureBridgeEvidence.empty_bridge
#print axioms ChartPort.LocalRawCurvatureBridgeEvidence.actual_curvatureAux_definition
#print axioms CovariantDerivative.curvatureAux
#print axioms IsCovariantDerivativeOn.congr_of_eventuallyEq
#print axioms ChartPort.timeFamilyChosen_contMDiffCovariantDerivative
#print axioms DifferentialGeometry.Geometry.Connection.chartLeviCivita_contMDiffCovariantDerivativeOn
#print axioms RicciFlow.SmoothForward.toC2
