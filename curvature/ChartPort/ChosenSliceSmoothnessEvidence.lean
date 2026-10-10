import ChartPort.ChosenSliceSmoothness

noncomputable section
open Bundle
open scoped Manifold Topology ContDiff

namespace ChartPort.ChosenSliceSmoothnessEvidence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

/-- The actual choice of the literal downgraded family has spatial infinity regularity. -/
theorem actualFamilySlice_contMDiffCovariantDerivative
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
        (I := I) (M := M) (fun s => RicciFlow.SmoothForward.toC2 (g s)) t) ∞ := by
  exact ChartPort.timeFamilyChosen_contMDiffCovariantDerivative g t

omit [BoundarylessManifold I M] in
/-- The genuine chart regularity theorem is available at rank zero without a NeZero instance. -/
theorem chartRankZero_case (hzero : Module.finrank ℝ E = 0)
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M) :
    ContMDiffCovariantDerivativeOn (V := (TangentSpace I : M → Type _))
      E ∞ (DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) g α)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α) := by
  have _rankIsZero := hzero
  exact DifferentialGeometry.Geometry.Connection.chartLeviCivita_contMDiffCovariantDerivativeOn g α

/-- The chosen slice has spatial infinity regularity also when the real model has rank zero. -/
theorem chosenRankZero_case (hzero : Module.finrank ℝ E = 0)
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative (ChartPort.timeFamilyChosen g t) ∞ := by
  have _rankIsZero := hzero
  exact ChartPort.timeFamilyChosen_contMDiffCovariantDerivative g t

omit [BoundarylessManifold I M] in
/-- In rank zero the actual chosen and chart operators both take values in a zero fiber. -/
theorem rankZero_values_case (hzero : Module.finrank ℝ E = 0)
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    (σ : Π y : M, TangentSpace I y) (α x : M) (v : TangentSpace I x) :
    ChartPort.timeFamilyChosen g t σ x v = 0 ∧
      DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) α σ x v = 0 := by
  letI : Subsingleton (TangentSpace I x) := by
    change Subsingleton E
    exact Module.finrank_zero_iff.mp hzero
  exact ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

omit [BoundarylessManifold I M] in
/-- Empty manifolds supply their M-only boundaryless instance for the chosen-slice result. -/
theorem emptyChosen_case [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative (ChartPort.timeFamilyChosen g t) ∞ := by
  exact ChartPort.timeFamilyChosen_contMDiffCovariantDerivative g t

omit [BoundarylessManifold I M] in
/-- The genuine chart result also elaborates with an empty base manifold. -/
theorem emptyChart_case [IsEmpty M]
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (α : M) :
    ContMDiffCovariantDerivativeOn (V := (TangentSpace I : M → Type _))
      E ∞ (DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) g α)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α) := by
  exact DifferentialGeometry.Geometry.Connection.chartLeviCivita_contMDiffCovariantDerivativeOn g α

end ChartPort.ChosenSliceSmoothnessEvidence

#print ContMDiffCovariantDerivativeOn
#print CovariantDerivative.ContMDiffCovariantDerivative
#print ChartPort.timeFamilyChosen_contMDiffCovariantDerivative
#print ChartPort.ChosenSliceSmoothnessEvidence.actualFamilySlice_contMDiffCovariantDerivative
#print ChartPort.ChosenSliceSmoothnessEvidence.chartRankZero_case
#print ChartPort.ChosenSliceSmoothnessEvidence.chosenRankZero_case
#print ChartPort.ChosenSliceSmoothnessEvidence.rankZero_values_case
#print ChartPort.ChosenSliceSmoothnessEvidence.emptyChosen_case
#print ChartPort.ChosenSliceSmoothnessEvidence.emptyChart_case
#print ChartPort.downgradedC2Family
#print ChartPort.timeFamilyChosen
#print ChartPort.eventually_timeFamilyChosen_eq_chartLeviCivita
#print axioms ChartPort.timeFamilyChosen_contMDiffCovariantDerivative
#print axioms ChartPort.ChosenSliceSmoothnessEvidence.actualFamilySlice_contMDiffCovariantDerivative
#print axioms ChartPort.ChosenSliceSmoothnessEvidence.chartRankZero_case
#print axioms ChartPort.ChosenSliceSmoothnessEvidence.chosenRankZero_case
#print axioms ChartPort.ChosenSliceSmoothnessEvidence.rankZero_values_case
#print axioms ChartPort.ChosenSliceSmoothnessEvidence.emptyChosen_case
#print axioms ChartPort.ChosenSliceSmoothnessEvidence.emptyChart_case
#print axioms ChartPort.eventually_timeFamilyChosen_eq_chartLeviCivita
#print axioms ChartPort.timeFamilyChosen_eq_chartLeviCivita
#print axioms RicciFlow.SmoothForward.toC2

#print DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_image_isOpen
#print DifferentialGeometry.Geometry.Connection.christoffelBlockCLM
#print DifferentialGeometry.Geometry.Connection.christoffelCorrectionCLM
#print DifferentialGeometry.Geometry.Connection.christoffelCorrectionCLM_apply
#print DifferentialGeometry.Geometry.Connection.christoffelCorrection_eq_christoffelCorrectionCLM
#print DifferentialGeometry.Geometry.Connection.chartE_pullback_contDiffOn_goodSet
#print DifferentialGeometry.Geometry.Connection.chartE_section_repr_contMDiffOn_goodSet
#print DifferentialGeometry.Geometry.Connection.chartE_section_repr_basis_component_contMDiffOn
#print DifferentialGeometry.Geometry.Connection.chartChristoffel_contMDiffOn_goodSet
#print DifferentialGeometry.Geometry.Connection.christoffelCorrectionCLM_contMDiffOn
#print DifferentialGeometry.Geometry.Connection.fderiv_chartE_pullback_contDiffOn_goodSet
#print DifferentialGeometry.Geometry.Connection.fderiv_chartE_pullback_contMDiffOn
#print DifferentialGeometry.Geometry.Connection.inCoordinates_chartLeviCivita_eq
#print DifferentialGeometry.Geometry.Connection.chartLeviCivita_contMDiffCovariantDerivativeOn
#print axioms DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_image_isOpen
#print axioms DifferentialGeometry.Geometry.Connection.christoffelBlockCLM
#print axioms DifferentialGeometry.Geometry.Connection.christoffelCorrectionCLM
#print axioms DifferentialGeometry.Geometry.Connection.christoffelCorrectionCLM_apply
#print axioms DifferentialGeometry.Geometry.Connection.christoffelCorrection_eq_christoffelCorrectionCLM
#print axioms DifferentialGeometry.Geometry.Connection.chartE_pullback_contDiffOn_goodSet
#print axioms DifferentialGeometry.Geometry.Connection.chartE_section_repr_contMDiffOn_goodSet
#print axioms DifferentialGeometry.Geometry.Connection.chartE_section_repr_basis_component_contMDiffOn
#print axioms DifferentialGeometry.Geometry.Connection.chartChristoffel_contMDiffOn_goodSet
#print axioms DifferentialGeometry.Geometry.Connection.christoffelCorrectionCLM_contMDiffOn
#print axioms DifferentialGeometry.Geometry.Connection.fderiv_chartE_pullback_contDiffOn_goodSet
#print axioms DifferentialGeometry.Geometry.Connection.fderiv_chartE_pullback_contMDiffOn
#print axioms DifferentialGeometry.Geometry.Connection.inCoordinates_chartLeviCivita_eq
#print axioms DifferentialGeometry.Geometry.Connection.chartLeviCivita_contMDiffCovariantDerivativeOn
