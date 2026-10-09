import ChartPort.BoundarylessChartCoverage

noncomputable section
open Bundle
open scoped Manifold Topology ContDiff

namespace ChartPort.BoundarylessCoverageEvidence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

/-- Write the actual chosen C2 family explicitly in the pointwise target. -/
theorem actualFamilySlice_eq_pointChartLeviCivita
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    {σ : Π y : M, TangentSpace I y} (x : M)
    (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) (fun s => RicciFlow.SmoothForward.toC2 (g s)) t σ x v =
      DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) x σ x v := by
  exact ChartPort.timeFamilyChosen_eq_pointChartLeviCivita g t x hσ v

/-- Write the same actual family explicitly in the fixed-chart neighborhood target. -/
theorem eventually_actualFamilySlice_eq_chartLeviCivita
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (x : M)
    (σ : Π y : M, TangentSpace I y) :
    ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y → ∀ v : TangentSpace I y,
      CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
        (I := I) (M := M) (fun s => RicciFlow.SmoothForward.toC2 (g s)) t σ y v =
        DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) x σ y v := by
  exact ChartPort.eventually_timeFamilyChosen_eq_chartLeviCivita g t x σ

/-- No positive-rank hypothesis is needed: the pointwise values are both zero at rank zero. -/
theorem rankZero_case (hzero : Module.finrank ℝ E = 0)
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    {σ : Π y : M, TangentSpace I y} (x : M)
    (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    ChartPort.timeFamilyChosen g t σ x v =
      DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) x σ x v ∧
    ChartPort.timeFamilyChosen g t σ x v = 0 ∧
      DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) x σ x v = 0 := by
  letI : Subsingleton (TangentSpace I x) := by
    change Subsingleton E
    exact Module.finrank_zero_iff.mp hzero
  exact ⟨ChartPort.timeFamilyChosen_eq_pointChartLeviCivita g t x hσ v,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

omit [BoundarylessManifold I M] in
/-- Empty manifolds supply the M-only boundaryless instance; coverage still elaborates. -/
theorem emptyCoverage_case [IsEmpty M] :
    ∀ x : M, x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) x := by
  intro x
  exact ChartPort.self_mem_chartLeviCivitaGoodSet (I := I) x

omit [BoundarylessManifold I M] in
/-- The pointwise comparison elaborates on an empty manifold without an ambient instance. -/
theorem emptyPoint_case [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) :
    ∀ (t : ℝ) (x : M) (σ : Π y : M, TangentSpace I y) (v : TangentSpace I x),
      MDiffAt (T% σ) x →
      ChartPort.timeFamilyChosen g t σ x v =
        DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) x σ x v := by
  intro t x σ v hσ
  exact ChartPort.timeFamilyChosen_eq_pointChartLeviCivita g t x hσ v

omit [BoundarylessManifold I M] in
/-- The neighborhood comparison also elaborates with the boundaryless instance from emptiness. -/
theorem emptyNeighborhood_case [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (x : M)
    (σ : Π y : M, TangentSpace I y) :
    ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y → ∀ v : TangentSpace I y,
      ChartPort.timeFamilyChosen g t σ y v =
        DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) x σ y v := by
  exact ChartPort.eventually_timeFamilyChosen_eq_chartLeviCivita g t x σ

end ChartPort.BoundarylessCoverageEvidence

set_option pp.universes true in
#print ChartPort.self_mem_chartLeviCivitaGoodSet
set_option pp.universes true in
#print ChartPort.chartLeviCivitaGoodSet_mem_nhds
set_option pp.universes true in
#print ChartPort.timeFamilyChosen_eq_pointChartLeviCivita
set_option pp.universes true in
#print ChartPort.eventually_timeFamilyChosen_eq_chartLeviCivita
set_option pp.universes true in
#print ChartPort.BoundarylessCoverageEvidence.actualFamilySlice_eq_pointChartLeviCivita
set_option pp.universes true in
#print ChartPort.BoundarylessCoverageEvidence.eventually_actualFamilySlice_eq_chartLeviCivita
set_option pp.universes true in
#print ChartPort.BoundarylessCoverageEvidence.rankZero_case
set_option pp.universes true in
#print ChartPort.BoundarylessCoverageEvidence.emptyCoverage_case
set_option pp.universes true in
#print ChartPort.BoundarylessCoverageEvidence.emptyPoint_case
set_option pp.universes true in
#print ChartPort.BoundarylessCoverageEvidence.emptyNeighborhood_case
#print BoundarylessManifold
#print ModelWithCorners.isInteriorPoint_iff
#print BoundarylessManifold.isInteriorPoint
#print ChartPort.downgradedC2Family
#print ChartPort.timeFamilyChosen
#print DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet
#print axioms ChartPort.self_mem_chartLeviCivitaGoodSet
#print axioms ChartPort.chartLeviCivitaGoodSet_mem_nhds
#print axioms ChartPort.timeFamilyChosen_eq_pointChartLeviCivita
#print axioms ChartPort.eventually_timeFamilyChosen_eq_chartLeviCivita
#print axioms ChartPort.BoundarylessCoverageEvidence.actualFamilySlice_eq_pointChartLeviCivita
#print axioms ChartPort.BoundarylessCoverageEvidence.eventually_actualFamilySlice_eq_chartLeviCivita
#print axioms ChartPort.BoundarylessCoverageEvidence.rankZero_case
#print axioms ChartPort.BoundarylessCoverageEvidence.emptyCoverage_case
#print axioms ChartPort.BoundarylessCoverageEvidence.emptyPoint_case
#print axioms ChartPort.BoundarylessCoverageEvidence.emptyNeighborhood_case
#print axioms ModelWithCorners.isInteriorPoint_iff
#print axioms BoundarylessManifold.isInteriorPoint
#print axioms DifferentialGeometry.Geometry.Connection.mem_chartLeviCivitaGoodSet_iff
#print axioms DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_isOpen
#print axioms DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
#print axioms ChartPort.timeFamilyChosen_eq_chartLeviCivita
