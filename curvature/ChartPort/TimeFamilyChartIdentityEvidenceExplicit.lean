import ChartPort.TimeFamilyChartIdentity

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace ChartPort.TimeFamilyEvidence

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- The target with the actual C2 family and actual project choice written explicitly. -/
theorem actualFamilySlice_eq_chartLeviCivita
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {σ : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection
      (I := I) (M := M) (fun s => RicciFlow.SmoothForward.toC2 (g s)) t σ x v =
      DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) α σ x v := by
  exact ChartPort.timeFamilyChosen_eq_chartLeviCivita g t α hx hσ v

/-- Rank zero is admitted by the same local identity; both values are zero. -/
theorem rankZero_case
    (hzero : Module.finrank ℝ E = 0)
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {σ : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    ChartPort.timeFamilyChosen g t σ x v =
      DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) α σ x v ∧
    ChartPort.timeFamilyChosen g t σ x v = 0 ∧
      DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) α σ x v = 0 := by
  letI : Subsingleton (TangentSpace I x) := by
    change Subsingleton E
    exact Module.finrank_zero_iff.mp hzero
  exact ⟨ChartPort.timeFamilyChosen_eq_chartLeviCivita g t α hx hσ v,
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The actual chosen family exists and is slicewise Levi-Civita on an empty manifold. -/
theorem emptyFamily_case [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) :
    (ChartPort.downgradedC2Family g).IsLeviCivita
      (ChartPort.downgradedC2Family g).someContMDiffLeviCivitaConnection :=
  (ChartPort.downgradedC2Family g).someContMDiffLeviCivitaConnection_isLeviCivita

/-- The local comparison also elaborates with an empty manifold instance. -/
theorem emptyLocal_case [IsEmpty M]
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) :
    ∀ (t : ℝ) (α x : M) (σ : Π y : M, TangentSpace I y) (v : TangentSpace I x),
      x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α →
      MDiffAt (T% σ) x →
      ChartPort.timeFamilyChosen g t σ x v =
        DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) α σ x v := by
  intro t α x σ v hx hσ
  exact ChartPort.timeFamilyChosen_eq_chartLeviCivita g t α hx hσ v

end ChartPort.TimeFamilyEvidence

set_option pp.universes true in
#print ChartPort.downgradedC2Family
set_option pp.universes true in
#print ChartPort.timeFamilyChosen
set_option pp.universes true in
#print ChartPort.timeFamilyChosen_torsion
set_option pp.universes true in
#print ChartPort.timeFamilyChosen_metricCompatible
set_option pp.universes true in
#print ChartPort.timeFamilyChosen_eq_chartLeviCivita
set_option pp.universes true in
#print ChartPort.TimeFamilyEvidence.actualFamilySlice_eq_chartLeviCivita
set_option pp.universes true in
#print ChartPort.TimeFamilyEvidence.rankZero_case
set_option pp.universes true in
#print ChartPort.TimeFamilyEvidence.emptyFamily_case
set_option pp.universes true in
#print ChartPort.TimeFamilyEvidence.emptyLocal_case
set_option pp.universes true in
#print CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita
set_option pp.universes true in
#print CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
#print axioms ChartPort.timeFamilyChosen_torsion
#print axioms ChartPort.timeFamilyChosen_metricCompatible
#print axioms ChartPort.timeFamilyChosen_eq_chartLeviCivita
#print axioms ChartPort.TimeFamilyEvidence.actualFamilySlice_eq_chartLeviCivita
#print axioms ChartPort.TimeFamilyEvidence.rankZero_case
#print axioms ChartPort.TimeFamilyEvidence.emptyFamily_case
#print axioms ChartPort.TimeFamilyEvidence.emptyLocal_case
#print axioms CovariantDerivative.TimeDependentRiemannianMetric.someContMDiffLeviCivitaConnection_isLeviCivita
#print axioms ChartPort.metricCompatible_iff
#print axioms DifferentialGeometry.Geometry.Connection.chartLeviCivita_torsion_free_on
#print axioms DifferentialGeometry.Geometry.Connection.chartLeviCivita_isMetricCompatibleOn
#print axioms DifferentialGeometry.Geometry.Connection.koszul_local_uniqueness
#print axioms ContMDiffSection.exists_eq_at
#print axioms RicciFlow.SmoothForward.toC2
