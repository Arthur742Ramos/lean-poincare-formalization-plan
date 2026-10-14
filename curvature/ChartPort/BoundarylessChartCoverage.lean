import ChartPort.TimeFamilyChartIdentity
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

noncomputable section
open Bundle
open scoped Manifold Topology ContDiff

namespace ChartPort

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

/-- Each point lies in its actual chart good set on a boundaryless manifold. -/
theorem self_mem_chartLeviCivitaGoodSet (x : M) :
    x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) x := by
  apply (DifferentialGeometry.Geometry.Connection.mem_chartLeviCivitaGoodSet_iff
    (I := I)).mpr
  refine ⟨mem_extChartAt_source x, ?_, ?_⟩
  · rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source
      (I := I) x]
    exact mem_chart_source H x
  · exact (ModelWithCorners.isInteriorPoint_iff (I := I)).mp
      (BoundarylessManifold.isInteriorPoint (I := I) (x := x))

/-- The fixed chart at a point has a genuine good-set neighborhood of that point. -/
theorem chartLeviCivitaGoodSet_mem_nhds (x : M) :
    DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) x ∈ 𝓝 x :=
  (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_isOpen (I := I) x).mem_nhds
    (self_mem_chartLeviCivitaGoodSet (I := I) x)

/-- Compare the actual chosen family with the chart centered at each evaluation point. -/
theorem timeFamilyChosen_eq_pointChartLeviCivita
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    {σ : Π y : M, TangentSpace I y} (x : M)
    (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    timeFamilyChosen g t σ x v =
      DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) x σ x v :=
  timeFamilyChosen_eq_chartLeviCivita g t x
    (self_mem_chartLeviCivitaGoodSet (I := I) x) hσ v

/-- In the fixed chart centered at `x`, the comparison holds near `x` whenever
the tested section is differentiable at the evaluation point. -/
theorem eventually_timeFamilyChosen_eq_chartLeviCivita
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (x : M)
    (σ : Π y : M, TangentSpace I y) :
    ∀ᶠ y in 𝓝 x, MDiffAt (T% σ) y → ∀ v : TangentSpace I y,
      timeFamilyChosen g t σ y v =
        DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) x σ y v := by
  filter_upwards [chartLeviCivitaGoodSet_mem_nhds (I := I) x] with y hy
  intro hσ v
  exact timeFamilyChosen_eq_chartLeviCivita g t x hy hσ v

end ChartPort
