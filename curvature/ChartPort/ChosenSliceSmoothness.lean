import ChartPort.BoundarylessChartCoverage
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartSmooth

noncomputable section
open Bundle
open scoped Manifold Topology ContDiff

namespace ChartPort

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

/-- Spatial infinity regularity of the actual chosen slice follows from genuine chart
regularity and local agreement on the smooth sections tested by the predicate. -/
theorem timeFamilyChosen_contMDiffCovariantDerivative
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative (timeFamilyChosen g t) ∞ where
  contMDiff := by
    refine ⟨?_⟩
    intro σ hσ
    have hσ_global : ContMDiff I (I.prod 𝓘(ℝ, E)) ((∞ : WithTop ℕ∞) + 1) (T% σ) :=
      contMDiffOn_univ.mp hσ
    have hσ_diff (y : M) : MDiffAt (T% σ) y :=
      hσ_global.mdifferentiableAt (by simp)
    intro x _
    have hchart :=
      DifferentialGeometry.Geometry.Connection.chartLeviCivita_contMDiffCovariantDerivativeOn
        (I := I) (g t) x
    have hchart_on := hchart.contMDiff (hσ.mono (Set.subset_univ _))
    have hchart_at := hchart_on.contMDiffAt (chartLeviCivitaGoodSet_mem_nhds (I := I) x)
    have hCLM : ∀ᶠ y in 𝓝 x,
        timeFamilyChosen g t σ y =
          DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) x σ y := by
      filter_upwards [eventually_timeFamilyChosen_eq_chartLeviCivita g t x σ] with y hy
      ext v
      exact hy (hσ_diff y) v
    have hsection :
        (fun y : M => (⟨y, timeFamilyChosen g t σ y⟩ :
          TotalSpace (E →L[ℝ] E) (fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z)))
          =ᶠ[𝓝 x]
        (fun y : M => (⟨y,
          DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) x σ y⟩ :
          TotalSpace (E →L[ℝ] E) (fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z))) := by
      filter_upwards [hCLM] with y hy
      rw [hy]
    exact (hchart_at.congr_of_eventuallyEq hsection).contMDiffWithinAt

end ChartPort
