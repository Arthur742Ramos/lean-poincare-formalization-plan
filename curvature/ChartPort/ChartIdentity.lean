import ChartPort.MetricAPI
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartTorsion
import DifferentialGeometry.Geometry.Connection.LeviCivita.LeviCivitaChartMetric

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace ChartPort

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Local comparison for a constant downgraded metric on differentiable sections. -/
theorem projectChosen_eq_chartLeviCivita
    (g : RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {σ : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    projectChosen g t σ x v =
      DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) g α σ x v := by
  classical
  obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  have hX : MDiffAt (T% fun y => X y) x := X.mdifferentiableAt
  have hTF : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y →
      y ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α →
      projectChosen g t B y (A y) - projectChosen g t A y (B y) =
        VectorField.mlieBracket I A B y := by
    intro A B y hA hB _
    exact (CovariantDerivative.torsion_eq_zero_iff (projectChosen g t)).mp
      (projectChosen_torsion g t) hA hB
  have hlocal := DifferentialGeometry.Geometry.Connection.koszul_local_uniqueness
    (g := g) (s := DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (cov₂ := DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) g α)
    hTF (fun {A B y} hA hB hy =>
      DifferentialGeometry.Geometry.Connection.chartLeviCivita_torsion_free_on
        (I := I) g α (X := A) (Y := B) (x := y) hA hB hy)
    (projectChosen_metricCompatible g t).toIsMetricCompatibleOn
    (DifferentialGeometry.Geometry.Connection.chartLeviCivita_isMetricCompatibleOn g α)
    hX hσ hx
  simpa only [hXx] using hlocal

end ChartPort
