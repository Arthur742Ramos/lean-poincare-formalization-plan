import ChartPort.ChartIdentity

noncomputable section
open Bundle
open scoped Manifold ContDiff

namespace ChartPort

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

/-- Downgrade each smooth metric using the project's proved `SmoothForward.toC2`. -/
def downgradedC2Family
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) :
    CovariantDerivative.TimeDependentRiemannianMetric (I := I) (M := M) :=
  fun s => RicciFlow.SmoothForward.toC2 (g s)

/-- The actual chosen connection family of the downgraded metrics. -/
def timeFamilyChosen
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M))
    (t : ℝ) : CovariantDerivative I E (TangentSpace I : M → Type _) :=
  (downgradedC2Family g).someContMDiffLeviCivitaConnection t

theorem timeFamilyChosen_torsion
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    (timeFamilyChosen g t).torsion = 0 :=
  ((downgradedC2Family g).someContMDiffLeviCivitaConnection_isLeviCivita t).1

theorem timeFamilyChosen_metricCompatible
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) :
    DifferentialGeometry.Geometry.Connection.IsMetricCompatible
      (timeFamilyChosen g t) (g t) := by
  apply (metricCompatible_iff (g t) (timeFamilyChosen g t)).mp
  exact ((downgradedC2Family g).someContMDiffLeviCivitaConnection_isLeviCivita t).2

/-- At each time, the chosen connection agrees with the actual chart formula on the
chart good set and differentiable sections. No regularity in time is required. -/
theorem timeFamilyChosen_eq_chartLeviCivita
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {σ : Π x : M, TangentSpace I x} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hσ : MDiffAt (T% σ) x) (v : TangentSpace I x) :
    timeFamilyChosen g t σ x v =
      DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) α σ x v := by
  classical
  obtain ⟨X, hXx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x v
  have hX : MDiffAt (T% fun y => X y) x := X.mdifferentiableAt
  have hTF : ∀ ⦃A B : Π y : M, TangentSpace I y⦄ ⦃y : M⦄,
      MDiffAt (T% A) y → MDiffAt (T% B) y →
      y ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α →
      timeFamilyChosen g t B y (A y) - timeFamilyChosen g t A y (B y) =
        VectorField.mlieBracket I A B y := by
    intro A B y hA hB _
    exact (CovariantDerivative.torsion_eq_zero_iff (timeFamilyChosen g t)).mp
      (timeFamilyChosen_torsion g t) hA hB
  have hlocal := DifferentialGeometry.Geometry.Connection.koszul_local_uniqueness
    (g := g t) (s := DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (cov₂ := DifferentialGeometry.Geometry.Connection.chartLeviCivita (I := I) (g t) α)
    hTF (fun {A B y} hA hB hy =>
      DifferentialGeometry.Geometry.Connection.chartLeviCivita_torsion_free_on
        (I := I) (g t) α (X := A) (Y := B) (x := y) hA hB hy)
    (timeFamilyChosen_metricCompatible g t).toIsMetricCompatibleOn
    (DifferentialGeometry.Geometry.Connection.chartLeviCivita_isMetricCompatibleOn (g t) α)
    hX hσ hx
  simpa only [hXx] using hlocal

end ChartPort
