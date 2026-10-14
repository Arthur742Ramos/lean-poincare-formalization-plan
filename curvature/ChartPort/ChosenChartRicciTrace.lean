import ChartPort.SourceLocalRicciTrace
import ChartPort.ChosenChartRiemannComponents

noncomputable section
open Bundle
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology

namespace ChartPort
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

/-- Upstream Ricci indices i,k correspond to actual chosen Ricci arguments frame k,frame i.
The ordinary trace contracts the first curvature argument with the output coefficient. -/
theorem chartRicciTensor_eq_timeFamilyChosen_ricciCurvature_transposed
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    (α : M) (i k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartRicciTensor (I := I) (g t) α i k (extChartAt I α x) =
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
      letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
      CovariantDerivative.ricciCurvature (cov := timeFamilyChosen g t) x
        (chartLocalFrame (I := I) α k x) (chartLocalFrame (I := I) α i x) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
  letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
  rw [SourceLocalRicciTrace.ricciCurvature_eq_sum_localFrameCoeff (cov := timeFamilyChosen g t)
    (chartModelBasis E) α (chartLeviCivitaGoodSet_mem_baseSet hx)]
  rw [chartRicciTensor_def]
  apply Finset.sum_congr rfl
  intro j _
  exact (timeFamilyChosenChartCurvatureComponent_eq_chartRiemannTensor g t α j k i j hx).symm

end ChartPort
