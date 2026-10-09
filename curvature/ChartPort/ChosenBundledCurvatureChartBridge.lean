import ChartPort.SourceLocalCurvature
import ChartPort.LocalBundledCurvatureBridge

noncomputable section
open Bundle
open scoped Manifold ContDiff Topology

namespace ChartPort

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [BoundarylessManifold I M]

/-- The actual chosen bundled curvature agrees with the actual chart connection's
raw commutator, for sections smooth on its genuine chart good set.
The C1 instance in the conclusion is the proved downgrade of chosen spatial infinity. -/
theorem timeFamilyChosen_curvatureTensor_eq_chartCommutator
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ) (α : M)
    {X Y σ : Π y : M, TangentSpace I y} {x : M}
    (hx : x ∈ DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)
    (hX : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% X)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hY : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% Y)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α))
    (hσ : ContMDiffOn I (I.prod 𝓘(ℝ, E)) ∞ (T% σ)
      (DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet (I := I) α)) :
    letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
    CovariantDerivative.curvatureTensor (cov := timeFamilyChosen g t) x (X x) (Y x) (σ x) =
      chartCurvatureCommutator (g t) α X Y σ x := by
  letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
  have hopen := DifferentialGeometry.Geometry.Connection.chartLeviCivitaGoodSet_isOpen (I := I) α
  have hlocal := SourceLocalCurvature.curvatureAux_apply_eq_curvatureTensor_of_contMDiffOn_frame
    (cov := timeFamilyChosen g t) hopen hx
    (hX.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
    (hY.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
    (hσ.of_le (show (2 : WithTop ℕ∞) ≤ ∞ by decide))
  exact hlocal.symm.trans (timeFamilyChosen_curvatureAux_eq_chartCommutator g t α hx hX hY hσ)

end ChartPort
