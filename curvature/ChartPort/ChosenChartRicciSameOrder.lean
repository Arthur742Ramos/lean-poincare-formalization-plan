import ChartPort.ChosenChartRicciTrace

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

/-- Genuine project Levi-Civita Ricci symmetry for the actual chosen slice,
with every metric and connection regularity instance derived from the same g t. -/
theorem timeFamilyChosen_ricciCurvature_symm
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    (x : M) (u w : TangentSpace I x) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
    letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
    CovariantDerivative.ricciCurvature (cov := timeFamilyChosen g t) x u w =
      CovariantDerivative.ricciCurvature (cov := timeFamilyChosen g t) x w u := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
  letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
  letI : ∀ y : M, NormedAddCommGroup (TangentSpace I y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
      (E := (TangentSpace I : M → Type _)) y
  letI : ∀ y : M, InnerProductSpace ℝ (TangentSpace I y) := fun y =>
    Bundle.instInnerProductSpaceReal (E := (TangentSpace I : M → Type _)) y
  letI : IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _) := by infer_instance
  haveI : IsManifold I (minSmoothness ℝ 3) M := by
    rw [minSmoothness_of_isRCLikeNormedField (𝕜 := ℝ)]
    infer_instance
  haveI : IsManifold I ((2 : ℕ∞) + 1) M := by
    norm_num
    infer_instance
  have hLevi : (timeFamilyChosen g t).IsLeviCivita :=
    (downgradedC2Family g).someContMDiffLeviCivitaConnection_isLeviCivita t
  exact CovariantDerivative.ricciCurvature_symm_of_isLeviCivita
    (cov := timeFamilyChosen g t) hLevi x u w

/-- Same-order chart Ricci identification, obtained by actual chosen Ricci symmetry.
The independently proved transposed trace theorem remains a separate declaration. -/
theorem chartRicciTensor_eq_timeFamilyChosen_ricciCurvature
    (g : ℝ → RicciFlow.SmoothForward.Metric (I := I) (M := M)) (t : ℝ)
    (α : M) (i k : Fin (Module.finrank ℝ E)) {x : M}
    (hx : x ∈ chartLeviCivitaGoodSet (I := I) α) :
    chartRicciTensor (I := I) (g t) α i k (extChartAt I α x) =
      letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
        ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
      letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
      CovariantDerivative.ricciCurvature (cov := timeFamilyChosen g t) x
        (chartLocalFrame (I := I) α i x) (chartLocalFrame (I := I) α k x) := by
  letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨(RicciFlow.SmoothForward.toC2 (g t)).toRiemannianMetric⟩
  letI := timeFamilyChosen_contMDiffCovariantDerivative_one g t
  exact (chartRicciTensor_eq_timeFamilyChosen_ricciCurvature_transposed g t α i k hx).trans
    (timeFamilyChosen_ricciCurvature_symm g t x (chartLocalFrame (I := I) α k x)
      (chartLocalFrame (I := I) α i x))

end ChartPort
