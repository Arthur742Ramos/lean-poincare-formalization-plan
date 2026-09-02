import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions

public noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

namespace PoincareCurvature.Palomar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 2 M]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

theorem exists_contMDiffLeviCivitaConnection
    [SigmaCompactSpace M]
    [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)] :
    ∃ cov : CovariantDerivative I E (TangentSpace I : M → Type _),
      cov.IsLeviCivita ∧ cov.ContMDiffCovariantDerivative 1 := by
  exact CovariantDerivative.exists_contMDiffLeviCivitaConnection
    (I := I) (E := E) (M := M)

section CurvatureTensor

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {cov cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [cov.ContMDiffCovariantDerivative 1] [cov'.ContMDiffCovariantDerivative 1]

theorem curvatureTensor_eq_of_isLeviCivita
    (hcov : cov.IsLeviCivita)
    (hcov' : cov'.IsLeviCivita)
    (x : M) (u v w : TangentSpace I x) :
    CovariantDerivative.curvatureTensor (cov := cov) x u v w =
      CovariantDerivative.curvatureTensor (cov := cov') x u v w := by
  exact CovariantDerivative.curvatureTensor_eq_of_isLeviCivita
    (I := I) (E := E) (M := M) hcov hcov' x u v w

end CurvatureTensor

section Ricci

variable [IsContMDiffRiemannianBundle I 2 E (TangentSpace I : M → Type _)]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [cov.ContMDiffCovariantDerivative 1]

theorem ricciCurvature_symm_of_isLeviCivita
    (hLevi : cov.IsLeviCivita)
    (x : M) (u w : TangentSpace I x) :
    CovariantDerivative.ricciCurvature (cov := cov) x u w =
      CovariantDerivative.ricciCurvature (cov := cov) x w u := by
  exact CovariantDerivative.ricciCurvature_symm_of_isLeviCivita
    (I := I) (E := E) (M := M) cov hLevi x u w

section Invariance

variable [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
  {cov' : CovariantDerivative I E (TangentSpace I : M → Type _)}
  [cov'.ContMDiffCovariantDerivative 1]

theorem ricciCurvature_eq_of_isLeviCivita
    (hcov : cov.IsLeviCivita)
    (hcov' : cov'.IsLeviCivita)
    (x : M) (u w : TangentSpace I x) :
    CovariantDerivative.ricciCurvature (cov := cov) x u w =
      CovariantDerivative.ricciCurvature (cov := cov') x u w := by
  exact CovariantDerivative.ricciCurvature_eq_of_isLeviCivita
    (I := I) (E := E) (M := M) cov hcov hcov' x u w

theorem scalarCurvature_eq_of_isLeviCivita
    (hcov : cov.IsLeviCivita)
    (hcov' : cov'.IsLeviCivita)
    (x : M) :
    CovariantDerivative.scalarCurvature (cov := cov) x =
      CovariantDerivative.scalarCurvature (cov := cov') x := by
  exact CovariantDerivative.scalarCurvature_eq_of_isLeviCivita
    (I := I) (E := E) (M := M) cov hcov hcov' x

end Invariance
end Ricci

end PoincareCurvature.Palomar
