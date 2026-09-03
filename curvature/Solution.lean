import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TimeDependent

public noncomputable section

open Bundle
open scoped Bundle Manifold ContDiff

namespace PoincareCurvature.Palomar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TCov" =>
  (CovariantDerivative.TimeDependentCovariantDerivative
    (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
local notation "TMetric" =>
  (CovariantDerivative.TimeDependentRiemannianMetric
    (E := E) (I := I) (M := M))

variable (g : CovariantDerivative.TimeDependentRiemannianMetric
  (E := E) (I := I) (M := M))
include g

theorem exists_contMDiffLeviCivitaConnection
    [SigmaCompactSpace M] :
    ∃ cov : TCov,
      CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov ∧
        ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := by
  exact CovariantDerivative.TimeDependentRiemannianMetric.exists_contMDiffLeviCivitaConnection
    (E := E) (I := I) (M := M) g

theorem leviCivitaConnection_isLeviCivita
    (cov : TCov) :
    CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g
      (CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection
        (E := E) (I := I) (M := M) g cov) := by
  exact CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection_isLeviCivita
    (E := E) (I := I) (M := M) g cov

theorem contMDiffCovariantDerivative_leviCivitaConnection
    (cov : TCov)
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) :
    CovariantDerivative.ContMDiffCovariantDerivative
      ((CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection
        (E := E) (I := I) (M := M) g cov) t) 1 := by
  exact CovariantDerivative.TimeDependentRiemannianMetric.contMDiffCovariantDerivative_leviCivitaConnection
    (E := E) (I := I) (M := M) g cov hcov t

theorem leviCivitaConnection_eq_leviCivitaConnection
    (cov cov' : TCov)
    {t : ℝ} {x : M} {σ : Π y : M, TangentSpace I y}
    (hσ : MDiffAt (T% σ) x) :
    CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection
        (E := E) (I := I) (M := M) g cov t σ x =
      CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection
        (E := E) (I := I) (M := M) g cov' t σ x := by
  exact CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection_eq_leviCivitaConnection
    (E := E) (I := I) (M := M) g cov cov' hσ

theorem contMDiffCovariantDerivative_of_isLeviCivita
    [SigmaCompactSpace M]
    {cov : TCov}
    (hcov : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov) :
    ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1 := by
  exact CovariantDerivative.TimeDependentRiemannianMetric.contMDiffCovariantDerivative_of_isLeviCivita
    (E := E) (I := I) (M := M) g hcov

section Ricci

variable [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]

theorem ricciCurvature_symm_of_isLeviCivita
    (cov : TCov)
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov)
    (t : ℝ) (x : M) (u w : TM x) :
    CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature g cov hcov t x u w =
      CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature g cov hcov t x w u := by
  exact CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature_symm_of_isLeviCivita
    (E := E) (I := I) (M := M) g cov hcov hLevi t x u w

end Ricci

theorem ricciCurvature_eq_of_isLeviCivita
    {cov cov' : TCov}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hcov' : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov' t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov)
    (hLevi' : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov')
    (t : ℝ) (x : M) (u w : TM x) :
    CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature g cov hcov t x u w =
      CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature g cov' hcov' t x u w := by
  exact CovariantDerivative.TimeDependentRiemannianMetric.ricciCurvature_eq_of_isLeviCivita
    (E := E) (I := I) (M := M) g hcov hcov' hLevi hLevi' t x u w

theorem scalarCurvature_eq_of_isLeviCivita
    {cov cov' : TCov}
    (hcov : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov t) 1)
    (hcov' : ∀ t : ℝ, CovariantDerivative.ContMDiffCovariantDerivative (cov' t) 1)
    (hLevi : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov)
    (hLevi' : CovariantDerivative.TimeDependentRiemannianMetric.IsLeviCivita g cov')
    (t : ℝ) (x : M) :
    CovariantDerivative.TimeDependentRiemannianMetric.scalarCurvature g cov hcov t x =
      CovariantDerivative.TimeDependentRiemannianMetric.scalarCurvature g cov' hcov' t x := by
  exact CovariantDerivative.TimeDependentRiemannianMetric.scalarCurvature_eq_of_isLeviCivita
    (E := E) (I := I) (M := M) g hcov hcov' hLevi hLevi' t x

end PoincareCurvature.Palomar
