module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RaisedRicci
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TimeDependent

/-!
# Three-dimensional curvature spectrum along a metric family

This file lifts the intrinsic three-dimensional curvature spectrum to each
time slice of a time-dependent Riemannian metric and a Levi-Civita connection
family.  It supplies the geometric `lambda`, `mu`, and `nu` fields used by the
Hamilton--Ivey estimate.  Their ordering and scalar-curvature sum are inherited
from the self-adjoint spectral theorem and the actual curvature contractions.
-/

@[expose] public noncomputable section

set_option linter.style.haveILetI false

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The ordered triple of actual curvature-operator eigenvalues at a spacetime
point, in the normalization where each is twice a sectional curvature. -/
def curvatureEigenvalues
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : Fin 3 → ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  exact CovariantDerivative.ricciComplementEigenvalues
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)

/-- Largest curvature-operator eigenvalue. -/
def curvatureLambda
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : ℝ :=
  g.curvatureEigenvalues cov hcov hLevi hdim t x 0

/-- Middle curvature-operator eigenvalue. -/
def curvatureMu
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : ℝ :=
  g.curvatureEigenvalues cov hcov hLevi hdim t x 1

/-- Least curvature-operator eigenvalue. -/
def curvatureNu
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) : ℝ :=
  g.curvatureEigenvalues cov hcov hLevi hdim t x 2

/-- The three curvature eigenvalues are decreasingly ordered at every
spacetime point. -/
theorem curvatureEigenvalues_antitone
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    Antitone (g.curvatureEigenvalues cov hcov hLevi hdim t x) := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  exact CovariantDerivative.ricciComplementEigenvalues_antitone
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)

theorem curvatureLambda_ge_mu
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    g.curvatureMu cov hcov hLevi hdim t x ≤
      g.curvatureLambda cov hcov hLevi hdim t x :=
  g.curvatureEigenvalues_antitone cov hcov hLevi hdim t x (by decide)

theorem curvatureMu_ge_nu
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    g.curvatureNu cov hcov hLevi hdim t x ≤
      g.curvatureMu cov hcov hLevi hdim t x :=
  g.curvatureEigenvalues_antitone cov hcov hLevi hdim t x (by decide)

/-- The geometric scalar curvature equals `lambda + mu + nu` at every
spacetime point. -/
theorem curvatureLambda_add_mu_add_nu_eq_scalarCurvature
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    g.curvatureLambda cov hcov hLevi hdim t x +
        g.curvatureMu cov hcov hLevi hdim t x +
        g.curvatureNu cov hcov hLevi hdim t x =
      g.scalarCurvature cov hcov t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  haveI : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1 := hcov t
  exact CovariantDerivative.threeDimensionalCurvatureLambda_add_mu_add_nu_eq_scalarCurvature
    (I := I) (M := M) (E := E)
    (cov t) (hLevi t).1 (hLevi t).2 x (hdim x)

end CovariantDerivative.TimeDependentRiemannianMetric
