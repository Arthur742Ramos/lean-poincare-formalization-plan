module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.TimeDependent
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacianMaximum
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RicciNorm

/-!
# Scalar quantities for a time-dependent Riemannian metric

This module puts the intrinsic scalar Laplacian and squared Ricci norm on the
same time-slice metric used by the existing Ricci-flow API.  It also lifts the
pointwise trace estimate to time-dependent metrics.  The evolution identity
itself is deliberately not postulated here; it will be derived from metric
variation in the subsequent layer.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)

namespace TimeDependentRiemannianMetric

variable (g : TimeDependentRiemannianMetric (I := I) (M := M))

/-- The scalar Laplace--Beltrami operator at time `t`, using the metric `g t`
and the supplied connection slice. -/
def scalarLaplacian
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (f : ℝ → M → ℝ) (t : ℝ) (x : M) : ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  exact CovariantDerivative.scalarLaplacian (cov t) (f t) x

@[simp] lemma scalarLaplacian_apply
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (f : ℝ → M → ℝ) (t : ℝ) (x : M) :
    g.scalarLaplacian cov f t x = (by
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact CovariantDerivative.scalarLaplacian (cov t) (f t) x) := rfl

/-- The squared Hilbert--Schmidt norm of the Ricci tensor at time `t`. -/
def ricciNormSq
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) : ℝ := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact CovariantDerivative.ricciNormSq (cov := cov t) x

theorem scalarCurvature_sq_le_finrank_mul_ricciNormSq
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (t : ℝ) (x : M) :
    (g.scalarCurvature cov hcov t x) ^ 2 ≤
      (Module.finrank ℝ (TM x) : ℝ) * g.ricciNormSq cov hcov t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  exact CovariantDerivative.scalarCurvature_sq_le_finrank_mul_ricciNormSq
    (cov := cov t) x

/-- In dimension three, `R² ≤ 3 |Ric|²`. -/
theorem scalarCurvature_sq_le_three_mul_ricciNormSq
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative (cov t) 1)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t : ℝ) (x : M) :
    (g.scalarCurvature cov hcov t x) ^ 2 ≤
      3 * g.ricciNormSq cov hcov t x := by
  simpa [hdim x] using
    g.scalarCurvature_sq_le_finrank_mul_ricciNormSq cov hcov t x

end TimeDependentRiemannianMetric
end CovariantDerivative
