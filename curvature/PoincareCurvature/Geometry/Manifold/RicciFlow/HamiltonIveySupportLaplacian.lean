module

public import PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveySupportEvolution
public import PoincareCurvature.Geometry.Manifold.RicciFlow.ScalarEvolution
public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacianProduct

/-!
# Spatial Laplacian of the Hamilton--Ivey support

At a contact point the Rayleigh support is a quotient `a / d`, where `a` is
the curvature quadratic form and `d` is the evolving metric square of the
contact vector field.  On the open set where `d ≠ 0`, the identity

`support * d = a`

is exact.  Since `d = 1` and `dd = 0` at the contact point, the scalar
Laplacian product rule gives

`Δ support = Δa - ν Δd`.

This file proves that cancellation without assuming it as a PDE premise.
The remaining bridge is to identify the right-hand side with the connection
Laplacian of the curvature tensor on the contact eigenvector.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 3000000

open Bundle Set
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
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- The spatial denominator of the contact Rayleigh quotient. -/
def curvatureNuContactMetricSquare
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (y : M) : ℝ :=
  (g t₀).inner y
    (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ y)
    (g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ y)

/-- The spatial numerator of the contact Rayleigh quotient. -/
def curvatureNuContactNumerator
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (y : M) : ℝ :=
  let V := g.curvatureNuContactVectorField cov hcov hLevi hdim t₀ x₀ y
  (g t₀).inner y V (g.curvatureEndomorphismApply cov hcov t₀ y V)

@[simp] theorem curvatureNuContactMetricSquare_apply_contact
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) :
    g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀ x₀ = 1 := by
  unfold curvatureNuContactMetricSquare curvatureNuContactVectorField
  rw [firstOrderParallelSmoothExtend_apply_center]
  exact g.inner_curvatureNuEigenvector_self cov hcov hLevi hdim t₀ x₀

/-- On every point where the denominator is nonzero, the support times its
denominator is exactly its curvature numerator. -/
theorem curvatureNuSpacetimeSupport_mul_metricSquare
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ y : M)
    (hden : g.curvatureNuContactMetricSquare
      cov hcov hLevi hdim t₀ x₀ y ≠ 0) :
    g.curvatureNuSpacetimeSupport cov hcov hLevi hdim t₀ x₀ (t₀, y) *
        g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀ y =
      g.curvatureNuContactNumerator cov hcov hLevi hdim t₀ x₀ y := by
  unfold curvatureNuSpacetimeSupport curvatureRayleighQuotient
    curvatureNuContactMetricSquare curvatureNuContactNumerator
  exact div_mul_cancel₀ _ hden

/-- The spatial differential of the contact denominator vanishes. -/
theorem scalarDifferential_curvatureNuContactMetricSquare_eq_zero
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) :
    scalarDifferential (I := I)
      (g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀) x₀ = 0 := by
  ext u
  exact g.mvfderiv_curvatureNuContactMetricSquare_eq_zero
    cov hcov hLevi hdim t₀ x₀ u

/-- **Contact quotient-Laplacian identity.**  The assumptions are only the
second-order regularity needed to form the three scalar Laplacians and an open
neighborhood on which the contact vector remains nonzero.  The quotient
cancellation itself is proved. -/
theorem scalarLaplacian_curvatureNuSpacetimeSupport_eq
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (t₀ : ℝ) (x₀ : M) (U : Set M)
    (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hden : ∀ y ∈ U, g.curvatureNuContactMetricSquare
      cov hcov hLevi hdim t₀ x₀ y ≠ 0)
    (hq : ∀ y, MDiffAt
      (fun z => g.curvatureNuSpacetimeSupport
        cov hcov hLevi hdim t₀ x₀ (t₀, z)) y)
    (hd : ∀ y, MDiffAt
      (g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀) y)
    (hDq : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (fun z => g.curvatureNuSpacetimeSupport
            cov hcov hLevi hdim t₀ x₀ (t₀, z)) y)) x₀)
    (hDd : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (g.curvatureNuContactMetricSquare
            cov hcov hLevi hdim t₀ x₀) y)) x₀)
    (hDa : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I)
          (g.curvatureNuContactNumerator
            cov hcov hLevi hdim t₀ x₀) y)) x₀) :
    g.scalarLaplacian cov
        (fun _ y => g.curvatureNuSpacetimeSupport
          cov hcov hLevi hdim t₀ x₀ (t₀, y)) t₀ x₀ =
      g.scalarLaplacian cov
          (fun _ => g.curvatureNuContactNumerator
            cov hcov hLevi hdim t₀ x₀) t₀ x₀ -
        g.curvatureNu cov hcov hLevi hdim t₀ x₀ *
          g.scalarLaplacian cov
            (fun _ => g.curvatureNuContactMetricSquare
              cov hcov hLevi hdim t₀ x₀) t₀ x₀ := by
  letI : RiemannianBundle TM := ⟨(g t₀).toRiemannianMetric⟩
  let q : M → ℝ := fun y => g.curvatureNuSpacetimeSupport
    cov hcov hLevi hdim t₀ x₀ (t₀, y)
  let d : M → ℝ :=
    g.curvatureNuContactMetricSquare cov hcov hLevi hdim t₀ x₀
  let a : M → ℝ :=
    g.curvatureNuContactNumerator cov hcov hLevi hdim t₀ x₀
  have hDprod : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) (q * d) y)) x₀ := by
    have heq : scalarDifferential (I := I) (q * d) =
        q • scalarDifferential (I := I) d +
          d • scalarDifferential (I := I) q := by
      funext y
      exact scalarDifferential_mul (I := I) (hq y) (hd y)
    rw [heq]
    exact mdifferentiableAt_add_section
      ((hq x₀).smul_section hDd) ((hd x₀).smul_section hDq)
  have hcongr : CovariantDerivative.scalarLaplacian (cov t₀) (q * d) x₀ =
      CovariantDerivative.scalarLaplacian (cov t₀) a x₀ := by
    apply scalarLaplacian_congr_on_open (cov t₀) hU hx₀
    · intro y hy
      exact g.curvatureNuSpacetimeSupport_mul_metricSquare
        cov hcov hLevi hdim t₀ x₀ y (hden y hy)
    · exact hDprod
    · exact hDa
  have hprod := scalarLaplacian_mul_of_second_differential_eq_zero
    (cov t₀) hq hd hDq hDd
      (g.scalarDifferential_curvatureNuContactMetricSquare_eq_zero
        cov hcov hLevi hdim t₀ x₀)
  have hq0 : q x₀ = g.curvatureNu cov hcov hLevi hdim t₀ x₀ := by
    exact g.curvatureNuSpacetimeSupport_eq_at_contact
      cov hcov hLevi hdim t₀ x₀
  have hd0 : d x₀ = 1 := by
    exact g.curvatureNuContactMetricSquare_apply_contact
      cov hcov hLevi hdim t₀ x₀
  dsimp [q, d, a] at hcongr ⊢
  dsimp [q, d] at hprod hq0 hd0
  rw [hq0, hd0, one_mul] at hprod
  linarith

end CovariantDerivative.TimeDependentRiemannianMetric
