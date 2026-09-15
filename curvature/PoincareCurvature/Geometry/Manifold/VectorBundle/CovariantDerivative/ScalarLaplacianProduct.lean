module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ScalarLaplacian

/-!
# Product rules for the scalar Laplacian

The scalar differential and Hessian satisfy their intrinsic Leibniz rules.
Tracing the Hessian gives the Laplace--Beltrami product rule, together with the
critical-factor specialization used for Rayleigh quotients at a contact point.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000

open Bundle FiberBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

namespace CovariantDerivative

local notation "TM" => (TangentSpace I : M → Type _)
local notation "T₁" => (fun x : M => TM x →L[ℝ] ℝ)

/-- Leibniz rule for the intrinsic scalar differential. -/
theorem scalarDifferential_mul {f g : M → ℝ} {x : M}
    (hf : MDiffAt f x) (hg : MDiffAt g x) :
    scalarDifferential (I := I) (f * g) x =
      f x • scalarDifferential (I := I) g x +
        g x • scalarDifferential (I := I) f x := by
  exact mvfderiv_mul (I := I) hf hg

/-- Pointwise Hessian Leibniz rule.  The two cross terms retain their order,
so no torsion or Hessian-symmetry premise is needed. -/
theorem scalarHessian_mul_apply
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y) (hg : ∀ y, MDiffAt g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x)
    (u v : TM x) :
    scalarHessian cov (f * g) x u v =
      f x * scalarHessian cov g x u v +
      scalarDifferential (I := I) f x u * scalarDifferential (I := I) g x v +
      g x * scalarHessian cov f x u v +
      scalarDifferential (I := I) g x u * scalarDifferential (I := I) f x v := by
  have hdiff : scalarDifferential (I := I) (f * g) =
      f • scalarDifferential (I := I) g +
        g • scalarDifferential (I := I) f := by
    funext y
    exact scalarDifferential_mul (I := I) (hf y) (hg y)
  have hfdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((f • scalarDifferential (I := I) g) y)) x :=
    (hf x).smul_section hdg
  have hgdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        ((g • scalarDifferential (I := I) f) y)) x :=
    (hg x).smul_section hdf
  have hadd := (covectorCovariantDerivative cov).isCovariantDerivativeOn.add
    hfdg hgdf (x := x)
  have hleft := (covectorCovariantDerivative cov).isCovariantDerivativeOn.leibniz
    hdg (hf x) (x := x)
  have hright := (covectorCovariantDerivative cov).isCovariantDerivativeOn.leibniz
    hdf (hg x) (x := x)
  have hadd_uv := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hadd
  have hleft_uv := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hleft
  have hright_uv := congrArg (fun A : TM x →L[ℝ] T₁ x => A u v) hright
  unfold scalarHessian
  rw [hdiff, hadd_uv]
  simp only [add_apply]
  rw [hleft_uv, hright_uv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  have hfdu : (d% f x) u = scalarDifferential (I := I) f x u := rfl
  have hgdu : (d% g x) u = scalarDifferential (I := I) g x u := rfl
  rw [hfdu, hgdu]
  ring

/-- At a critical point of the second factor, the scalar Laplacian product
rule has no gradient cross term. -/
theorem scalarLaplacian_mul_of_second_differential_eq_zero
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {x : M}
    (hf : ∀ y, MDiffAt f y) (hg : ∀ y, MDiffAt g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x)
    (hgcritical : scalarDifferential (I := I) g x = 0) :
    scalarLaplacian cov (f * g) x =
      f x * scalarLaplacian cov g x + g x * scalarLaplacian cov f x := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov (f * g) x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov g x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov f x b]
  simp_rw [scalarHessian_mul_apply cov hf hg hdf hdg]
  simp only [hgcritical, zero_apply, mul_zero, zero_mul, add_zero]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

/-- Scalar Laplacians agree when the functions agree on an open neighborhood
and both differential sections are differentiable at the base point.  This is
the second-order germ principle needed when a quotient identity holds only on
the open set where its denominator is nonzero. -/
theorem scalarLaplacian_congr_on_open
    (cov : CovariantDerivative I E TM) {f g : M → ℝ} {U : Set M} {x : M}
    (hU : IsOpen U) (hx : x ∈ U) (hfg : ∀ y ∈ U, f y = g y)
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hdg : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) g y)) x) :
    scalarLaplacian cov f x = scalarLaplacian cov g x := by
  have hdiff : ∀ᶠ y in nhds x,
      scalarDifferential (I := I) f y = scalarDifferential (I := I) g y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    have hfg_y : f =ᶠ[nhds y] g := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hfg z hz
    exact hfg_y.mfderiv_eq
  have hcov := IsCovariantDerivativeOn.congr_of_eventuallyEq
    (hcov := (covectorCovariantDerivative cov).isCovariantDerivativeOnUniv)
    hdf hdg Filter.univ_mem hdiff
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let b := stdOrthonormalBasis ℝ (TM x)
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov f x b,
    scalarLaplacian_eq_sum_orthonormalBasis cov g x b]
  apply Finset.sum_congr rfl
  intro i _
  unfold scalarHessian
  rw [hcov]

end CovariantDerivative
