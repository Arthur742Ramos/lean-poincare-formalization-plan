module

public import PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.ConnectionLaplacian

/-!
# The scalar Laplace--Beltrami operator

This file constructs the scalar Hessian and Laplace--Beltrami operator from
the same induced-connection machinery used by the connection Laplacian on
covariant two-tensors.  For a scalar function `f`, its differential is the
section `df` of the cotangent bundle obtained from ordinary manifold
differentiation.  The Hessian is the covariant derivative `∇(df)`, and the
Laplacian is its metric trace.

The construction is intrinsic: the contraction uses the basis-independent
canonical covariant metric tensor.  The orthonormal-basis formula below is a
proved evaluation theorem rather than the definition of the operator.
-/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000

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

/-- The intrinsic differential of a scalar function, viewed as a cotangent
section. -/
def scalarDifferential (f : M → ℝ) (x : M) : T₁ x :=
  realLineCovariantDerivative (I := I) (M := M) f x

@[simp]
theorem scalarDifferential_apply (f : M → ℝ) (x : M) (u : TM x) :
    scalarDifferential (I := I) f x u = mvfderiv (I := I) f x u :=
  rfl

/-- The scalar Hessian `∇(df)`.  Its two arguments are respectively the
covariant-derivative direction and the cotangent slot. -/
def scalarHessian (cov : CovariantDerivative I E TM)
    (f : M → ℝ) (x : M) : TM x →L[ℝ] TM x →L[ℝ] ℝ :=
  covectorCovariantDerivative cov (scalarDifferential (I := I) f) x

/-- Expanded intrinsic formula for the scalar Hessian at a point where `df`
is differentiable as a cotangent section. -/
theorem scalarHessian_apply_of_mdifferentiableAt
    (cov : CovariantDerivative I E TM) (f : M → ℝ) {x : M}
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (u v : TM x) :
    scalarHessian cov f x u v =
      mvfderiv (I := I) (fun y =>
        scalarDifferential (I := I) f y
          (smoothExtend (I := I) (F := E) (V := TM) x v y)) x u
      - scalarDifferential (I := I) f x
          (cov (smoothExtend (I := I) (F := E) (V := TM) x v) x u) := by
  simp only [scalarHessian, covectorCovariantDerivative,
    inducedHomCovariantDerivative, dif_pos hdf, inducedHomAtOfMDiff_apply,
    realLineCovariantDerivative, trivialCovariantDerivative_apply]

/-- At a critical point the connection correction in the scalar Hessian
vanishes. -/
theorem scalarHessian_apply_of_mdifferentiableAt_of_differential_eq_zero
    (cov : CovariantDerivative I E TM) (f : M → ℝ) {x : M}
    (hdf : MDiffAt
      (fun y => TotalSpace.mk' (E →L[ℝ] ℝ) (E := T₁) y
        (scalarDifferential (I := I) f y)) x)
    (hcritical : scalarDifferential (I := I) f x = 0)
    (u v : TM x) :
    scalarHessian cov f x u v =
      mvfderiv (I := I) (fun y =>
        scalarDifferential (I := I) f y
          (smoothExtend (I := I) (F := E) (V := TM) x v y)) x u := by
  rw [scalarHessian_apply_of_mdifferentiableAt cov f hdf u v, hcritical]
  simp

/-- The scalar Laplace--Beltrami operator `tr_g(∇²f)`, with the heat
equation sign convention `+∑ᵢ ∂ᵢ²`. -/
def scalarLaplacian (cov : CovariantDerivative I E TM)
    (f : M → ℝ) (x : M) : ℝ :=
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  let B := scalarHessian cov f x
  let L : TM x →ₗ[ℝ] TM x →ₗ[ℝ] ℝ :=
    { toFun := fun u => (B u).toLinearMap
      map_add' := by
        intro u v
        ext w
        simp
      map_smul' := by
        intro c u
        ext w
        simp }
  TensorProduct.lift L (InnerProductSpace.canonicalCovariantTensor (TM x))

/-- Evaluation of the scalar Laplacian using any orthonormal basis. -/
theorem scalarLaplacian_eq_sum_orthonormalBasis
    (cov : CovariantDerivative I E TM) (f : M → ℝ) (x : M)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) :
    scalarLaplacian cov f x =
      ∑ i, scalarHessian cov f x (b i) (b i) := by
  let _ : FiniteDimensional ℝ (TM x) :=
    VectorBundle.finiteDimensional ℝ E TM x
  rw [scalarLaplacian,
    InnerProductSpace.canonicalCovariantTensor_eq_sum (TM x) b, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rfl

@[simp]
theorem scalarLaplacian_apply
    (cov : CovariantDerivative I E TM) (f : M → ℝ) (x : M) :
    scalarLaplacian cov f x =
      letI : FiniteDimensional ℝ (TM x) :=
        VectorBundle.finiteDimensional ℝ E TM x
      let b := stdOrthonormalBasis ℝ (TM x)
      ∑ i : Fin (Module.finrank ℝ (TM x)),
        scalarHessian cov f x (b i) (b i) := by
  rw [scalarLaplacian_eq_sum_orthonormalBasis cov f x
    (stdOrthonormalBasis ℝ (TM x))]

end CovariantDerivative
